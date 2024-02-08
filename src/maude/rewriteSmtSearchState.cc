//
//	Implementation for class RewriteSmtSearchState.
//

//	utility stuff
#include "macros.hh"
#include "vector.hh"

//	forward declarations
#include "interface.hh"
#include "core.hh"
#include "mixfix.hh"

//	interface class definitions
#include "symbol.hh"
#include "dagNode.hh"
#include "subproblem.hh"
#include "variableDagNode.hh"
#include "token.hh"

//	core class definitions
#include "rewritingContext.hh"
#include "lhsAutomaton.hh"
// #include "rhsAutomaton.hh"
#include "preEquation.hh"
#include "conditionState.hh"
#include "dagRoot.hh"
#include "rule.hh"
#include "rewriteSmtSearchState.hh"

#include "freshVariableGenerator.hh"

RewriteSmtSearchState::RewriteSmtSearchState(
    RewritingContext *context,
    FreshVariableGenerator *freshVariableGenerator,
    const mpz_class &avoidVariableNumber,
    int label,
    int flags,
    int minDepth,
    int maxDepth)
    : freshVariableGenerator(freshVariableGenerator), avoidVariableNumber(avoidVariableNumber),
      label(label), withExtension(maxDepth >= 0), PositionState(context->root(), flags | RESPECT_FROZEN, minDepth, maxDepth),
      context(context)
{
  matchingSubproblem = 0;

  Assert(label == NONE || !(getFlags() & SET_UNREWRITABLE),
         "shouldn't set unrewritable flag if only looking at rules with a given label");
  ruleIndex = -1;
}

RewriteSmtSearchState::~RewriteSmtSearchState()
{
  //
  //	Delete stuff we created.
  //
  while (!conditionStack.empty())
  {
    delete conditionStack.top();
    conditionStack.pop();
  }
  delete matchingSubproblem;
  //
  //	Delete stuff entrusted to us by our creator.
  //
  if (getFlags() & GC_SUBSTITUTION)
  {
    int nrUserVars = substVariables.length();
    for (int i = 0; i < nrUserVars; i++)
    {
      substVariables[i]->deepSelfDestruct();
      delete substValues[i];
    }
  }
  if (getFlags() & GC_CONTEXT)
    delete context;
}

local_inline bool
RewriteSmtSearchState::hasCondition(const PreEquation *preEqn)
{
  //
  //	First test most likely to fail so we do it first.
  //
  return preEqn->hasCondition() && !(getFlags() & IGNORE_CONDITION);
}

Rule *
RewriteSmtSearchState::getRule() const
{
  return (getDagNode()->symbol()->getRules())[ruleIndex];
}

DagNode *
RewriteSmtSearchState::getReplacement() const
{
  return getRule()->getRhsBuilder().construct(*(getContext()));
}

bool RewriteSmtSearchState::findNextRewrite()
{
  // Verbose("overwrite find next rewrite??");
  bool rewriteSeenAtCurrentPosition;
  if (ruleIndex > -1)
  {
    if (findNextSolution())
      return true;
    rewriteSeenAtCurrentPosition = true;
  }
  else
  {
    if (!findNextPosition())
      return false;
    rewriteSeenAtCurrentPosition = false;
  }
  ++ruleIndex;
  bool allowNonexec = getFlags() & ALLOW_NONEXEC;
  allowNonexec = true;
  do
  {
    DagNode *d = getDagNode();
    if (!(d->isUnrewritable()))
    {
      const Vector<Rule *> &rules = d->symbol()->getRules();
      for (int nrRules = rules.length(); ruleIndex < nrRules; ruleIndex++)
      {
        Rule *rl = rules[ruleIndex];
        if ((allowNonexec || !(rl->isNonexec())) &&
            (label == UNDEFINED || rl->getLabel().id() == label))
        {
          LhsAutomaton *a = withExtension ? rl->getExtLhsAutomaton() : rl->getNonExtLhsAutomaton();
          // cerr << "trying " << rl << " at " << " positionIndex " <<  getPositionIndex() << " dagNode " << getDagNode() << endl;
          Verbose("trying " << rl << " at "
                            << " positionIndex " << getPositionIndex() << " dagNode " << getDagNode());
          if (findFirstSolution(rl, a))
            return true;
        }
      }
      if (!rewriteSeenAtCurrentPosition && (getFlags() & SET_UNREWRITABLE))
        d->setUnrewritable();
    }
    rewriteSeenAtCurrentPosition = false;
    ruleIndex = 0;
  } while (findNextPosition());
  return false;
}

bool RewriteSmtSearchState::findFirstSolution(const PreEquation *preEqn, LhsAutomaton *automaton)
{
  // Verbose("first solution this is called?");
  delete matchingSubproblem;
  matchingSubproblem = 0;
  DagNode *subject = getDagNode();
  //
  //	If we're searching with nonzero maxDepth it is reasonable for pattern
  //	and subject to be in different components.
  //
  if (preEqn->getLhs()->getComponent() == subject->symbol()->rangeComponent())
  {
    context->clear(preEqn->getNrProtectedVariables());
    if (initSubstitution(*preEqn) &&
        automaton->match(subject, *context, matchingSubproblem, getExtensionInfo()) &&
        (matchingSubproblem == 0 ||
         matchingSubproblem->solve(true, *context)) &&
        (!hasCondition(preEqn) ||
         preEqn->checkCondition(true,
                                subject,
                                *context,
                                matchingSubproblem,
                                trialRef,
                                conditionStack)))
    {
      preEquation = preEqn;
      // Verbose(" rule matching succeedss in smt search state");
      return true;
    }
  }
  return false;
}

bool RewriteSmtSearchState::findNextSolution()
{
  if (hasCondition(preEquation))
  {
    return preEquation->checkCondition(false,
                                       getDagNode(),
                                       *context,
                                       matchingSubproblem,
                                       trialRef,
                                       conditionStack);
  }
  else
    return matchingSubproblem != 0 && matchingSubproblem->solve(false, *context);
}

bool RewriteSmtSearchState::initSubstitution(const VariableInfo &varInfo)
{
  // mapping.clear();
  // Verbose("    inside initSubstitution from rewrite smt search state");
  if (substVariables.empty())
  {
    newVariableNumber = avoidVariableNumber;
    if (varInfo.getUnboundVariables().empty())
      return true;
    // Verbose("    Subst variable empty and "<<bb << " with # variable " << varInfo.getNrRealVariables());

    const NatSet &unboundSet = varInfo.getUnboundVariables();
    size_t nrVars = varInfo.getNrRealVariables();

    for (size_t k = 0; k < nrVars; k++)
    {
      if (unboundSet.contains(k))
      {
        ++newVariableNumber;
        Symbol *baseSymbol = varInfo.index2Variable(k)->symbol();

        string newNameString = "%%ubVar$";
        char *name = mpz_get_str(0, 10, newVariableNumber.get_mpz_t());
        newNameString += name;
        free(name);
        int newId = Token::encode(newNameString.c_str());
        
        DagNode *v = new VariableDagNode(baseSymbol, newId, NONE);
        v->computeTrueSort(*context);
        context->bind(k, v);
        Verbose("      unbound Variable " << varInfo.index2Variable(k) << " is bound to " << (DagNode *)v);
      }
    }

    return true;
  }
  int nrUserVars = substVariables.length();
  int nrVars = varInfo.getNrRealVariables();
  NatSet bound;
  for (int i = 0; i < nrUserVars; i++)
  {
    Term *userVar = substVariables[i];
    for (int j = 0; j < nrVars; j++)
    {
      if (userVar->equal(varInfo.index2Variable(j)))
      {
        context->bind(j, substValues[i]->getNode());
        bound.insert(j);
        break;
      }
    }
  }
  return bound.contains(varInfo.getUnboundVariables());
}
