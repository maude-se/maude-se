//
//	Implementation for class RewriteSmtSequenceSearch.
//

//	utility stuff
#include "macros.hh"
#include "vector.hh"

//	forward declarations
#include "interface.hh"
#include "core.hh"
#include "higher.hh"
#include "mixfix.hh"

//	interface class definitions
#include "symbol.hh"
#include "dagNode.hh"
#include "rawDagArgumentIterator.hh"

//	core class definitions
#include "rewritingContext.hh"
#include "pattern.hh"
#include "rewriteSmtSearchState.hh"
#include "rewriteSmtSequenceSearch.hh"

#include "../StrategyLanguage/strategyLanguage.hh"
#include "../Mixfix/mixfixModule.hh"
#include "freshVariableSource.hh"
#include "token.hh"
#include "equalityConditionFragment.hh" // for printing purpose ...

RewriteSmtSequenceSearch::RewriteSmtSequenceSearch(RewritingContext *initial,
                                                   SearchType searchType,
                                                   Pattern *goal,
                                                   const SMT_Info &smtInfo,
                                                   SMT_EngineWrapper *engine,
                                                   FreshVariableGenerator *freshVariableGenerator,
                                                   PyObject *connector, PyObject *converter,
                                                   bool fold, bool merge,
                                                   int maxDepth,
                                                   const mpz_class &avoidVariableNumber)
    : SmtStateTransitionGraph(initial, smtInfo, engine, freshVariableGenerator, connector, converter, fold, merge, avoidVariableNumber),
      goal(goal),
      maxDepth((searchType == ONE_STEP) ? 1 : maxDepth)
{
  // newVariableNumber = avoidVariableNumber;
  // Verbose("make new goal " << goal->getLhs()->term2Dag());
  DagNode *goalAbst = smtInfo.getTrueSymbol()->makeDagNode();
  DagNode *newGoal = makeAbstBuiltin(goal->getLhs()->term2Dag(), &goalAbst, initial);

  goalAbstConst = convDag2Term(goalAbst);

  Term *newGoalTerm = newGoal->symbol()->termify(newGoal);
  Verbose("abst const " << goalAbst);
  Verbose("make new goal " << newGoalTerm);
  trueGoal = new Pattern(newGoalTerm, false);

  PyObject *goalAbstConstStr = PyObject_Repr(goalAbstConst);
  const char *gS = PyUnicode_AsUTF8(goalAbstConstStr);
  Verbose("python const " << gS);

  initState->constTermIndex = consTermSeen[initState->hashConsIndex].size();
  DagNode *initConst = makeConstraintFromCondition(goal->getCondition());

  PyObject *initRi = convDag2Term(initConst);

  PyObject *next = PyObject_CallMethodObjArgs(connector, add_const, Py_None, initRi, NULL);
  if (next == nullptr)
  {
    IssueWarning("failed to make a constraint22");
  }
  ConstrainedTerm *t = new ConstrainedTerm(initial->root(), next);

  consTermSeen.insert(ConstrainedTermMap::value_type(initState->hashConsIndex, Vector<ConstrainedTerm *>()));
  consTermSeen[initState->hashConsIndex].append(t);

  findSMT_Variables();

  newVariableNumber = 0;

  finalConstraint = 0;
  matchState = 0;
  explore = -1;
  exploreDepth = -1;
  firstDeeperNodeNr = 0;
  needToTryInitialState = (searchType == ANY_STEPS);
  reachingInitialStateOK = (searchType == AT_LEAST_ONE_STEP || searchType == ONE_STEP);
  normalFormNeeded = (searchType == NORMAL_FORM);
  nextArc = NONE;
}

RewriteSmtSequenceSearch::~RewriteSmtSequenceSearch()
{
  delete matchState;
  delete goal;
  delete engine;

  // for (auto& i : smtVarDags){
  //   if (i.second) delete i.second;
  // }
  unlink();
  // delete trueGoal; // virtual do not call this...
}

void RewriteSmtSequenceSearch::markReachableNodes()
{
  // cout << "marking is called" << endl;
  //
  //	Protect dagnode versions of any SMT variables in the pattern.
  //
  for (auto &i : smtVarDags)
    i.second->mark();
  //
  //	Constraints aren't otherwise protected once the search object
  //	they were passed to is deleted.
  //
  for (State *s : seen)
  {
    s->dag->mark();
    // cout << "marking " << s->dag << endl;
  }

  for (auto it = consTermSeen.begin(); it != consTermSeen.end(); it++)
  {
    for (ConstrainedTerm *c : it->second)
    {
      c->dag->mark();
      // for (auto m : c->mapping){
      //   m.first->mark();
      //   m.second->mark();
      // }
    }
  }
  //
  //	Need to protect any final constraint we made.
  //
  // if (finalConstraint != 0)
  //   finalConstraint->mark();
}

DagNode *RewriteSmtSequenceSearch::makeAbstBuiltin(DagNode *dag, DagNode **goalAbstConstDag, RewritingContext *initial)
{
  // some type of constant dag nodes can return null
  // e.g., FreeDagNode
  RawDagArgumentIterator *arg = dag->arguments();
  if (arg == nullptr)
  {
    dag->computeTrueSort(*initial);
    Sort *dag_sort = dag->getSort();
    SMT_Info::SMT_Type type = smtInfo.getType(dag_sort);
    if (type != SMT_Info::NOT_SMT)
    {
      Symbol *baseVariableSymbol = freshVariableGenerator->getBaseVariableSymbol(dag_sort);

      string newNameString = "#newVar$";
      char *name = mpz_get_str(0, 10, newVariableNumber.get_mpz_t());
      newNameString += name;
      free(name);
      int newId = Token::encode(newNameString.c_str());
      DagNode *newVariable = new VariableDagNode(baseVariableSymbol, newId, NONE);
      newVariable->computeTrueSort(*initial);

      ++newVariableNumber;

      Symbol *eqOp = smtInfo.getEqualityOperator(dag, newVariable);
      if (eqOp == 0)
      {
        IssueWarning(dag << ": no SMT equality operator available for this type");
      }
      Vector<DagNode *> args(2);
      args[0] = dag;
      args[1] = newVariable;
      DagNode *eqConst = eqOp->makeDagNode(args);

      Vector<DagNode *> args2(2);
      args2[0] = *goalAbstConstDag;
      args2[1] = eqConst;
      *goalAbstConstDag = smtInfo.getConjunctionOperator()->makeDagNode(args2);

      return newVariable;
    }
    else
    {
      return dag;
    }
  }
  else
  {
    Vector<DagNode *> newChild;
    while (arg->valid())
    {
      DagNode *lhs = arg->argument();
      lhs->computeTrueSort(*initial);
      // Verbose("call this " << lhs << ": " << lhs->getSort());
      // check SMT sort
      Sort *lhs_sort = lhs->getSort();
      SMT_Info::SMT_Type type = smtInfo.getType(lhs_sort);
      if (type != SMT_Info::NOT_SMT)
      {
        // make a new fresh variable

        Symbol *baseVariableSymbol = freshVariableGenerator->getBaseVariableSymbol(lhs_sort);

        string newNameString = "#newVar$";
        char *name = mpz_get_str(0, 10, newVariableNumber.get_mpz_t());
        newNameString += name;
        free(name);
        int newId = Token::encode(newNameString.c_str());
        DagNode *newVariable = new VariableDagNode(baseVariableSymbol, newId, NONE);
        newVariable->computeTrueSort(*initial);

        Verbose("      new variable " << newVariable);
        // delete freshVariableSource;
        ++newVariableNumber;

        Symbol *eqOp = smtInfo.getEqualityOperator(lhs, newVariable);
        if (eqOp == 0)
        {
          IssueWarning(lhs << ": no SMT equality operator available for this type");
          continue;
        }
        Vector<DagNode *> args(2);
        args[0] = lhs;
        args[1] = newVariable;
        DagNode *eqConst = eqOp->makeDagNode(args);

        Vector<DagNode *> args2(2);
        args2[0] = *goalAbstConstDag;
        args2[1] = eqConst;
        *goalAbstConstDag = smtInfo.getConjunctionOperator()->makeDagNode(args2);
        newChild.append(newVariable);
      }
      else
      {
        newChild.append(makeAbstBuiltin(lhs, goalAbstConstDag, initial));
      }
      arg->next();
    }

    return dag->symbol()->makeDagNode(newChild);
  }
}

bool RewriteSmtSequenceSearch::findNextMatch()
{
  if (matchState != 0)
    goto tryMatch; // non-startup case

  for (;;)
  {
    stateNr = findNextInterestingState();
    if (stateNr == NONE)
      break;

    Verbose("\n");
    Verbose("  goal original : " << goal->getLhs() << " (" << trueGoal->getLhs() << ") which should match with " << getStateDag(stateNr) << " index : " << stateNr);

    for (ConditionFragment *cf : goal->getCondition())
    {
      EqualityConditionFragment *ag = dynamic_cast<EqualityConditionFragment *>(cf);
      Verbose("  " << ag->getLhs() << " = " << ag->getRhs());
    }

    matchState = new MatchSearchState(getContext()->makeSubcontext(getStateDag(stateNr)),
                                      trueGoal,
                                      MatchSearchState::GC_CONTEXT);
  tryMatch:
    bool foundMatch = matchState->findNextMatch();

    Verbose("found match : " << foundMatch);
    matchState->transferCountTo(*(getContext()));
    if (foundMatch && checkMatchConstraint(stateNr))
    {
      Verbose("goal sat with final constraint");
      return true;
    }

    delete matchState;
  }

  matchState = 0;
  return false;
}

int RewriteSmtSequenceSearch::findNextInterestingState()
{
  if (needToTryInitialState)
  {
    //
    //	Special case: return the initial state.
    //
    needToTryInitialState = false; // don't do this again
    return 0;
  }

  if (nextArc != NONE)
    goto exploreArcs;

  for (;;)
  {
    //
    //	Get next state to explore.
    //
    ++explore;
    if (explore == getNrStates())
      break;
    if (explore == firstDeeperNodeNr)
    {
      ++exploreDepth;
      if (normalFormNeeded)
      {
        if (maxDepth > 0 && exploreDepth > maxDepth)
          break;
      }
      else
      {
        if (exploreDepth == maxDepth)
          break;
      }
      firstDeeperNodeNr = getNrStates();
    }
    nextArc = 0;

  exploreArcs:
    int nrStates = getNrStates();
    int nextStateNr;
    while ((nextStateNr = getNextState(explore, nextArc)) != NONE)
    {
      ++nextArc;
      if (normalFormNeeded)
      {
        if (exploreDepth == maxDepth)
          break; // no point looking for further arcs
      }
      else
      {
        if (nextStateNr == nrStates)
        { // new state reached
          Verbose("add a new state " << nextStateNr);
          return nextStateNr;
        }
        if (nextStateNr == 0 && reachingInitialStateOK)
        {
          //
          //	We have arrived back at our initial state, but because
          //	we didn't try matching the initial state, we do it now.
          //
          reachingInitialStateOK = false; // don't do this again
          return 0;
        }
      }
    }
    if (getContext()->traceAbort())
      return NONE;
    if (normalFormNeeded && nextArc == 0)
    {
      nextArc = NONE;
      return explore;
    }
  }

  return NONE;
}

Rule *
RewriteSmtSequenceSearch::getStateRule(int stateNr) const
{
  const ArcMap &fwdArcs = getStateFwdArcs(getStateParent(stateNr));
  return *(fwdArcs.find(stateNr)->second.begin());
}

void RewriteSmtSequenceSearch::findSMT_Variables()
{
  //
  //	Find any SMT variables in the pattern, make dagnode versions and record their indices.
  //
  int nrVariables = trueGoal->getNrRealVariables();
  for (int i = 0; i < nrVariables; ++i)
  {
    VariableTerm *v = safeCast(VariableTerm *, trueGoal->index2Variable(i));
    VariableSymbol *vs = safeCast(VariableSymbol *, v->symbol());
    SMT_Info::SMT_Type type = smtInfo.getType(vs->getSort());
    if (type != SMT_Info::NOT_SMT)
    {
      smtVarIndices.insert(i);
      smtVarDags[i] = v->dagify2();
      // cout << "found " << smtVarDags[i] << endl;
    }
  }
  Verbose("found " << smtVarDags.size() << " SMT variables");
}

bool RewriteSmtSequenceSearch::checkMatchConstraint(int stateNr)
{
  //
  //	We have a matching substitution, but some of the bound variables may be SMT
  //	in which case they may be mentioned in the existing condition and we
  //	need to check that equality implied by the binding is satisfiable.
  //
  Vector<DagNode *> args(2);
  const Substitution *substitution = matchState->getContext();
  DagNode *matchConstraint = 0;
  for (auto &i : smtVarDags)
  {
    Verbose("smtVarDags " << i.first << " : " << i.second);
  }

  for (auto &i : smtVarDags)
  {
    DagNode *lhs = i.second;
    DagNode *rhs = substitution->value(i.first);
    //
    //	Make equality constraint.
    //
    Vector<DagNode *> args(2);
    args[0] = lhs;
    args[1] = rhs;
    DagNode *equalityConstraint = smtInfo.getEqualityOperator(lhs, rhs)->makeDagNode(args);
    //
    //	Conjunct it in if needed.
    //
    if (matchConstraint == 0)
    {
      matchConstraint = equalityConstraint;
    }
    else
    {
      args[0] = matchConstraint;
      args[1] = equalityConstraint;
      matchConstraint = smtInfo.getConjunctionOperator()->makeDagNode(args);
    }
    Verbose("matchConstraint: " << matchConstraint);
  }

  if (matchConstraint != 0)
  {
    PyObject *matchTerm = convDag2Term(matchConstraint);
    ConstrainedTerm *constrained = consTermSeen[seen[stateNr]->hashConsIndex][seen[stateNr]->constTermIndex];
    PyObject *pyConst = constrained->constraint;

    PyObject *goalAbstConstStr = PyObject_Repr(goalAbstConst);
    const char *gS = PyUnicode_AsUTF8(goalAbstConstStr);
    Verbose("python const " << gS);

    PyObject *check_sat_r = PyObject_CallMethodObjArgs(connector, check_sat, pyConst, matchTerm, goalAbstConst, NULL);
    if (check_sat_r != nullptr)
    {
      if (PyObject_RichCompareBool(check_sat_r, Py_True, Py_EQ) <= 0)
      {
        return false;
      }
    }
    else
    {
      IssueWarning("fail to checkSat");
    }
  }
  return true;
}

DagNode *
RewriteSmtSequenceSearch::makeConstraintFromCondition(const Vector<ConditionFragment *> &condition)
{
  Vector<DagNode *> args(2);
  DagNode *constraint = 0;

  for (ConditionFragment *cf : condition)
  {
    //
    //	Check to see that condition fragment is of the form t1 = t2.
    //
    EqualityConditionFragment *fragment = dynamic_cast<EqualityConditionFragment *>(cf);
    if (fragment == 0)
    {
      IssueWarning("goal... : condition fragment " << cf << " not supported for searching modulo SMT.");
      continue;
    }
    //
    //	Dagify and optimize out equal case.
    //
    fragment->normalize(false);
    DagNode *lhs = fragment->getLhs()->term2Dag();
    DagNode *rhs = fragment->getRhs()->term2Dag();
    if (lhs->equal(rhs))
      continue;
    //
    //	Generate an SMT clause.
    //
    DagNode *clause;
    if (rhs->symbol() == smtInfo.getTrueSymbol())
      clause = lhs; // optimize QF = true
    else if (lhs->symbol() == smtInfo.getTrueSymbol())
      clause = rhs; // optimize true = QF
    else
    {
      Symbol *eqOp = smtInfo.getEqualityOperator(lhs, rhs);
      if (eqOp == 0)
      {
        IssueWarning(*(fragment->getLhs()) << ": no SMT equality operator available for condition fragment " << cf);
        continue;
      }
      args[0] = lhs;
      args[1] = rhs;
      clause = eqOp->makeDagNode(args);
    }
    //
    //	Conjunct with existing constraint.
    //
    if (constraint == 0)
      constraint = clause;
    else
    {
      args[0] = constraint;
      args[1] = clause;
      constraint = smtInfo.getConjunctionOperator()->makeDagNode(args);
    }
  }
  //
  //	Default to true.
  //
  return constraint == 0 ? smtInfo.getTrueSymbol()->makeDagNode() : constraint;
}