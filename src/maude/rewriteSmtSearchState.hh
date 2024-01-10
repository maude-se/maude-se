//
//	Class for searching for one step rewrites within a DAG.
//
#ifndef _rewriteSmtSearchState_hh_
#define _rewriteSmtSearchState_hh_
#include "gmpxx.h"
#include "stack.hh"
#include "cacheableState.hh"
#include "positionState.hh"
#include "rewritingContext.hh"
#include <map>

class RewriteSmtSearchState : public CacheableState, public PositionState
{
  NO_COPYING(RewriteSmtSearchState);

public:
  enum Flags
  {
    ALLOW_NONEXEC = 32,
    SET_UNREWRITABLE = 256,

    GC_CONTEXT = 2,      // delete context in our dtor
    GC_SUBSTITUTION = 4, // delete substitution in our dtor
    IGNORE_CONDITION = 8 // ignore conditions of conditional PreEquations
  };
  //
  //	context is passed through to SearchState where it is used to construct
  //	matching substitutions in.
  //
  //	label may be UNDEFINED to make any rule usable.
  //
  //	maxDepth may be NONE to force at top rewrites without extension;
  //	otherwise rewriting is done with extension and maxDepth may be
  //	UNBOUNDED to indicate no bound.
  //
  RewriteSmtSearchState(RewritingContext *context,
                        FreshVariableGenerator *freshVariableGenerator,
                        const mpz_class &avoidVariableNumber,
                        int label = UNDEFINED,
                        int flags = 0,
                        int minDepth = 0,
                        int maxDepth = NONE);
  ~RewriteSmtSearchState();

  bool findNextRewrite();
  bool findFirstSolution(const PreEquation *preEqn, LhsAutomaton *automaton);
  bool findNextSolution();

  const mpz_class &getMaxVariableNumber() const;

  Rule *getRule() const;
  DagNode *getReplacement() const;

  RewritingContext *getContext() const;
  void transferCountTo(RewritingContext &recipient);

  //
  //	Takes responsibility for deleting the Term and DagRoot objects,
  //	if instance was created with GC_SUBSTITUTION flag.
  //
  void setInitialSubstitution(Vector<Term *> &variables, Vector<DagRoot *> &values);

  typedef map<DagNode *, DagNode *> Mapping;
  Mapping mapping;

private:
  bool initSubstitution(const VariableInfo &varInfo);
  bool hasCondition(const PreEquation *preEqn);

  RewritingContext *const context;
  const PreEquation *preEquation;
  //
  //	Initial (partial) substitution.
  //
  Vector<Term *> substVariables;
  Vector<DagRoot *> substValues;
  //
  //	For backtracking over matches.
  //
  Subproblem *matchingSubproblem;
  //
  //	For backtracking of solutions to a rule condition.
  //
  int trialRef;
  Stack<ConditionState *> conditionStack;

  FreshVariableGenerator *freshVariableGenerator;

  const mpz_class &avoidVariableNumber;
  mpz_class newVariableNumber; // number of largest fresh variables that appears in newState

  const int label;
  const bool withExtension;
  int ruleIndex;
};

inline const mpz_class &
RewriteSmtSearchState::getMaxVariableNumber() const
{
  return newVariableNumber;
}

inline RewritingContext *
RewriteSmtSearchState::getContext() const
{
  return context;
}

inline void
RewriteSmtSearchState::transferCountTo(RewritingContext &recipient)
{
  recipient.transferCountFrom(*context);
}

inline void
RewriteSmtSearchState::setInitialSubstitution(Vector<Term *> &variables, Vector<DagRoot *> &values)
{
  substVariables.swap(variables);
  substValues.swap(values);
}

#endif
