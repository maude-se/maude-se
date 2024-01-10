//
//	Class for searching for sequences of rewrites within a DAG.
//
#ifndef _rewriteSmtSequenceSearch_hh_
#define _rewriteSmtSequenceSearch_hh_
#include "natSet.hh"
#include "sequenceSearch.hh"
#include "smtStateTransitionGraph.hh"
#include "matchSearchState.hh"
#include "simpleRootContainer.hh"

class RewriteSmtSequenceSearch : public SequenceSearch, public SmtStateTransitionGraph, public SimpleRootContainer
{
  NO_COPYING(RewriteSmtSequenceSearch);

public:
  RewriteSmtSequenceSearch(RewritingContext *initial,
                           SearchType searchType,
                           Pattern *goal,
                           const SMT_Info &smtInfo,
                           SMT_EngineWrapper *engine,
                           FreshVariableGenerator *freshVariableGenerator,
                           PyObject *connector, PyObject *converter,
                           bool fold = true, bool merge = false,
                           int maxDepth = -1,
                           const mpz_class &avoidVariableNumber = 0);
  ~RewriteSmtSequenceSearch();

  bool findNextMatch();
  const Pattern *getGoal() const;
  Rule *getStateRule(int stateNr) const;
  int getStateNr() const;
  const Substitution *getSubstitution() const;
  DagNode *getFinalConstraint() const;

private:
  int findNextInterestingState();

  DagNode *makeAbstBuiltin(DagNode *dag, DagNode **goalAbstConstDag, RewritingContext *initial);
  PyObject *goalAbstConst;
  PyObject *finalConstraint;

  DagNode *makeConstraintFromCondition(
      const Vector<ConditionFragment *> &condition);

  void findSMT_Variables();
  bool checkMatchConstraint(int stateNr);
  void markReachableNodes();

  typedef map<int, DagNode *> SMT_VarDags;

  //
  //	Information abound SMT variables in target, computed at initialization.
  //
  NatSet smtVarIndices;
  SMT_VarDags smtVarDags;

  mpz_class newVariableNumber;

  Pattern *const goal;
  Pattern *trueGoal;
  const int maxDepth;
  int explore;
  int exploreDepth;
  int firstDeeperNodeNr;
  int nextArc;
  bool needToTryInitialState;
  bool reachingInitialStateOK;
  bool normalFormNeeded;
  MatchSearchState *matchState;
  int stateNr;
};

inline const Pattern *
RewriteSmtSequenceSearch::getGoal() const
{
  return goal;
}

inline const Substitution *
RewriteSmtSequenceSearch::getSubstitution() const
{
  return matchState->getContext();
}

inline int
RewriteSmtSequenceSearch::getStateNr() const
{
  return stateNr;
}

inline DagNode *
RewriteSmtSequenceSearch::getFinalConstraint() const
{
  return nullptr;
}
#endif
