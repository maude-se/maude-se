//
//	Class for building a state transition graph on-the-fly, with hash consing.
//
#ifndef _smtStateTransitionGraph_hh_
#define _smtStateTransitionGraph_hh_
#include <set>
#include <map>
#include "SMT_Info.hh"
#include "hashConsSet.hh"
#include "rewritingContext.hh"
// #include "narrowingFolder.hh"
#include "folder.hh"

#include "variableDagNode.hh"
#include "SMT_EngineWrapper.hh"

#include "Python.h"
#include <ctime>

class SmtStateTransitionGraph
{
  NO_COPYING(SmtStateTransitionGraph);

public:
  typedef map<int, set<Rule *>> ArcMap;
  typedef map<DagNode *, DagNode *> Mapping;

  SmtStateTransitionGraph(RewritingContext *initial,
                          const SMT_Info &smtInfo, SMT_EngineWrapper *engine,
                          FreshVariableGenerator *freshVariableGenerator, PyObject *connector, PyObject *converter, bool fold, bool merge,
                          const mpz_class &avoidVariableNumber = 0);
  ~SmtStateTransitionGraph();

  int getNrStates() const;
  int getNextState(int stateNr, int index);
  DagNode *getStateDag(int stateNr);
  PyObject* getStateConst(int stateNr);
  int getStateDepth(int stateNr) const;
  const ArcMap &getStateFwdArcs(int stateNr) const;
  //
  //	Stuff needed for search.
  //
  RewritingContext *getContext();
  void transferCountTo(RewritingContext &recipient);
  int getStateParent(int stateNr) const;

protected:
  struct State
  {
    State(int hashConsIndex, int parent);
    const int parent;

    int constTermIndex;

    mpz_class avoidVariableNumber;
    const int hashConsIndex;
    RewriteSmtSearchState *rewriteState;

    Vector<int> nextStates;
    bool fullyExplored;
    ArcMap fwdArcs;

    DagNode *dag;
    int depth;
  };

  struct ConstrainedTerm
  {
    ConstrainedTerm(DagNode *dag, PyObject *constraint);
    ~ConstrainedTerm();

    DagNode *dag;
    PyObject *constraint;
    // for matching
    VariableInfo variableInfo;
    Term *term;
    LhsAutomaton *matchingAutomaton;
    int nrMatchingVariables; // number of variables needed for matching; includes any abstraction variables

    bool findMatching(DagNode *other, SmtStateTransitionGraph *pointer);
    PyObject *subst;
  };

  bool fold;
  bool merge;

  // key: State index
  typedef map<int, Vector<ConstrainedTerm *>> ConstrainedTermMap;

  // state index , const id?
  typedef tuple<int, int> StateId;
  typedef map<StateId, int> Map2Seen;

  // void insertNewState(int parent);
  const SMT_Info &smtInfo;         // information about SMT sort; might get folded into wrapper
  SMT_EngineWrapper *const engine; // wrapper to call the SMT engine
  FreshVariableGenerator *freshVariableGenerator;

  PyObject *dag2maudeTerm(DagNode *dag);
  DagNode *maudeTerm2dag(PyObject *term);

  State *initState;
  int counter;
  RewritingContext *initial;

  ConstrainedTermMap consTermSeen;
  Vector<State *> seen;

  // Vector<int> hashCons2seen;  // partial map of hashCons indices to state indices
  // HashConsSet hashConsSet;
  Map2Seen map2seen;

  Folder stateCollection;

protected:
  void printStateConst(int depth);

protected:
  PyObject *mainModule;
  PyObject *maudeModule;
  PyObject *stateManager;
  PyObject *solver;
  PyObject *termConverter;
  PyObject *connector;
  PyObject *easySubst;

  // state manager
  PyObject *subsume;
  PyObject *mergeF;

  // solver method
  PyObject *push;
  PyObject *check_sat;
  PyObject *add;
  PyObject *pop;
  PyObject *make_assignment;

  PyObject *sat;
  PyObject *unsat;

  PyObject *prefix1;
  PyObject *prefix2;

  // termConv method

  PyObject *dag2term;
  PyObject *term2dag;

  // Connector
  PyObject *add_const;
  PyObject *makeConjunct;
  PyObject *makeEq;
  PyObject *add2match;
  PyObject *clearMatch;

  // Easy subst
  PyObject *insert;
  PyObject *instantiate;

  // for sort
  Sort *boolSort;

  //
  typedef map<const char *, PyObject *> SortMap;
  typedef map<const char *, PyObject *> FuncMap;

  SortMap sortMap;
  FuncMap funcMap;

  double nextTime;
  double rewriteTime;
  double elseTime;

protected:
  PyObject *convDag2Term(DagNode *dag);
};

inline SmtStateTransitionGraph::State::State(int hashConsIndex, int parent)
    : hashConsIndex(hashConsIndex),
      parent(parent)
{
  rewriteState = 0;
  fullyExplored = false;
}

inline int
SmtStateTransitionGraph::getNrStates() const
{
  return seen.size();
}

inline DagNode *
SmtStateTransitionGraph::getStateDag(int stateNr)
{
  // TODO: return const DAG
  if (seen.size() <= stateNr)
  {
    IssueWarning("not found in seen states");
  }

  State *state = seen[stateNr];

  if (consTermSeen[state->hashConsIndex].size() <= state->constTermIndex)
  {
    IssueWarning("consTermseen length wrong");
  }
  ConstrainedTerm *ct = consTermSeen[state->hashConsIndex][state->constTermIndex];
  return ct->dag;
}

inline PyObject *
SmtStateTransitionGraph::getStateConst(int stateNr)
{
  // TODO: return const DAG
  if (seen.size() <= stateNr)
  {
    IssueWarning("not found in seen states");
  }

  State *state = seen[stateNr];

  if (consTermSeen[state->hashConsIndex].size() <= state->constTermIndex)
  {
    IssueWarning("consTermseen length wrong");
  }
  ConstrainedTerm *ct = consTermSeen[state->hashConsIndex][state->constTermIndex];
  return ct->constraint;
}

inline int SmtStateTransitionGraph::getStateDepth(int stateNr) const
{
  return seen[stateNr]->depth;
}

inline const SmtStateTransitionGraph::ArcMap &
SmtStateTransitionGraph::getStateFwdArcs(int stateNr) const
{
  return seen[stateNr]->fwdArcs;
}

inline RewritingContext *
SmtStateTransitionGraph::getContext()
{
  return initial;
}

inline void
SmtStateTransitionGraph::transferCountTo(RewritingContext &recipient)
{
  recipient.transferCountFrom(*initial);
}

inline int
SmtStateTransitionGraph::getStateParent(int stateNr) const
{
  return seen[stateNr]->parent;
}

inline PyObject *SmtStateTransitionGraph::dag2maudeTerm(DagNode *dag)
{
  PyObject *capsuleObj = PyCapsule_New((void *)(dag), NULL, NULL);
  PyObject *pyDag = PyObject_CallMethodObjArgs(maudeModule, dag2term, capsuleObj, NULL);
  if (pyDag == nullptr)
  {
    IssueWarning("failed to call maude.dag2term");
  }
  return pyDag;
}

inline DagNode *SmtStateTransitionGraph::maudeTerm2dag(PyObject *term)
{
  PyObject *dagCapsuleObj = PyObject_CallMethodObjArgs(maudeModule, term2dag, term, NULL);
  if (dagCapsuleObj == nullptr)
  {
    IssueWarning("failed to call maude.term2dag");
  }
  DagNode *dag = (DagNode *)(PyCapsule_GetPointer(dagCapsuleObj, NULL));
  // Py_DECREF(dagCapsuleObj);
  return dag;
}

inline PyObject *SmtStateTransitionGraph::convDag2Term(DagNode *dag)
{
  // call Python the dag2Term method of the Converter class
  PyObject *maudeTerm = dag2maudeTerm(dag);
  clock_t loop_s = clock();
  PyObject *term = PyObject_CallMethodObjArgs(termConverter, dag2term, maudeTerm, NULL);
  clock_t loop_e = clock();
  elseTime += (double)(loop_e - loop_s);
  if (term == nullptr)
  {
    IssueWarning("failed to call Converter's dag2term for " << dag);
  }
  // remove a maude object
  // Py_DECREF(maudeTerm);
  Py_XINCREF(term);
  return term;
}

#endif
