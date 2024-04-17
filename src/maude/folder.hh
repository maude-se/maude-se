//
//	Class for folding and maintaining the history of a search.
//
#ifndef _folder_hh_
#define _folder_hh_
#include <set>
#include <map>
#include "simpleRootContainer.hh"

class Folder : private SimpleRootContainer
{
  NO_COPYING(Folder);

public:
  Folder(bool fold);
  ~Folder();

  bool insertState(int index, DagNode *state, int parentIndex, int *gIdx);
  void getState(int index, DagNode *&state) const;

private:
  struct RetainedState
  {
    RetainedState(DagNode *state, int parentIndex, bool fold);
    ~RetainedState();
    bool subsumes(DagNode *state) const;

    DagNode *const state;
    const int parentIndex;
    int depth;
    //
    //	Only used for folding.
    //
    Term *stateTerm;
    LhsAutomaton *matchingAutomaton;
    int nrMatchingVariables; // number of variables needed for matching; includes
                             // any abstraction variables
  };

  typedef map<int, RetainedState *> RetainedStateMap;
  typedef set<int> StateSet;

  void markReachableNodes();

  const bool fold; // we do folding to prune less general states
  RetainedStateMap mostGeneralSoFar;
  int currentStateIndex;
};

inline void
Folder::getState(int index, DagNode *&state) const
{
  RetainedStateMap::const_iterator i = mostGeneralSoFar.find(index);
  Assert(i != mostGeneralSoFar.end(), "couldn't find state with index " << index);
  state = i->second->state;
}

#endif
