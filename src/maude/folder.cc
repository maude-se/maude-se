//
//	Implementation for class Folder.
//

//	utility stuff
#include "macros.hh"
#include "vector.hh"

//	forward declarations
#include "interface.hh"
#include "core.hh"

//	interface class definitions
#include "symbol.hh"
#include "dagNode.hh"
#include "term.hh"
#include "lhsAutomaton.hh"
#include "subproblem.hh"

//	core class definitions
#include "rewritingContext.hh"
#include "variableInfo.hh"
#include "subproblemAccumulator.hh"

//	higher class definitions
#include "folder.hh"

Folder::Folder(bool fold)
    : fold(fold)
{
  currentStateIndex = -1;
}

Folder::~Folder()
{
  for (auto &i : mostGeneralSoFar)
    delete i.second;
}

void Folder::markReachableNodes()
{
  for (auto &i : mostGeneralSoFar)
  {
    i.second->state->mark();
  }
}

bool Folder::insertState(int index, DagNode *state, int parentIndex, int *gIdx)
{
  if (fold)
  {
    //
    //	See if state is subsumed by an existing state.
    //
    for (auto &i : mostGeneralSoFar)
    {
      if (i.second->subsumes(state))
      {
        DebugAdvisory("new state " << index << " subsumed by " << i.first);
        Verbose("New state " << state << " subsumed by " << i.second->state);
        *gIdx = i.first;
        return false;
      }
    }
  }
  Verbose("new state " << index << " added");
  RetainedState *newState = new RetainedState(state, parentIndex, fold);
  int depth = 0;
  if (parentIndex != NONE)
  {
    RetainedStateMap::const_iterator j = mostGeneralSoFar.find(parentIndex);
    if (j == mostGeneralSoFar.end()){
      IssueWarning("assertion failed with " << parentIndex << " where its index is " << index);
    }
    Assert(j != mostGeneralSoFar.end(), "couldn't find state with index " << parentIndex);
    depth = j->second->depth + 1;
  }
  newState->depth = depth;
  if (fold)
  {
    //
    //	Compute ancestor set.
    //
    StateSet ancestors;
    for (int i = parentIndex; i != NONE;)
    {
      ancestors.insert(i);
      RetainedStateMap::const_iterator j = mostGeneralSoFar.find(i);
      Assert(j != mostGeneralSoFar.end(), "couldn't find state with index " << i);
      i = j->second->parentIndex;
    }
    //
    //	See if newState can evict an existing state.
    //
    StateSet existingStatesSubsumed;
    RetainedStateMap::iterator i = mostGeneralSoFar.begin();
    while (i != mostGeneralSoFar.end())
    {
      RetainedStateMap::iterator next = i;
      ++next;
      if (ancestors.find(i->first) == ancestors.end()) // can't mess with ancestors of new state
      {
        RetainedState *potentialVictim = i->second;
        if (existingStatesSubsumed.find(potentialVictim->parentIndex) !=
            existingStatesSubsumed.end())
        {
          //
          //	Our parent was subsumed so we are also subsumed.
          //
          DebugAdvisory("new state evicted descendent of an older state " << i->first);
          Verbose("New state " << state << " evicted descendent of an older state " << i->second->state << " by subsuming an ancestor.");
          existingStatesSubsumed.insert(i->first);
          delete potentialVictim;
          mostGeneralSoFar.erase(i);
        }
        else if (newState->subsumes(potentialVictim->state))
        {
          //
          //	Direct subsumption by new state.
          //
          DebugAdvisory("new state evicted an older state " << i->first);
          Verbose("New state " << state << " subsumed older state " << i->second->state);
          existingStatesSubsumed.insert(i->first);
          delete potentialVictim;
          mostGeneralSoFar.erase(i);
        }
      }
      i = next;
    }
  }
  mostGeneralSoFar.insert(RetainedStateMap::value_type(index, newState));
  *gIdx = index;
  return true;
}

Folder::RetainedState::RetainedState(DagNode *state, int parentIndex, bool fold)
    : state(state),
      parentIndex(parentIndex)
{
  if (fold)
  {
    //
    //	Make term version of state.
    //
    Term *t = state->symbol()->termify(state);
    //
    //	Even thoug t should be in normal form we need to set hash values.
    //
    t = t->normalize(true);
    VariableInfo variableInfo;
    t->indexVariables(variableInfo);
    t->symbol()->fillInSortInfo(t);
    t->analyseCollapses();

    NatSet boundUniquely;
    bool subproblemLikely;

    t->determineContextVariables();
    t->insertAbstractionVariables(variableInfo);

    matchingAutomaton = t->compileLhs(false, variableInfo, boundUniquely, subproblemLikely);
    stateTerm = t;
    nrMatchingVariables = variableInfo.getNrProtectedVariables(); // may also have some
                                                                  // abstraction variables
  }
  else
  {
    stateTerm = 0;
    matchingAutomaton = 0;
    nrMatchingVariables = 0;
  }
}

Folder::RetainedState::~RetainedState()
{
  delete matchingAutomaton;
  if (stateTerm)
    stateTerm->deepSelfDestruct();
}

bool Folder::RetainedState::subsumes(DagNode *state) const
{
  MemoryCell::okToCollectGarbage(); // otherwise we have huge accumulation of junk from matching
  int nrSlotsToAllocate = nrMatchingVariables;
  if (nrSlotsToAllocate == 0)
    nrSlotsToAllocate = 1; // substitutions subject to clear() must always have at least one slot

  RewritingContext matcher(nrSlotsToAllocate);
  matcher.clear(nrMatchingVariables);
  Subproblem *subproblem = 0;

  bool result = matchingAutomaton->match(state, matcher, subproblem) &&
                (subproblem == 0 || subproblem->solve(true, matcher));
  delete subproblem;
  return result;
}
