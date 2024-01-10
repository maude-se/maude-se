//
//	Code for smt-search commands.
//

void Interpreter::doRewriteSmtSearching(Timer &timer,
                                        VisibleModule *module,
                                        RewriteSmtSequenceSearch *state,
                                        Int64 solutionCount,
                                        Int64 limit)
{
  const VariableInfo *variableInfo = state->getGoal();
  Int64 i = 0;
  for (; i != limit; i++)
  {
    bool result = state->findNextMatch();
    if (UserLevelRewritingContext::aborted())
      break; // HACK: Is this safe - shouldn't we destroy context?
    Int64 real = 0;
    Int64 virt = 0;
    Int64 prof = 0;
    bool showTiming = getFlag(SHOW_TIMING) && timer.getTimes(real, virt, prof);
    bool showStats = getFlag(SHOW_STATS);
    if (!result)
    {
      const char *reply = (solutionCount == 0) ? "No solution." : "No more solutions.";
      cout << "\n"
           << reply << endl;
      // if (showStats)
      //   printStats(*(state->getContext()), prof, real, showTiming, state->getNrStates());
      // if (xmlBuffer != 0)
      //   {
      //     xmlBuffer->generateSearchResult(NONE,
      // 			      state,
      // 			      timer,
      // 			      getFlag(SHOW_STATS),
      // 			      getFlag(SHOW_TIMING),
      // 			      getFlag(SHOW_BREAKDOWN));
      //   }
      // if (latexBuffer != 0)
      //   {
      //     latexBuffer->generateSearchNonResult(state,
      // 				   reply,
      // 				   prof,
      // 				   real,
      // 				   showStats,
      // 				   showTiming,
      // 				   getFlag(SHOW_BREAKDOWN));
      //   }
      break;
    }

    ++solutionCount;
    cout << "\nSolution " << solutionCount << " (state " << state->getStateNr() << ")\n";
    cout << "where " << state->getFinalConstraint() << endl;
    // if (showStats)
    // printStats(*(state->getContext()), prof, real, showTiming, state->getNrStates());
    UserLevelRewritingContext::printSubstitution(*(state->getSubstitution()), *variableInfo);
    //     if (xmlBuffer != 0)
    // {
    //   xmlBuffer->generateSearchResult(solutionCount,
    // 				  state,
    // 				  timer,
    // 				  getFlag(SHOW_STATS),
    // 				  getFlag(SHOW_TIMING),
    // 				  getFlag(SHOW_BREAKDOWN));
    // }
    //     if (latexBuffer != 0)
    // {
    //   latexBuffer->generateSearchResult(state,
    // 				    solutionCount,
    // 				    prof,
    // 				    real,
    // 				    showStats,
    // 				    showTiming,
    // 				    getFlag(SHOW_BREAKDOWN));
    //   latexBuffer->generateSubstitution(*(state->getSubstitution()), *variableInfo);
  }
  // }
  QUANTIFY_STOP();
  // if (latexBuffer)
  //   latexBuffer->cleanUp();
  clearContinueInfo(); // just in case debugger left info
  //
  //	We always save these things even if we can't continue
  //	in order to allow inspection of the search graph.
  //
  savedState = state;
  savedModule = module;
  if (i == limit)
  {
    //
    //	The loop terminated because we hit user's limit so
    //	continuation is still possible. We save the state,
    //	solutionCount and module, and set a continutation function.
    //
    state->getContext()->clearCount();
    savedSolutionCount = solutionCount;
    continueFunc = &Interpreter::rewriteSmtSearchCont;
  }
  UserLevelRewritingContext::clearDebug();
}

void Interpreter::rewriteSmtSearchCont(Int64 limit, bool debug)
{
  RewriteSmtSequenceSearch *state = safeCast(RewriteSmtSequenceSearch *, savedState);
  VisibleModule *fm = savedModule;
  savedState = 0;
  savedModule = 0;
  continueFunc = 0;
  // if (xmlBuffer != 0 && getFlag(SHOW_COMMAND))
  //   xmlBuffer->generateContinue("search", fm, limit);
  // if (latexBuffer)
  //   latexBuffer->generateContinue(getFlag(SHOW_COMMAND), limit, debug);

  if (debug)
    UserLevelRewritingContext::setDebug();

  QUANTIFY_START();
  Timer timer(getFlag(SHOW_TIMING));
  doRewriteSmtSearching(timer, fm, state, savedSolutionCount, limit);
}