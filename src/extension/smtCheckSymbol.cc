// utility stuff
#include "macros.hh"
#include "vector.hh"

// forward declarations
#include "interface.hh"
#include "core.hh"
#include "freeTheory.hh"
#include "variable.hh"
#include "builtIn.hh"
#include "mixfix.hh"

// interface class definitions
#include "symbol.hh"
#include "term.hh"

// core class definitions
#include "rewritingContext.hh"
#include "symbolMap.hh"

// variable class definitions
#include "variableSymbol.hh"
#include "variableDagNode.hh"

// free theory class definitions
#include "freeDagNode.hh"


// builtin class definition
#include "bindingMacros.hh"

// SMT stuff
#include "SMT_Info.hh"
#include "SMT_Symbol.hh"
#include "SMT_NumberSymbol.hh"
#include "SMT_NumberDagNode.hh"

// Qid
#include "quotedIdentifierSymbol.hh"
#include "quotedIdentifierDagNode.hh"

#include "smtCheckSymbol.hh"

// Need to get right SMTInfo.
#include "../StrategyLanguage/strategyLanguage.hh"
#include "../Mixfix/mixfixModule.hh"

SmtCheckerSymbol::SmtCheckerSymbol(int id, int arity)
        : ExtensionSymbol(id, arity)
{

    /**
     * SmtCheckResult symbol
     *
     * satResultSymbol (sat : ~> SmtCheckResult)
     * unsatResultSymbol (unsat : ~> SmtCheckResult)
     * unknownResultSymbol (unknown : ~> SmtCheckResult)
     * smtAssignmentResultSymbol ({_} : SatAssignmentSet ~> SmtCheckResult)
     */
    unknownResultSymbol = 0;
    smtAssignmentResultSymbol = 0;

    /**
     * SatAssignmentSet symbol.
     *
     * emptySatAssignmentSetSymbol (empty : ~> SatAssignmentSet)
     * concatSatAssignmentSetSymbol (_,_ : SatAssignmentSet SatAssignmentSet ~> SatAssignmentSet)
     */
    emptySatAssignmentSetSymbol = 0;
    concatSatAssignmentSetSymbol = 0;

    /**
     * Assignment symbol.
     *
     * intAssignmentSymbol (_|->_ : IntegerVar Integer ~> SatAssignment)
     * boolAssignmentSymbol (_|->_ : BooleanVar Boolean ~> SatAssignment)
     * realAssignmentSymbol (_|->_ : RealVar Real ~> SatAssignment)
     */
    intAssignmentSymbol = 0;
    boolAssignmentSymbol = 0;
    realAssignmentSymbol = 0;

    intervalSymbol = 0;
    undefinedIntervalSymbol = 0;
    minusInfIntervalBoundSymbol = 0;
    infIntervalBoundSymbol = 0;
    intIntervalAssignmentSymbol = 0;
    realIntervalAssignmentSymbol = 0;
}

bool SmtCheckerSymbol::attachData(const Vector<Sort*>& opDeclaration,
                const char* purpose,
                const Vector<const char*>& data){
    DebugAdvisory("SmtCheckerSymbol attach data called");
    NULL_DATA(purpose, SmtCheckerSymbol, data);
    return ExtensionSymbol::attachData(opDeclaration, purpose, data);
}

bool SmtCheckerSymbol::attachSymbol(const char* purpose, Symbol* symbol){
    BIND_SYMBOL(purpose, symbol, unknownResultSymbol, Symbol*);
    BIND_SYMBOL(purpose, symbol, smtAssignmentResultSymbol, Symbol*);
    BIND_SYMBOL(purpose, symbol, emptySatAssignmentSetSymbol, Symbol*);
    BIND_SYMBOL(purpose, symbol, concatSatAssignmentSetSymbol, Symbol*);

    BIND_SYMBOL(purpose, symbol, intAssignmentSymbol, Symbol*);
    BIND_SYMBOL(purpose, symbol, boolAssignmentSymbol, Symbol*);
    BIND_SYMBOL(purpose, symbol, realAssignmentSymbol, Symbol*);

    BIND_SYMBOL(purpose, symbol, intervalSymbol, Symbol*);
    BIND_SYMBOL(purpose, symbol, undefinedIntervalSymbol, Symbol*);
    BIND_SYMBOL(purpose, symbol, minusInfIntervalBoundSymbol, Symbol*);
    BIND_SYMBOL(purpose, symbol, infIntervalBoundSymbol, Symbol*);

    BIND_SYMBOL(purpose, symbol, intIntervalAssignmentSymbol, Symbol*);
    BIND_SYMBOL(purpose, symbol, realIntervalAssignmentSymbol, Symbol*);
    return ExtensionSymbol::attachSymbol(purpose, symbol);
}

void SmtCheckerSymbol::copyAttachments(Symbol* original, SymbolMap* map){

    SmtCheckerSymbol *orig = safeCast(SmtCheckerSymbol * , original);
    COPY_SYMBOL(orig, unknownResultSymbol, map, Symbol*);
    COPY_SYMBOL(orig, smtAssignmentResultSymbol, map, Symbol*);
    COPY_SYMBOL(orig, emptySatAssignmentSetSymbol, map, Symbol*);
    COPY_SYMBOL(orig, concatSatAssignmentSetSymbol, map, Symbol*);

    COPY_SYMBOL(orig, intAssignmentSymbol, map, Symbol*);
    COPY_SYMBOL(orig, boolAssignmentSymbol, map, Symbol*);
    COPY_SYMBOL(orig, realAssignmentSymbol, map, Symbol*);

    COPY_SYMBOL(orig, intervalSymbol, map, Symbol*);
    COPY_SYMBOL(orig, undefinedIntervalSymbol, map, Symbol*);
    COPY_SYMBOL(orig, minusInfIntervalBoundSymbol, map, Symbol*);
    COPY_SYMBOL(orig, infIntervalBoundSymbol, map, Symbol*);

    COPY_SYMBOL(orig, intIntervalAssignmentSymbol, map, Symbol*);
    COPY_SYMBOL(orig, realIntervalAssignmentSymbol, map, Symbol*);

    COPY_TERM(orig, builtinTrueTerm, map);
    COPY_TERM(orig, builtinFalseTerm, map);

    ExtensionSymbol::copyAttachments(original, map);
}

void SmtCheckerSymbol::getTermAttachments(Vector<const char *> &purposes,
                                         Vector<Term *> &terms) {
    APPEND_TERM(purposes, terms, builtinTrueTerm);
    APPEND_TERM(purposes, terms, builtinFalseTerm);
    ExtensionSymbol::getTermAttachments(purposes, terms);
}


void SmtCheckerSymbol::postInterSymbolPass() {
    PREPARE_TERM(builtinTrueTerm);
    PREPARE_TERM(builtinFalseTerm);
    ExtensionSymbol::postInterSymbolPass();
}

void SmtCheckerSymbol::reset() {
    builtinTrueTerm.reset();
    builtinFalseTerm.reset();
    ExtensionSymbol::reset();
}

void SmtCheckerSymbol::getSymbolAttachments(Vector<const char*>& purposes,
                          Vector<Symbol*>& symbols) {

    APPEND_SYMBOL(purposes, symbols, unknownResultSymbol);
    APPEND_SYMBOL(purposes, symbols, smtAssignmentResultSymbol);
    APPEND_SYMBOL(purposes, symbols, emptySatAssignmentSetSymbol);
    APPEND_SYMBOL(purposes, symbols, concatSatAssignmentSetSymbol);

    APPEND_SYMBOL(purposes, symbols, intAssignmentSymbol);
    APPEND_SYMBOL(purposes, symbols, boolAssignmentSymbol);
    APPEND_SYMBOL(purposes, symbols, realAssignmentSymbol);

    APPEND_SYMBOL(purposes, symbols, intervalSymbol);
    APPEND_SYMBOL(purposes, symbols, undefinedIntervalSymbol);
    APPEND_SYMBOL(purposes, symbols, minusInfIntervalBoundSymbol);
    APPEND_SYMBOL(purposes, symbols, infIntervalBoundSymbol);

    APPEND_SYMBOL(purposes, symbols, intIntervalAssignmentSymbol);
    APPEND_SYMBOL(purposes, symbols, realIntervalAssignmentSymbol);

    ExtensionSymbol::getSymbolAttachments(purposes, symbols);
}

bool SmtCheckerSymbol::attachTerm(const char *purpose, Term *term) {
    BIND_TERM(purpose, term, builtinTrueTerm);
    BIND_TERM(purpose, term, builtinFalseTerm);
    return ExtensionSymbol::attachTerm(purpose, term);
}

bool SmtCheckerSymbol::eqRewrite(DagNode* subject, RewritingContext& context){

    Assert(this == subject->symbol(), "bad symbol");
    FreeDagNode *f = safeCast(FreeDagNode * , subject);
    RewritingContext* newContext = context.makeSubcontext((f->getArgument(0)));
    newContext->reduce();
    context.addInCount(*newContext);
    DagNode* resultDag = newContext->root();

    try {
        if(MixfixModule* m = dynamic_cast<MixfixModule*>(this->getModule())) {
            SmtManager smtManager(m->getSMT_Info());
            bool isMakeAssignment = false;
            if (f->getArgument(1)->symbol() == this->builtinTrueTerm.getDag()->symbol()) {
                isMakeAssignment = true;
            }
            DagNode *newRoot = newContext->root();

            // smtManager.push();
            SmtManager::SmtResult checkResult = smtManager.checkDagContextFree(newRoot, this);

            switch (checkResult) {
                case SmtManager::SMT_BAD_DAG:
                    throw ExtensionException("bad dag!");
                case SmtManager::SMT_UNSAT:
                    resultDag = this->builtinFalseTerm.getDag();
                    break;
                case SmtManager::SMT_SAT:
                    if (isMakeAssignment) {
                        try {
                            resultDag = smtManager.generateAssignment(newRoot, this);
                        } catch (ExtensionException &ex) {
                            IssueWarning("Error while smt solving : " << ex.c_str());
                            throw ExtensionException("Error while smt solving");
                        }
                    } else {
                        resultDag = this->builtinTrueTerm.getDag();
                    }
                    break;
                case SmtManager::SMT_SAT_UNKNOWN:
                    resultDag = this->unknownResultSymbol->makeDagNode();
                    break;
            }
            delete newContext;
            // smtManager.pop();
            smtManager.clearAssertions();
        } else {
            IssueWarning("Error occurred while getting a Module");
        }
    } catch (ExtensionException& ex){
        IssueWarning("Error while generating assignments: " << ex.c_str());
        delete newContext;
    }
    return context.builtInReplace(subject, resultDag);
}
