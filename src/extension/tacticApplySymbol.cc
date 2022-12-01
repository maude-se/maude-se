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

#include "tacticApplySymbol.hh"

// Need for get right SMTInfo.
#include "../StrategyLanguage/strategyLanguage.hh"
#include "../Mixfix/mixfixModule.hh"

TacticApplySymbol::TacticApplySymbol(int id, int arity)
        : ExtensionSymbol(id, arity) {
    simplifySymbol = 0;
    qeSymbol = 0;
    qe2Symbol = 0;
    ctxSolverSimplifySymbol = 0;
    propagateInEqsSymbol = 0;
    purifyArithSymbol = 0;
    thenSymbol = 0;
    andTacticSymbol = 0;
}

bool
TacticApplySymbol::attachData(const Vector<Sort *> &opDeclaration,
                            const char *purpose,
                            const Vector<const char *> &data) {
    NULL_DATA(purpose, TacticApplySymbol, data);
    return ExtensionSymbol::attachData(opDeclaration, purpose, data);
}

bool TacticApplySymbol::attachSymbol(const char* purpose, Symbol* symbol){
    BIND_SYMBOL(purpose, symbol, simplifySymbol, Symbol*);
    BIND_SYMBOL(purpose, symbol, qeSymbol, Symbol*);
    BIND_SYMBOL(purpose, symbol, qe2Symbol, Symbol*);
    BIND_SYMBOL(purpose, symbol, ctxSolverSimplifySymbol, Symbol*);
    BIND_SYMBOL(purpose, symbol, propagateInEqsSymbol, Symbol*);
    BIND_SYMBOL(purpose, symbol, purifyArithSymbol, Symbol*);
    BIND_SYMBOL(purpose, symbol, thenSymbol, Symbol*);
    BIND_SYMBOL(purpose, symbol, andTacticSymbol, Symbol*);
    return ExtensionSymbol::attachSymbol(purpose, symbol);
}

void TacticApplySymbol::copyAttachments(Symbol* original, SymbolMap* map){
    TacticApplySymbol *orig = safeCast(TacticApplySymbol* , original);
    COPY_SYMBOL(orig, simplifySymbol, map, Symbol*);
    COPY_SYMBOL(orig, qeSymbol, map, Symbol*);
    COPY_SYMBOL(orig, qe2Symbol, map, Symbol*);
    COPY_SYMBOL(orig, ctxSolverSimplifySymbol, map, Symbol*);
    COPY_SYMBOL(orig, propagateInEqsSymbol, map, Symbol*);
    COPY_SYMBOL(orig, purifyArithSymbol, map, Symbol*);
    COPY_SYMBOL(orig, thenSymbol, map, Symbol*);
    COPY_SYMBOL(orig, andTacticSymbol, map, Symbol*);
    ExtensionSymbol::copyAttachments(original, map);
}

void TacticApplySymbol::getSymbolAttachments(Vector<const char*>& purposes,
                                            Vector<Symbol*>& symbols) {
    APPEND_SYMBOL(purposes, symbols, simplifySymbol);
    APPEND_SYMBOL(purposes, symbols, qeSymbol);
    APPEND_SYMBOL(purposes, symbols, qe2Symbol);
    APPEND_SYMBOL(purposes, symbols, ctxSolverSimplifySymbol);
    APPEND_SYMBOL(purposes, symbols, propagateInEqsSymbol);
    APPEND_SYMBOL(purposes, symbols, purifyArithSymbol);
    APPEND_SYMBOL(purposes, symbols, thenSymbol);
    APPEND_SYMBOL(purposes, symbols, andTacticSymbol);
    ExtensionSymbol::getSymbolAttachments(purposes, symbols);
}

bool TacticApplySymbol::eqRewrite(DagNode *subject, RewritingContext &context) {

    Assert(this == subject->symbol(), "bad symbol");
    FreeDagNode *f = safeCast(FreeDagNode * , subject);
    RewritingContext* newContext = context.makeSubcontext((f->getArgument(0)));
    newContext->reduce();
    context.addInCount(*newContext);
    DagNode* resultDag = newContext->root();

    try{
        if(MixfixModule* m = dynamic_cast<MixfixModule*>(this->getModule())) {
            SmtManager smtManager(m->getSMT_Info());
            resultDag = smtManager.applyTactic(newContext->root(), f->getArgument(1),
                                               shareWith ? static_cast<ExtensionSymbol *>(this->shareWith) : this);
            if (resultDag == nullptr) {
                resultDag = newContext->root();
            }
        } else {
            IssueWarning("Error occurred while getting a Module");
        }
    } catch (ExtensionException & ex) {
        IssueWarning("tactic application error : " << ex.c_str());
    }
    delete newContext;
    return context.builtInReplace(subject, resultDag);
}

TacticApplySymbol::TacticType TacticApplySymbol::getTacticType(DagNode* dagNode) {
    if (dagNode->symbol() == simplifySymbol) {
        return SIMPLIFY;
    } else if (dagNode->symbol() == qeSymbol) {
        return QE;
    } else if (dagNode->symbol() == qe2Symbol) {
        return QE2;
    } else if (dagNode->symbol() == ctxSolverSimplifySymbol) {
        return CTX_SOLVER_SIMPLIFY;
    } else if (dagNode->symbol() == propagateInEqsSymbol) {
        return PROP_IN_EQS;
    } else if (dagNode->symbol() == purifyArithSymbol) {
        return PURIFY_ARITH;
    } else if (dagNode->symbol() == thenSymbol) {
        return THEN;
    } else if (dagNode->symbol() == andTacticSymbol) {
        return AND;
    }
    return NONE;
}

