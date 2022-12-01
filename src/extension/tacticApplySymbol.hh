#ifndef TACTIC_APPLY_SYMBOL_HH
#define TACTIC_APPLY_SYMBOL_HH
#include "extensionSymbol.hh"
#include "smtManager.hh"

class TacticApplySymbol : public ExtensionSymbol
{
    NO_COPYING(TacticApplySymbol);
public:

    TacticApplySymbol(int id, int arity);
    bool eqRewrite(DagNode* subject, RewritingContext& context);
    bool attachData(const Vector<Sort *> &opDeclaration,
                                      const char *purpose,
                                      const Vector<const char *> &data);
    bool attachSymbol(const char* purpose, Symbol* symbol);
    void copyAttachments(Symbol* original, SymbolMap* map);
    void getSymbolAttachments(Vector<const char*>& purposes,
                              Vector<Symbol*>& symbols);

public:
    // tactic operators
    Symbol* simplifySymbol;
    Symbol* qeSymbol;
    Symbol* qe2Symbol;
    Symbol* ctxSolverSimplifySymbol;
    Symbol* propagateInEqsSymbol;
    Symbol* purifyArithSymbol;
    Symbol* thenSymbol;
    Symbol* andTacticSymbol;

public:
    enum TacticType {
        NONE,
        SIMPLIFY,
        QE,
        QE2,
        CTX_SOLVER_SIMPLIFY,
        PROP_IN_EQS,
        PURIFY_ARITH,
        THEN,
        AND,
    };

    TacticType getTacticType(DagNode* dagNode);
};

#endif
