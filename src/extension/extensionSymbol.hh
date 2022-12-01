#ifndef EXTENSION_SYMBOL_HH
#define EXTENSION_SYMBOL_HH

#include "freeSymbol.hh"
#include "cachedDag.hh"

class ExtensionSymbol : public FreeSymbol {
    NO_COPYING(ExtensionSymbol);

public:
    ExtensionSymbol(int id, int arity);

    // attach id
    bool attachData(const Vector<Sort*>& opDeclaration,
                    const char* purpose,
                    const Vector<const char*>& data);

    // attach opHooks and TermHooks
    bool attachSymbol(const char* purpose, Symbol* symbol);
    bool attachTerm(const char* purpose, Term* term);

    // copy all hooks
    void copyAttachments(Symbol* original, SymbolMap* map);

    // getter for the attached hooks
    void getDataAttachments(const Vector<Sort*>& opDeclaration,
                            Vector<const char*>& purposes,
                            Vector<Vector<const char*> >& data);

    void getSymbolAttachments(Vector<const char*>& purposes,
                              Vector<Symbol*>& symbols);
    void getTermAttachments(Vector<const char*>& purposes,
                            Vector<Term*>& terms);

    void postInterSymbolPass();
    void reset();


    SMT_NumberSymbol* integerSymbol;
    SMT_NumberSymbol* realSymbol;
    CachedDag trueTerm;
    CachedDag falseTerm;

    Symbol* intVarSymbol;
    Symbol* boolVarSymbol;
    Symbol* realVarSymbol;

    // BooleanExpr
    Symbol* notBoolSymbol;
    Symbol* andBoolSymbol;
    Symbol* xorBoolSymbol;
    Symbol* orBoolSymbol;
    Symbol* impliesBoolSymbol;
    Symbol* eqBoolSymbol;
    Symbol* neqBoolSymbol;
    Symbol* iteBoolSymbol;
    Symbol* forallBoolSymbol;
    Symbol* existsBoolSymbol;

    // IntegerExpr
    Symbol* unaryMinusIntSymbol;
    Symbol* plusIntSymbol;
    Symbol* minusIntSymbol;
    Symbol* divIntSymbol;
    Symbol* mulIntSymbol;
    Symbol* modIntSymbol;
    Symbol* ltIntSymbol;
    Symbol* leqIntSymbol;
    Symbol* gtIntSymbol;
    Symbol* geqIntSymbol;
    Symbol* eqIntSymbol;
    Symbol* neqIntSymbol;
    Symbol* iteIntSymbol;
    Symbol* divisibleIntSymbol;
    Symbol* forallIntSymbol;
    Symbol* existsIntSymbol;

    // RealExpr
    Symbol* unaryMinusRealSymbol;
    Symbol* plusRealSymbol;
    Symbol* minusRealSymbol;
    Symbol* divRealSymbol;
    Symbol* mulRealSymbol;
    Symbol* ltRealSymbol;
    Symbol* leqRealSymbol;
    Symbol* gtRealSymbol;
    Symbol* geqRealSymbol;
    Symbol* eqRealSymbol;
    Symbol* neqRealSymbol;
    Symbol* iteRealSymbol;

    Symbol* toRealSymbol;
    Symbol* toIntegerSymbol;
    Symbol* isIntegerSymbol;

    Symbol* forallRealSymbol;
    Symbol* existsRealSymbol;


    Symbol* shareWith;

    Symbol* freshBoolVarSymbol;
    Symbol* freshIntVarSymbol;
    Symbol* freshRealVarSymbol;

};

#endif
