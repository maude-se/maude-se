#ifndef SMT_CHECK_SYMBOL_HH
#define SMT_CHECK_SYMBOL_HH
#include "extensionSymbol.hh"
#include "smtManager.hh"

// forward declaration
class SmtManager;

class SmtCheckerSymbol : public ExtensionSymbol
{
    NO_COPYING(SmtCheckerSymbol);
public:

    SmtCheckerSymbol(int id, int arity);
    bool attachData(const Vector<Sort*>& opDeclaration,
                    const char* purpose,
                    const Vector<const char*>& data);
    bool attachSymbol(const char* purpose, Symbol* symbol);
    void copyAttachments(Symbol* original, SymbolMap* map);
    void getSymbolAttachments(Vector<const char*>& purposes,
                              Vector<Symbol*>& symbols);


    bool attachTerm(const char *purpose, Term *term);
    void getTermAttachments(Vector<const char *> &purposes,
                                              Vector<Term *> &terms);

    void reset();
    void postInterSymbolPass();
    bool eqRewrite(DagNode* subject, RewritingContext& context);

public:
    // SmtCheckResult symbol
    Symbol* unknownResultSymbol;
    Symbol* smtAssignmentResultSymbol;

    // SatAssignmentSet symbol
    Symbol* emptySatAssignmentSetSymbol;
    Symbol* concatSatAssignmentSetSymbol;

    // Assignment symbol
    Symbol* intAssignmentSymbol;
    Symbol* boolAssignmentSymbol;
    Symbol* realAssignmentSymbol;

    Symbol* intervalSymbol;
    Symbol* undefinedIntervalSymbol;
    Symbol* minusInfIntervalBoundSymbol;
    Symbol* infIntervalBoundSymbol;
    Symbol* intIntervalAssignmentSymbol;
    Symbol* realIntervalAssignmentSymbol;

    CachedDag builtinTrueTerm;
    CachedDag builtinFalseTerm;

};

#endif
