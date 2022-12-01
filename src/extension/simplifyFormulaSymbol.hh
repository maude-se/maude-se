#ifndef SIMPLIFY_FORMULA_SYMBOL_HH
#define SIMPLIFY_FORMULA_SYMBOL_HH
#include "extensionSymbol.hh"
#include "smtManager.hh"

class SimplifyFormulaSymbol : public ExtensionSymbol
{
    NO_COPYING(SimplifyFormulaSymbol);
public:

    SimplifyFormulaSymbol(int id, int arity);
    bool eqRewrite(DagNode* subject, RewritingContext& context);
    bool attachData(const Vector<Sort *> &opDeclaration,
                                      const char *purpose,
                                      const Vector<const char *> &data);
};

#endif
