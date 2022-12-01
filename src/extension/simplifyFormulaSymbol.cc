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

#include "simplifyFormulaSymbol.hh"

// Need to get right SMTInfo.
#include "../StrategyLanguage/strategyLanguage.hh"
#include "../Mixfix/mixfixModule.hh"

SimplifyFormulaSymbol::SimplifyFormulaSymbol(int id, int arity)
        : ExtensionSymbol(id, arity) {}

bool SimplifyFormulaSymbol::attachData(const Vector<Sort *> &opDeclaration,
                                       const char *purpose, const Vector<const char *> &data) {
    NULL_DATA(purpose, SimplifyFormulaSymbol, data);
    return ExtensionSymbol::attachData(opDeclaration, purpose, data);
}

bool SimplifyFormulaSymbol::eqRewrite(DagNode *subject, RewritingContext &context) {

    Assert(this == subject->symbol(), "bad symbol");
    FreeDagNode *f = safeCast(FreeDagNode * , subject);
    RewritingContext* newContext = context.makeSubcontext((f->getArgument(0)));
    newContext->reduce();
    context.addInCount(*newContext);
    DagNode* resultDag = newContext->root();

    try{
        if(MixfixModule* m = dynamic_cast<MixfixModule*>(this->getModule())) {
            SmtManager smtManager(m->getSMT_Info());
            resultDag = smtManager.simplifyDag(newContext->root(),
                                               shareWith ? static_cast<ExtensionSymbol *>(this->shareWith) : this);
            if (resultDag == nullptr) {
                resultDag = newContext->root();
            }
        } else {
            IssueWarning("Error occurred while getting a Module");
        }
    } catch (ExtensionException & ex) {
        IssueWarning("Simplify Error : " << ex.c_str());
    }
    delete newContext;
    return context.builtInReplace(subject, resultDag);
}


