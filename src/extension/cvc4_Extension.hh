#ifndef CVC4_EXTENSION_HH
#define CVC4_EXTENSION_HH

#include "abstractSmtManager.hh"
#include "cvc4/expr/expr_manager.h"
#include "cvc4/smt/smt_engine.h"
#include "SMT_EngineWrapper.hh"
#include <vector>
#include <gmpxx.h>

using namespace CVC4;

struct cmpExprById{
    bool operator( )(const Expr &lhs, const Expr &rhs) const {
        return lhs.getId() < rhs.getId();
    }
};

class SmtManager : public VariableGenerator, public AbstractSmtManager<Expr, cmpExprById> {
    NO_COPYING(SmtManager);
public:
    SmtManager(const SMT_Info &smtInfo);

    SmtResult checkDagContextFree(DagNode *dag, ExtensionSymbol* extensionSymbol);
    DagNode *generateAssignment(DagNode *dagNode, SmtCheckerSymbol* smtCheckerSymbol);
    VariableDagNode *makeFreshVariable(Term *baseVariable, const mpz_class &number);
    DagNode *simplifyDag(DagNode *dagNode, ExtensionSymbol* extensionSymbol);

private:

    typedef std::pair<Expr, Expr> AssignmentElem;
    typedef std::vector<AssignmentElem> Assignment;

    /**
     * cvc4 specific
     */
    Expr Dag2Term(DagNode* dag, ExtensionSymbol* extensionSymbol);
    DagNode* Term2Dag(Expr exp, ExprType exprType, ExtensionSymbol* extensionSymbol, ReverseSmtManagerVariableMap* rsv);
    Expr variableGenerator(DagNode *dag, ExprType exprType);

    Expr checkDagResultExp;

    void prefixGetValue(SmtEngine &smt, Expr e, Assignment *assn, int level = 0);
    DagNode *GenerateDag(Expr lhs, Expr rhs, SmtCheckerSymbol* smtCheckerSymbol, ReverseSmtManagerVariableMap* rsv);
};

#endif
