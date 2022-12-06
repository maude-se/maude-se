#ifndef CVC4_EXTENSION_HH
#define CVC4_EXTENSION_HH

#include "abstractSmtManager.hh"
#include "cvc4/expr/expr_manager.h"
#include "cvc4/smt/smt_engine.h"
#include "SMT_EngineWrapper.hh"
#include <vector>
#include <gmpxx.h>

using namespace CVC4;

typedef struct {
    Expr term;
    Type type;
} cvc4_term;

struct cmpExprById{
    bool operator( )(const cvc4_term &lhs, const cvc4_term &rhs) const {
        return lhs.term.getId() < rhs.term.getId();
    }
};

class SmtManager : public VariableGenerator, public AbstractSmtManager<cvc4_term, cmpExprById> {
    NO_COPYING(SmtManager);
public:
    SmtManager(const SMT_Info &smtInfo);

    void clearAssertions();

    SmtResult checkDagContextFree(DagNode *dag, ExtensionSymbol* extensionSymbol);
    DagNode *generateAssignment(DagNode *dagNode, SmtCheckerSymbol* smtCheckerSymbol);
    VariableDagNode *makeFreshVariable(Term *baseVariable, const mpz_class &number);
    DagNode *simplifyDag(DagNode *dagNode, ExtensionSymbol* extensionSymbol);
    DagNode* applyTactic(DagNode* dagNode, DagNode* tacticTypeDagNode, ExtensionSymbol* extensionSymbol);

private:

    typedef std::pair<Expr, Expr> AssignmentElem;
    typedef std::vector<AssignmentElem> Assignment;

    /**
     * cvc4 specific
     */
    cvc4_term Dag2Term(DagNode* dag, ExtensionSymbol* extensionSymbol);
    DagNode* Term2Dag(cvc4_term exp, ExtensionSymbol* extensionSymbol, ReverseSmtManagerVariableMap* rsv);
    cvc4_term variableGenerator(DagNode *dag, ExprType exprType);

    cvc4_term checkDagResultExp;

    void prefixGetValue(SmtEngine &smt, Expr e, Assignment *assn, int level = 0);
    DagNode *GenerateDag(Expr lhs, Expr rhs, SmtCheckerSymbol* smtCheckerSymbol, ReverseSmtManagerVariableMap* rsv);

    void setSolverTo(bool isLinear);
    bool isSolverLinear;
};

#endif
