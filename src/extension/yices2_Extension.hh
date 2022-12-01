#ifndef YICES2_EXTENSION_HH
#define YICES2_EXTENSION_HH

#include "abstractSmtManager.hh"
#include "SMT_EngineWrapper.hh"
#include "yices.h"
#include <vector>
#include <gmpxx.h>

struct cmpExprById{
    bool operator( )(const term_t &lhs, const term_t &rhs) const {
        return lhs < rhs;
    }
};

class SmtManager :
        public VariableGenerator,
        public AbstractSmtManager<term_t, cmpExprById> {
    NO_COPYING(SmtManager);

public:
    SmtManager(const SMT_Info &smtInfo);

    // backward compatibility
    Result assertDag(DagNode* dag);
    Result checkDag(DagNode* dag);
    VariableDagNode *makeFreshVariable(Term *baseVariable, const mpz_class &number);
    SmtResult checkDagContextFree(DagNode *dag, ExtensionSymbol* extensionSymbol=nullptr);

    // SMT manager requirements
    DagNode *generateAssignment(DagNode *dagNode, SmtCheckerSymbol* smtCheckerSymbol);
    DagNode *simplifyDag(DagNode *dagNode, ExtensionSymbol* extensionSymbol);

private:

    DagNode* GenerateDag(model_t *mdl, term_t e, SmtCheckerSymbol* smtCheckerSymbol, ReverseSmtManagerVariableMap* rsv);
    term_t variableGenerator(DagNode *dag, ExprType exprType);

    term_t Dag2Term(DagNode *dag, ExtensionSymbol* extensionSymbol);
    DagNode *Term2Dag(term_t e, ExprType exprType, ExtensionSymbol* extensionSymbol, ReverseSmtManagerVariableMap* rsv=nullptr);

    void setSolverTo(bool isLinear);
    inline void setSimplificationStrategy(){
        int32_t a = yices_context_enable_option(smtContext, "var-elim");
        int32_t b = yices_context_enable_option(smtContext, "arith-elim");
        int32_t c = yices_context_enable_option(smtContext, "keep-ite");
    }
    bool isSolverLinear;
};

#endif
