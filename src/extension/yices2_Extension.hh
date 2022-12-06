#ifndef YICES2_EXTENSION_HH
#define YICES2_EXTENSION_HH

#include "abstractSmtManager.hh"
#include "SMT_EngineWrapper.hh"
#include "yices.h"
#include <vector>
#include <gmpxx.h>

typedef struct {
    term_t term;
    type_t type;
} yices_term;

struct cmpExprById{
    bool operator( )(const yices_term &lhs, const yices_term &rhs) const {
        return lhs.term < rhs.term;
    }
};

class SmtManager :
        public VariableGenerator,
        public AbstractSmtManager<yices_term, cmpExprById> {
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
    DagNode* applyTactic(DagNode* dagNode, DagNode* tacticTypeDagNode, ExtensionSymbol* extensionSymbol);

private:

    DagNode* GenerateDag(model_t *mdl, yices_term e, SmtCheckerSymbol* smtCheckerSymbol, ReverseSmtManagerVariableMap* rsv);
    yices_term variableGenerator(DagNode *dag, ExprType exprType);

    yices_term Dag2Term(DagNode *dag, ExtensionSymbol* extensionSymbol);
    DagNode *Term2Dag(yices_term e, ExtensionSymbol* extensionSymbol, ReverseSmtManagerVariableMap* rsv=nullptr);

    void setSolverTo(bool isLinear);
    inline void setSimplificationStrategy(){
        int32_t a = yices_context_enable_option(smtContext, "var-elim");
        int32_t b = yices_context_enable_option(smtContext, "arith-elim");
        // int32_t c = yices_context_enable_option(smtContext, "keep-ite");
    }
    bool isSolverLinear;
};

#endif
