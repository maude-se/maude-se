#ifndef SMT_MANAGER_HH
#define SMT_MANAGER_HH
#include "abstractSmtManager.hh"
#include "variableGenerator.hh"

#ifdef USE_CVC4
#include "cvc4_Extension.hh"
#elif defined(USE_YICES2)
#include "yices2_Extension.hh"
#elif defined(USE_Z3)
#include "z3_Extension.hh"
#else

// Code for no SMT support case.
class SmtManager : public AbstractSmtManager, public VariableGenerator
{
public:
    SmtManager(const SMT_Info& smtInfo);
    ~SmtManager();

    // functions for SMT solving.
    Result assertDag(DagNode* dag);
    Result checkDag(DagNode* dag);
    Result checkDagWithResult(DagNode* dag);
    void clearAssertions();
    void push();
    void pop();

    VariableDagNode* makeFreshVariable(Term* baseVariable, const mpz_class& number);

private:
    DagNode* Term2Dag(T lhs, T rhs);
    T Dag2Term(DagNode* dag);

};

#endif
#endif
