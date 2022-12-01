// utility stuff
#include "macros.hh"
#include "vector.hh"

// forward declarations
#include "interface.hh"
#include "core.hh"
#include "variable.hh"
#include "mixfix.hh"
#include "SMT.hh"

// interface class definitions
#include "symbol.hh"
#include "term.hh"

// variable class definitions
#include "variableDagNode.hh"
#include "variableTerm.hh"

#include "freeDagNode.hh"

// SMT class definitions
#include "SMT_Symbol.hh"
#include "SMT_NumberSymbol.hh"
#include "SMT_NumberDagNode.hh"
#include "smtManager.hh"

#ifdef USE_CVC4
#include "cvc4_Extension.cc"
#elif defined(USE_YICES2)
#include "yices2_Extension.cc"
#elif defined(USE_Z3)
#include "z3_Extension.cc"
#else

// no SMT support case.
SmtManger::SmtManager(const SMT_Info& smtInfo){
    initializeCounter = 0;
    IssueWarning("No SMT solver linked at compile time.");
}

SmtManager::~SmtManager(){}

SmtManager::Result SmtManager::assertDag(DagNode* dag){
    return SAT_UNKNOWN;
}

SmtManager::Result SmtManager::checkDag(DagNode* dag){
    return SAT_UNKNOWN;
}

SmtManager::Result SmtManager::checkDagWithResult(DagNode *dag){
    return SAT_UNKNOWN;
}

void SmtManager::push(){}

void SmtManager::pop(){}

void SmtManager::clearAssertions(){}

DagNode* SmtManager::Term2Dag(T lhs_exp, T rhs_exp){
    return nullptr;
}

T SmtManager::Dag2Term(DagNode* dag){
    return false;
}

#endif

VariableDagNode* SmtManager::makeFreshVariable(Term* baseVariable, const mpz_class& number)
{
    Symbol* s = baseVariable->symbol();
    VariableTerm* vt = safeCast(VariableTerm*, baseVariable);

    string name = "#";
    int id = vt->id();
    char* name_c_str = mpz_get_str(0, 10, number.get_mpz_t());
    name += name_c_str;
    free(name_c_str);

    name += "-";
    name +=  Token::name(id);
    int newId = Token::encode(name.c_str());

    return new VariableDagNode(s, newId, NONE);
}
