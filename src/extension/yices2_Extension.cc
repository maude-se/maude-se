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

// front end class definitions
#include "token.hh"
#include "yices2_Extension.hh"
#include <sstream>

SmtManager::SmtManager(const SMT_Info &smtInfo)
        : AbstractSmtManager(smtInfo), VariableGenerator(smtInfo) {
    hasVariable = false;
    setSimplificationStrategy();
}

void SmtManager::setSolverTo(bool isLinear) {
    yices_free_context(smtContext);
    if (isLinear){
        smtContext = yices_new_context(NULL);
        isSolverLinear = true;
    } else {
        ctx_config_t *config = yices_new_config();
        yices_set_config(config, "solver-type", "mcsat");
        smtContext = yices_new_context(config);
        yices_free_config(config);
        isSolverLinear = false;
    }
}

SmtManager::Result SmtManager::checkDag(DagNode* dag) {
    setSolverTo(true);
    yices_term t = makeExpr(dag, nullptr, true);
    if (t.term == NULL_TERM)
        return BAD_DAG;

    yices_push(smtContext);
    int code = yices_assert_formula(smtContext, t.term);
    if (code < 0) {
        setSolverTo(false);
    }
    code = yices_assert_formula(smtContext, t.term);
    if (code < 0) {
        IssueWarning("Yices2 reported an error - giving up:");
        yices_print_error(stderr);
        yices_pop(smtContext);
        return SAT_UNKNOWN;
    }

    smt_status_t result = yices_check_context(smtContext, NULL);
    yices_pop(smtContext);

    if (result == STATUS_SAT)
        return SAT;
    if (result == STATUS_UNSAT)
        return UNSAT;

    IssueWarning("Yices2 not able to determine satisfiability - giving up.");
    return SAT_UNKNOWN;
}

SmtManager::Result SmtManager::assertDag(DagNode* dag) {
    setSolverTo(true);
    yices_term t = makeExpr(dag, nullptr, true);
    if (t.term == NULL_TERM)
        return BAD_DAG;

    int code = yices_assert_formula(smtContext, t.term);
    if (code < 0) {
        setSolverTo(false);
    }
    code = yices_assert_formula(smtContext, t.term);
    if (code < 0) {
        IssueWarning("Yices2 reported an error - giving up:");
        yices_print_error(stderr);
        yices_pop(smtContext);
        return SAT_UNKNOWN;
    }

    smt_status_t result = yices_check_context(smtContext, NULL);

    if (result == STATUS_SAT)
        return SAT;
    if (result == STATUS_UNSAT)
        return UNSAT;

    IssueWarning("Yices2 is not able to determine satisfiability - giving up.");
    return SAT_UNKNOWN;
}

SmtManager::SmtResult SmtManager::checkDagContextFree(DagNode *dag,
                                                      ExtensionSymbol* extensionSymbol) {
    setSolverTo(true);
    resetFormulaSize();
    yices_term t = makeExpr(dag, extensionSymbol, true);

    Verbose("SmtCheckSymbol : Formula size " << formulaSize);
    resetFormulaSize();
    if (t.term == NULL_TERM)
        return SMT_BAD_DAG;

    // yices_push(smtContext);
    int code = yices_assert_formula(smtContext, t.term);
    if (code < 0) {
        setSolverTo(false);
    }
    code = yices_assert_formula(smtContext, t.term);
    if (code < 0) {
        yices_print_error(stderr);
        throw ExtensionException("Yices2 give up");
    }

    smt_status_t result = yices_check_context(smtContext, NULL);

    // yices_pop(smtContext);
    if (result == STATUS_SAT)
        return SMT_SAT;
    if (result == STATUS_UNSAT)
        return SMT_UNSAT;

    IssueWarning("Yices2 is not able to determine satisfiability  - giving up.");
    return SMT_SAT_UNKNOWN;
}

DagNode *SmtManager::simplifyDag(DagNode *dagNode, ExtensionSymbol* extensionSymbol) {
    hasVariable = false;

    try{
        push();
        resetFormulaSize();
        yices_term t = makeExpr(dagNode, extensionSymbol, false);
        Verbose("SimplifyFormulaSymbol : Formula size " << formulaSize);
        resetFormulaSize();

        ReverseSmtManagerVariableMap* rsv = nullptr;
        if (hasVariable){
            rsv = generateReverseVariableMap();
        }

        DagNode* dn = Term2Dag(t, extensionSymbol, rsv);

        if (hasVariable)
            delete rsv;
        pop();
        return dn;
    } catch(ExtensionException& ex){
        if (strcmp(ex.c_str(), "Exception but ok")){
            throw ExtensionException(yices_error_string());
        }
    }
    return nullptr;
}

DagNode* SmtManager::generateAssignment(DagNode *dagNode,
                                        SmtCheckerSymbol* smtCheckerSymbol) {

    Vector < DagNode * > dv;
    Vector < DagNode * > finalResult;

    model_t *model = yices_get_model(smtContext, true);

    if(model!=NULL) {
        // resultTerms must not be a pointer of term_vector_t.
        // if not, it will raise memory error.
        term_vector_t resultTerms;
        yices_init_term_vector(&resultTerms);
        yices_model_collect_defined_terms(model, &resultTerms);
        uint32_t num = resultTerms.size;

        // actual value
        int32_t va;

        ReverseSmtManagerVariableMap* rsv = nullptr;
        if (hasVariable)
            rsv = generateReverseVariableMap();

        // empty set
        if (num == 0) {
            finalResult.append(smtCheckerSymbol->emptySatAssignmentSetSymbol->makeDagNode());
        } else if (num == 1) {
            yices_term rTerm{};
            rTerm.term = resultTerms.data[0];
            rTerm.type = yices_type_of_term(rTerm.term);

            if (yices_get_bool_value(model, rTerm.term, &va) == TYPE_MISMATCH) {
                IssueWarning("This is not numeral type");
                throw ExtensionException("cannot make assignments");
            }

            dv.append(GenerateDag(model, rTerm, smtCheckerSymbol, rsv));
            dv.append(smtCheckerSymbol->emptySatAssignmentSetSymbol->makeDagNode());
            finalResult.append(smtCheckerSymbol->concatSatAssignmentSetSymbol->makeDagNode(dv));
        } else {
            if (num % 2 == 1) {
                for (int i = 0; i < num; i++) {
                    yices_term rTerm{};
                    rTerm.term = resultTerms.data[i];
                    rTerm.type = yices_type_of_term(rTerm.term);

                    if (yices_get_bool_value(model, rTerm.term, &va) == TYPE_MISMATCH) {
                        IssueWarning("This is not numeral type");
                        throw ExtensionException("cannot make assignments");
                    }
                    dv.append(GenerateDag(model, rTerm, smtCheckerSymbol, rsv));
                }
                dv.append(smtCheckerSymbol->emptySatAssignmentSetSymbol->makeDagNode());
            } else {
                for (int i = 0; i < num; i++) {
                    yices_term rTerm{};
                    rTerm.term = resultTerms.data[i];
                    rTerm.type = yices_type_of_term(rTerm.term);

                    if (yices_get_bool_value(model, rTerm.term, &va) == TYPE_MISMATCH) {
                        IssueWarning("This is not numeral type");
                        throw ExtensionException("cannot make assignments");
                    }
                    dv.append(GenerateDag(model, rTerm, smtCheckerSymbol, rsv));
                }
            }
            finalResult.append(smtCheckerSymbol->concatSatAssignmentSetSymbol->makeDagNode(dv));
        }
        DagNode *assn = smtCheckerSymbol->smtAssignmentResultSymbol->makeDagNode(finalResult);
        pop();

        if (hasVariable)
            delete rsv;

        yices_delete_term_vector(&resultTerms);
        yices_free_model(model);
        clearAssertions();
        return assn;
    }
    // sat but cannot generate model.
    throw ExtensionException("the context is sat but cannot generate model");
}

DagNode* SmtManager::GenerateDag(model_t *mdl, yices_term e, SmtCheckerSymbol* smtCheckerSymbol,
                                 ReverseSmtManagerVariableMap* rsv) {

    Vector < DagNode * > args(2);
    ReverseSmtManagerVariableMap::const_iterator it = rsv->find(e);
    if(it != rsv->end()){
        args[0] = it->second;
    }

    if (yices_term_is_int(e.term)) {
        int32_t returnVal;
        yices_get_int32_value(mdl, e.term, &returnVal);
        args[1] = new SMT_NumberDagNode(smtCheckerSymbol->integerSymbol, mpq_class(returnVal));
        return smtCheckerSymbol->intAssignmentSymbol->makeDagNode(args);
    } else if (yices_term_is_bool(e.term)) {
        int32_t returnVal;
        yices_get_bool_value(mdl, e.term, &returnVal);

        if (returnVal) {
            args[1] = smtCheckerSymbol->trueTerm.getDag();
        } else {
            args[1] = smtCheckerSymbol->falseTerm.getDag();
        }
        return smtCheckerSymbol->boolAssignmentSymbol->makeDagNode(args);
    } else if (yices_term_is_real(e.term)) {
        int32_t num;
        uint32_t den;
        yices_get_rational32_value(mdl, e.term, &num, &den);
        args[1] = new SMT_NumberDagNode(smtCheckerSymbol->realSymbol, mpq_class(num, den));
        return smtCheckerSymbol->realAssignmentSymbol->makeDagNode(args);
    } else {
        IssueWarning("Unsupported type");
    }
}

DagNode* SmtManager::Term2Dag(yices_term e, ExtensionSymbol* extensionSymbol,
                              ReverseSmtManagerVariableMap* rsv) {
    if(rsv != nullptr){
        ReverseSmtManagerVariableMap::const_iterator it = rsv->find(e);
        if (it != rsv->end()) {
            return it->second;
        }
    }

    switch (yices_term_constructor(e.term)) {
        case YICES_CONSTRUCTOR_ERROR:
            throw ExtensionException("Yices constructor error");
        case YICES_BOOL_CONSTANT: {
            int32_t returnVal;
            yices_bool_const_value(e.term, &returnVal);
            if (returnVal) {
                return extensionSymbol->trueTerm.getDag();
            } else {
                return extensionSymbol->falseTerm.getDag();
            }
        }
        case YICES_NOT_TERM: {
            Vector < DagNode * > arg(1);

            yices_term child{};
            child.term = yices_term_child(e.term, 0);
            child.type = yices_bool_type();

            arg[0] = Term2Dag(child, extensionSymbol, rsv);
            return extensionSymbol->notBoolSymbol->makeDagNode(arg);
        }
        case YICES_OR_TERM: {
            Vector < DagNode * > arg(2);

            yices_term child1{};
            yices_term child2{};

            child1.term = yices_term_child(e.term, 0);
            child1.type = yices_bool_type();

            child2.term = yices_term_child(e.term, 1);
            child2.type = yices_bool_type();

            arg[0] = Term2Dag(child1, extensionSymbol, rsv);
            arg[1] = Term2Dag(child2, extensionSymbol, rsv);
            return extensionSymbol->orBoolSymbol->makeDagNode(arg);
        }
        case YICES_XOR_TERM: {
            Vector < DagNode * > arg(2);

            yices_term child1{};
            yices_term child2{};

            child1.term = yices_term_child(e.term, 0);
            child1.type = yices_bool_type();

            child2.term = yices_term_child(e.term, 1);
            child2.type = yices_bool_type();

            arg[0] = Term2Dag(child1, extensionSymbol, rsv);
            arg[1] = Term2Dag(child2, extensionSymbol, rsv);
            return extensionSymbol->xorBoolSymbol->makeDagNode(arg);
        }
        case YICES_EQ_TERM: {
            Vector < DagNode * > arg(2);
            yices_term child1{};
            yices_term child2{};

            child1.term = yices_term_child(e.term, 0);
            child2.term = yices_term_child(e.term, 1);

            // real type
            if (yices_type_of_term(child1.term) == yices_real_type() ||
                yices_type_of_term(child2.term) == yices_real_type()){

                child1.type = yices_real_type();
                child2.type = yices_real_type();

                arg[0] = Term2Dag(child1, extensionSymbol, rsv);
                arg[1] = Term2Dag(child2, extensionSymbol, rsv);
                return extensionSymbol->eqRealSymbol->makeDagNode(arg);
            } else if (yices_type_of_term(child1.term) == yices_int_type() &&
                        yices_type_of_term(child2.term) == yices_int_type()){

                child1.type = yices_int_type();
                child2.type = yices_int_type();

                arg[0] = Term2Dag(child1, extensionSymbol, rsv);
                arg[1] = Term2Dag(child2, extensionSymbol, rsv);
                return extensionSymbol->eqIntSymbol->makeDagNode(arg);
            } else {

                child1.type = yices_bool_type();
                child2.type = yices_bool_type();

                arg[0] = Term2Dag(child1, extensionSymbol, rsv);
                arg[1] = Term2Dag(child2, extensionSymbol, rsv);
                return extensionSymbol->eqBoolSymbol->makeDagNode(arg);
            }
        }
        case YICES_ITE_TERM: {
            Vector < DagNode * > arg(3);
            yices_term child1{};
            yices_term child2{};
            yices_term child3{};

            child1.term = yices_term_child(e.term, 0);
            child2.term = yices_term_child(e.term, 1);
            child3.term = yices_term_child(e.term, 2);

            child1.type = yices_bool_type();

            if (yices_type_of_term(child2.term) == yices_int_type()){
                child2.type = yices_int_type();
                child3.type = yices_int_type();

                arg[0] = Term2Dag(child1, extensionSymbol, rsv);
                arg[1] = Term2Dag(child2, extensionSymbol, rsv);
                arg[2] = Term2Dag(child3, extensionSymbol, rsv);

                return extensionSymbol->iteIntSymbol->makeDagNode(arg);
            } else if (yices_type_of_term(child2.term) == yices_real_type()){
                child2.type = yices_real_type();
                child3.type = yices_real_type();

                arg[0] = Term2Dag(child1, extensionSymbol, rsv);
                arg[1] = Term2Dag(child2, extensionSymbol, rsv);
                arg[2] = Term2Dag(child3, extensionSymbol, rsv);

                return extensionSymbol->iteRealSymbol->makeDagNode(arg);
            } else {
                child2.type = yices_bool_type();
                child3.type = yices_bool_type();

                arg[0] = Term2Dag(child1, extensionSymbol, rsv);
                arg[1] = Term2Dag(child2, extensionSymbol, rsv);
                arg[2] = Term2Dag(child3, extensionSymbol, rsv);

                return extensionSymbol->iteBoolSymbol->makeDagNode(arg);
            }
        }
        case YICES_ARITH_GE_ATOM: {
   	        Vector < DagNode * > arg(2);
            yices_term child1{};
            yices_term child2{};

            child1.term = yices_term_child(e.term, 0);
	        child2.term = yices_term_child(e.term, 1);

	        if (yices_type_of_term(child1.term) == yices_real_type() ||
                yices_type_of_term(child2.term) == yices_real_type()){

                child1.type = yices_real_type();
                child2.type = yices_real_type();

                arg[0] = Term2Dag(child1, extensionSymbol, rsv);
                arg[1] = Term2Dag(child2, extensionSymbol, rsv);
                return extensionSymbol->geqRealSymbol->makeDagNode(arg);
            } else {
                child1.type = yices_int_type();
                child2.type = yices_int_type();

                arg[0] = Term2Dag(child1, extensionSymbol, rsv);
                arg[1] = Term2Dag(child2, extensionSymbol, rsv);
                return extensionSymbol->geqIntSymbol->makeDagNode(arg);
            }
        }
        case YICES_IS_INT_ATOM: {
            Vector < DagNode * > arg(1);

            yices_term child{};
            child.term = yices_term_child(e.term, 0);
            child.type = yices_real_type();

            arg[0] = Term2Dag(child, extensionSymbol, rsv);
            return extensionSymbol->isIntegerSymbol->makeDagNode(arg);
        }
        case YICES_IDIV: {
            Vector < DagNode * > arg(2);

            yices_term child1{};
            yices_term child2{};

            child1.term = yices_term_child(e.term, 0);
            child2.term = yices_term_child(e.term, 1);
            child1.type = yices_int_type();
            child2.type = yices_int_type();

            arg[0] = Term2Dag(child1, extensionSymbol, rsv);
            arg[1] = Term2Dag(child2, extensionSymbol, rsv);
            return extensionSymbol->divIntSymbol->makeDagNode(arg);
        }
        case YICES_RDIV: {
            Vector < DagNode * > arg(2);

            yices_term child1{};
            yices_term child2{};

            child1.term = yices_term_child(e.term, 0);
            child2.term = yices_term_child(e.term, 1);
            child1.type = yices_real_type();
            child2.type = yices_real_type();

            arg[0] = Term2Dag(child1, extensionSymbol, rsv);
            arg[1] = Term2Dag(child2, extensionSymbol, rsv);
            return extensionSymbol->divRealSymbol->makeDagNode(arg);
        }
        case YICES_IMOD: {
            Vector < DagNode * > arg(2);

            yices_term child1{};
            yices_term child2{};

            child1.term = yices_term_child(e.term, 0);
            child2.term = yices_term_child(e.term, 1);
            child1.type = yices_int_type();
            child2.type = yices_int_type();

            arg[0] = Term2Dag(child1, extensionSymbol, rsv);
            arg[1] = Term2Dag(child2, extensionSymbol, rsv);
            return extensionSymbol->modIntSymbol->makeDagNode(arg);
        }
        case YICES_FLOOR: {
            Vector < DagNode * > arg(1);

            yices_term child{};
            child.term = yices_term_child(e.term, 0);
            child.type = yices_real_type();

            arg[0] = Term2Dag(child, extensionSymbol, rsv);
            return extensionSymbol->toIntegerSymbol->makeDagNode(arg);
	    }
        case YICES_POWER_PRODUCT: {
            int child_num = yices_term_num_children(e.term);
            Vector < DagNode* > arg(child_num);
            for(int i = 0; i < child_num; i++){
                uint32_t exp;
                yices_term child{};
                child.type = e.type;
                yices_product_component(e.term, i, &child.term, &exp);
                arg[i] = Term2Dag(child, extensionSymbol, rsv);
            }

            if(yices_type_is_int(e.type))
                return multipleGen(&arg, 0, MulType::INT_MUL, extensionSymbol);
            else
                return multipleGen(&arg, 0, MulType::REAL_MUL, extensionSymbol);

        }
        case YICES_ARITH_SUM: {
            int child_num = yices_term_num_children(e.term);

            Vector < DagNode* > arg(child_num);

            for(int i = 0; i < child_num; i++){
                mpq_t coeff;
                mpq_init(coeff);

                yices_term child;
                yices_sum_component(e.term, i, coeff, &child.term);
                child.type = e.type;

                yices_term coeffTerm{};
                coeffTerm.term = yices_mpq(coeff);
                coeffTerm.type = e.type;

                if (child.term == NULL_TERM){
                    arg[i] = Term2Dag(coeffTerm, extensionSymbol, rsv);
                } else {
                    Vector < DagNode * > innerArg(2);
                    innerArg[0] = Term2Dag(coeffTerm, extensionSymbol, rsv);
                    innerArg[1] = Term2Dag(child, extensionSymbol, rsv);
                    if(child_num == 1){
                        if(yices_type_is_int(e.type)){
                            return extensionSymbol->mulIntSymbol->makeDagNode(innerArg);
                        } else {
                            return extensionSymbol->mulRealSymbol->makeDagNode(innerArg);
                        }
                    } else {
                        if(yices_type_is_int(e.type)){
                            arg[i] = extensionSymbol->mulIntSymbol->makeDagNode(innerArg);
                        } else {
                            arg[i] = extensionSymbol->mulRealSymbol->makeDagNode(innerArg);
                        }
                    }
                }
            }
            if(yices_type_is_int(e.type))
                return multipleGen(&arg, 0, MulType::INT_ADD, extensionSymbol);
            else
                return multipleGen(&arg, 0, MulType::REAL_ADD, extensionSymbol);
        }
        case YICES_UNINTERPRETED_TERM: {
            ReverseSmtManagerVariableMap::const_iterator it = rsv->find(e);
            if (it != rsv->end()) {
                if(it->second->symbol() == extensionSymbol->toRealSymbol){
                    Vector <DagNode*> tmp_arg(1);
                    tmp_arg[0] = it->second;
                    return extensionSymbol->toRealSymbol->makeDagNode(tmp_arg);
                }
                return it->second;
            }
        }
        case YICES_ARITH_CONSTANT: {
            mpq_t num;
            mpq_init(num);
            yices_rational_const_value(e.term, num);
            if (yices_type_is_int(e.type)) {
                return new SMT_NumberDagNode(extensionSymbol->integerSymbol, mpq_class(num));
            } else {
                return new SMT_NumberDagNode(extensionSymbol->realSymbol, mpq_class(num));
            }
        }
        default:
            throw ExtensionException("Exception but ok");
        }
}

yices_term SmtManager::variableGenerator(DagNode *dag, ExprType exprType) {
    hasVariable = true;

    // Two dag nodes are the same
    SmtManagerVariableMap::const_iterator it = smtManagerVariableMap.find(dag);
    if (it != smtManagerVariableMap.end())
        return it->second;

    // Dags are different while they both point to the same symbol
    for(auto it = smtManagerVariableMap.begin(); it != smtManagerVariableMap.end(); it++){
        if(dag->equal(it->first)){
            smtManagerVariableMap.insert(SmtManagerVariableMap::value_type(dag, it->second));
            return it->second;
        }
    }

    type_t type = NULL_TYPE;
    string name;

    if (VariableDagNode* v = dynamic_cast<VariableDagNode*>(dag)){
        Symbol *s = v->symbol();

        Sort *sort = s->getRangeSort();
        int id = v->id();
        name = Token::name(id);

        switch (AbstractSmtManager::smtInfo.getType(sort)) {
            case SMT_Info::NOT_SMT: {
                IssueWarning(
                        "Variable " << QUOTE(static_cast<DagNode *>(v)) <<
                        " does not belong to an SMT sort.");
                SMT_NULL_TERM();
            }
            case SMT_Info::BOOLEAN: {
                type = yices_bool_type();
                name = name + "_" + string("Boolean");
                break;
            }
            case SMT_Info::INTEGER: {
                type = yices_int_type();
                name = name + "_" + string("Integer");
                break;
            }
            case SMT_Info::REAL: {
                type = yices_int_type();
                name = name + "_" + string("Real");
                break;
            }
        }
    } else if(exprType != ExprType::BUILTIN) {
        switch (exprType){
            case BOOL:
                type = yices_bool_type();
                name = "b_";
                break;
            case INT:
                type = yices_int_type();
                name = "i_";
                break;
            case REAL:
                type = yices_real_type();
                name = "r_";
                break;
        }
        const void * address = static_cast<const void*>(dag);
        std::stringstream ss;
        ss << address;
        string varId = ss.str();
        name += varId;
    } else {
        SMT_NULL_TERM();
    }
    incrFormulaSize();
    yices_term newTerm{};
    newTerm.term = yices_new_uninterpreted_term(type);
    newTerm.type = type;
    yices_set_term_name(newTerm.term, name.c_str());

    smtManagerVariableMap.insert(SmtManagerVariableMap::value_type(dag, newTerm));
    return newTerm;
}

yices_term SmtManager::Dag2Term(DagNode *dag, ExtensionSymbol* extensionSymbol){
    if (SMT_NumberDagNode* n = dynamic_cast<SMT_NumberDagNode*>(dag)){
        incrFormulaSize();
        Sort *sort = n->symbol()->getRangeSort();
        if(AbstractSmtManager::smtInfo.getType(sort) == SMT_Info::INTEGER) {
            yices_term term{};
            term.term = yices_mpz(n->getValue().get_num_mpz_t());
            term.type = yices_int_type();
            return term;
        } else if (AbstractSmtManager::smtInfo.getType(sort) == SMT_Info::REAL) {
            yices_term term{};
            term.term = yices_mpq(n->getValue().get_mpq_t());
            term.type = yices_real_type();
            return term;
        }
    }

    try {
        return makeExtensionVariable(dag, extensionSymbol);
    } catch (ExtensionException& ex) {
        if (isNull(ex.c_str())) {
            if (SMT_Symbol * s = dynamic_cast<SMT_Symbol *>(dag->symbol())) {
                int nrArgs = s->arity();
                Vector <yices_term> terms(nrArgs);
                FreeDagNode *f = safeCast(FreeDagNode * , dag);

                for (int i = 0; i < nrArgs; ++i) {
                    terms[i] = Dag2Term(f->getArgument(i), extensionSymbol);
                }

                switch (s->getOperator()) {
                    //
                    //	Boolean stuff.
                    //
                    case SMT_Symbol::CONST_TRUE: {
                        incrFormulaSize();
                        yices_term term{};
                        term.term = yices_true();
                        term.type = yices_bool_type();
                        return term;
                    }
                    case SMT_Symbol::CONST_FALSE: {
                        incrFormulaSize();
                        yices_term term{};
                        term.term = yices_false();
                        term.type = yices_bool_type();
                        return term;
                    }
                    case SMT_Symbol::NOT: {
                        incrFormulaSize();
                        yices_term term{};
                        term.term = yices_not(terms[0].term);
                        term.type = yices_bool_type();
                        return term;
                    }
                    case SMT_Symbol::AND: {
                        incrFormulaSize();
                        yices_term term{};
                        term.term = yices_and2(terms[0].term, terms[1].term);
                        term.type = yices_bool_type();
                        return term;
                    }
                    case SMT_Symbol::OR: {
                        incrFormulaSize();
                        yices_term term{};
                        term.term = yices_or2(terms[0].term, terms[1].term);
                        term.type = yices_bool_type();
                        return term;
                    }
                    case SMT_Symbol::XOR: {
                        incrFormulaSize();
                        yices_term term{};
                        term.term = yices_xor2(terms[0].term, terms[1].term);
                        term.type = yices_bool_type();
                        return term;
                    }
                    case SMT_Symbol::IMPLIES: {
                        incrFormulaSize();
                        yices_term term{};
                        term.term = yices_implies(terms[0].term, terms[1].term);
                        term.type = yices_bool_type();
                        return term;
                    }
                        //
                        //	Polymorphic Boolean stuff.
                        //
                    case SMT_Symbol::EQUALS: {
                        incrFormulaSize();
                        yices_term term{};
                        term.term = yices_eq(terms[0].term, terms[1].term);
                        term.type = yices_bool_type();
                        return term;
                    }
                    case SMT_Symbol::NOT_EQUALS: {
                        incrFormulaSize();
                        yices_term term{};
                        term.term = yices_neq(terms[0].term, terms[1].term);
                        term.type = yices_bool_type();
                        return term;
                    }
                    case SMT_Symbol::ITE: {
                        incrFormulaSize();
                        yices_term term{};
                        term.term = yices_ite(terms[0].term, terms[1].term, terms[2].term);
                        term.type = terms[1].type;
                        return term;
                    }
                        //
                        //	Integer stuff.
                        //
                    case SMT_Symbol::UNARY_MINUS: {
                        incrFormulaSize();
                        yices_term term{};
                        term.term = yices_neg(terms[0].term);
                        term.type = terms[0].type;
                        return term;
                    }
                    case SMT_Symbol::MINUS: {
                        incrFormulaSize();
                        yices_term term{};
                        term.term = yices_sub(terms[0].term, terms[1].term);
                        term.type = terms[0].type;
                        return term;
                    }
                    case SMT_Symbol::PLUS: {
                        incrFormulaSize();
                        yices_term term{};
                        term.term = yices_add(terms[0].term, terms[1].term);
                        term.type = terms[0].type;
                        return term;
                    }
                    case SMT_Symbol::MULT: {
                        incrFormulaSize();
                        yices_term term{};
                        term.term = yices_mul(terms[0].term, terms[1].term);
                        term.type = terms[0].type;
                        return term;
                    }
                    case SMT_Symbol::DIV: {
                        incrFormulaSize();
                        yices_term term{};
                        term.term = yices_idiv(terms[0].term, terms[1].term);
                        term.type = terms[0].type;
                        return term;
                    }
                    case SMT_Symbol::MOD: {
                        incrFormulaSize();
                        yices_term term{};
                        term.term = yices_imod(terms[0].term, terms[1].term);
                        term.type = terms[0].type;
                        return term;
                    }
                        //
                        //	Integer tests.
                        //
                    case SMT_Symbol::LT: {
                        incrFormulaSize();
                        yices_term term{};
                        term.term = yices_arith_lt_atom(terms[0].term, terms[1].term);
                        term.type = yices_bool_type();
                        return term;
                    }
                    case SMT_Symbol::LEQ: {
                        incrFormulaSize();
                        yices_term term{};
                        term.term = yices_arith_leq_atom(terms[0].term, terms[1].term);
                        term.type = yices_bool_type();
                        return term;
                    }
                    case SMT_Symbol::GT: {
                        incrFormulaSize();
                        yices_term term{};
                        term.term = yices_arith_gt_atom(terms[0].term, terms[1].term);
                        term.type = yices_bool_type();
                        return term;
                    }
                    case SMT_Symbol::GEQ: {
                        incrFormulaSize();
                        yices_term term{};
                        term.term = yices_arith_geq_atom(terms[0].term, terms[1].term);
                        term.type = yices_bool_type();
                        return term;
                    }
                    case SMT_Symbol::DIVISIBLE: {
                        incrFormulaSize();
                        DagNode *a = f->getArgument(1);
                        if (SMT_NumberDagNode * n = dynamic_cast<SMT_NumberDagNode *>(a)) {
                            const mpq_class &rat = n->getValue();
                            if (rat > 0){
                                yices_term term{};
                                term.term = yices_divides_atom(terms[1].term, terms[0].term);
                                term.type = yices_bool_type();
                                return term;
                            }
                        }
                        IssueWarning("bad divisor in " << QUOTE(dag) << ".");
                        goto fail;
                    }
                        //
                        //	Stuff that is extra to reals.
                        //
                    case SMT_Symbol::REAL_DIVISION: {
                        incrFormulaSize();
                        yices_term term{};
                        term.term = yices_division(terms[0].term, terms[1].term);
                        term.type = terms[0].type;
                        return term;
                    }
                    case SMT_Symbol::TO_REAL: {
                        //
                        //	Yices2 treats integers as a subset of the reals.
                        //
                        incrFormulaSize();
                        yices_term term = terms[0];
                        term.type = yices_real_type();
                        return term;
                    }
                    case SMT_Symbol::TO_INTEGER: {
                        incrFormulaSize();
                        yices_term term{};
                        term.term = yices_floor(terms[0].term);
                        term.type = yices_int_type();
                        return term;
                    }
                    case SMT_Symbol::IS_INTEGER: {
                        incrFormulaSize();
                        yices_term term{};
                        term.term = yices_is_int_atom(terms[0].term);
                        term.type = yices_bool_type();
                        return term;
                    }
                }
            }
            // No issue warning
            IssueWarning("term " << QUOTE(dag) << " is not a valid SMT term.");
            fail:
            resetFormulaSize();
            throw ExtensionException("not a valid term, return original term instead");
        }
    }
}

DagNode* SmtManager::applyTactic(DagNode* dagNode, DagNode* tacticTypeDagNode, ExtensionSymbol* extensionSymbol){
    return dagNode;
}