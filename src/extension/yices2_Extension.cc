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
    term_t t = makeBooleanExpr(dag);
    if (t == NULL_TERM)
        return BAD_DAG;

    yices_push(smtContext);
    int code = yices_assert_formula(smtContext, t);
    if (code < 0) {
        setSolverTo(false);
    }
    code = yices_assert_formula(smtContext, t);
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
    term_t t = makeBooleanExpr(dag);
    if (t == NULL_TERM)
        return BAD_DAG;

    int code = yices_assert_formula(smtContext, t);
    if (code < 0) {
        setSolverTo(false);
    }
    code = yices_assert_formula(smtContext, t);
    if (code < 0) {
        IssueWarning("Yices2 reported an error - giving up:");
        yices_print_error(stderr);
        yices_pop(smtContext);
        return SAT_UNKNOWN;
    }

    smt_status_t result = yices_check_context(smtContext, NULL);
    DebugAdvisory("yices_check_context() returned " << result);

    if (result == STATUS_SAT)
        return SAT;
    if (result == STATUS_UNSAT)
        return UNSAT;

    IssueWarning("Yices2 not able to determine satisfiability - giving up.");
    return SAT_UNKNOWN;
}

SmtManager::SmtResult SmtManager::checkDagContextFree(DagNode *dag,
                                                      ExtensionSymbol* extensionSymbol) {
    setSolverTo(true);
    resetFormulaSize();
    term_t t = makeExpr(dag, extensionSymbol, true);

    Verbose("SmtCheckSymbol : Formula size " << formulaSize);
    resetFormulaSize();
    if (t == NULL_TERM)
        return SMT_BAD_DAG;

    // yices_push(smtContext);
    int code = yices_assert_formula(smtContext, t);
    if (code < 0) {
        setSolverTo(false);
    }
    code = yices_assert_formula(smtContext, t);
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

    IssueWarning("Yices2 not able to determine satisfiability  - giving up.");
    return SMT_SAT_UNKNOWN;
}

DagNode *SmtManager::simplifyDag(DagNode *dagNode, ExtensionSymbol* extensionSymbol) {
    hasVariable = false;

    try{
        push();
        resetFormulaSize();
        term_t t = makeExpr(dagNode, extensionSymbol, false);
        Verbose("SimplifyFormulaSymbol : Formula size " << formulaSize);
        resetFormulaSize();

        DagNode* dn;
        ReverseSmtManagerVariableMap* rsv = nullptr;
        if (hasVariable){
            rsv = generateReverseVariableMap();
            for (auto it = rsv->begin(); it != rsv->end(); it++){
                char* s = yices_term_to_string(it->first, 80, 40, 0);
                yices_free_string(s);
            }
        }

        Symbol* symbol = dagNode->symbol();

        if(symbol == extensionSymbol->toIntegerSymbol)
            dn = Term2Dag(t, ExprType::INT, extensionSymbol, rsv);
        else if (symbol == extensionSymbol->toRealSymbol)
            dn = Term2Dag(t, ExprType::REAL, extensionSymbol, rsv);
        else if(symbol == extensionSymbol->intVarSymbol)
            dn = Term2Dag(t, ExprType::INT, extensionSymbol, rsv);
        else if(symbol == extensionSymbol->realVarSymbol)
            dn = Term2Dag(t, ExprType::REAL, extensionSymbol, rsv);
        else if(symbol == extensionSymbol->boolVarSymbol)
            dn = Term2Dag(t, ExprType::BOOL, extensionSymbol, rsv);
        else {
            Sort *sort = dagNode->symbol()->getRangeSort();

            switch (AbstractSmtManager::smtInfo.getType(sort)) {
                case SMT_Info::NOT_SMT: {
                    IssueWarning("dag " << QUOTE(dagNode) << " is not valid term.");
                    throw ExtensionException("dag is not valid term.");
                }
                case SMT_Info::BOOLEAN: {
                    dn = Term2Dag(t, ExprType::BOOL, extensionSymbol, rsv);
                    break;
                }
                case SMT_Info::INTEGER: {
                    dn = Term2Dag(t, ExprType::INT, extensionSymbol, rsv);
                    break;
                }
                case SMT_Info::REAL: {
                    dn = Term2Dag(t, ExprType::REAL, extensionSymbol, rsv);
                    break;
                }
            }
        }

        if (hasVariable)
            delete rsv;
        pop();
        return dn;
    } catch(ExtensionException& ex){
        if (strcmp(ex.c_str(), "Exception but ok")){
            throw ExtensionException("Yices2 catch error");
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
            term_t rTerm = resultTerms.data[0];

            if (yices_get_bool_value(model, rTerm, &va) == TYPE_MISMATCH) {
                IssueWarning("This is not numeral type");
                throw ExtensionException("cannot make assignments");
            }

            dv.append(GenerateDag(model, rTerm, smtCheckerSymbol, rsv));
            dv.append(smtCheckerSymbol->emptySatAssignmentSetSymbol->makeDagNode());
            finalResult.append(smtCheckerSymbol->concatSatAssignmentSetSymbol->makeDagNode(dv));
        } else {
            if (num % 2 == 1) {
                for (int i = 0; i < num; i++) {
                    term_t rTerm = resultTerms.data[i];

                    if (yices_get_bool_value(model, rTerm, &va) == TYPE_MISMATCH) {
                        IssueWarning("This is not numeral type");
                        throw ExtensionException("cannot make assignments");
                    }
                    dv.append(GenerateDag(model, rTerm, smtCheckerSymbol, rsv));
                }
                dv.append(smtCheckerSymbol->emptySatAssignmentSetSymbol->makeDagNode());
            } else {
                for (int i = 0; i < num; i++) {

                    term_t rTerm = resultTerms.data[i];
                    if (yices_get_bool_value(model, rTerm, &va) == TYPE_MISMATCH) {
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

DagNode* SmtManager::GenerateDag(model_t *mdl, term_t e, SmtCheckerSymbol* smtCheckerSymbol,
                                 ReverseSmtManagerVariableMap* rsv) {

    Vector < DagNode * > args(2);
    ReverseSmtManagerVariableMap::const_iterator it = rsv->find(e);
    if(it != rsv->end()){
        args[0] = it->second;
    }

    if (yices_term_is_int(e)) {
        int32_t returnVal;
        yices_get_int32_value(mdl, e, &returnVal);
        args[1] = new SMT_NumberDagNode(smtCheckerSymbol->integerSymbol, mpq_class(returnVal));
        return smtCheckerSymbol->intAssignmentSymbol->makeDagNode(args);
    } else if (yices_term_is_bool(e)) {
        int32_t returnVal;
        yices_get_bool_value(mdl, e, &returnVal);

        if (returnVal) {
            args[1] = smtCheckerSymbol->trueTerm.getDag();
        } else {
            args[1] = smtCheckerSymbol->falseTerm.getDag();
        }
        return smtCheckerSymbol->boolAssignmentSymbol->makeDagNode(args);
    } else if (yices_term_is_real(e)) {
        int32_t num;
        uint32_t den;
        yices_get_rational32_value(mdl, e, &num, &den);
        args[1] = new SMT_NumberDagNode(smtCheckerSymbol->realSymbol, mpq_class(num, den));
        return smtCheckerSymbol->realAssignmentSymbol->makeDagNode(args);
    } else {
        IssueWarning("Unsupported type");
    }
}

DagNode* SmtManager::Term2Dag(term_t e, ExprType exprType, ExtensionSymbol* extensionSymbol,
                              ReverseSmtManagerVariableMap* rsv) {

    switch (yices_term_constructor(e)) {
        case YICES_CONSTRUCTOR_ERROR:
            throw ExtensionException("Yices constructor error");
        case YICES_BOOL_CONSTANT: {
            int32_t returnVal;
            yices_bool_const_value(e, &returnVal);
            if (returnVal) {
                return extensionSymbol->trueTerm.getDag();
            } else {
                return extensionSymbol->falseTerm.getDag();
            }
        }
        case YICES_NOT_TERM: {
            Vector < DagNode * > arg(1);
            arg[0] = Term2Dag(yices_term_child(e, 0), exprType, extensionSymbol, rsv);
            return extensionSymbol->notBoolSymbol->makeDagNode(arg);
        }
        case YICES_OR_TERM: {
            Vector < DagNode * > arg(2);
            arg[0] = Term2Dag(yices_term_child(e, 0), exprType, extensionSymbol, rsv);
            arg[1] = Term2Dag(yices_term_child(e, 1), exprType, extensionSymbol, rsv);
            return extensionSymbol->orBoolSymbol->makeDagNode(arg);
        }
        case YICES_XOR_TERM: {
            Vector < DagNode * > arg(2);
            arg[0] = Term2Dag(yices_term_child(e, 0), exprType, extensionSymbol, rsv);
            arg[1] = Term2Dag(yices_term_child(e, 1), exprType, extensionSymbol, rsv);
            return extensionSymbol->xorBoolSymbol->makeDagNode(arg);
        }
        case YICES_EQ_TERM: {
            Vector < DagNode * > arg(2);
            term_t child0 = yices_term_child(e, 0);
            term_t child1 = yices_term_child(e, 1);

            // real type
            if (yices_type_of_term(child0) == yices_real_type() || yices_type_of_term(child1) == yices_real_type()){
                arg[0] = Term2Dag(child0, ExprType::REAL, extensionSymbol, rsv);
                arg[1] = Term2Dag(child1, ExprType::REAL, extensionSymbol, rsv);
            } else if (yices_type_of_term(child0) == yices_int_type() && yices_type_of_term(child1) == yices_int_type()){
                arg[0] = Term2Dag(child0, ExprType::INT, extensionSymbol, rsv);
                arg[1] = Term2Dag(child1, ExprType::INT, extensionSymbol, rsv);
            } else {
                arg[0] = Term2Dag(child0, ExprType::BOOL, extensionSymbol, rsv);
                arg[1] = Term2Dag(child1, ExprType::BOOL, extensionSymbol, rsv);
            }
            return extensionSymbol->eqBoolSymbol->makeDagNode(arg);
        }
        case YICES_ITE_TERM: {
            Vector < DagNode * > arg(3);
            term_t child0 = yices_term_child(e, 0);
            term_t child1 = yices_term_child(e, 1);
            term_t child2 = yices_term_child(e, 2);
            ExprType miniType;
            ExprType miniType2;
            if (yices_type_of_term(child0) == yices_real_type()){
                miniType = ExprType::REAL;
            } else if (yices_type_of_term(child0) == yices_int_type()){
                miniType = ExprType::INT;
            } else {
                miniType = ExprType::BOOL;
            }

            if (yices_type_of_term(child1) == yices_real_type()){
                miniType2 = ExprType::REAL;
            } else if (yices_type_of_term(child1) == yices_int_type()){
                miniType2 = ExprType::INT;
            } else {
                miniType2 = ExprType::BOOL;
            }

            arg[0] = Term2Dag(yices_term_child(e, 0), miniType, extensionSymbol, rsv);
            arg[1] = Term2Dag(child1, miniType2, extensionSymbol, rsv);
            arg[2] = Term2Dag(child2, miniType2, extensionSymbol, rsv);

            if (exprType == ExprType::INT)
                return extensionSymbol->iteIntSymbol->makeDagNode(arg);
            else if (exprType == ExprType::REAL)
                return extensionSymbol->iteRealSymbol->makeDagNode(arg);
            return extensionSymbol->iteBoolSymbol->makeDagNode(arg);
        }
        case YICES_ARITH_GE_ATOM: {
   	        Vector < DagNode * > arg(2);
            term_t child0 = yices_term_child(e, 0);
	        term_t child1 = yices_term_child(e, 1);

	        if (yices_type_of_term(child0) == yices_real_type() || yices_type_of_term(child1) == yices_real_type()){
                arg[0] = Term2Dag(child0, ExprType::REAL, extensionSymbol, rsv);
                arg[1] = Term2Dag(child1, ExprType::REAL, extensionSymbol, rsv);
                return extensionSymbol->geqRealSymbol->makeDagNode(arg);
            } else {
                arg[0] = Term2Dag(child0, ExprType::INT, extensionSymbol, rsv);
                arg[1] = Term2Dag(child1, ExprType::INT, extensionSymbol, rsv);
                return extensionSymbol->geqIntSymbol->makeDagNode(arg);
            }
        }
        case YICES_IS_INT_ATOM: {
            Vector < DagNode * > arg(1);
            arg[0] = Term2Dag(yices_term_child(e, 0), exprType, extensionSymbol, rsv);
            return extensionSymbol->isIntegerSymbol->makeDagNode(arg);
        }
        case YICES_IDIV: {
            Vector < DagNode * > arg(2);
            arg[0] = Term2Dag(yices_term_child(e, 0), exprType, extensionSymbol, rsv);
            arg[1] = Term2Dag(yices_term_child(e, 1), exprType, extensionSymbol, rsv);
            return extensionSymbol->divIntSymbol->makeDagNode(arg);
        }
        case YICES_RDIV: {
            Vector < DagNode * > arg(2);
            arg[0] = Term2Dag(yices_term_child(e, 0), exprType, extensionSymbol, rsv);
            arg[1] = Term2Dag(yices_term_child(e, 1), exprType, extensionSymbol, rsv);
            return extensionSymbol->divRealSymbol->makeDagNode(arg);
        }
        case YICES_IMOD: {
            Vector < DagNode * > arg(2);
            arg[0] = Term2Dag(yices_term_child(e, 0), exprType, extensionSymbol, rsv);
            arg[1] = Term2Dag(yices_term_child(e, 1), exprType, extensionSymbol, rsv);
            return extensionSymbol->modIntSymbol->makeDagNode(arg);
        }
        case YICES_FLOOR: {
            Vector < DagNode * > arg(1);
            arg[0] = Term2Dag(yices_term_child(e, 0), exprType, extensionSymbol, rsv);
            return extensionSymbol->toIntegerSymbol->makeDagNode(arg);
	    }
        case YICES_POWER_PRODUCT: {
            int child_num = yices_term_num_children(e);
            Vector < DagNode* > arg(child_num);
            for(int i = 0; i < child_num; i++){
                uint32_t exp;
                term_t child;
                yices_product_component(e, i, &child, &exp);
                arg[i] = Term2Dag(child, exprType, extensionSymbol, rsv);
            }

            if(exprType == ExprType::INT)
                return multipleGen(&arg, 0, MulType::INT_MUL, extensionSymbol);
            else
                return multipleGen(&arg, 0, MulType::REAL_MUL, extensionSymbol);

        }
        case YICES_ARITH_SUM: {
            int child_num = yices_term_num_children(e);
            Vector < DagNode* > arg(child_num);
            int isInt = exprType == ExprType::INT;
            for(int i = 0; i < child_num; i++){
                mpq_t coeff;
                mpq_init(coeff);
                term_t child;
                yices_sum_component(e, i, coeff, &child);

                if (child == NULL_TERM){
                    arg[i] = Term2Dag(yices_mpq(coeff), exprType, extensionSymbol, rsv);
                } else {
                    Vector < DagNode * > innerArg(2);
                    innerArg[0] = Term2Dag(yices_mpq(coeff), exprType, extensionSymbol, rsv);
                    innerArg[1] = Term2Dag(child, exprType, extensionSymbol, rsv);
                    if(child_num == 1){
                        if(isInt)
                            return extensionSymbol->mulIntSymbol->makeDagNode(innerArg);
                        else
                            return extensionSymbol->mulRealSymbol->makeDagNode(innerArg);
                    } else {
                        if(isInt)
                            arg[i] = extensionSymbol->mulIntSymbol->makeDagNode(innerArg);
                        else
                            arg[i] = extensionSymbol->mulRealSymbol->makeDagNode(innerArg);
                    }
                }
            }
            if(isInt)
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
                    DagNode* d = extensionSymbol->toRealSymbol->makeDagNode(tmp_arg);
                    return d;
                }
                return it->second;
            }
        }
        case YICES_ARITH_CONSTANT: {
            mpq_t num;
            mpq_init(num);
            yices_rational_const_value(e, num);
            if (exprType == ExprType::INT) {
                return new SMT_NumberDagNode(extensionSymbol->integerSymbol, mpq_class(num));
            } else if (exprType == ExprType::REAL) {
                return new SMT_NumberDagNode(extensionSymbol->realSymbol, mpq_class(num));
            }
        }
        default:
            throw ExtensionException("Exception but ok");
        }
}

term_t SmtManager::variableGenerator(DagNode *dag, ExprType exprType) {
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
    term_t newVariable = yices_new_uninterpreted_term(type);
    yices_set_term_name(newVariable, name.c_str());

    smtManagerVariableMap.insert(SmtManagerVariableMap::value_type(dag, newVariable));
    return newVariable;
}

term_t SmtManager::Dag2Term(DagNode *dag, ExtensionSymbol* extensionSymbol){
    if (SMT_NumberDagNode* n = dynamic_cast<SMT_NumberDagNode*>(dag)){
        incrFormulaSize();
        return yices_mpq(n->getValue().get_mpq_t());
    }

    try {
        return makeExtensionVariable(dag, extensionSymbol);
    } catch (ExtensionException& ex) {
        if (isNull(ex.c_str())) {
            if (SMT_Symbol * s = dynamic_cast<SMT_Symbol *>(dag->symbol())) {
                int nrArgs = s->arity();
                Vector <term_t> terms(nrArgs);
                FreeDagNode *f = safeCast(FreeDagNode * , dag);

                for (int i = 0; i < nrArgs; ++i) {
                    term_t t = Dag2Term(f->getArgument(i), extensionSymbol);
                    terms[i] = t;
                }

                switch (s->getOperator()) {
                    //
                    //	Boolean stuff.
                    //
                    case SMT_Symbol::CONST_TRUE: {
                        incrFormulaSize();
                        return yices_true();
                    }
                    case SMT_Symbol::CONST_FALSE: {
                        incrFormulaSize();
                        return yices_false();
                    }
                    case SMT_Symbol::NOT: {
                        incrFormulaSize();
                        return yices_not(terms[0]);
                    }
                    case SMT_Symbol::AND: {
                        incrFormulaSize();
                        return yices_and2(terms[0], terms[1]);
                    }
                    case SMT_Symbol::OR: {
                        incrFormulaSize();
                        return yices_or2(terms[0], terms[1]);
                    }
                    case SMT_Symbol::XOR: {
                        incrFormulaSize();
                        return yices_xor2(terms[0], terms[1]);
                    }
                    case SMT_Symbol::IMPLIES: {
                        incrFormulaSize();
                        return yices_implies(terms[0], terms[1]);
                    }
                        //
                        //	Polymorphic Boolean stuff.
                        //
                    case SMT_Symbol::EQUALS: {
                        incrFormulaSize();
                        return yices_eq(terms[0], terms[1]);
                    }
                    case SMT_Symbol::NOT_EQUALS: {
                        incrFormulaSize();
                        return yices_neq(terms[0], terms[1]);
                    }
                    case SMT_Symbol::ITE: {
                        incrFormulaSize();
                        return yices_ite(terms[0], terms[1], terms[2]);
                    }
                        //
                        //	Integer stuff.
                        //
                    case SMT_Symbol::UNARY_MINUS: {
                        incrFormulaSize();
                        return yices_neg(terms[0]);
                    }
                    case SMT_Symbol::MINUS: {
                        incrFormulaSize();
                        return yices_sub(terms[0], terms[1]);
                    }
                    case SMT_Symbol::PLUS: {
                        incrFormulaSize();
                        return yices_add(terms[0], terms[1]);
                    }
                    case SMT_Symbol::MULT: {
                        incrFormulaSize();
                        return yices_mul(terms[0], terms[1]);
                    }
                    case SMT_Symbol::DIV: {
                        incrFormulaSize();
                        return yices_idiv(terms[0], terms[1]);
                    }
                    case SMT_Symbol::MOD: {
                        incrFormulaSize();
                        return yices_imod(terms[0], terms[1]);
                    }
                        //
                        //	Integer tests.
                        //
                    case SMT_Symbol::LT: {
                        incrFormulaSize();
                        return yices_arith_lt_atom(terms[0], terms[1]);
                    }
                    case SMT_Symbol::LEQ: {
                        incrFormulaSize();
                        return yices_arith_leq_atom(terms[0], terms[1]);
                    }
                    case SMT_Symbol::GT: {
                        incrFormulaSize();
                        return yices_arith_gt_atom(terms[0], terms[1]);
                    }
                    case SMT_Symbol::GEQ: {
                        incrFormulaSize();
                        return yices_arith_geq_atom(terms[0], terms[1]);
                    }
                    case SMT_Symbol::DIVISIBLE: {
                        incrFormulaSize();
                        DagNode *a = f->getArgument(1);
                        if (SMT_NumberDagNode * n = dynamic_cast<SMT_NumberDagNode *>(a)) {
                            const mpq_class &rat = n->getValue();
                            if (rat > 0)
                                return yices_divides_atom(terms[1], terms[0]);
                        }
                        IssueWarning("bad divisor in " << QUOTE(dag) << ".");
                        goto fail;
                    }
                        //
                        //	Stuff that is extra to reals.
                        //
                    case SMT_Symbol::REAL_DIVISION: {
                        incrFormulaSize();
                        return yices_division(terms[0], terms[1]);
                    }
                    case SMT_Symbol::TO_REAL: {
                        //
                        //	Yices2 treats integers as a subset of the reals.
                        //
                        incrFormulaSize();
                        return terms[0];
                    }
                    case SMT_Symbol::TO_INTEGER: {
                        incrFormulaSize();
                        return yices_floor(terms[0]);
                    }
                    case SMT_Symbol::IS_INTEGER: {
                        incrFormulaSize();
                        return yices_is_int_atom(terms[0]);

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