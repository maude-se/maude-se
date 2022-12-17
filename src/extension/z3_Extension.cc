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

#include "dagArgumentIterator.hh"
#include "argumentIterator.hh"

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
#include "z3_Extension.hh"

SmtManager::SmtManager(const SMT_Info &smtInfo) : AbstractSmtManager(smtInfo) {
    pushCount = 0;
    s = new solver(ctx);
    hasVariable = false;
}

SmtManager::~SmtManager() {
    delete s;
}

SmtManager::Result SmtManager::assertDag(DagNode *dag) {
    expr ex = makeExpr(dag, nullptr, true);
    s->add(ex);

    switch (s->check()) {
        case unsat:
            return UNSAT;
        case sat:
            return SAT;
        case unknown:
            IssueWarning("Z3 reported an error - giving up:");
            return SAT_UNKNOWN;
    }
    IssueWarning("Z3 not able to determine satisfiability  - giving up.");
    return SAT_UNKNOWN;
}

SmtManager::Result SmtManager::checkDag(DagNode *dag) {
    try {
        expr e = makeExpr(dag, nullptr, true);
        s->add(e);
        switch (s->check()) {
            case unsat:
                return UNSAT;
            case sat: {
                return SAT;
            }
            case unknown:
                IssueWarning("Z3 not able to determine satisfiability  - giving up.");
                return SAT_UNKNOWN;
        }
    } catch (ExtensionException &ex) {
        IssueWarning("Error while smt solving : " << ex.c_str());
        throw ExtensionException("Error while smt solving");
    }
}

SmtManager::SmtResult SmtManager::checkDagContextFree(DagNode *dag,
                                                      ExtensionSymbol *extensionSymbol) {
    try {
        resetFormulaSize();
        expr e = makeExpr(dag, extensionSymbol, false);
        Verbose("SmtCheckSymbol : Formula size " << formulaSize);
        resetFormulaSize();
        s->add(e);

        switch (s->check()) {
            case unsat:
                return SMT_UNSAT;
            case sat: {
                return SMT_SAT;
            }
            case unknown:
                IssueWarning("Z3 not able to determine satisfiability  - giving up.");
                return SMT_SAT_UNKNOWN;
        }
    } catch (ExtensionException &ex) {
        IssueWarning("Error while smt solving : " << ex.c_str());
        throw ExtensionException("Error while smt solving");
    }
}

void SmtManager::push() {
    s->push();
    ++pushCount;
}

void SmtManager::pop() {
    Assert(pushCount > 0, "bad pop");
    s->pop();
    --pushCount;
}

void SmtManager::clearAssertions() {
    pushCount = 0;
    s->reset();
}

expr SmtManager::Dag2Term(DagNode *dag, ExtensionSymbol* extensionSymbol) {
    if (SMT_NumberDagNode * n = dynamic_cast<SMT_NumberDagNode *>(dag)) {
        incrFormulaSize();
        mpq_class value = n->getValue();
        Sort *sort = n->symbol()->getRangeSort();
        if(smtInfo.getType(sort) == SMT_Info::INTEGER){
            return ctx.int_val(value.get_str().c_str());
        } else if (smtInfo.getType(sort) == SMT_Info::REAL){
            return ctx.real_val(value.get_str().c_str());
        }
    }

    try {
        return makeExtensionVariable(dag, extensionSymbol);
    } catch (ExtensionException& ex) {
        if (isNull(ex.c_str())) {
            int nrArgs = dag->symbol()->arity();

            // need to be initialized with original ctx.
            std::vector <expr> exprs;

            FreeDagNode *f = safeCast(FreeDagNode * , dag);
            for (int i = 0; i < nrArgs; ++i) {

                expr e = Dag2Term(f->getArgument(i), extensionSymbol);
                exprs.push_back(e);
            }

            if (SMT_Symbol * s = dynamic_cast<SMT_Symbol *>(dag->symbol())) {
                switch (s->getOperator()) {
                    //
                    //	Boolean stuff.
                    //
                    case SMT_Symbol::CONST_TRUE: {
                        incrFormulaSize();
                        return ctx.bool_val(true);
                    }
                    case SMT_Symbol::CONST_FALSE: {
                        incrFormulaSize();
                        return ctx.bool_val(false);
                    }
                    case SMT_Symbol::NOT: {
                        incrFormulaSize();
                        return !exprs[0];
                    }

                    case SMT_Symbol::AND: {
                        incrFormulaSize();
                        return exprs[0] && exprs[1];
                    }
                    case SMT_Symbol::OR: {
                        incrFormulaSize();
                        return exprs[0] || exprs[1];
                    }
                    case SMT_Symbol::XOR: {
                        incrFormulaSize();
                        // there is no xor operation for c++ api
                        return expr(ctx, Z3_mk_xor(ctx, exprs[0], exprs[1]));
                    }
                    case SMT_Symbol::IMPLIES: {
                        incrFormulaSize();
                        return implies(exprs[0], exprs[1]);
                    }
                        //
                        //	Polymorphic Boolean stuff.
                        //
                    case SMT_Symbol::EQUALS: {
                        incrFormulaSize();
                        return exprs[0] == exprs[1];
                    }
                    case SMT_Symbol::NOT_EQUALS: {
                        incrFormulaSize();
                        return exprs[0] != exprs[1];
                    }
                    case SMT_Symbol::ITE: {
                        incrFormulaSize();
                        return ite(exprs[0], exprs[1], exprs[2]);
                    }
                        //
                        //	Integer stuff.
                        //
                    case SMT_Symbol::UNARY_MINUS: {
                        incrFormulaSize();
                        return -exprs[0];
                    }
                    case SMT_Symbol::MINUS: {
                        incrFormulaSize();
                        return exprs[0] - exprs[1];
                    }
                    case SMT_Symbol::PLUS: {
                        incrFormulaSize();
                        return exprs[0] + exprs[1];
                    }
                    case SMT_Symbol::MULT: {
                        incrFormulaSize();
                        return exprs[0] * exprs[1];
                    }
                    case SMT_Symbol::DIV: {
                        incrFormulaSize();
                        return exprs[0] / exprs[1];
                    }
                    case SMT_Symbol::MOD: {
                        incrFormulaSize();
                        return mod(exprs[0], exprs[1]);
                    }
                        //
                        //	Integer tests.
                        //

                    case SMT_Symbol::LT: {
                        incrFormulaSize();
                        return exprs[0] < exprs[1];
                    }
                    case SMT_Symbol::LEQ: {
                        incrFormulaSize();
                        return exprs[0] <= exprs[1];
                    }
                    case SMT_Symbol::GT: {
                        incrFormulaSize();
                        return exprs[0] > exprs[1];
                    }
                    case SMT_Symbol::GEQ: {
                        incrFormulaSize();
                        return exprs[0] >= exprs[1];
                    }

                    case SMT_Symbol::DIVISIBLE: {
                        //
                        //	Second argument must be a positive constant.
                        //	Typing ensures it is an integer.
                        //
                        incrFormulaSize();
                        DagNode *a = f->getArgument(1);
                        if (SMT_NumberDagNode * n = dynamic_cast<SMT_NumberDagNode *>(a)) {
                            const mpq_class &rat = n->getValue();
                            if (rat > 0) {
                                return exprs[1] / exprs[0];
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
                        return exprs[0] / exprs[1];
                    }
                    case SMT_Symbol::TO_REAL: {
                        incrFormulaSize();
                        return expr(ctx, Z3_mk_int2real(ctx, exprs[0]));
                    }
                    case SMT_Symbol::TO_INTEGER: {
                        incrFormulaSize();
                        return expr(ctx, Z3_mk_real2int(ctx, exprs[0]));
                    }
                    case SMT_Symbol::IS_INTEGER: {
                        incrFormulaSize();
                        return expr(ctx, Z3_mk_is_int(ctx, exprs[0]));;
                    }
                }
            } else {
                if(dag->symbol() == extensionSymbol->forallBoolSymbol ||
                   dag->symbol() == extensionSymbol->forallIntSymbol ||
                   dag->symbol() == extensionSymbol->forallRealSymbol){
                    incrFormulaSize();
                    return forall(exprs[0], exprs[1]);
                }

                if(dag->symbol() == extensionSymbol->existsBoolSymbol ||
                   dag->symbol() == extensionSymbol->existsIntSymbol ||
                   dag->symbol() == extensionSymbol->existsRealSymbol){
                    incrFormulaSize();
                    return exists(exprs[0], exprs[1]);
                }
            }
            IssueWarning("term " << QUOTE(dag) << " is not a valid SMT term.");
            fail:
            resetFormulaSize();
            throw ExtensionException("not a valid term, return original term instead");
        }
    }
}

expr SmtManager::variableGenerator(DagNode *dag, ExprType exprType) {
    hasVariable = true;

    // Two dag nodes are the same
    SmtManagerVariableMap::const_iterator it = smtManagerVariableMap.find(dag);
    if (it != smtManagerVariableMap.end())
        return it->second;

    // Two dag nodes are different while they both point to the same symbol
    for(auto it = smtManagerVariableMap.begin(); it != smtManagerVariableMap.end(); it++){
        if(dag->equal(it->first)){
            smtManagerVariableMap.insert(SmtManagerVariableMap::value_type(dag, it->second));
            return it->second;
        }
    }

    z3::sort type(ctx);
    string name;

    if (VariableDagNode* v = dynamic_cast<VariableDagNode*>(dag)){
        Symbol *s = v->symbol();

        Sort *sort = s->getRangeSort();
        int id = v->id();
        name = Token::name(id);

        switch (smtInfo.getType(sort)) {
            case SMT_Info::NOT_SMT: {
                IssueWarning("Variable " << QUOTE(static_cast<DagNode *>(v)) << " does not belong to an SMT sort.");
                SMT_NULL_TERM();
            }
            case SMT_Info::BOOLEAN: {
                type = ctx.bool_sort();
                name = name + "_" + string("Boolean");
                break;
            }
            case SMT_Info::INTEGER: {
                type = ctx.int_sort();
                name = name + "_" + string("Integer");
                break;
            }
            case SMT_Info::REAL: {
                type = ctx.real_sort();
                name = name + "_" + string("Real");
                break;
            }
        }
    } else if(exprType != ExprType::BUILTIN) {
        switch (exprType){
            case BOOL:
                type = ctx.bool_sort();
                name = "b_";
                break;
            case INT:
                type = ctx.int_sort();
                name = "i_";
                break;
            case REAL:
                type = ctx.real_sort();
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
    expr newVariable = ctx.constant(name.c_str(), type);
    smtManagerVariableMap.insert(SmtManagerVariableMap::value_type(dag, newVariable));
    return newVariable;
}

DagNode* SmtManager::Term2Dag(expr e, ExtensionSymbol* extensionSymbol,
                              ReverseSmtManagerVariableMap* rsv){
    if(rsv != nullptr){
        ReverseSmtManagerVariableMap::const_iterator it = rsv->find(e);
        if (it != rsv->end()) {
            return it->second;
        }
    }

    if (e.is_true()) {
        return extensionSymbol->trueTerm.getDag();
    }

    if (e.is_false()) {
        return extensionSymbol->falseTerm.getDag();
    }

    if (e.is_forall()) {
        unsigned num = Z3_get_quantifier_num_bound(ctx, e);
        DagNode* prev = nullptr;
        for (unsigned i = 0; i < num; i++) {
            DagNode* q_var = nullptr;
            Symbol* symbol = nullptr;

            unsigned at = (num - i) - 1;
            Z3_sort_kind type = Z3_get_sort_kind(ctx, Z3_get_quantifier_bound_sort(ctx, e, at));

            // make id, use "i" instead of "at"
            // because z3 use right-to-left de-Bruijn index
            std::stringstream ss;
            ss << i;
            string varId = ss.str();

            mpq_t total;
            mpq_init(total);
            mpq_set_str(total, varId.c_str(), 10);
            mpq_canonicalize(total);
            mpq_class mpNum (total);

            Vector < DagNode * > id_args(1);
            id_args[0] = new SMT_NumberDagNode(extensionSymbol->integerSymbol, mpNum);
            if (type == Z3_BOOL_SORT){
                q_var = extensionSymbol->freshBoolVarSymbol->makeDagNode(id_args);
                symbol = extensionSymbol->forallBoolSymbol;
            } else if (type == Z3_INT_SORT){
                q_var = extensionSymbol->freshIntVarSymbol->makeDagNode(id_args);
                symbol = extensionSymbol->forallIntSymbol;
            } else if (type == Z3_REAL_SORT){
                q_var = extensionSymbol->freshRealVarSymbol->makeDagNode(id_args);
                symbol = extensionSymbol->forallRealSymbol;
            } else {
                // raise error
            }

            if (q_var == nullptr || symbol == nullptr){
                // raise error
            }

            Vector < DagNode* > arg(2);
            arg[0] = q_var;

            if (prev == nullptr){
                arg[1] = Term2Dag(e.body(), extensionSymbol, rsv);
                prev = symbol->makeDagNode(arg);
            } else {
                arg[1] = prev;
                prev = symbol->makeDagNode(arg);
            }
        }

        if (prev == nullptr){
            // raise error
        }

        return prev;
    }

    if (e.is_exists()) {
        unsigned num = Z3_get_quantifier_num_bound(ctx, e);
        DagNode* prev = nullptr;
        for (unsigned i = 0; i < num; i++) {
            DagNode* q_var = nullptr;
            Symbol* symbol = nullptr;

            unsigned at = (num - i) - 1;
            Z3_sort_kind type = Z3_get_sort_kind(ctx, Z3_get_quantifier_bound_sort(ctx, e, at));

            // make id, use "i" instead of "at"
            // because z3 use right-to-left de-Bruijn index
            std::stringstream ss;
            ss << i;
            string varId = ss.str();

            mpq_t total;
            mpq_init(total);
            mpq_set_str(total, varId.c_str(), 10);
            mpq_canonicalize(total);
            mpq_class mpNum (total);

            Vector < DagNode * > id_args(1);
            id_args[0] = new SMT_NumberDagNode(extensionSymbol->integerSymbol, mpNum);
            if (type == Z3_BOOL_SORT){
                q_var = extensionSymbol->freshBoolVarSymbol->makeDagNode(id_args);
                symbol = extensionSymbol->existsBoolSymbol;
            } else if (type == Z3_INT_SORT){
                q_var = extensionSymbol->freshIntVarSymbol->makeDagNode(id_args);
                symbol = extensionSymbol->existsIntSymbol;
            } else if (type == Z3_REAL_SORT){
                q_var = extensionSymbol->freshRealVarSymbol->makeDagNode(id_args);
                symbol = extensionSymbol->existsRealSymbol;
            } else {
                // raise error
            }

            if (q_var == nullptr || symbol == nullptr){
                // raise error
            }

            Vector < DagNode* > arg(2);
            arg[0] = q_var;

            if (prev == nullptr){
                arg[1] = Term2Dag(e.body(), extensionSymbol, rsv);
                prev = symbol->makeDagNode(arg);
            } else {
                arg[1] = prev;
                prev = symbol->makeDagNode(arg);
            }
        }

        if (prev == nullptr){
            // raise error
        }

        return prev;
    }

    if (e.is_not()) {
        Vector < DagNode * > arg(1);
        arg[0] = Term2Dag(e.arg(0), extensionSymbol, rsv);
        return extensionSymbol->notBoolSymbol->makeDagNode(arg);
    }

    if (e.is_and()) {
        unsigned child_num = e.num_args();
        Vector < DagNode* > arg(child_num);
        for (unsigned i = 0; i < child_num; i++){
            arg[i] = Term2Dag(e.arg(i), extensionSymbol, rsv);
        }
        return multipleGen(&arg, 0, MulType::AND, extensionSymbol);
    }

    if (e.is_or()) {
        unsigned child_num = e.num_args();
        Vector < DagNode* > arg(child_num);
        for (unsigned i = 0; i < child_num; i++){
            arg[i] = Term2Dag(e.arg(i), extensionSymbol, rsv);
        }
        return multipleGen(&arg, 0, MulType::OR, extensionSymbol);
    }

    if (e.is_xor()) {
        Vector < DagNode * > arg(2);
        arg[0] = Term2Dag(e.arg(0), extensionSymbol, rsv);
        arg[1] = Term2Dag(e.arg(1), extensionSymbol, rsv);
        return extensionSymbol->xorBoolSymbol->makeDagNode(arg);
    }

    if (e.is_implies()) {
        Vector < DagNode * > arg(2);
        arg[0] = Term2Dag(e.arg(0), extensionSymbol, rsv);
        arg[1] = Term2Dag(e.arg(1), extensionSymbol, rsv);
        return extensionSymbol->impliesBoolSymbol->makeDagNode(arg);
    }

    if (e.is_eq()) {
        expr e1 = e.arg(0);
        expr e2 = e.arg(1);

        bool check_bool_eq = (!e1.is_bool() || e2.is_bool()) && (e1.is_bool() || !e2.is_bool());
        bool check_int_eq = (!e1.is_int() || e2.is_int()) && (e1.is_int() || !e2.is_int());
        bool check_real_eq = (!e1.is_real() || e2.is_real()) && (e1.is_real() || !e2.is_real());

        Assert(check_bool_eq && check_int_eq && check_real_eq, "lhs and rhs should have the same type");

        Vector < DagNode * > arg(2);
        arg[0] = Term2Dag(e1, extensionSymbol, rsv);
        arg[1] = Term2Dag(e2, extensionSymbol, rsv);
        if (e1.is_bool()){
            return extensionSymbol->eqBoolSymbol->makeDagNode(arg);
        } else if (e1.is_int()){
            return extensionSymbol->eqIntSymbol->makeDagNode(arg);
        } else if (e1.is_real()){
            return extensionSymbol->eqRealSymbol->makeDagNode(arg);
        }
    }

    // boolean
    if (e.is_ite()) {
        Vector < DagNode * > arg(3);
        arg[0] = Term2Dag(e.arg(0), extensionSymbol, rsv);
        arg[1] = Term2Dag(e.arg(1), extensionSymbol, rsv);
        arg[2] = Term2Dag(e.arg(2), extensionSymbol, rsv);
        if (e.arg(1).is_int())
            return extensionSymbol->iteIntSymbol->makeDagNode(arg);
        else if (e.arg(1).is_real())
            return extensionSymbol->iteRealSymbol->makeDagNode(arg);
        return extensionSymbol->iteBoolSymbol->makeDagNode(arg);
    }

    // boolean type
    if (e.is_app() && Z3_OP_LT == e.decl().decl_kind()) {
        Vector < DagNode * > arg(2);
        arg[0] = Term2Dag(e.arg(0), extensionSymbol, rsv);
        arg[1] = Term2Dag(e.arg(1), extensionSymbol, rsv);
        if (e.arg(0).is_int()) {
            return extensionSymbol->ltIntSymbol->makeDagNode(arg);
        } else {
            return extensionSymbol->ltRealSymbol->makeDagNode(arg);
        }
    }

    if (e.is_app() && Z3_OP_LE == e.decl().decl_kind()) {
        Vector < DagNode * > arg(2);
        arg[0] = Term2Dag(e.arg(0), extensionSymbol, rsv);
        arg[1] = Term2Dag(e.arg(1), extensionSymbol, rsv);
        if (e.arg(0).is_int()) {
            return extensionSymbol->leqIntSymbol->makeDagNode(arg);
        } else {
            return extensionSymbol->leqRealSymbol->makeDagNode(arg);
        }
    }

    if (e.is_app() && Z3_OP_GT == e.decl().decl_kind()) {
        Vector < DagNode * > arg(2);
        arg[0] = Term2Dag(e.arg(0), extensionSymbol, rsv);
        arg[1] = Term2Dag(e.arg(1), extensionSymbol, rsv);
        if (e.arg(0).is_int()) {
            return extensionSymbol->gtIntSymbol->makeDagNode(arg);
        } else {
            return extensionSymbol->gtRealSymbol->makeDagNode(arg);
        }
    }

    if (e.is_app() && Z3_OP_GE == e.decl().decl_kind()) {
        Vector < DagNode * > arg(2);
        arg[0] = Term2Dag(e.arg(0), extensionSymbol, rsv);
        arg[1] = Term2Dag(e.arg(1), extensionSymbol, rsv);
        if (e.arg(0).is_int()) {
            return extensionSymbol->geqIntSymbol->makeDagNode(arg);
        } else {
            return extensionSymbol->geqRealSymbol->makeDagNode(arg);
        }
    }

    if (e.is_app() && Z3_OP_EQ == e.decl().decl_kind()) {
        Vector < DagNode * > arg(2);
        arg[0] = Term2Dag(e.arg(0), extensionSymbol, rsv);
        arg[1] = Term2Dag(e.arg(1), extensionSymbol, rsv);
        if (e.arg(0).is_int()) {
            return extensionSymbol->eqIntSymbol->makeDagNode(arg);
        } else {
            return extensionSymbol->eqRealSymbol->makeDagNode(arg);
        }
    }

    if (e.is_app() && Z3_OP_IS_INT == e.decl().decl_kind()) {
        Vector < DagNode * > arg(1);
        arg[0] = Term2Dag(e.arg(0), extensionSymbol, rsv);
        return extensionSymbol->isIntegerSymbol->makeDagNode(arg);
    }

    /**
     * Integer operation
     */
    if (e.is_app() && Z3_OP_TO_INT == e.decl().decl_kind()) {
        Vector < DagNode * > arg(1);
        arg[0] = Term2Dag(e.arg(0), extensionSymbol, rsv);
        return extensionSymbol->toIntegerSymbol->makeDagNode(arg);
    }
    if (e.is_int() && e.is_app() && Z3_OP_UMINUS == e.decl().decl_kind()) {
        Vector < DagNode * > arg(1);
        arg[0] = Term2Dag(e.arg(0), extensionSymbol, rsv);
        return extensionSymbol->unaryMinusIntSymbol->makeDagNode(arg);
    }

    if (e.is_int() && e.is_app() && Z3_OP_ADD == e.decl().decl_kind()) {
        unsigned child_num = e.num_args();
        Vector < DagNode* > arg(child_num);
        for (unsigned i = 0; i < child_num; i++) {
            arg[i] = Term2Dag(e.arg(i), extensionSymbol, rsv);
        }
        return multipleGen(&arg, 0, MulType::INT_ADD, extensionSymbol);
    }

    if (e.is_int() && e.is_app() && Z3_OP_SUB == e.decl().decl_kind()) {
        unsigned child_num = e.num_args();
        Vector < DagNode* > arg(child_num);
        for (unsigned i = 0; i < child_num; i++){
            arg[i] = Term2Dag(e.arg(i), extensionSymbol, rsv);
        }
        return multipleGen(&arg, 0, MulType::INT_SUB, extensionSymbol);
    }

    if (e.is_int() && e.is_app() && Z3_OP_MUL == e.decl().decl_kind()) {
        unsigned child_num = e.num_args();
        Vector < DagNode* > arg(child_num);
        for (unsigned i = 0; i < child_num; i++) {
            arg[i] = Term2Dag(e.arg(i), extensionSymbol, rsv);
        }
        return multipleGen(&arg, 0, MulType::INT_MUL, extensionSymbol);
    }

    if (e.is_int() && e.is_app() && Z3_OP_DIV == e.decl().decl_kind()) {
        Vector < DagNode * > arg(2);
        arg[0] = Term2Dag(e.arg(0), extensionSymbol, rsv);
        arg[1] = Term2Dag(e.arg(1), extensionSymbol, rsv);
        return extensionSymbol->divIntSymbol->makeDagNode(arg);
    }


    if (e.is_int() && e.is_app() && Z3_OP_MOD == e.decl().decl_kind()) {
        Vector < DagNode * > arg(2);
        arg[0] = Term2Dag(e.arg(0), extensionSymbol, rsv);
        arg[1] = Term2Dag(e.arg(1), extensionSymbol, rsv);
        return extensionSymbol->modIntSymbol->makeDagNode(arg);
    }

    if (e.is_int() && e.is_numeral()) {
        try {
            mpq_t total;
            mpq_init(total);
            mpq_set_str(total, e.get_decimal_string(0).c_str(), 10);
            mpq_canonicalize(total);
            mpq_class mpNum (total);
            return new SMT_NumberDagNode(extensionSymbol->integerSymbol, mpNum);
        } catch (ExtensionException & ex){
            IssueWarning("[Term2Dag Error] " << ex.c_str() << " integer... ::>"<<e);
            throw ex;
        }
    }

    /**
     * Real type
     */
    if (e.is_app() && Z3_OP_TO_REAL == e.decl().decl_kind()) {
        Vector < DagNode * > arg(1);
        arg[0] = Term2Dag(e.arg(0), extensionSymbol, rsv);
        return extensionSymbol->toRealSymbol->makeDagNode(arg);
    }

    if (e.is_real() && e.is_app() && Z3_OP_UMINUS == e.decl().decl_kind()) {
        Vector < DagNode * > arg(1);
        arg[0] = Term2Dag(e.arg(0), extensionSymbol, rsv);
        return extensionSymbol->unaryMinusRealSymbol->makeDagNode(arg);
    }

    if (e.is_real() && e.is_app() && Z3_OP_ADD == e.decl().decl_kind()) {
        unsigned child_num = e.num_args();
        Vector < DagNode* > arg(child_num);
        for (unsigned i = 0; i < child_num; i++){
            arg[i] = Term2Dag(e.arg(i), extensionSymbol, rsv);
        }
        return multipleGen(&arg, 0, MulType::REAL_ADD, extensionSymbol);
    }

    if (e.is_real() && e.is_app() && Z3_OP_SUB == e.decl().decl_kind()) {
        unsigned child_num = e.num_args();
        Vector < DagNode* > arg(child_num);
        for (unsigned i = 0; i < child_num; i++){
            arg[i] = Term2Dag(e.arg(i), extensionSymbol, rsv);
        }
        return multipleGen(&arg, 0, MulType::REAL_SUB, extensionSymbol);
    }

    if (e.is_real() && e.is_app() && Z3_OP_MUL == e.decl().decl_kind()) {
        unsigned child_num = e.num_args();
        Vector < DagNode* > arg(child_num);
        for (unsigned i = 0; i < child_num; i++){
            arg[i] = Term2Dag(e.arg(i), extensionSymbol, rsv);
        }
        return multipleGen(&arg, 0, MulType::REAL_MUL, extensionSymbol);
    }

    if (e.is_real() && e.is_app() && Z3_OP_DIV == e.decl().decl_kind()) {
        Vector < DagNode * > arg(2);
        arg[0] = Term2Dag(e.arg(0), extensionSymbol, rsv);
        arg[1] = Term2Dag(e.arg(1), extensionSymbol, rsv);
        return extensionSymbol->divRealSymbol->makeDagNode(arg);
    }

    if (e.is_real() && e.is_numeral()) {
        try {
            mpq_t total;
            mpq_init(total);
            string newNum(e.numerator().get_decimal_string(0) + "/" + e.denominator().get_decimal_string(0));
            mpq_set_str(total, newNum.c_str(), 10);
            mpq_canonicalize(total);
            mpq_class mpNum (total);
            return new SMT_NumberDagNode(extensionSymbol->realSymbol, mpNum);
        }
        catch (ExtensionException & ex){
            throw ex;
        }
    }

    // for fresh quantified variable
    if (e.is_var()){
        unsigned index = Z3_get_index_value(ctx, e);

        std::stringstream ss;
        ss << index;
        string varId = ss.str();

        Vector< DagNode* > arg(1);

        mpq_t total;
        mpq_init(total);
        mpq_set_str(total, varId.c_str(), 10);
        mpq_canonicalize(total);
        mpq_class mpNum (total);
        arg[0] = new SMT_NumberDagNode(extensionSymbol->integerSymbol, mpNum);

        if (e.is_int()){
            return extensionSymbol->freshIntVarSymbol->makeDagNode(arg);
        } else if (e.is_real()){
            return extensionSymbol->freshRealVarSymbol->makeDagNode(arg);
        } else if (e.is_bool()){
            return extensionSymbol->freshBoolVarSymbol->makeDagNode(arg);
        } else {
            // raise exception
        }
    }
    throw ExtensionException("no matching case");
}

DagNode* SmtManager::generateAssignment(DagNode *dagNode,
                                        SmtCheckerSymbol* smtCheckerSymbol) {

    Vector < DagNode * > dv;
    Vector < DagNode * > finalResult;

    model m(ctx, s->get_model());
    int num = m.num_consts();
    if(!ctx.check_error()){
        ReverseSmtManagerVariableMap* rsv = nullptr;
        if (hasVariable)
            rsv = generateReverseVariableMap();

        if (num == 0) {
            finalResult.append(smtCheckerSymbol->emptySatAssignmentSetSymbol->makeDagNode());
        } else if (num == 1) {
            func_decl c = m.get_const_decl(0);
            expr r = m.get_const_interp(c);

            if (r.is_arith() && !r.is_numeral()) {
                IssueWarning("This is not numeral type");
                throw ExtensionException("not numeral");
            }

            dv.append(GenerateDag(c(), r, smtCheckerSymbol, rsv));
            dv.append(smtCheckerSymbol->emptySatAssignmentSetSymbol->makeDagNode());
            finalResult.append(smtCheckerSymbol->concatSatAssignmentSetSymbol->makeDagNode(dv));
        } else {
            if (num % 2 == 1) {
                for (int i = 0; i < num; i++) {
                    func_decl c = m.get_const_decl(i);
                    expr r = m.get_const_interp(c);

                    if (r.is_arith() && !r.is_numeral()) {
                        IssueWarning("This is not numeral type");
                        throw ExtensionException("not numeral");
                    }

                    dv.append(GenerateDag(c(), r, smtCheckerSymbol, rsv));
                }
                dv.append(smtCheckerSymbol->emptySatAssignmentSetSymbol->makeDagNode());
            } else {
                for (int i = 0; i < num; i++) {

                    func_decl c = m.get_const_decl(i);
                    expr r = m.get_const_interp(c);

                    if (r.is_arith() && !r.is_numeral()) {
                        IssueWarning("This is not numeral type");
                        throw ExtensionException("not numeral");
                    }

                    dv.append(GenerateDag(c(), r, smtCheckerSymbol, rsv));
                }
            }
            finalResult.append(smtCheckerSymbol->concatSatAssignmentSetSymbol->makeDagNode(dv));
        }

        if (hasVariable)
            delete rsv;

        return smtCheckerSymbol->smtAssignmentResultSymbol->makeDagNode(finalResult);
    }
    throw ExtensionException("the context is sat but cannot generate model");
}

DagNode* SmtManager::GenerateDag(expr lhs, expr rhs, SmtCheckerSymbol* smtCheckerSymbol,
                                 ReverseSmtManagerVariableMap* rsv) {
    try {
        Vector < DagNode * > args(2);
        ReverseSmtManagerVariableMap::const_iterator it = rsv->find(lhs);
        if(it != rsv->end()){
            args[0] = it->second;
        } else {
            throw ExtensionException("cannot generate assignment");
        }

        if (rhs.is_int()) {
            mpq_t total;
            mpq_init(total);
            // 10 base,
            mpq_set_str(total, rhs.get_decimal_string(0).c_str(), 10);
            mpq_canonicalize(total);
            mpq_class mpNum (total);
            args[1] = new SMT_NumberDagNode(smtCheckerSymbol->integerSymbol,mpNum);
            return smtCheckerSymbol->intAssignmentSymbol->makeDagNode(args);
        } else if (rhs.is_bool()) {
            if (rhs.is_true()) {
                args[1] = smtCheckerSymbol->trueTerm.getDag();
            } else {
                args[1] = smtCheckerSymbol->falseTerm.getDag();
            }
            return smtCheckerSymbol->boolAssignmentSymbol->makeDagNode(args);
        } else if (rhs.is_real()) {
            mpq_t total;
            mpq_init(total);

            string newNum(rhs.numerator().get_decimal_string(0) + "/" + rhs.denominator().get_decimal_string(0));
            mpq_set_str(total, newNum.c_str(), 10);
            mpq_canonicalize(total);
            mpq_class mpNum (total);

            args[1] = new SMT_NumberDagNode(smtCheckerSymbol->realSymbol,mpNum);
            return smtCheckerSymbol->realAssignmentSymbol->makeDagNode(args);
        } else {
            IssueWarning("Unsupported type");
        }
    } catch (ExtensionException &ex) {
        IssueWarning("Error while smt solving : " << ex.c_str());
        throw ex;
    }
}

DagNode* SmtManager::simplifyDag(DagNode *dagNode, ExtensionSymbol* extensionSymbol){
    try {
        resetFormulaSize();
        expr e = makeExpr(dagNode, extensionSymbol, false);
        resetFormulaSize();
        e = e.simplify();

        ReverseSmtManagerVariableMap* rsv = nullptr;
        if (hasVariable){
            rsv = generateReverseVariableMap();
        }
        DagNode* dn = Term2Dag(e, extensionSymbol, rsv);
        if (hasVariable)
            delete rsv;
        return dn;
    } catch (ExtensionException &ex) {
        IssueWarning("error simplify dag with " << ex.c_str());
        throw ExtensionException("Error while smt solving");
    }
}

DagNode* SmtManager::applyTactic(DagNode* dagNode, DagNode* tacticTypeDagNode, ExtensionSymbol* extensionSymbol){
    if (TacticApplySymbol* tacticApplySymbol = dynamic_cast<TacticApplySymbol*>(extensionSymbol)){
        goal g(ctx);
        expr e = makeExpr(dagNode, extensionSymbol, false);
        g.add(e);

        tactic t = Dag2Tactic(tacticApplySymbol, tacticTypeDagNode);
        apply_result r = t(g);
        int r_size = r.size();

        ReverseSmtManagerVariableMap* rsv = nullptr;
        if (hasVariable){
            rsv = generateReverseVariableMap();
        }

        Vector < DagNode * > arg(r_size);
        for (int i = 0; i < r_size; i++) {
            arg[i] = Term2Dag(r[i].as_expr(), extensionSymbol, rsv);
        }

        if (r_size == 1) {
            return arg[0];
        }

        if (hasVariable)
            delete rsv;

        return extensionSymbol->orBoolSymbol->makeDagNode(arg);
    } else {
        return dagNode;
    }
}

tactic SmtManager::Dag2Tactic(TacticApplySymbol* tacticApplySymbol, DagNode* tacticTypeDagNode){
    TacticApplySymbol::TacticType tacticType = tacticApplySymbol->getTacticType(tacticTypeDagNode);

    if (tacticType == TacticApplySymbol::NONE){
        IssueWarning("cannot find right tactic");
        throw ExtensionException("fail to find proper tactic");
    }

    if (tacticType == TacticApplySymbol::THEN) {
        FreeDagNode* f = safeCast(FreeDagNode*, tacticTypeDagNode);
        tactic t1 = Dag2Tactic(tacticApplySymbol, f->getArgument(0));
        tactic t2 = Dag2Tactic(tacticApplySymbol, f->getArgument(1));
        return par_and_then(t1, t2);
    } else if (tacticType == TacticApplySymbol::SIMPLIFY) {
        return tactic(ctx, "simplify");
    } else if (tacticType == TacticApplySymbol::QE) {
        return tactic(ctx, "qe");
    } else if (tacticType == TacticApplySymbol::QE2) {
        return tactic(ctx, "qe2");
    } else if (tacticType == TacticApplySymbol::CTX_SOLVER_SIMPLIFY) {
        return tactic(ctx, "ctx-solver-simplify");
    } else if (tacticType == TacticApplySymbol::PROP_IN_EQS) {
        return tactic(ctx, "propagate-ineqs");
    } else if (tacticType == TacticApplySymbol::PURIFY_ARITH) {
        return tactic(ctx, "purify-arith");
    } else if (tacticType == TacticApplySymbol::AND) {
        DagArgumentIterator i(tacticTypeDagNode);
        tactic t1 = Dag2Tactic(tacticApplySymbol, i.argument());
        i.next();
        tactic t2 = Dag2Tactic(tacticApplySymbol, i.argument());
        return t1 & t2;
    }

    IssueWarning("cannot find right tactic");
    throw ExtensionException("fail to find proper tactic");
}
