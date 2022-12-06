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

#include "token.hh"
#include "cvc4_Extension.hh"
#include <sstream>

SmtManager::SmtManager(const SMT_Info &smtInfo)
        : AbstractSmtManager(smtInfo), VariableGenerator(smtInfo) {
    hasVariable = false;
}

void SmtManager::setSolverTo(bool isLinear) {
    smtEngine->reset();
    smtEngine->setOption("produce-models", new SExpr(true));
    if (isLinear){
        smtEngine->setLogic("QF_LIRA");
        isSolverLinear = true;
    } else {
        smtEngine->setLogic("QF_NIRA");
        isSolverLinear = false;
    }
}

void SmtManager::prefixGetValue(SmtEngine &smt, Expr e, Assignment *assn, int level) {

    // Checks if this is correct or not.
    if (e.getKind() == kind::UNINTERPRETED_CONSTANT || e.getKind() == kind::VARIABLE) {
        AssignmentElem assnElem = std::pair<Expr, Expr>(e, smt.getValue(e));
        Assignment::iterator iter = std::find(assn->begin(), assn->end(), assnElem);
        // If not exists
        if (iter == assn->end()){
            assn->push_back(assnElem);
        }

    }

    if (e.hasOperator() && e.getOperator().getKind() != kind::BUILTIN) {
        prefixGetValue(smt, e.getOperator(), assn, level + 1);
    }

    for (Expr::const_iterator term_i = e.begin(), term_end = e.end();
         term_i != term_end; ++term_i) {
        Expr curr = *term_i;
        prefixGetValue(smt, curr, assn, level + 1);
    }
}

SmtManager::SmtResult SmtManager::checkDagContextFree(DagNode *dag,
                                                      ExtensionSymbol* extensionSymbol){
    setSolverTo(true);
    resetFormulaSize();
    checkDagResultExp = makeExpr(dag, extensionSymbol, true);
    Verbose("SmtCheckSymbol : Formula size " << formulaSize);
    resetFormulaSize();
    if (checkDagResultExp.term.isNull())
        return SMT_BAD_DAG;

    bool logicError = false;
    CVC4::Result result;
    try {
        result = smtEngine->checkSat(checkDagResultExp.term);
    } catch (const CVC4::LogicException&) {
        logicError = true;
    }

    if (logicError){
        setSolverTo(false);
        try {
            result = smtEngine->checkSat(checkDagResultExp.term);
        } catch (const CVC4::LogicException&) {
            //	An expression is out-side of the supported logic - e.g. nonlinear.
            IssueWarning("Caught CVC4::LogicException - giving up.");
            return SMT_SAT_UNKNOWN;
        }
    }

    CVC4::Result::Sat sat = result.isSat();
    if (sat == CVC4::Result::SAT_UNKNOWN) {
        IssueWarning("CVC4 not able to determine satisfiability  - giving up.");
        return SMT_SAT_UNKNOWN;
    }
    return (sat == false) ? SMT_UNSAT : SMT_SAT;
}

// Assumption: must be called after all satCheck is done.
DagNode* SmtManager::generateAssignment(DagNode *dagNode,
                                        SmtCheckerSymbol* smtCheckerSymbol) {
    Vector < DagNode * > dv;
    Vector < DagNode * > finalResult;

    Assignment assignment;
    prefixGetValue(*smtEngine, checkDagResultExp.term, &assignment);

    int num = assignment.size();

    ReverseSmtManagerVariableMap* rsv = nullptr;
    if (hasVariable)
        rsv = generateReverseVariableMap();

    // num == 0: empty set, num == 1: only one assignment in the set
    if (num == 0) {
        finalResult.append(smtCheckerSymbol->emptySatAssignmentSetSymbol->makeDagNode());
    }
    else if (num == 1) {
        dv.append(GenerateDag(assignment[0].first, assignment[0].second, smtCheckerSymbol, rsv));
        dv.append(smtCheckerSymbol->emptySatAssignmentSetSymbol->makeDagNode());
        finalResult.append(smtCheckerSymbol->concatSatAssignmentSetSymbol->makeDagNode(dv));
    } else {
        if (num % 2 == 1) {
            for (int i = 0; i < num; i++) {
                dv.append(GenerateDag(assignment[i].first, assignment[i].second, smtCheckerSymbol, rsv));
            }
            dv.append(smtCheckerSymbol->emptySatAssignmentSetSymbol->makeDagNode());
        } else {
            for (int i = 0; i < num; i++) {
                dv.append(GenerateDag(assignment[i].first, assignment[i].second, smtCheckerSymbol, rsv));
            }
        }
        finalResult.append(smtCheckerSymbol->concatSatAssignmentSetSymbol->makeDagNode(dv));
    }

    if (hasVariable)
        delete rsv;

    return smtCheckerSymbol->smtAssignmentResultSymbol->makeDagNode(finalResult);
}

void SmtManager::clearAssertions() {
    // overriding variable generator's clear assertions
    pushCount = 0;
    smtEngine->reset();
}

DagNode* SmtManager::GenerateDag(Expr lhs, Expr rhs, SmtCheckerSymbol* smtCheckerSymbol,
                                 ReverseSmtManagerVariableMap* rsv) {

    Vector < DagNode * > args(2);
    bool isNone = true;
    for(auto it = rsv->begin(); it != rsv->end(); it++){
        if (it->first.term.getId() == lhs.getId()){
            args[0] = it->second;
            isNone = false;
            break;
        }
    }

    if(isNone){
        throw ExtensionException("cannot generate assignment");
    }

    if (lhs.getType().isInteger()) {
        mpq_class returnVal = rhs.getConst<Rational>().getValue();
        args[1] = new SMT_NumberDagNode(smtCheckerSymbol->integerSymbol,returnVal);
        return smtCheckerSymbol->intAssignmentSymbol->makeDagNode(args);
    } else if (lhs.getType().isBoolean()) {
        std::stringstream ss;
        ss << rhs;
        string boolVal = ss.str();

        if (boolVal == "TRUE") {
            args[1] = smtCheckerSymbol->trueTerm.getDag();
        } else {
            args[1] = smtCheckerSymbol->falseTerm.getDag();
        }
        return smtCheckerSymbol->boolAssignmentSymbol->makeDagNode(args);
    } else if (lhs.getType().isReal()) {
        mpq_class returnVal = rhs.getConst<Rational>().getValue();
        args[1] = new SMT_NumberDagNode(smtCheckerSymbol->realSymbol,returnVal);
        return smtCheckerSymbol->realAssignmentSymbol->makeDagNode(args);
    } else {
        IssueWarning("Unsupported type");
    }

}

DagNode *SmtManager::Term2Dag(cvc4_term expr, ExtensionSymbol* extensionSymbol,
                              ReverseSmtManagerVariableMap* rsv){
    if(rsv != nullptr){
        ReverseSmtManagerVariableMap::const_iterator it = rsv->find(expr);
        if (it != rsv->end()) {
            return it->second;
        }
    }

    Expr e = expr.term;

    switch (e.getKind()) {
        case kind::UNDEFINED_KIND:
            throw ExtensionException("undefined kind error");
        case kind::CONST_BOOLEAN: {
            std::stringstream ss;
            ss << e;
            string boolVal = ss.str();

            if (boolVal == "TRUE") {
                return extensionSymbol->trueTerm.getDag();
            } else {
                return extensionSymbol->falseTerm.getDag();
            }
        }
        case kind::NOT: {
            Vector < DagNode * > arg(1);

            cvc4_term child{};
            child.term = e[0];
            child.type = exprManager->booleanType();

            arg[0] = Term2Dag(child, extensionSymbol, rsv);
            return extensionSymbol->notBoolSymbol->makeDagNode(arg);
        }
        case kind::AND: {
            size_t child_num = e.getNumChildren();
            Vector < DagNode* > arg(child_num);
            for(size_t i = 0; i < child_num; i++){
                cvc4_term child{};
                child.term = e[i];
                child.type = exprManager->booleanType();

                arg[i] = Term2Dag(child, extensionSymbol, rsv);
            }
            return multipleGen(&arg, 0, MulType::AND, extensionSymbol);
        }
        case kind::IMPLIES: {
            Vector < DagNode * > arg(2);

            cvc4_term child1{};
            cvc4_term child2{};

            child1.term = e[0];
            child2.term = e[1];

            child1.type = exprManager->booleanType();
            child2.type = exprManager->booleanType();

            arg[0] = Term2Dag(child1, extensionSymbol, rsv);
            arg[1] = Term2Dag(child2, extensionSymbol, rsv);
            return extensionSymbol->impliesBoolSymbol->makeDagNode(arg);

        }
        case kind::OR: {
            size_t child_num = e.getNumChildren();
            Vector < DagNode* > arg(child_num);
            for(size_t i = 0; i < child_num; i++){
                cvc4_term child{};
                child.term = e[i];
                child.type = exprManager->booleanType();

                arg[i] = Term2Dag(child, extensionSymbol, rsv);
            }
            return multipleGen(&arg, 0, MulType::OR, extensionSymbol);
        }
        case kind::XOR: {
            Vector < DagNode * > arg(2);

            cvc4_term child1{};
            cvc4_term child2{};

            child1.term = e[0];
            child2.term = e[1];

            child1.type = exprManager->booleanType();
            child2.type = exprManager->booleanType();

            arg[0] = Term2Dag(child1, extensionSymbol, rsv);
            arg[1] = Term2Dag(child2, extensionSymbol, rsv);
            return extensionSymbol->xorBoolSymbol->makeDagNode(arg);
        }
        case kind::EQUAL: {
            Vector < DagNode * > arg(2);

            cvc4_term child1{};
            cvc4_term child2{};

            child1.term = e[0];
            child2.term = e[1];

            if (e[0].getType().isInteger()) {
                child1.type = exprManager->integerType();
                child2.type = exprManager->integerType();

                arg[0] = Term2Dag(child1, extensionSymbol, rsv);
                arg[1] = Term2Dag(child2, extensionSymbol, rsv);
                return extensionSymbol->eqIntSymbol->makeDagNode(arg);
            } else if (e[0].getType().isReal()) {
                child1.type = exprManager->realType();
                child2.type = exprManager->realType();

                arg[0] = Term2Dag(child1, extensionSymbol, rsv);
                arg[1] = Term2Dag(child2, extensionSymbol, rsv);
                return extensionSymbol->eqRealSymbol->makeDagNode(arg);
            } else if (e[0].getType().isBoolean()){
                child1.type = exprManager->booleanType();
                child2.type = exprManager->booleanType();

                arg[0] = Term2Dag(child1, extensionSymbol, rsv);
                arg[1] = Term2Dag(child2, extensionSymbol, rsv);
                return extensionSymbol->eqBoolSymbol->makeDagNode(arg);
            } else {
                // raise error
            }
        }
        case kind::ITE: {
            Vector < DagNode * > arg(3);

            cvc4_term child1{};
            cvc4_term child2{};
            cvc4_term child3{};

            child1.term = e[0];
            child2.term = e[1];
            child3.term = e[2];

            child1.type = exprManager->booleanType();
            arg[0] = Term2Dag(child1, extensionSymbol, rsv);

            if (e[1].getType().isInteger()) {
                child2.type = exprManager->integerType();
                child3.type = exprManager->integerType();

                arg[1] = Term2Dag(child2, extensionSymbol, rsv);
                arg[2] = Term2Dag(child3, extensionSymbol, rsv);
                return extensionSymbol->iteIntSymbol->makeDagNode(arg);
            } else if (e[1].getType().isReal()) {
                child2.type = exprManager->realType();
                child3.type = exprManager->realType();

                arg[1] = Term2Dag(child2, extensionSymbol, rsv);
                arg[2] = Term2Dag(child3, extensionSymbol, rsv);
                return extensionSymbol->iteRealSymbol->makeDagNode(arg);
            } else if (e[1].getType().isBoolean()) {
                child2.type = exprManager->booleanType();
                child3.type = exprManager->booleanType();

                arg[1] = Term2Dag(child2, extensionSymbol, rsv);
                arg[2] = Term2Dag(child3, extensionSymbol, rsv);
                return extensionSymbol->iteBoolSymbol->makeDagNode(arg);
            } else {
                // raise error
            }
        }

        /**
         * Arithmatic operation on both integer and real
         */
        case kind::PLUS: {
            size_t child_num = e.getNumChildren();
            Vector < DagNode* > arg(child_num);
            for(size_t i = 0; i < child_num; i++){
                cvc4_term child{};
                child.term = e[i];

                if (e[i].getType().isInteger()){
                    child.type = exprManager->integerType();
                } else {
                    child.type = exprManager->realType();
                }

                arg[i] = Term2Dag(child, extensionSymbol, rsv);
            }

            if (expr.type.isInteger()){
                return multipleGen(&arg, 0, MulType::INT_ADD, extensionSymbol);
            } else {
                return multipleGen(&arg, 0, MulType::REAL_ADD, extensionSymbol);
            }
        }
        case kind::MULT: {
            size_t child_num = e.getNumChildren();
            Vector < DagNode* > arg(child_num);
            for(size_t i = 0; i < child_num; i++){
                cvc4_term child{};
                child.term = e[i];

                if (e[i].getType().isInteger()){
                    child.type = exprManager->integerType();
                } else {
                    child.type = exprManager->realType();
                }

                arg[i] = Term2Dag(child, extensionSymbol, rsv);
            }
            if (expr.type.isInteger()){
                return multipleGen(&arg, 0, MulType::INT_MUL, extensionSymbol);
            } else {
                return multipleGen(&arg, 0, MulType::REAL_MUL, extensionSymbol);
            }

        }
        case kind::NONLINEAR_MULT: {
            size_t child_num = e.getNumChildren();
            Vector < DagNode* > arg(child_num);
            for(size_t i = 0; i < child_num; i++){
                cvc4_term child{};
                child.term = e[i];

                if (e[i].getType().isInteger()){
                    child.type = exprManager->integerType();
                } else {
                    child.type = exprManager->realType();
                }
                arg[i] = Term2Dag(child, extensionSymbol, rsv);
            }
            if (expr.type.isInteger()){
                return multipleGen(&arg, 0, MulType::INT_MUL, extensionSymbol);
            } else {
                return multipleGen(&arg, 0, MulType::REAL_MUL, extensionSymbol);
            }
        }
        case kind::MINUS: {
            Vector < DagNode * > arg(2);
            cvc4_term child1{};
            cvc4_term child2{};

            child1.term = e[0];
            child2.term = e[1];

            if (expr.type.isInteger()) {
                child1.type = exprManager->integerType();
                child2.type = exprManager->integerType();

                arg[0] = Term2Dag(child1, extensionSymbol, rsv);
                arg[1] = Term2Dag(child2, extensionSymbol, rsv);
                return extensionSymbol->mulIntSymbol->makeDagNode(arg);
            } else {
                child1.type = exprManager->realType();
                child2.type = exprManager->realType();

                arg[0] = Term2Dag(child1, extensionSymbol, rsv);
                arg[1] = Term2Dag(child2, extensionSymbol, rsv);
                return extensionSymbol->minusRealSymbol->makeDagNode(arg);
            }
        }
        case kind::UMINUS: {
            Vector < DagNode * > arg(2);

            cvc4_term child1{};
            cvc4_term child2{};

            child1.term = e[0];
            child2.term = e[1];

            if (expr.type.isInteger()) {
                child1.type = exprManager->integerType();
                child2.type = exprManager->integerType();

                arg[0] = Term2Dag(child1, extensionSymbol, rsv);
                arg[1] = Term2Dag(child2, extensionSymbol, rsv);
                return extensionSymbol->unaryMinusIntSymbol->makeDagNode(arg);
            } else {
                child1.type = exprManager->realType();
                child2.type = exprManager->realType();

                arg[0] = Term2Dag(child1, extensionSymbol, rsv);
                arg[1] = Term2Dag(child2, extensionSymbol, rsv);
                return extensionSymbol->unaryMinusRealSymbol->makeDagNode(arg);
            }
        }
        case kind::DIVISION: {
            Vector < DagNode * > arg(2);

            cvc4_term child1{};
            cvc4_term child2{};

            child1.term = e[0];
            child1.type = exprManager->realType();

            child2.term = e[1];
            child2.type = exprManager->realType();

            arg[0] = Term2Dag(child1, extensionSymbol, rsv);
            arg[1] = Term2Dag(child2, extensionSymbol, rsv);
            return extensionSymbol->divRealSymbol->makeDagNode(arg);
        }
        case kind::INTS_DIVISION: {
            Vector < DagNode * > arg(2);

            cvc4_term child1{};
            cvc4_term child2{};

            child1.term = e[0];
            child1.type = exprManager->integerType();

            child2.term = e[1];
            child2.type = exprManager->integerType();

            arg[0] = Term2Dag(child1, extensionSymbol, rsv);
            arg[1] = Term2Dag(child2, extensionSymbol, rsv);
            return extensionSymbol->divIntSymbol->makeDagNode(arg);
        }
        case kind::INTS_MODULUS: {
            Vector < DagNode * > arg(2);

            cvc4_term child1{};
            cvc4_term child2{};

            child1.term = e[0];
            child1.type = exprManager->integerType();

            child2.term = e[1];
            child2.type = exprManager->integerType();

            arg[0] = Term2Dag(child1, extensionSymbol, rsv);
            arg[1] = Term2Dag(child2, extensionSymbol, rsv);
            return extensionSymbol->modIntSymbol->makeDagNode(arg);
        }
        case kind::LT: {
            Vector < DagNode * > arg(2);

            cvc4_term child1{};
            cvc4_term child2{};

            child1.term = e[0];
            child2.term = e[1];

            if (expr.type.isInteger()) {
                child1.type = exprManager->integerType();
                child2.type = exprManager->integerType();

                arg[0] = Term2Dag(child1, extensionSymbol, rsv);
                arg[1] = Term2Dag(child2, extensionSymbol, rsv);
                return extensionSymbol->ltIntSymbol->makeDagNode(arg);
            } else {
                child1.type = exprManager->realType();
                child2.type = exprManager->realType();

                arg[0] = Term2Dag(child1, extensionSymbol, rsv);
                arg[1] = Term2Dag(child2, extensionSymbol, rsv);
                return extensionSymbol->ltRealSymbol->makeDagNode(arg);
            }
        }
        case kind::GT: {
            Vector < DagNode * > arg(2);

            cvc4_term child1{};
            cvc4_term child2{};

            child1.term = e[0];
            child2.term = e[1];

            if (expr.type.isInteger()) {
                child1.type = exprManager->integerType();
                child2.type = exprManager->integerType();

                arg[0] = Term2Dag(child1, extensionSymbol, rsv);
                arg[1] = Term2Dag(child2, extensionSymbol, rsv);
                return extensionSymbol->gtIntSymbol->makeDagNode(arg);
            } else {
                child1.type = exprManager->realType();
                child2.type = exprManager->realType();

                arg[0] = Term2Dag(child1, extensionSymbol, rsv);
                arg[1] = Term2Dag(child2, extensionSymbol, rsv);
                return extensionSymbol->gtRealSymbol->makeDagNode(arg);
            }
        }
        case kind::LEQ: {
            Vector < DagNode * > arg(2);

            cvc4_term child1{};
            cvc4_term child2{};

            child1.term = e[0];
            child2.term = e[1];

            if (expr.type.isInteger()) {
                child1.type = exprManager->integerType();
                child2.type = exprManager->integerType();

                arg[0] = Term2Dag(child1, extensionSymbol, rsv);
                arg[1] = Term2Dag(child2, extensionSymbol, rsv);
                return extensionSymbol->leqIntSymbol->makeDagNode(arg);
            } else {
                child1.type = exprManager->realType();
                child2.type = exprManager->realType();

                arg[0] = Term2Dag(child1, extensionSymbol, rsv);
                arg[1] = Term2Dag(child2, extensionSymbol, rsv);
                return extensionSymbol->leqRealSymbol->makeDagNode(arg);
            }
        }
        case kind::GEQ: {
            Vector < DagNode * > arg(2);

            cvc4_term child1{};
            cvc4_term child2{};

            child1.term = e[0];
            child2.term = e[1];

            if (expr.type.isInteger()) {
                child1.type = exprManager->integerType();
                child2.type = exprManager->integerType();

                arg[0] = Term2Dag(child1, extensionSymbol, rsv);
                arg[1] = Term2Dag(child2, extensionSymbol, rsv);
                return extensionSymbol->geqIntSymbol->makeDagNode(arg);
            } else {
                child1.type = exprManager->realType();
                child2.type = exprManager->realType();

                arg[0] = Term2Dag(child1, extensionSymbol, rsv);
                arg[1] = Term2Dag(child2, extensionSymbol, rsv);
                return extensionSymbol->geqRealSymbol->makeDagNode(arg);
            }
        }

        case kind::IS_INTEGER: {
            Vector < DagNode * > arg(1);
            cvc4_term child{};
            child.term = e[0];
            child.type = exprManager->booleanType();

            arg[0] = Term2Dag(child, extensionSymbol, rsv);
            return extensionSymbol->isIntegerSymbol->makeDagNode(arg);
        }
        case kind::TO_REAL: {
            // not a valid matching case, since integer is subtype of rational in cvc4.
            Vector < DagNode * > arg(1);
            cvc4_term child{};
            child.term = e[0];
            child.type = exprManager->realType();

            arg[0] = Term2Dag(child, extensionSymbol, rsv);
            return extensionSymbol->toRealSymbol->makeDagNode(arg);
        }
        case kind::TO_INTEGER: {
            Vector < DagNode * > arg(1);

            cvc4_term child{};
            child.term = e[0];
            child.type = exprManager->integerType();

            arg[0] = Term2Dag(child, extensionSymbol, rsv);
            return extensionSymbol->toIntegerSymbol->makeDagNode(arg);
        }
        case kind::CONST_RATIONAL: {
            if (expr.type.isInteger()) {
                return new SMT_NumberDagNode(extensionSymbol->integerSymbol, e.getConst<Rational>().getValue());
            } else {
                return new SMT_NumberDagNode(extensionSymbol->realSymbol, e.getConst<Rational>().getValue());
            }
        }
        case kind::VARIABLE: {
            if (rsv != nullptr) {
                ReverseSmtManagerVariableMap::const_iterator it = rsv->find(expr);
                if (it != rsv->end()) {
                    return it->second;
                }
            }
        }
        default:
            IssueWarning("no matching with " << e.getKind());
            throw ExtensionException("No matching case");
    }
}

cvc4_term SmtManager::Dag2Term(DagNode *dag, ExtensionSymbol* extensionSymbol) {
    //	Deal with number constants (Integer or Real - CVC4 doesn't make much distinction).
    if (SMT_NumberDagNode* n = dynamic_cast<SMT_NumberDagNode*>(dag)){
        incrFormulaSize();
        Sort *sort = n->symbol()->getRangeSort();
        if(AbstractSmtManager::smtInfo.getType(sort) == SMT_Info::INTEGER) {
            cvc4_term term{};
            term.term = exprManager->mkConst(Rational(n->getValue().get_str()));
            term.type = exprManager->integerType();
            return term;
        } else if (AbstractSmtManager::smtInfo.getType(sort) == SMT_Info::REAL) {
            cvc4_term term{};
            term.term = exprManager->mkConst(Rational(n->getValue().get_str()));
            term.type = exprManager->realType();
            return term;
        }
    }

    try {
        return makeExtensionVariable(dag, extensionSymbol);
    } catch (ExtensionException& ex) {
        if (isNull(ex.c_str())) {
            if (SMT_Symbol * s = dynamic_cast<SMT_Symbol *>(dag->symbol())) {
                int nrArgs = s->arity();

                // need to be initialized with original ctx.
                std::vector <cvc4_term> exprs;

                FreeDagNode *f = safeCast(FreeDagNode * , dag);
                for (int i = 0; i < nrArgs; ++i) {

                    cvc4_term e = Dag2Term(f->getArgument(i), extensionSymbol);
                    //if (expr.isNull())
                    //    return expr;
                    exprs.push_back(e);
                }


                switch (s->getOperator()) {
                    //
                    //	Boolean stuff.
                    //
                    case SMT_Symbol::CONST_TRUE: {
                        incrFormulaSize();
                        cvc4_term term{};
                        term.term = exprManager->mkConst(true);
                        term.type = exprManager->booleanType();
                        return term;
                    }
                    case SMT_Symbol::CONST_FALSE: {
                        incrFormulaSize();
                        cvc4_term term{};
                        term.term = exprManager->mkConst(false);
                        term.type = exprManager->booleanType();
                        return term;
                    }
                    case SMT_Symbol::NOT: {
                        incrFormulaSize();
                        cvc4_term term{};
                        term.term = exprManager->mkExpr(kind::NOT, exprs[0].term);
                        term.type = exprManager->booleanType();
                        return term;
                    }

                    case SMT_Symbol::AND: {
                        incrFormulaSize();
                        cvc4_term term{};
                        term.term = exprManager->mkExpr(kind::AND, exprs[0].term, exprs[1].term);
                        term.type = exprManager->booleanType();
                        return term;
                    }
                    case SMT_Symbol::OR: {
                        incrFormulaSize();
                        cvc4_term term{};
                        term.term = exprManager->mkExpr(kind::OR, exprs[0].term, exprs[1].term);
                        term.type = exprManager->booleanType();
                        return term;
                    }
                    case SMT_Symbol::XOR: {
                        incrFormulaSize();
                        cvc4_term term{};
                        term.term = exprManager->mkExpr(kind::XOR, exprs[0].term, exprs[1].term);
                        term.type = exprManager->booleanType();
                        return term;
                    }
                    case SMT_Symbol::IMPLIES: {
                        incrFormulaSize();
                        cvc4_term term{};
                        term.term = exprManager->mkExpr(kind::IMPLIES, exprs[0].term, exprs[1].term);
                        term.type = exprManager->booleanType();
                        return term;
                    }
                        //
                        //	Polymorphic Boolean stuff.
                        //
                    case SMT_Symbol::EQUALS: {
                        //
                        //	Bizarrely CVC4 requires the IFF be used for Boolean equality so we need to
                        //	check the SMT type associated with our first argument sort to catch this case.
                        //
                        Sort* domainSort = s->getOpDeclarations()[0].getDomainAndRange()[0];
                        SMT_Info::SMT_Type smtType = AbstractSmtManager::smtInfo.getType(domainSort);
                        if (smtType == SMT_Info::NOT_SMT)
                        {
                            IssueWarning("term " << QUOTE(dag) << " does not belong to an SMT sort.");
                            goto fail;
                        }
                        incrFormulaSize();
                        cvc4_term term{};
                        term.term = exprManager->mkExpr(kind::EQUAL, exprs[0].term, exprs[1].term);
                        term.type = exprManager->booleanType();
                        return term;
                    }
                    case SMT_Symbol::NOT_EQUALS: {
                        incrFormulaSize();
                        cvc4_term term{};
                        term.term = exprManager->mkExpr(kind::DISTINCT, exprs[0].term, exprs[1].term);
                        term.type = exprManager->booleanType();
                        return term;
                    }
                    case SMT_Symbol::ITE: {
                        incrFormulaSize();
                        cvc4_term term{};
                        term.term = exprManager->mkExpr(kind::ITE, exprs[0].term, exprs[1].term, exprs[2].term);
                        term.type = exprs[1].type;
                        return term;
                    }
                        //
                        //	Integer stuff.
                        //
                    case SMT_Symbol::UNARY_MINUS: {
                        incrFormulaSize();
                        cvc4_term term{};
                        term.term = exprManager->mkExpr(kind::UMINUS, exprs[0].term);
                        term.type = exprs[0].type;
                        return term;
                    }
                    case SMT_Symbol::MINUS: {
                        incrFormulaSize();
                        cvc4_term term{};
                        term.term = exprManager->mkExpr(kind::MINUS, exprs[0].term, exprs[1].term);
                        term.type = exprs[0].type;
                        return term;
                    }
                    case SMT_Symbol::PLUS: {
                        incrFormulaSize();
                        cvc4_term term{};
                        term.term = exprManager->mkExpr(kind::PLUS, exprs[0].term, exprs[1].term);
                        term.type = exprs[0].type;
                        return term;
                    }
                    case SMT_Symbol::MULT: {
                        incrFormulaSize();
                        cvc4_term term{};
                        term.term = exprManager->mkExpr(kind::MULT, exprs[0].term, exprs[1].term);
                        term.type = exprs[0].type;
                        return term;
                    }
                    case SMT_Symbol::DIV: {
                        incrFormulaSize();
                        cvc4_term term{};
                        term.term = exprManager->mkExpr(kind::INTS_DIVISION, exprs[0].term, exprs[1].term);
                        term.type = exprs[0].type;
                        return term;
                    }
                    case SMT_Symbol::MOD: {
                        incrFormulaSize();
                        cvc4_term term{};
                        term.term = exprManager->mkExpr(kind::INTS_MODULUS, exprs[0].term, exprs[1].term);
                        term.type = exprs[0].type;
                        return term;
                    }
                        //
                        //	Integer tests.
                        //

                    case SMT_Symbol::LT: {
                        incrFormulaSize();
                        cvc4_term term{};
                        term.term = exprManager->mkExpr(kind::LT, exprs[0].term, exprs[1].term);
                        term.type = exprManager->booleanType();
                        return term;
                    }
                    case SMT_Symbol::LEQ: {
                        incrFormulaSize();
                        cvc4_term term{};
                        term.term = exprManager->mkExpr(kind::LEQ, exprs[0].term, exprs[1].term);
                        term.type = exprManager->booleanType();
                        return term;
                    }
                    case SMT_Symbol::GT: {
                        incrFormulaSize();
                        cvc4_term term{};
                        term.term = exprManager->mkExpr(kind::GT, exprs[0].term, exprs[1].term);
                        term.type = exprManager->booleanType();
                        return term;
                    }
                    case SMT_Symbol::GEQ: {
                        incrFormulaSize();
                        cvc4_term term{};
                        term.term = exprManager->mkExpr(kind::GEQ, exprs[0].term, exprs[1].term);
                        term.type = exprManager->booleanType();
                        return term;
                    }

                    case SMT_Symbol::DIVISIBLE: {
                        //
                        //	Second argument must be a positive constant.
                        //	Typing ensures it is an integer.
                        //
                        DagNode* a = f->getArgument(1);
                        if (SMT_NumberDagNode* n = dynamic_cast<SMT_NumberDagNode*>(a))
                        {
                            const mpq_class& rat = n->getValue();
                            if (rat > 0)
                            {
                                string ratStr = rat.get_str();
                                Integer k(ratStr.c_str());
                                Divisible div(k);
                                Expr divOp = exprManager->mkConst(div);
                                incrFormulaSize();
                                cvc4_term term{};
                                term.term = exprManager->mkExpr(divOp, exprs[0].term);
                                term.type = exprManager->booleanType();
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
                        cvc4_term term{};
                        term.term = exprManager->mkExpr(kind::DIVISION, exprs[0].term, exprs[1].term);
                        term.type = exprs[0].type;
                        return term;
                    }
                    case SMT_Symbol::TO_REAL: {
                        incrFormulaSize();
                        cvc4_term term{};
                        term.term = exprManager->mkExpr(kind::TO_REAL, exprs[0].term);
                        term.type = exprManager->realType();
                        return term;
                    }
                    case SMT_Symbol::TO_INTEGER: {
                        incrFormulaSize();
                        cvc4_term term{};
                        term.term = exprManager->mkExpr(kind::TO_INTEGER, exprs[0].term);
                        term.type = exprManager->integerType();
                        return term;
                    }
                    case SMT_Symbol::IS_INTEGER: {
                        incrFormulaSize();
                        cvc4_term term{};
                        term.term = exprManager->mkExpr(kind::IS_INTEGER, exprs[0].term);
                        term.type = exprManager->booleanType();
                        return term;
                    }
                }
            }
            IssueWarning("term " << QUOTE(dag) << " is not a valid SMT term.");
            fail:
            resetFormulaSize();
            throw ExtensionException("not a valid term, return original term instead");
        }
    }
}

cvc4_term SmtManager::variableGenerator(DagNode *dag, ExprType exprType) {
    hasVariable = true;

    // Find if there is already a dag node registered.
    SmtManagerVariableMap::const_iterator it = smtManagerVariableMap.find(dag);
    if (it != smtManagerVariableMap.end())
        return it->second;

    // Two dag nodes may be different while they both point to the same symbol.
    for(auto it = smtManagerVariableMap.begin(); it != smtManagerVariableMap.end(); it++){
        if(dag->equal(it->first)){
            smtManagerVariableMap.insert(SmtManagerVariableMap::value_type(dag, it->second));
            return it->second;
        }
    }

    Type type;
    string name;

    if (VariableDagNode* v = dynamic_cast<VariableDagNode*>(dag)){
        Symbol *s = v->symbol();

        Sort *sort = s->getRangeSort();
        int id = v->id();
        name = Token::name(id);

        switch (AbstractSmtManager::smtInfo.getType(sort)) {
            case SMT_Info::NOT_SMT: {
                IssueWarning("Variable " << QUOTE(static_cast<DagNode *>(v)) << " does not belong to an SMT sort.");
                SMT_NULL_TERM();
            }
            case SMT_Info::BOOLEAN: {
                type = exprManager->booleanType();
                name = name + "_" + string("Boolean");
                break;
            }
            case SMT_Info::INTEGER: {
                type = exprManager->integerType();
                name = name + "_" + string("Integer");
                break;
            }
            case SMT_Info::REAL: {
                type = exprManager->realType();
                name = name + "_" + string("Real");
                break;
            }
        }
    } else if(exprType != ExprType::BUILTIN) {
        switch (exprType){
            case BOOL:
                type = exprManager->booleanType();
                name = "b_";
                break;
            case INT:
                type = exprManager->integerType();
                name = "i_";
                break;
            case REAL:
                type = exprManager->realType();
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

    cvc4_term newTerm{};
    newTerm.term = exprManager->mkVar(name.c_str(), type);
    newTerm.type = type;
    smtManagerVariableMap.insert(SmtManagerVariableMap::value_type(dag, newTerm));
    return newTerm;
}

DagNode *SmtManager::simplifyDag(DagNode *dagNode, ExtensionSymbol* extensionSymbol) {
    try {
        resetFormulaSize();
        cvc4_term expr = makeExpr(dagNode, extensionSymbol, false);
        Verbose("SimplifyFormulaSymbol : Formula size " << formulaSize);
        resetFormulaSize();

        expr.term = smtEngine->simplify(expr.term);

        ReverseSmtManagerVariableMap* rsv = nullptr;
        if (hasVariable){
            rsv = generateReverseVariableMap();
        }

        DagNode* dn = Term2Dag(expr, extensionSymbol, rsv);

        if (hasVariable)
            delete rsv;
        return dn;
    } catch (ExtensionException &ex) {
        IssueWarning("error simplify dag with " << ex.c_str());
        throw ExtensionException("error while smt solving");
    } catch(CVC4::IllegalArgumentException){
        throw ExtensionException("CVC4 return illegalArgument error");
    }
}

DagNode* SmtManager::applyTactic(DagNode* dagNode, DagNode* tacticTypeDagNode, ExtensionSymbol* extensionSymbol){
    return dagNode;
}
