// utility stuff
#include "macros.hh"
#include "vector.hh"

// forward declarations
#include "interface.hh"
#include "core.hh"
#include "freeTheory.hh"
#include "variable.hh"
#include "builtIn.hh"
#include "mixfix.hh"

// interface class definitions
#include "symbol.hh"
#include "term.hh"

// core class definitions
#include "rewritingContext.hh"
#include "symbolMap.hh"

// variable class definitions
#include "variableSymbol.hh"
#include "variableDagNode.hh"

// free theory class definitions
#include "freeDagNode.hh"

// builtin class definition
#include "bindingMacros.hh"

// SMT stuff
#include "SMT_Info.hh"
#include "SMT_Symbol.hh"
#include "SMT_NumberSymbol.hh"
#include "SMT_NumberDagNode.hh"

// Qid
#include "quotedIdentifierSymbol.hh"
#include "quotedIdentifierDagNode.hh"
#include "extensionSymbol.hh"

ExtensionSymbol::ExtensionSymbol(int id, int arity) : FreeSymbol(id, arity) {
    /**
     * Type symbol.
     *
     * integerSymbol (<Integers> : ~> Integer)
     * realSymbol (<Reals> : ~> Real)
     * trueTerm (true)
     * falseTerm (false)
     */
    integerSymbol = 0;
    realSymbol = 0;

    intVarSymbol = 0;
    boolVarSymbol = 0;
    realVarSymbol = 0;

    /**
     * Boolean symbol.
     *
     * op-hook notBoolSymbol                      (not_ : BooleanExpr ~> BooleanExpr)
     * op-hook andBoolSymbol                      (_and_ : BooleanExpr BooleanExpr ~> BooleanExpr)
     * op-hook xorBoolSymbol                      (_xor_ : BooleanExpr BooleanExpr ~> BooleanExpr)
     * op-hook orBoolSymbol                       (_or_ : BooleanExpr BooleanExpr ~> BooleanExpr)
     * op-hook impliesBoolSymbol                  (_implies_ : BooleanExpr BooleanExpr ~> BooleanExpr)
     * op-hook eqBoolSymbol                       (_===_ : BooleanExpr BooleanExpr ~> BooleanExpr)
     * op-hook neqBoolSymbol                      (_=/==_ : BooleanExpr BooleanExpr ~> BooleanExpr)
     * op-hook iteBoolSymbol                      (_?_:_ : BooleanExpr BooleanExpr BooleanExpr ~> BooleanExpr)
     * op-hook forallBoolSymbol                   (forall : BooleanVar BooleanExpr ~> BooleanExpr)
     * op-hook existsBoolSymbol                   (exists : BooleanVar BooleanExpr ~> BooleanExpr)
     */
    notBoolSymbol = 0;
    andBoolSymbol = 0;
    xorBoolSymbol = 0;
    orBoolSymbol = 0;
    impliesBoolSymbol = 0;
    eqBoolSymbol = 0;
    neqBoolSymbol = 0;
    iteBoolSymbol = 0;
    forallBoolSymbol = 0;
    existsBoolSymbol = 0;

    /**
     * Integer symbol.
     *
     * op-hook unaryMinusIntSymbol                (-_ : IntegerExpr ~> IntegerExpr)
     * op-hook plusIntSymbol                      (_+_ : IntegerExpr IntegerExpr ~> IntegerExpr)
     * op-hook minusIntSymbol                     (_-_ : IntegerExpr IntegerExpr ~> IntegerExpr)
     * op-hook divIntSymbol                       (_div_ : IntegerExpr IntegerExpr ~> IntegerExpr)
     * op-hook mulIntSymbol                       (_*_ : IntegerExpr IntegerExpr ~> IntegerExpr)
     * op-hook modIntSymbol                       (_mod_ : IntegerExpr IntegerExpr ~> IntegerExpr)
     * op-hook ltIntSymbol                        (_<_ : IntegerExpr IntegerExpr ~> BooleanExpr)
     * op-hook leqIntSymbol                       (_<=_ : IntegerExpr IntegerExpr ~> BooleanExpr)
     * op-hook gtIntSymbol                        (_>_ : IntegerExpr IntegerExpr ~> BooleanExpr)
     * op-hook geqIntSymbol                       (_>=_ : IntegerExpr IntegerExpr ~> BooleanExpr)
     * op-hook eqIntSymbol                        (_===_ : IntegerExpr IntegerExpr ~> BooleanExpr)
     * op-hook neqIntSymbol                       (_=/==_ : IntegerExpr IntegerExpr ~> BooleanExpr)
     * op-hook iteIntSymbol                       (_?_:_ : BooleanExpr IntegerExpr IntegerExpr ~> IntegerExpr)
     * op-hook divisibleIntSymbol                 (_divisible_ : IntegerExpr IntegerExpr ~> BooleanExpr)
     * op-hook forallIntSymbol                    (forall : IntegerVar BooleanExpr ~> BooleanExpr)
     * op-hook existsIntSymbol                    (exists : IntegerVar BooleanExpr ~> BooleanExpr)
     */
    unaryMinusIntSymbol = 0;
    plusIntSymbol = 0;
    minusIntSymbol = 0;
    divIntSymbol = 0;
    mulIntSymbol = 0;
    modIntSymbol = 0;
    ltIntSymbol = 0;
    leqIntSymbol = 0;
    gtIntSymbol = 0;
    geqIntSymbol = 0;
    eqIntSymbol = 0;
    neqIntSymbol = 0;
    iteIntSymbol = 0;
    divisibleIntSymbol = 0;
    forallIntSymbol = 0;
    existsIntSymbol = 0;

    /**
     * Real symbol
     *
     * op-hook unaryMinusRealSymbol               (-_ : RealExpr ~> RealExpr)
     * op-hook plusRealSymbol                     (_+_ : RealExpr RealExpr ~> RealExpr)
     * op-hook minusRealSymbol                    (_-_ : RealExpr RealExpr ~> RealExpr)
     * op-hook divRealSymbol                      (_/_ : RealExpr RealExpr ~> RealExpr)
     * op-hook mulRealSymbol                      (_*_ : RealExpr RealExpr ~> RealExpr)
     * op-hook ltRealSymbol                       (_<_ : RealExpr RealExpr ~> BooleanExpr)
     * op-hook leqRealSymbol                      (_<=_ : RealExpr RealExpr ~> BooleanExpr)
     * op-hook gtRealSymbol                       (_>_ : RealExpr RealExpr ~> BooleanExpr)
     * op-hook geqRealSymbol                      (_>=_ : RealExpr RealExpr ~> BooleanExpr)
     * op-hook eqRealSymbol                       (_===_ : RealExpr RealExpr ~> BooleanExpr)
     * op-hook neqRealSymbol                      (_=/==_ : RealExpr RealExpr ~> BooleanExpr)
     * op-hook iteRealSymbol                      (_?_:_ : BooleanExpr RealExpr RealExpr ~> RealExpr)
     * op-hook forallRealSymbol                   (forall : RealVar BooleanExpr ~> BooleanExpr)
     * op-hook existsRealSymbol                   (exists : RealVar BooleanExpr ~> BooleanExpr)
     */
    unaryMinusRealSymbol = 0;
    plusRealSymbol = 0;
    minusRealSymbol = 0;
    divRealSymbol = 0;
    mulRealSymbol = 0;
    ltRealSymbol = 0;
    leqRealSymbol = 0;
    gtRealSymbol = 0;
    geqRealSymbol = 0;
    eqRealSymbol = 0;
    neqRealSymbol = 0;
    iteRealSymbol = 0;

    toRealSymbol = 0;
    toIntegerSymbol = 0;
    isIntegerSymbol = 0;

    forallRealSymbol = 0;
    existsRealSymbol = 0;

    shareWith = 0;

    freshBoolVarSymbol = 0;
    freshIntVarSymbol = 0;
    freshRealVarSymbol = 0;
}

bool ExtensionSymbol::attachData(const Vector<Sort *> &opDeclaration,
                                  const char *purpose,
                                  const Vector<const char *> &data) {
    NULL_DATA(purpose, ExtensionSymbol, data);
    return FreeSymbol::attachData(opDeclaration, purpose, data);
}

bool ExtensionSymbol::attachTerm(const char *purpose, Term *term) {
    BIND_TERM(purpose, term, trueTerm);
    BIND_TERM(purpose, term, falseTerm);
    return FreeSymbol::attachTerm(purpose, term);
}

bool ExtensionSymbol::attachSymbol(const char *purpose, Symbol *symbol) {

    BIND_SYMBOL(purpose, symbol, integerSymbol, SMT_NumberSymbol * );
    BIND_SYMBOL(purpose, symbol, realSymbol, SMT_NumberSymbol * );

    BIND_SYMBOL(purpose, symbol, intVarSymbol, Symbol * );
    BIND_SYMBOL(purpose, symbol, boolVarSymbol, Symbol * );
    BIND_SYMBOL(purpose, symbol, realVarSymbol, Symbol * );
    BIND_SYMBOL(purpose, symbol, shareWith, Symbol * );

    // BooleanExpr
    BIND_SYMBOL(purpose, symbol, notBoolSymbol, Symbol * );
    BIND_SYMBOL(purpose, symbol, andBoolSymbol, Symbol * );
    BIND_SYMBOL(purpose, symbol, xorBoolSymbol, Symbol * );
    BIND_SYMBOL(purpose, symbol, orBoolSymbol, Symbol * );
    BIND_SYMBOL(purpose, symbol, impliesBoolSymbol, Symbol * );
    BIND_SYMBOL(purpose, symbol, eqBoolSymbol, Symbol * );
    BIND_SYMBOL(purpose, symbol, neqBoolSymbol, Symbol * );
    BIND_SYMBOL(purpose, symbol, iteBoolSymbol, Symbol * );
    BIND_SYMBOL(purpose, symbol, forallBoolSymbol, Symbol * );
    BIND_SYMBOL(purpose, symbol, existsBoolSymbol, Symbol * );

    // IntegerExpr
    BIND_SYMBOL(purpose, symbol, unaryMinusIntSymbol, Symbol * );
    BIND_SYMBOL(purpose, symbol, plusIntSymbol, Symbol * );
    BIND_SYMBOL(purpose, symbol, minusIntSymbol, Symbol * );
    BIND_SYMBOL(purpose, symbol, divIntSymbol, Symbol * );
    BIND_SYMBOL(purpose, symbol, mulIntSymbol, Symbol * );
    BIND_SYMBOL(purpose, symbol, modIntSymbol, Symbol * );
    BIND_SYMBOL(purpose, symbol, ltIntSymbol, Symbol * );
    BIND_SYMBOL(purpose, symbol, leqIntSymbol, Symbol * );
    BIND_SYMBOL(purpose, symbol, gtIntSymbol, Symbol * );
    BIND_SYMBOL(purpose, symbol, geqIntSymbol, Symbol * );
    BIND_SYMBOL(purpose, symbol, eqIntSymbol, Symbol * );
    BIND_SYMBOL(purpose, symbol, neqIntSymbol, Symbol * );
    BIND_SYMBOL(purpose, symbol, iteIntSymbol, Symbol * );
    BIND_SYMBOL(purpose, symbol, divisibleIntSymbol, Symbol * );
    BIND_SYMBOL(purpose, symbol, forallIntSymbol, Symbol * );
    BIND_SYMBOL(purpose, symbol, existsIntSymbol, Symbol * );

    // RealExpr
    BIND_SYMBOL(purpose, symbol, unaryMinusRealSymbol, Symbol * );
    BIND_SYMBOL(purpose, symbol, plusRealSymbol, Symbol * );
    BIND_SYMBOL(purpose, symbol, minusRealSymbol, Symbol * );
    BIND_SYMBOL(purpose, symbol, divRealSymbol, Symbol * );
    BIND_SYMBOL(purpose, symbol, mulRealSymbol, Symbol * );
    BIND_SYMBOL(purpose, symbol, ltRealSymbol, Symbol * );
    BIND_SYMBOL(purpose, symbol, leqRealSymbol, Symbol * );
    BIND_SYMBOL(purpose, symbol, gtRealSymbol, Symbol * );
    BIND_SYMBOL(purpose, symbol, geqRealSymbol, Symbol * );
    BIND_SYMBOL(purpose, symbol, eqRealSymbol, Symbol * );
    BIND_SYMBOL(purpose, symbol, neqRealSymbol, Symbol * );
    BIND_SYMBOL(purpose, symbol, iteRealSymbol, Symbol * );

    BIND_SYMBOL(purpose, symbol, toRealSymbol, Symbol * );
    BIND_SYMBOL(purpose, symbol, toIntegerSymbol, Symbol * );
    BIND_SYMBOL(purpose, symbol, isIntegerSymbol, Symbol * );

    BIND_SYMBOL(purpose, symbol, forallRealSymbol, Symbol * );
    BIND_SYMBOL(purpose, symbol, existsRealSymbol, Symbol * );

    BIND_SYMBOL(purpose, symbol, freshBoolVarSymbol, Symbol * );
    BIND_SYMBOL(purpose, symbol, freshIntVarSymbol, Symbol * );
    BIND_SYMBOL(purpose, symbol, freshRealVarSymbol, Symbol * );

    return FreeSymbol::attachSymbol(purpose, symbol);
}

void ExtensionSymbol::copyAttachments(Symbol *original, SymbolMap *map) {

    ExtensionSymbol *orig = safeCast(ExtensionSymbol * , original);
    COPY_SYMBOL(orig, integerSymbol, map, SMT_NumberSymbol * );
    COPY_SYMBOL(orig, realSymbol, map, SMT_NumberSymbol * );

    COPY_SYMBOL(orig, intVarSymbol, map, Symbol * );
    COPY_SYMBOL(orig, boolVarSymbol, map, Symbol * );
    COPY_SYMBOL(orig, realVarSymbol, map, Symbol * );
    COPY_SYMBOL(orig, shareWith, map, Symbol * );

    COPY_TERM(orig, trueTerm, map);
    COPY_TERM(orig, falseTerm, map);

    // BooleanExpr
    COPY_SYMBOL(orig, notBoolSymbol, map, Symbol * );
    COPY_SYMBOL(orig, andBoolSymbol, map, Symbol * );
    COPY_SYMBOL(orig, xorBoolSymbol, map, Symbol * );
    COPY_SYMBOL(orig, orBoolSymbol, map, Symbol * );
    COPY_SYMBOL(orig, impliesBoolSymbol, map, Symbol * );
    COPY_SYMBOL(orig, eqBoolSymbol, map, Symbol * );
    COPY_SYMBOL(orig, neqBoolSymbol, map, Symbol * );
    COPY_SYMBOL(orig, iteBoolSymbol, map, Symbol * );
    COPY_SYMBOL(orig, forallBoolSymbol, map, Symbol * );
    COPY_SYMBOL(orig, existsBoolSymbol, map, Symbol * );

    // IntegerExpr
    COPY_SYMBOL(orig, unaryMinusIntSymbol, map, Symbol * );
    COPY_SYMBOL(orig, plusIntSymbol, map, Symbol * );
    COPY_SYMBOL(orig, minusIntSymbol, map, Symbol * );
    COPY_SYMBOL(orig, divIntSymbol, map, Symbol * );
    COPY_SYMBOL(orig, mulIntSymbol, map, Symbol * );
    COPY_SYMBOL(orig, modIntSymbol, map, Symbol * );
    COPY_SYMBOL(orig, ltIntSymbol, map, Symbol * );
    COPY_SYMBOL(orig, leqIntSymbol, map, Symbol * );
    COPY_SYMBOL(orig, gtIntSymbol, map, Symbol * );
    COPY_SYMBOL(orig, geqIntSymbol, map, Symbol * );
    COPY_SYMBOL(orig, eqIntSymbol, map, Symbol * );
    COPY_SYMBOL(orig, neqIntSymbol, map, Symbol * );
    COPY_SYMBOL(orig, iteIntSymbol, map, Symbol * );
    COPY_SYMBOL(orig, divisibleIntSymbol, map, Symbol * );
    COPY_SYMBOL(orig, forallIntSymbol, map, Symbol * );
    COPY_SYMBOL(orig, existsIntSymbol, map, Symbol * );

    // RealExpr
    COPY_SYMBOL(orig, unaryMinusRealSymbol, map, Symbol * );
    COPY_SYMBOL(orig, plusRealSymbol, map, Symbol * );
    COPY_SYMBOL(orig, minusRealSymbol, map, Symbol * );
    COPY_SYMBOL(orig, divRealSymbol, map, Symbol * );
    COPY_SYMBOL(orig, mulRealSymbol, map, Symbol * );
    COPY_SYMBOL(orig, ltRealSymbol, map, Symbol * );
    COPY_SYMBOL(orig, leqRealSymbol, map, Symbol * );
    COPY_SYMBOL(orig, gtRealSymbol, map, Symbol * );
    COPY_SYMBOL(orig, geqRealSymbol, map, Symbol * );
    COPY_SYMBOL(orig, eqRealSymbol, map, Symbol * );
    COPY_SYMBOL(orig, neqRealSymbol, map, Symbol * );
    COPY_SYMBOL(orig, iteRealSymbol, map, Symbol * );

    COPY_SYMBOL(orig, toRealSymbol, map, Symbol * );
    COPY_SYMBOL(orig, toIntegerSymbol, map, Symbol * );
    COPY_SYMBOL(orig, isIntegerSymbol, map, Symbol * );

    COPY_SYMBOL(orig, forallRealSymbol, map, Symbol * );
    COPY_SYMBOL(orig, existsRealSymbol, map, Symbol * );

    COPY_SYMBOL(orig, freshBoolVarSymbol, map, Symbol * );
    COPY_SYMBOL(orig, freshIntVarSymbol, map, Symbol * );
    COPY_SYMBOL(orig, freshRealVarSymbol, map, Symbol * );

    FreeSymbol::copyAttachments(original, map);
}

void ExtensionSymbol::getDataAttachments(const Vector<Sort *> &opDeclaration,
                                          Vector<const char *> &purposes,
                                          Vector <Vector<const char *>> &data) {
    APPEND_DATA(purposes, data, ExtensionSymbol);
    FreeSymbol::getDataAttachments(opDeclaration, purposes, data);
}

void ExtensionSymbol::getSymbolAttachments(Vector<const char *> &purposes,
                                                 Vector<Symbol *> &symbols) {
    APPEND_SYMBOL(purposes, symbols, integerSymbol);
    APPEND_SYMBOL(purposes, symbols, realSymbol);

    APPEND_SYMBOL(purposes, symbols, intVarSymbol);
    APPEND_SYMBOL(purposes, symbols, boolVarSymbol);
    APPEND_SYMBOL(purposes, symbols, realVarSymbol);
    APPEND_SYMBOL(purposes, symbols, shareWith);

    // BooleanExpr
    APPEND_SYMBOL(purposes, symbols, notBoolSymbol);
    APPEND_SYMBOL(purposes, symbols, andBoolSymbol);
    APPEND_SYMBOL(purposes, symbols, xorBoolSymbol);
    APPEND_SYMBOL(purposes, symbols, orBoolSymbol);
    APPEND_SYMBOL(purposes, symbols, impliesBoolSymbol);
    APPEND_SYMBOL(purposes, symbols, eqBoolSymbol);
    APPEND_SYMBOL(purposes, symbols, neqBoolSymbol);
    APPEND_SYMBOL(purposes, symbols, iteBoolSymbol);
    APPEND_SYMBOL(purposes, symbols, forallBoolSymbol);
    APPEND_SYMBOL(purposes, symbols, existsBoolSymbol);

    // IntegerExpr
    APPEND_SYMBOL(purposes, symbols, unaryMinusIntSymbol);
    APPEND_SYMBOL(purposes, symbols, plusIntSymbol);
    APPEND_SYMBOL(purposes, symbols, minusIntSymbol);
    APPEND_SYMBOL(purposes, symbols, divIntSymbol);
    APPEND_SYMBOL(purposes, symbols, mulIntSymbol);
    APPEND_SYMBOL(purposes, symbols, modIntSymbol);
    APPEND_SYMBOL(purposes, symbols, ltIntSymbol);
    APPEND_SYMBOL(purposes, symbols, leqIntSymbol);
    APPEND_SYMBOL(purposes, symbols, gtIntSymbol);
    APPEND_SYMBOL(purposes, symbols, geqIntSymbol);
    APPEND_SYMBOL(purposes, symbols, eqIntSymbol);
    APPEND_SYMBOL(purposes, symbols, neqIntSymbol);
    APPEND_SYMBOL(purposes, symbols, iteIntSymbol);
    APPEND_SYMBOL(purposes, symbols, divisibleIntSymbol);
    APPEND_SYMBOL(purposes, symbols, forallIntSymbol);
    APPEND_SYMBOL(purposes, symbols, existsIntSymbol);

    // RealExpr
    APPEND_SYMBOL(purposes, symbols, unaryMinusRealSymbol);
    APPEND_SYMBOL(purposes, symbols, plusRealSymbol);
    APPEND_SYMBOL(purposes, symbols, minusRealSymbol);
    APPEND_SYMBOL(purposes, symbols, divRealSymbol);
    APPEND_SYMBOL(purposes, symbols, mulRealSymbol);
    APPEND_SYMBOL(purposes, symbols, ltRealSymbol);
    APPEND_SYMBOL(purposes, symbols, leqRealSymbol);
    APPEND_SYMBOL(purposes, symbols, gtRealSymbol);
    APPEND_SYMBOL(purposes, symbols, geqRealSymbol);
    APPEND_SYMBOL(purposes, symbols, eqRealSymbol);
    APPEND_SYMBOL(purposes, symbols, neqRealSymbol);
    APPEND_SYMBOL(purposes, symbols, iteRealSymbol);

    APPEND_SYMBOL(purposes, symbols, toRealSymbol);
    APPEND_SYMBOL(purposes, symbols, toIntegerSymbol);
    APPEND_SYMBOL(purposes, symbols, isIntegerSymbol);

    APPEND_SYMBOL(purposes, symbols, forallRealSymbol);
    APPEND_SYMBOL(purposes, symbols, existsRealSymbol);

    APPEND_SYMBOL(purposes, symbols, freshBoolVarSymbol);
    APPEND_SYMBOL(purposes, symbols, freshIntVarSymbol);
    APPEND_SYMBOL(purposes, symbols, freshRealVarSymbol);

    FreeSymbol::getSymbolAttachments(purposes, symbols);
}

void ExtensionSymbol::getTermAttachments(Vector<const char *> &purposes,
                                               Vector<Term *> &terms) {

    APPEND_TERM(purposes, terms, trueTerm);
    APPEND_TERM(purposes, terms, falseTerm);
    FreeSymbol::getTermAttachments(purposes, terms);
}

void ExtensionSymbol::postInterSymbolPass() {
    PREPARE_TERM(trueTerm);
    PREPARE_TERM(falseTerm);
    FreeSymbol::postInterSymbolPass();
}

void ExtensionSymbol::reset() {
    trueTerm.reset();
    falseTerm.reset();
    FreeSymbol::reset();
}

