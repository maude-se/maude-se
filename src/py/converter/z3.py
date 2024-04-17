from typing import Dict
from ..interface import *
from ..util import *
from functools import reduce
# from ..maude import *
from maudeSE.maude import *

import z3
import re


class Z3Converter(Converter):
    """A term converter from Maude to Z3"""

    def __init__(self):
        self._g = id_gen()
        self._symbol_info = dict()
        self._symbol_map = dict()
        self._var_map = dict()

        # smt.maude map
        self._op_dict = {
            "not_"          : z3.Not,
            "_and_"         : z3.And,
            "_or_"          : z3.Or,
            "_xor_"         : z3.Xor,
            "_implies_"     : z3.Implies,
            "_===_"         : z3.z3.BoolRef.__eq__,
            "_=/==_"        : z3.z3.BoolRef.__ne__,
            "_?_:_"         : z3.If,

            "-_"            : z3.z3.ArithRef.__neg__,
            "_+_"           : z3.z3.ArithRef.__add__,
            "_-_"           : z3.z3.ArithRef.__sub__,
            "_*_"           : z3.z3.ArithRef.__mul__,
            "_div_"         : z3.z3.ArithRef.__div__,
            "_/_"           : z3.z3.ArithRef.__div__,
            "_mod_"         : z3.z3.ArithRef.__mod__,

            # "_divisible_" : ?

            "_<_"           : z3.z3.ArithRef.__lt__,
            "_<=_"          : z3.z3.ArithRef.__le__,
            "_>_"           : z3.z3.ArithRef.__gt__,
            "_>=_"          : z3.z3.ArithRef.__ge__,
        }

        self._const_dict = {
            "true"          : z3.BoolVal,
            "false"         : z3.BoolVal,
            "<Integers>"    : z3.IntVal,
            "<Reals>"       : z3.RealVal,
        }

        self._special_const = {
            # var constructor
            "IntegerVar"    : z3.IntSort,
            "BoolVar"       : z3.BoolSort,
            "RealVar"       : z3.Real,
        }

        self._sort_dict = {
            "Integer"           : z3.IntSort,
            "Real"              : z3.RealSort,
            "Boolean"           : z3.BoolSort,
            "IntegerVar"        : z3.IntSort,
            "RealVar"           : z3.RealSort,
            "BooleanVar"        : z3.BoolSort,
            "IntegerExpr"       : z3.IntSort,
            "RealExpr"          : z3.RealSort,
            "BooleanExpr"       : z3.BoolSort,
            "Array"             : z3.ArraySort
        }

        self._param_sort = dict()
        self._user_sort_dict = dict()
        self._special_id = dict()

        # extra theory symbol map 
        self._theory_dict = {
            "array" : {
                "select"    : z3.Select,
                "store"     : z3.Store,
            }
        }

        self._func_dict = dict()
        self._module = None

    def prepareFor(self, module: Module):
        # clear previous
        self._param_sort.clear()
        self._user_sort_dict.clear()
        self._func_dict.clear()
        self._symbol_map.clear()
        self._symbol_info.clear()
        self._special_id.clear()
        self._var_map.clear()
        self._module = None

        # recreate the id generator
        self._g = id_gen()

        self._symbol_info = get_symbol_info(module)

        # build symbol map table
        for k in self._symbol_info:
            user_symbol, sorts = k
            z3_sorts = [self._decl_sort(sort) for sort in sorts]

            th, sym = self._symbol_info[k]

            key = (user_symbol, tuple(z3_sorts))

            # euf
            if sym is None:
                assert th == "euf"
            
                f = self._decl_func(user_symbol, *z3_sorts)
                if key in self._symbol_map:
                    raise Exception("found ambiguous symbol ({} : {})".format(user_symbol, " ".join(sorts)))
                else:
                    self._symbol_map[key] = f
            else:
                # mapping an interpreted function
                if th not in self._theory_dict:
                    raise Exception(f"theory {th} is not registered")

                if sym not in self._theory_dict[th]:
                    raise Exception(f"a symbol {sym} does not exist in the theory {th}")
                
                self._symbol_map[key] = self._theory_dict[th][sym]
        
        self._module = module

    def _get_param_sort_info(self, sort: str):
        m = re.match(r'.*{.*}', sort)
        if m is not None:
            g = m.group().split('{')
            name, p_str = g[0], g[1].replace('}', '')

            # parametric sort name should be in sort dict
            if name not in self._sort_dict:
                raise Exception(f"failed to declare sort {sort}")

            # parse params
            p_str = p_str.replace(' ','')
            params = p_str.split(',')

            return (name, *params)
        
        return None

    def _decl_sort(self, sort: str):
        # check if sort is parametric
        paramInfo = self._get_param_sort_info(sort)
        if paramInfo is not None:
            (name, *params) = paramInfo
            param_sorts = [self._decl_sort(p_sort) for p_sort in params]

            k = (name, tuple(param_sorts))
            # check if it already declared
            if k in self._param_sort:
                return self._param_sort[k]
            
            self._param_sort[k] = self._sort_dict[name](*param_sorts)

            return self._param_sort[k]

        if sort in self._sort_dict:
            return self._sort_dict[sort]()

        if sort not in self._user_sort_dict:
            self._user_sort_dict[sort] = z3.DeclareSort(sort)

        return self._user_sort_dict[sort]

    def _decl_func(self, func: str, *args):
        key = (func, *args)
        if key not in self._func_dict:
            self._func_dict[key] = z3.Function(func, *args)

        return self._func_dict[key]
    
    def term2dag(self, term):
        t, _, _ = term
        return self._module.parseTerm(self._term2dag(t))

    def _term2dag(self, term):

        if z3.is_and(term):
            return " and ".join([self._term2dag(c) for c in term.children()])
        
        if z3.is_or(term):
            return " or ".join([self._term2dag(c) for c in term.children()])

        if z3.is_not(term):
            return f"(not {self._term2dag(term.arg(0))})"

        if z3.is_eq(term):
            l, r = self._term2dag(term.arg(0)), self._term2dag(term.arg(1))
            return f"{l} === {r}"

        if z3.is_gt(term):
            l, r = self._term2dag(term.arg(0)), self._term2dag(term.arg(1))
            return f"{l} > {r}"

        if z3.is_ge(term):
            l, r = self._term2dag(term.arg(0)), self._term2dag(term.arg(1))
            return f"{l} >= {r}"

        if z3.is_lt(term):
            l, r = self._term2dag(term.arg(0)), self._term2dag(term.arg(1))
            return f"{l} < {r}"

        if z3.is_le(term):
            l, r = self._term2dag(term.arg(0)), self._term2dag(term.arg(1))
            return f"{l} <= {r}"
        
        if z3.is_add(term):
            l, r = self._term2dag(term.arg(0)), self._term2dag(term.arg(1))
            return f"{l} + {r}"

        if z3.is_sub(term):
            l, r = self._term2dag(term.arg(0)), self._term2dag(term.arg(1))
            return f"{l} - {r}"

        if z3.is_mul(term):
            l, r = self._term2dag(term.arg(0)), self._term2dag(term.arg(1))
            return f"{l} * {r}"

        if z3.is_div(term):
            l, r = self._term2dag(term.arg(0)), self._term2dag(term.arg(1))

            if term.is_int():
                return f"{l} div {r}"
            else:
                return f"{l} / {r}"
        
        # variable or function
        if isinstance(term, z3.z3.FuncDeclRef):
            if term.arity() > 0:
                # currently, not supported
                # # function
                # params = ",".join([self._term2dag(p) for p in term.params()])
                # return f"{term.name()}({params})"
                raise Exception("currently, term2dag does not support function symbol translation")
            else:
                # variable
                sort_table = {"Int" : "Integer", "Real" : "Real", "Bool" : "Boolean"}

                sort_s = str(term.range())
                assert sort_s in sort_table

                return f"{term.name()}:{sort_table[sort_s]}"

        # rational
        if isinstance(term, z3.RatNumRef):
            return f"({term.numerator()}/{term.denominator()}).Real"
            
        # irrational
        if isinstance(term, z3.z3.AlgebraicNumRef):
            # make rational
            rat = term.approx()
            return f"({rat.numerator()}/{rat.denominator()}).Real"
        
        # Integer
        if isinstance(term, z3.z3.IntNumRef):
            return f"({term.as_string()}).Integer"
        
        # Boolean
        if isinstance(term, z3.z3.BoolRef):
            return f"({str(term).lower()}).Boolean"
        
        # In this case, the term must be a variable
        if isinstance(term, z3.z3.ArithRef):
            if term.is_int():
                return f"{term}:Integer"
            else:
                return f"{term}:Real"
        
        raise Exception("failed to apply term2dag")

    def dag2term(self, t: Term):
        """translate a maude term to a SMT solver term

        :param t: A maude term
        :returns: A pair of an SMT solver term and its variables
        """
        term, v_set = self._dag2term(t)
        return tuple([term, None, list(v_set)])

    def _dag2term(self, t: Term):

        if t.isVariable():
            v_sort, v_name = str(t.getSort()), t.getVarName()

            v = None
            if v_sort in self._sort_dict:
                sort = self._sort_dict[v_sort]()
                v = z3.Const(v_name, sort)
            
            if v_sort in self._user_sort_dict:
                sort = self._user_sort_dict[v_sort]
                v = z3.Const(v_name, sort)

            paramInfo = self._get_param_sort_info(v_sort)
            if paramInfo is not None:
                (name, *params) = paramInfo
                param_sorts = [self._decl_sort(p_sort) for p_sort in params]

                k = (name, tuple(param_sorts))

                if k in self._param_sort:
                    sort = self._param_sort[k]
                    v = z3.Const(v_name, sort)
            
            if v is not None:
                v_hash = hash(v)
                if v_hash not in self._var_map:
                    self._var_map[v_hash] = t
                return tuple([v, set([v])])

            raise Exception("wrong variable {} with sort {}".format(v_name, v_sort))

        symbol, symbol_sort = str(t.symbol()), str(t.getSort())

        if symbol_sort in self._special_const:
            if t not in self._special_id:
                self._special_id[t] = next(self._g)

            # remove "var" from type for backward compatibility
            name = f"{symbol}_{symbol_sort[:-3]}_{self._special_id[t]}"
            sort = self._special_const[symbol_sort]()
            
            v = z3.Const(name, sort)

            # keep track of special const
            v_hash = hash(v)
            if v_hash not in self._var_map:
                self._var_map[v_hash] = t
            return tuple([v, set([v])])

        sorts = [self._decl_sort(str(arg.symbol().getRangeSort())) for arg in t.arguments()]
        sorts.append(self._decl_sort(str(t.symbol().getRangeSort())))
        k = (symbol, tuple(sorts))

        if k in self._symbol_map:
            p_args = [self._dag2term(arg) for arg in t.arguments()]
            sym = self._symbol_map[k]

            return tuple([sym(*map(lambda x: x[0], p_args)), reduce(lambda acc, cur: acc.union(cur[1]), p_args, set())])

        if symbol in self._const_dict:
            val = str(t)
            # remove unnecessary postfix
            for s in self._sort_dict:
                val = val.replace(f".{s}", "")

            # remove parenthesis 
            val = val.replace("(", "").replace(")", "")
            c = self._const_dict[symbol](val)
            return tuple([c, set()])

        if symbol in self._op_dict:
            p_args = [self._dag2term(arg) for arg in t.arguments()]
            op = self._op_dict[symbol]

            return tuple([op(*map(lambda x: x[0], p_args)), reduce(lambda acc, cur: acc.union(cur[1]), p_args, set())])
        
        raise Exception(f"fail to apply dag2term to \"{t}\"")

    def mkApp(self, op, args):
        """make an application term

        :param op: An operator
        :param args: a list of arguments
        :returns: A pair of an SMT solver term and its variables
        """
        return tuple([op(*map(lambda x: x[0], args)), None, list()])
    
    def getSymbol(self, t: Term):
        """returns a corresponding operator

        :param t: A maude term
        :returns: A corresponding operator
        """
        if t.isVariable():
            raise Exception("an input term cannot be a variable")

        symbol = str(t.symbol())

        if symbol in self._op_dict:
            op = self._op_dict[symbol]
            return op
        
        raise Exception(f"fail to get corresponding symbol of \"{t}\"")
