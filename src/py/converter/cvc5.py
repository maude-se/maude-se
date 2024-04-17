from ..interface import *
from ..util import *
from functools import reduce

from maudeSE.maude import *

import cvc5
from cvc5 import Kind


class Cvc5Converter(Converter):
    """A term converter from Maude to Yices"""

    def __init__(self):
        self._s = cvc5.Solver()
        self._g = id_gen()
        self._symbol_info = dict()
        self._symbol_map = dict()
        self._var_dict = dict()
        self._fun_dict = dict()

        # smt.maude map
        self._op_dict = {
            "not_"          : [Kind.NOT],
            "_and_"         : [Kind.AND],
            "_or_"          : [Kind.OR],
            "_xor_"         : [Kind.XOR],
            "_implies_"     : [Kind.IMPLIES],
            "_===_"         : [Kind.EQUAL],
            "_=/==_"        : [Kind.EQUAL, Kind.NOT],
            "_?_:_"         : [Kind.ITE],

            "-_"            : [Kind.NEG],
            "_+_"           : [Kind.ADD],
            "_-_"           : [Kind.SUB],
            "_*_"           : [Kind.MULT],
            "_div_"         : [Kind.INTS_DIVISION],
            "_/_"           : [Kind.DIVISION],
            "_mod_"         : [Kind.INTS_MODULUS],

            # "_divisible_" : ?

            "_<_"           : [Kind.LT],
            "_<=_"          : [Kind.LEQ],
            "_>_"           : [Kind.GT],
            "_>=_"          : [Kind.GEQ],
        }

        self._bool_const = {
            "true"          : self._s.mkTrue,
            "false"         : self._s.mkFalse,
        }

        self._num_const = {
            "<Integers>"    : self._s.mkInteger,
            "<Reals>"       : self._s.mkReal,
        }

        self._sort_dict = {
            "Integer"           : self._s.getIntegerSort,
            "Real"              : self._s.getRealSort,
            "Boolean"           : self._s.getBooleanSort,
            "Array"             : self._s.mkArraySort,
        }

        self._param_sort = dict()
        self._user_sort_dict = dict()
        self._special_id = dict()

        # extra theory symbol map 
        self._theory_dict = {
            "array" : {
                "select"    : [Kind.SELECT],
                "store"     : [Kind.STORE],
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
        self._var_dict.clear()
        self._fun_dict.clear()
        self._module = None

        # recreate the id generator
        self._g = id_gen()

        self._symbol_info = get_symbol_info(module)

        # build symbol map table
        for k in self._symbol_info:
            user_symbol, sorts = k
            cvc5_sorts = [self._decl_sort(sort) for sort in sorts]

            th, sym = self._symbol_info[k]

            key = (user_symbol, tuple(cvc5_sorts))

            # euf
            if sym is None:
                assert th == "euf"
            
                f = self._decl_func(user_symbol, *cvc5_sorts)
                if key in self._symbol_map:
                    raise Exception("found ambiguous symbol ({} : {})".format(user_symbol, " ".join(sorts)))
                else:
                    self._symbol_map[key] = (f, th)
            else:
                # mapping an interpreted function
                if th not in self._theory_dict:
                    raise Exception(f"theory {th} is not registered")

                if sym not in self._theory_dict[th]:
                    raise Exception(f"a symbol {sym} does not exist in the theory {th}")
                
                self._symbol_map[key] = (self._theory_dict[th][sym], th)
        
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
            
            doms, rng = param_sorts[:-1], param_sorts[-1]
            
            # see if we can get sort in the dict
            if name in self._sort_dict:
                # currently only array is available
                self._param_sort[k] = self._sort_dict[name](doms[0], rng)
            else:
                self._param_sort[k] = self._s.declareSort(name, len(doms))

            return self._param_sort[k]

        if sort in self._sort_dict:
            return self._sort_dict[sort]()

        if sort not in self._user_sort_dict:
            self._user_sort_dict[sort] = self._s.declareSort(sort, 0)

        return self._user_sort_dict[sort]

    def _decl_func(self, func: str, *sorts):
        # we assume that the functions with the same domain must have the same range
        raw_args = list(sorts)
        doms, rng = raw_args[:-1], raw_args[-1]

        key = (func, *doms)
        if key not in self._func_dict:
            self._func_dict[key] = self._s.declareFun(func, doms, rng)

        return self._func_dict[key]
    
    def term2dag(self, term):
        t, _, _ = term
        return self._module.parseTerm(self._term2dag(t))

    def _term2dag(self, term):
        # t, ty = term

        kind, sort = term.getKind(), term.getSort()
        if kind == Kind.AND:
            return " and ".join([self._term2dag(c) for c in term])
        
        if kind == Kind.OR:
            return " or ".join([self._term2dag(c) for c in term])
        
        if kind == Kind.NOT:
            return f"(not {self._term2dag(term[0])})"
        
        if kind == Kind.EQUAL:
            l, r = self._term2dag(term[0]), self._term2dag(term[1])
            return f"({l} === {r})"

        if kind == Kind.GT:
            l, r = self._term2dag(term[0]), self._term2dag(term[1])
            return f"{l} > {r}"

        if kind == Kind.GEQ:
            l, r = self._term2dag(term[0]), self._term2dag(term[1])
            return f"{l} >= {r}"

        if kind == Kind.LT:
            l, r = self._term2dag(term[0]), self._term2dag(term[1])
            return f"{l} < {r}"

        if kind == Kind.LEQ:
            l, r = self._term2dag(term[0]), self._term2dag(term[1])
            return f"{l} <= {r}"
        
        if kind == Kind.ADD:
            l, r = self._term2dag(term[0]), self._term2dag(term[1])
            return f"{l} + {r}"

        if kind == Kind.SUB:
            l, r = self._term2dag(term[0]), self._term2dag(term[1])
            return f"{l} - {r}"

        if kind == Kind.MULT:
            l, r = self._term2dag(term[0]), self._term2dag(term[1])
            return f"{l} * {r}"

        if kind == Kind.DIVISION:
            l, r = self._term2dag(term[0]), self._term2dag(term[1])

            if sort.isInteger():
                return f"{l} div {r}"
            else:
                return f"{l} / {r}"

        # variable
        if kind == Kind.CONSTANT:
            # variable
            sort_table = {self._s.getIntegerSort()  : "Integer", 
                          self._s.getRealSort()     : "Real", 
                          self._s.getBooleanSort()  : "Boolean"}

            assert sort in sort_table

            return f"{term}:{sort_table[sort]}"
        
        # numerical
        if kind == Kind.CONST_INTEGER:
            return f"({term}).Integer"
        
        if kind == Kind.CONST_RATIONAL:
            rv = term.getRealValue()
            return f"({rv.numerator}/{rv.denominator}).Real"

        # Boolean
        if kind == Kind.CONST_BOOLEAN:
            return f"({term}).Boolean"
        
        raise Exception("failed to apply term2dag")

    def dag2term(self, t: Term):
        """translate a maude term to a Yices SMT solver term

        :param t: A maude term
        :returns: A pair of
          an SMT solver term and its variables
        """
        term, v_set = self._dag2term(t)
        return tuple([term, None, list(v_set)])
    
    def _dag2term(self, t: Term):

        if t.isVariable():
            v_sort, v_name = str(t.getSort()), t.getVarName()

            key = (v_sort, v_name)

            if key in self._var_dict:
                v = self._var_dict[key]
                return tuple([v, set([v])])

            v = None
            if v_sort in self._sort_dict:
                sort = self._sort_dict[v_sort]()
                v = self._s.mkConst(sort, v_name)
            
            if v_sort in self._user_sort_dict:
                sort = self._user_sort_dict[v_sort]
                v = self._s.mkConst(sort, v_name)

            paramInfo = self._get_param_sort_info(v_sort)
            if paramInfo is not None:
                (name, *params) = paramInfo
                param_sorts = [self._decl_sort(p_sort) for p_sort in params]

                k = (name, tuple(param_sorts))

                if k in self._param_sort:
                    sort = self._param_sort[k]
                    v = self._s.mkConst(sort, v_name)
            
            if v is not None:
                self._var_dict[key] = v
                return tuple([v, set([v])])

            raise Exception("wrong variable {} with sort {}".format(v_name, v_sort))

        symbol, symbol_sort = str(t.symbol()), str(t.getSort())

        sorts = [self._decl_sort(str(arg.symbol().getRangeSort())) for arg in t.arguments()]
        sorts.append(self._decl_sort(str(t.symbol().getRangeSort())))
        k = (symbol, tuple(sorts))

        if k in self._symbol_map:
            p_args = [self._dag2term(arg) for arg in t.arguments()]

            op_s, th = self._symbol_map[k]

            raw_args = list(map(lambda x: x[0], p_args))
            v_s = reduce(lambda acc, cur: acc.union(cur[1]), p_args, set())

            # fun_key = (sym, symbol)
            if th == "euf": 
                # we only know domains
                doms, rng = list(map(lambda x: x.getSort(), raw_args)), None
                
                # make sure to declare the function
                self._decl_func(symbol, *doms, rng)

                fun_key = (symbol, *doms)

                _f = self._func_dict[fun_key]

                f = self._s.mkTerm(Kind.APPLY_UF, _f, *raw_args)
            else:
                f = None
                for op in op_s:
                    if f is None:
                        f = self._s.mkTerm(op, *raw_args)
                    else:
                        f = self._s.mkTerm(op, f)
            
            return tuple([f, v_s])

        if symbol in self._bool_const:
            c = self._bool_const[symbol]()
            return tuple([c, set()])
        
        if symbol in self._num_const:
            val = str(t)
            # remove unnecessary postfix
            for s in self._sort_dict:
                val = val.replace(f".{s}", "")

            # remove parenthesis 
            val = val.replace("(", "").replace(")", "")
            c = self._num_const[symbol](val)

            return tuple([c, set()])

        if symbol in self._op_dict:
            p_args = [self._dag2term(arg) for arg in t.arguments()]
            op_s = self._op_dict[symbol]

            v_s = reduce(lambda acc, cur: acc.union(cur[1]), p_args, set())

            t = None
            for op in op_s:
                if t is None:
                    t = self._s.mkTerm(op, *map(lambda x: x[0], p_args))
                else:
                    t = self._s.mkTerm(op, t)

            return tuple([t, v_s])
        
        raise Exception(f"fail to apply dag2term to \"{t}\"")
    
    def mkApp(self, op, args):
        """make an application term

        :param op: An operator
        :param args: a list of arguments
        :returns: A pair of an SMT solver term and its variables
        """
        op_c, th = op

        if th == "euf": 
            f = self._s.mkTerm(Kind.APPLY_UF, op_c, *map(lambda x: x[0], args))
            return tuple([f, None, list()])
        else:
            t = None
            for op in op_c:
                if t is None:
                    t = self._s.mkTerm(op, *map(lambda x: x[0], args))
                else:
                    t = self._s.mkTerm(op, t)

            return tuple([t, None, list()])

    def getSymbol(self, t: Term):
        """returns a corresponding operator

        :param t: A maude term
        :returns: A corresponding operator
        """
        if t.isVariable():
            raise Exception("an input term cannot be a variable")

        symbol = str(t.symbol())

        sorts = [self._decl_sort(str(arg.symbol().getRangeSort())) for arg in t.arguments()]
        sorts.append(self._decl_sort(str(t.symbol().getRangeSort())))
        k = (symbol, tuple(sorts))

        if k in self._symbol_map:
            return self._symbol_map[k]

        if symbol in self._op_dict:
            return tuple([self._op_dict[symbol], "builtin"])
        
        raise Exception(f"fail to get corresponding symbol of \"{t}\"")
