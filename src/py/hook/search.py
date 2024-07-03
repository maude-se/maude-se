from ..maude import *
from maudeSE.maude import PyConnector, PyConverter

class SearchHook(Hook):
    def __init__(self, connector: PyConnector, converter: PyConverter, path: bool):
        super().__init__()
        self.conn = connector
        self.conv = converter

        self._is_path = path
        self._data = None

        # special symbol dict
        self._symbol_dict = {
            "fail"          : "failureSymbol",
            "success"       : "resultSymbol",
            "traceStep"     : "traceStepSymbol",
            "traceStepRoot" : "traceStepRootSymbol",
            "nilTrace"      : "nilTraceSymbol",
            "trace"         : "traceSymbol",
            "traceResult"   : "traceResultSymbol",
            "getOrigRule"   : "getOrigRuleSymbol",
            "getOrigTerm"   : "getOrigTermSymbol"
        }

        self._step_dict = {
            "'=>*": ANY_STEPS,
            "'=>1": ONE_STEP,
            "'=>+": AT_LEAST_ONE_STEP,
            "'=>!": NORMAL_FORM,
        }

    def _get_symbol(self, name):
        assert self._data is not None
        assert name in self._symbol_dict

        return self._data.getSymbol(self._symbol_dict[name])

    def _make_assn(self, top_module: Module):
        m = self.conn.get_model()

        assert m is not None
        assert self._data is not None

        assn = top_module.parseTerm("(none).Substitution")
        subst = dict()

        for d in m:
            v = self.conv.term2dag(d)
            val = self.conv.term2dag(m[d])

            subst[v] = val

            t = top_module.parseTerm(
                f"{top_module.upTerm(v)} <- {top_module.upTerm(val)}"
            )

            assn = top_module.parseTerm(f"{assn} ; {t}")
        return assn, Substitution(subst)
    
    def _make_trace(self, meta_module, module, path):

        nil, trace = self._get_symbol("nilTrace"), self._get_symbol("trace")
        step, stepR = self._get_symbol("traceStep"), self._get_symbol("traceStepRoot")

        oterm, orule = self._get_symbol("getOrigTerm"), self._get_symbol("getOrigRule")

        nilTerm = nil.makeTerm([])
        if len(path) <= 1:
            return nilTerm

        prev = nilTerm
        tot = None

        while len(path) > 0:
            # get state
            s, c = path.pop(0)
            
            # get metaRepr
            u_s, u_c = meta_module.upTerm(s), meta_module.upTerm(self.conv.term2dag(c))
            
            # get original term
            u_s = oterm.makeTerm([u_s])
            u_s.reduce()

            # get down term
            d_s = module.downTerm(u_s)
            d_s.reduce()

            u_t = meta_module.upSort(d_s)

            # ignore if reached final
            if len(path) <= 0:
                cur = stepR.makeTerm([u_s, u_c, u_t])
                tot = trace.makeTerm([prev, cur])
                break

            # get original rule
            rule = path.pop(0)
            u_r = self._up_rule(meta_module, rule)
            u_r = orule.makeTerm([u_r])
            u_r.reduce()

            # make trace step
            cur = step.makeTerm([u_s, u_c, u_t, u_r])
            
            tot = trace.makeTerm([prev, cur])
            prev = tot

        if tot is None:
            return nilTerm
        
        return tot
    
    def _up_rule(self, module, rule):
        
        lhs = module.upTerm(rule.getLhs())        
        rhs = module.upTerm(rule.getRhs())

        termk = module.findSort('Term').kind()
        attsk = module.findSort('AttrSet').kind()
        rulek = module.findSort('Rule').kind()
        condk = module.findSort('Condition').kind()
        attrk = module.findSort('Attr').kind()
        qqidk = module.findSort('Qid').kind()

        lbSymbol = module.findSymbol('label', [qqidk], attrk)
        lb = lbSymbol.makeTerm([module.parseTerm(f"'{rule.getLabel()}")])

        if rule.hasCondition():
            cond = self._up_cond(module, rule)
            rlSymbol = module.findSymbol('crl_=>_if_[_].', [termk, termk, condk, attsk], rulek)

            return rlSymbol.makeTerm([lhs, rhs, cond, lb])
        else:
            rlSymbol = module.findSymbol('rl_=>_[_].', [termk, termk, attsk], rulek)

            return rlSymbol.makeTerm([lhs, rhs, lb])

    def _up_cond(self, module, rule):
        termk = module.findSort('Term').kind()
        eqCondk = module.findSort('EqCondition').kind()
        condk = module.findSort('Condition').kind()
        
        eqSymbol = module.findSymbol('_=_', [termk, termk], eqCondk)
        assnSymbol = module.findSymbol('_:=_', [termk, termk], eqCondk)
        conjSymbol = module.findSymbol('_/\_', [condk, condk], condk)
        nilSymbol = module.findSymbol('nil', [], eqCondk)

        c_l = nilSymbol.makeTerm([])

        for cond in rule.getCondition():
            
            # currently only consider equality condition
            if isinstance(cond, EqualityCondition):
                
                l = module.upTerm(cond.getLhs())
                r = module.upTerm(cond.getRhs())

                c = eqSymbol.makeTerm([l, r])
                c_l = conjSymbol.makeTerm([c_l, c])
            
            if isinstance(cond, AssignmentCondition):
                l = module.upTerm(cond.getLhs())
                r = module.upTerm(cond.getRhs())

                c = assnSymbol.makeTerm([l, r])
                c_l = conjSymbol.makeTerm([c_l, c])
        
        return c_l            

    def run(self, term, data):
        # import time
        # s = time.time()
        # reduce arguments
        for arg in term.arguments():
            arg.reduce()

        # Module Term Term Condition Qid Bound Nat
        (
            mo,
            init,
            goal,
            cond,
            step,
            bound,
            sol,
            logic,
            fold,
            merge,
        ) = term.arguments()

        self._data = data

        module = downModule(mo)
        self.conv.prepareFor(module)

        ff = self._get_symbol("fail")
        symbol_mo = ff.getModule()

        init_t = module.downTerm(init)
        goal_t = module.downTerm(goal)

        searchType = self._step_dict[str(step)]
        sol_num = int(str(sol).split(".")[0].replace("(", "").replace(")", ""))

        b = str(bound)
        max_depth = (
            -1
            if b == "unbounded"
            else int(b.split(".")[0].replace("(", "").replace(")", ""))
        )

        if str(cond.getSort()) == "EqCondition":
            (
                l,
                r,
            ) = cond.arguments()

            downR = module.downTerm(r)

            if downR is None:
                downR = ff.getModule().downTerm(r)

            c = EqualityCondition(module.downTerm(l), downR)
        else:
            raise Exception("currently only a single equality condition is supported")

        is_fold = "true" in str(fold)
        is_merge = "true" in str(merge)

        self.conn.set_logic(str(logic).replace("'", ""))
        # e = time.time()

        # print("else : {:.3f}".format(e - s))
        for n, (sol, const, nrew, num, path) in enumerate(
            init_t.smtSearch2(
                searchType,
                goal_t,
                self.conn,
                self.conv,
                is_fold,
                is_merge,
                [c],
                max_depth,
            )
        ):
            if self._is_path:
                if sol_num == num:
                    subst_t, _ = self._make_assn(symbol_mo)
                    return self._get_symbol("traceResult").makeTerm(
                        [
                            self._make_trace(symbol_mo, module, path()),
                            subst_t
                        ]
                    )
                else:
                    continue
            
            cur_n = n + 1

            # already exceed
            if cur_n > sol_num:
                break

            if cur_n == sol_num:

                subst_t, subst = self._make_assn(symbol_mo)
                print("rewrites : ", nrew)
                # print("  # state explored : " + str(num))
                
                (s_t,) = sol.arguments()

                ct = self.conv.term2dag(const)

                return self._get_symbol("success").makeTerm(
                    [
                        symbol_mo.upTerm(s_t),
                        subst_t,
                        symbol_mo.upTerm(subst.instantiate(s_t)),
                        symbol_mo.upTerm(ct),
                        symbol_mo.parseTerm(f"({num}).Nat"),
                    ]
                )

        return ff.makeTerm([])
