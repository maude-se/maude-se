import os
from .maude import *

def smtSearch2(mo: Module, init: Term, goal: Term, 
               cond: EqualityCondition, searchType:str, bound, sol_num, logic, is_fold, is_merge) -> Term:
    load('smt-check.maude')

    meta = getModule("META-LEVEL")
    up_mo = meta.parseTerm(f"upModule(\'{mo}, false)")
    up_mo.reduce()

    up_init = meta.upTerm(init)
    up_goal = meta.upTerm(goal)

    nat = getModule('NAT')

    up_cond_list = [meta.upTerm(cond.getLhs()), meta.upTerm(cond.getRhs())]

    # print(up_init)
    # print(up_goal)

    # META-CONDITION
    t_k = meta.findSort('Term').kind()
    c_k = meta.findSort('EqCondition').kind()

    cond_sym = meta.findSymbol('_=_', [t_k, t_k], c_k)

    up_cond = cond_sym.makeTerm(up_cond_list)
    metaSearchMo = getModule('META-SMT-SEARCH2')

    
    b = meta.parseTerm(f"\'{searchType}")
    lo = meta.parseTerm(f"\'{logic}")
    d = "unbounded" if bound == "unbounded" else nat.parseTerm(str(bound)) 
    s_n = nat.parseTerm(str(sol_num))

    fold = "(true).Bool" if is_fold else "(false).Bool"
    merge = "(true).Bool" if is_merge else "(false).Bool"

    cmd = metaSearchMo.parseTerm(f"metaSmtSearch2({up_mo}, {up_init}, {up_goal}, {up_cond}, {b}, {d}, {s_n}, {lo}, {fold}, {merge})")
    cmd.reduce()
    return cmd

