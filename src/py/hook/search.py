from ..maude import *
from ..interface import *


class SearchHook(Hook):
  def __init__(self, connector: Connector, converter: Converter):
    super().__init__()
    self.conn = connector
    self.conv = converter

    self._data = None
  
    # special symbol dict
    self._symbol_dict = {
      "fail"      : "failureSymbol",
      "success"   : "resultSymbol",
    }

    self._step_dict = {
      "'=>*"  : ANY_STEPS,
      "'=>1"  : ONE_STEP,
      "'=>+"  : AT_LEAST_ONE_STEP,
      "'=>!"  : NORMAL_FORM,
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

      t = top_module.parseTerm(f"{top_module.upTerm(v)} <- {top_module.upTerm(val)}")
      
      assn = top_module.parseTerm(f"{assn} ; {t}")
    return assn, Substitution(subst)

  def run(self, term, data):
    # reduce arguments
    for arg in term.arguments():
      arg.reduce()

    # Module Term Term Condition Qid Bound Nat
    mo, init, goal, cond, step, bound, sol, logic, fold, merge, = term.arguments()
  
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
    max_depth = -1 if b == "unbounded" else int(b.split(".")[0].replace("(", "").replace(")", ""))

    if str(cond.getSort()) == "EqCondition":
      l, r, = cond.arguments()
      
      downR = module.downTerm(r)

      if downR is None:
        downR = ff.getModule().downTerm(r)
      
      c = EqualityCondition(module.downTerm(l), downR)
    else:
      raise Exception("currently only a single equality condition is supported")

    is_fold = "true" in str(fold)
    is_merge = "true" in str(merge)
    
    self.conn.set_logic(str(logic).replace("'", ""))

    for n, (sol, const, nrew, num) in enumerate(init_t.smtSearch2(searchType, goal_t, self.conn, self.conv, is_fold, is_merge, [c], max_depth)):
      cur_n = n + 1

      # already exceed
      if cur_n > sol_num:
        break

      if cur_n == sol_num:
        # print(sol, " with ", nrew)
        # print("  # state explored : " + str(num))
        subst_t, subst = self._make_assn(symbol_mo)
        s_t, = sol.arguments()

        # print("where")
        ct = self.conv.term2dag(const)
        return self._get_symbol("success").makeTerm([symbol_mo.upTerm(s_t), subst_t, symbol_mo.upTerm(subst.instantiate(s_t)), symbol_mo.upTerm(ct), symbol_mo.parseTerm(f"({num}).Nat")])

      # if n >= max_num - 1:
      #   break

    return ff.makeTerm([])