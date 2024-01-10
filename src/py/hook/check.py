from maudeSE.maude import *
from ..interface import *


class CheckHook(Hook):
  def __init__(self, connector: Connector, converter: Converter):
    super().__init__()
    self.conn = connector
    self.conv = converter

    self._data = None
  
    # special symbol dict
    self._symbol_dict = {
      # "int"     : "intAssnSymbol",
      # "real"    : "realAssnSymbol",
      # "bool"    : "boolAssnSymbol",
      "assnPair": "assnPairSymbol",
      "concat"  : "concatSatAssignmentSetSymbol",
      "empty"   : "emptySatAssignmentSetSymbol",
      "assn"    : "smtAssignmentResultSymbol",
      "unknown" : "unknownResultSymbol",
    }
  
  def _get_symbol(self, name):
    assert self._data is not None
    assert name in self._symbol_dict

    return self._data.getSymbol(self._symbol_dict[name])

  def _make_assn(self, module: Module):
    md = self.conn.get_model()

    assert md is not None
    assert self._data is not None
  
    empty_symbol = self._get_symbol("empty")
    top_module = empty_symbol.getModule()

    assn = empty_symbol.makeTerm([])

    for d in md:
      v = self.conv.term2dag(d)
      val = self.conv.term2dag(md[d])

      t = self._get_symbol("assnPair").makeTerm([top_module.upTerm(v), top_module.upTerm(val)])
      
      assn = self._get_symbol("concat").makeTerm([assn, t])
    return self._get_symbol("assn").makeTerm([assn])

  def run(self, term, data):
    # one argument
    mo, arg, logic, is_gen, = term.arguments()

    self._data = data

    tt = data.getTerm('builtinTrueTerm')
    ff = data.getTerm('builtinFalseTerm')

    module = downModule(mo)

    self.conv.prepareFor(module)
    term = self.conv.dag2term(module.downTerm(arg))
  
    try:
      self.conn.set_logic(str(logic).replace("'", ""))
      r = self.conn.check_sat(term)
      # print(self.solv.assertions())

      if r == True and is_gen == tt:
        try:
          assn = self._make_assn(module)
          return assn
        except:
          # contain some unsupported symbols
          # e.g., uninterpreted
          return tt

      # for printing purpose
      if r == True and is_gen == ff:
        self.conn.print_model()

      if r == True:
        return tt
      elif r == False:
        return ff
    except:
      return self._get_symbol("unknown").makeTerm([])
