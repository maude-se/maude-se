from .connector import *
from .converter import *

class Factory:
    def __init__(self):
        self._map = {
            "z3"       : (Z3Converter, Z3Connector),
            "yices"    : (YicesConverter, YicesConnector),
            "cvc5"     : (Cvc5Converter, Cvc5Connector),
        }

    def create(self, solver: str):
        if solver not in self._map:
            raise Exception("unsupported solver {}".format(solver))

        cv_f, cn_f = self._map[solver]
        conv = cv_f()
        conn = cn_f(conv)

        return conv, conn