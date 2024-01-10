import abc

class Converter:
    @abc.abstractmethod
    def prepareFor(self, module):
        pass
    
    @abc.abstractmethod
    def dag2term(self, dag):
        pass

    @abc.abstractmethod
    def term2dag(self, term):
        pass


class Connector:
    @abc.abstractmethod
    def check_sat(self, *consts):
        pass

    @abc.abstractmethod
    def subsume(self, subst, src_const, *target_consts):
        pass

    @abc.abstractmethod
    def merge(self, subst, src_const, *target_consts):
        pass

    @abc.abstractmethod
    def add_const(self, *consts):
        pass

    @abc.abstractmethod
    def get_model(self):
        pass

    @abc.abstractmethod
    def print_model(self):
        pass

    @abc.abstractmethod
    def set_logic(self, logic):
        pass