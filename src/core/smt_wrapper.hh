//
//	Class for folding and maintaining the history of a search.
//
#ifndef _smt_wrapper_h_
#define _smt_wrapper_h_

#include "easyTerm.hh"
#include "smt_wrapper_interface.hh"

class PyConverter : Converter
{
public:
	virtual ~PyConverter() {};
    virtual PyObject* prepareFor(PyObject* module) = 0;
    virtual SmtTerm* dag2term(EasyTerm* dag) = 0;
    virtual EasyTerm* term2dag(SmtTerm* term) = 0;
    virtual PyObject* mkApp(PyObject* symbol, PyObject* args) = 0;
    virtual PyObject* getSymbol(PyObject* dag) = 0;

public:
    inline EasyTerm* convert(DagNode* dag) { return new EasyTerm(dag); };
};

class PyConnector : Connector
{
public:
	virtual ~PyConnector() {};
    virtual bool check_sat(std::vector<SmtTerm*> consts) = 0;
    virtual bool subsume(TermSubst* subst, SmtTerm* prev, SmtTerm* acc, SmtTerm* cur) = 0;
    virtual TermSubst* mkSubst(std::vector<EasyTerm*> vars, std::vector<EasyTerm*> vals) = 0;
    // virtual PyObject* merge(PyObject* subst, PyObject* prev_const, std::vector<SmtTerm*> target_consts) = 0;
    virtual SmtTerm* add_const(SmtTerm* acc, SmtTerm* cur) = 0;
    virtual SmtModel* get_model() = 0;
    virtual void print_model() = 0;
    virtual void set_logic(std::string* logic) = 0;
};

#endif