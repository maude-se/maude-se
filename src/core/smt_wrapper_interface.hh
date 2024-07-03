//
//	Class for folding and maintaining the history of a search.
//
#ifndef _interface_h_
#define _interface_h_

#include "Python.h"
#include <vector>

// forward decl
class EasyTerm;

class SmtTerm{
    PyObject* data;

public:
    SmtTerm(PyObject* data) : data(data) { Py_INCREF(this->data); };
    PyObject* getData() { 
        Py_INCREF(this->data);
        return data; 
    };
};

class TermSubst{
    PyObject* subst;

public:
    TermSubst(PyObject* subst) : subst(subst) { Py_INCREF(this->subst); };
    PyObject* getSubst() { 
        Py_INCREF(this->subst);
        return subst; 
    };
};

class SmtModel{
public:
    PyObject* model;
    SmtModel(PyObject* model) : model(model) {
        Py_INCREF(this->model);
    };
    PyObject* getModel() {         
        Py_INCREF(this->model);
        return model; 
    };
};

class SmtResult{

public:
    virtual ~SmtResult() {};
    virtual bool is_sat() = 0;
    virtual bool is_unsat() = 0;
    virtual bool is_unknown() = 0;
};

class Converter
{
public:
	virtual ~Converter() {};
    virtual PyObject* prepareFor(PyObject* module) = 0;
    virtual SmtTerm* dag2term(EasyTerm* dag) = 0;
    virtual EasyTerm* term2dag(SmtTerm* term) = 0;
    virtual PyObject* mkApp(PyObject* symbol, PyObject* args) = 0;
    virtual PyObject* getSymbol(PyObject* dag) = 0;

public:
    virtual EasyTerm* convert(DagNode* dag) = 0;
};

class Connector
{
public:
	virtual ~Connector() {};
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