%module(directors="1") maudeSE

%{
#include "smt_wrapper.hh"
%}

%include std_vector.i

namespace std {
  %template (SmtTermVector) vector<SmtTerm*>;
}

%feature("director") PyConverter;
class PyConverter : public Converter
{
public:
  %newobject dag2term;

  virtual ~PyConverter() {};
  virtual PyObject* prepareFor(PyObject* module) = 0;
  virtual SmtTerm* dag2term(EasyTerm* dag) = 0;
  virtual EasyTerm* term2dag(SmtTerm* term) = 0;
  virtual PyObject* mkApp(PyObject* symbol, PyObject* args) = 0;
  virtual PyObject* getSymbol(PyObject* dag) = 0;
};

class SmtTerm{
public:
  SmtTerm() = delete;
  SmtTerm(PyObject* data);
  PyObject* getData();
};

class TermSubst{
public:
    TermSubst() = delete;
    TermSubst(PyObject* subst);
    PyObject* getSubst();
};

class SmtModel{
public:
    PyObject* model;

    SmtModel() = delete;
    SmtModel(PyObject* model);
    PyObject* getModel();
};

%feature("director") SmtResult;
class SmtResult{
public:
    
    virtual ~SmtResult() {};
    virtual bool is_sat() = 0;
    virtual bool is_unsat() = 0;
    virtual bool is_unknown() = 0;
};

%feature("director") PyConnector;
class PyConnector : public Connector
{
public:
  %newobject check_sat;
  %newobject add_const;
  %newobject get_model;

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