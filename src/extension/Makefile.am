noinst_LIBRARIES = libextension.a

libextension_a_CPPFLAGS = \
    -I$(top_srcdir)/src/Utility \
    -I$(top_srcdir)/src/Temporal \
    -I$(top_srcdir)/src/Interface \
    -I$(top_srcdir)/src/Core \
    -I$(top_srcdir)/src/Variable \
    -I$(top_srcdir)/src/FullCompiler \
    -I$(top_srcdir)/src/Higher \
    -I$(top_srcdir)/src/CUI_Theory \
    -I$(top_srcdir)/src/S_Theory \
    -I$(top_srcdir)/src/NA_Theory \
    -I$(top_srcdir)/src/FreeTheory \
    -I$(top_srcdir)/src/ObjectSystem \
    -I$(top_srcdir)/src/Mixfix \
    -I$(top_srcdir)/src/BuiltIn \
    -I$(top_srcdir)/src/SMT \
    -I$(top_srcdir)/src/IO_Stuff \
    -I$(top_srcdir)/src/ACU_Persistent \
    -I$(top_srcdir)/src/ACU_Theory \
    -I$(top_srcdir)/src/AU_Persistent \
    -I$(top_srcdir)/src/AU_Theory \
    -I$(top_srcdir)/src/Meta \
    -I$(top_srcdir)/src/3rdParty \
    -I$(top_srcdir)/src/FullCompiler \
    -I$(top_srcdir)/src/StrategyLanguage \
    -I$(top_srcdir)/src/Mixfix

libextension_a_SOURCES = \
	smtManager.cc \
	smtCheckSymbol.cc \
	simplifyFormulaSymbol.cc \
	extensionSymbol.cc \
	tacticApplySymbol.cc

EXTRA_DIST = \
    z3_Extension.cc \
    yices2_Extension.cc \
    cvc4_Extension.cc

noinst_HEADERS = \
    z3_Extension.hh \
    yices2_Extension.hh \
    cvc4_Extension.hh \
    abstractSmtManager.hh \
    smtManager.hh \
    smtCheckSymbol.hh \
    simplifyFormulaSymbol.hh \
    extensionSymbol.hh \
    tacticApplySymbol.hh

