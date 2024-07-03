project('Maude', 'cpp', version: '3.3.1+smc', default_options: ['cpp_std=c++11'])

#
## Configuration
#

add_project_arguments('-Wno-non-virtual-dtor', language : 'cpp')
add_project_arguments('-DHAVE_CONFIG_H', language : 'cpp')

conf = configuration_data()

# Replicates the options and settings of the original Autotools system
conf.set_quoted('PACKAGE',
	meson.project_name(),
	description: 'Name of package')
conf.set_quoted('VERSION',
	meson.project_version(),
	description: 'Version number of package')
conf.set_quoted('PACKAGE_VERSION',
	meson.project_version(),
	description: 'Define to the version of this package')
conf.set_quoted('PACKAGE_STRING',
	meson.project_name() + ' ' + meson.project_version(),
	description: 'Define to the full name and version of this package')
conf.set_quoted('PACKAGE_BUGREPORT',
	'maude-bugs@lists.cs.illinois.edu',
	description: 'Define to the address where bug reports for this package should be sent')

if get_option('enable-debug')
	conf.set('DUMP', 1, description: 'include dump code')
else
	conf.set('NO_ASSERT', 1, description: 'do not do runtime checks')
	conf.set('LOCAL_INLINES', 1, description: 'inline and discard selected local functions')
endif

if get_option('enable-compiler')
	conf.set('COMPILER', 1, description: 'build the experimental integrated compiler')
	conf.set('ANNOTATED', 1, description: 'annotate compiler output')
endif

# Add a macro to tell that the probabilistic strategy language is being used
conf.set('WITH_PROBABILISTIC_SLANG', 1, description: 'the probabilistic strategy language is included')

cxx = meson.get_compiler('cpp')

#
## Check for type sizes
#

systemTypes = {
	'INT' : 'int',
	'LONG' : 'long',
	'SHORT' : 'short',
	'UNSIGNED_LONG' : 'unsigned long',
	'VOID_P' : 'void *'
}

foreach key, type : systemTypes
	size = cxx.sizeof(type)
	if size > 0
		conf.set('SIZEOF_' + key, size,
			 description: 'The size of ' + type + ', as computed by sizeof.')
	endif
endforeach

#
## Check for system headers
#

systemHeaders = [
	'sys/time.h',
	'math.h',
	'ieeefp.h',
	'sys/termios.h',
	'stddef.h',
	'limits.h',
	'stdlib.h',
	'stdio.h',
	'ctype.h',
	'unistd.h',
	'ostream',
	'ostream.h',
	'string.h',
	'strings.h'
]

foreach header : systemHeaders
	name = header.to_upper().underscorify()
	if cxx.has_header(header)
		conf.set('HAVE_' + name, 1,
			 description: 'Define to 1 if you have the <' + header + '> header file.')
	endif
endforeach

#
## Check for functions
#

if cxx.has_function('ppoll', prefix: '#include <poll.h>')
	conf.set('HAVE_PPOLL', 1, description: 'use ppoll()')
endif

#
## Check for libraries
#

# Allow additional header and library directories
extraSearchPaths = get_option('extra-lib-dirs')
extraIncludePaths = get_option('extra-include-dirs')

r = run_command('python3-config', '--prefix', check: true)
output = r.stdout().strip()

extraSearchPaths += [output + '/lib', meson.current_source_dir() + '/.build/lib']

r = run_command('python3-config', '--includes', check: true)
output = r.stdout().strip()

extraIncludeArgs = [output.split(), '-I' + meson.current_source_dir() + '/.build/include']

foreach path : extraIncludePaths
	extraIncludeArgs += ['-I' + path]
endforeach

add_project_arguments(extraIncludeArgs, language: 'cpp')

# Indicate which libraries must be statically linked
staticLibs = get_option('static-libs')

libraries = []

gmpxx = cxx.find_library('gmpxx',
		static: 'gmp' in staticLibs,
		dirs: extraSearchPaths)
gmp = cxx.find_library('gmp',
		static: 'gmp' in staticLibs,
		dirs: extraSearchPaths)

libraries += [gmp, gmpxx]


# GNU readline (https://tiswww.case.edu/php/chet/readline/rltop.html)
readline = dependency('readline',
		static: 'readline' in staticLibs,
		required: get_option('with-readline'))

# BuDDy library (http://sourceforge.net/projects/buddy)
buddy = cxx.find_library('bdd',
		static: 'buddy' in staticLibs,
		dirs: extraSearchPaths)

# GNU libsigsegv (https://www.gnu.org/software/libsigsegv/)
sigsegv = cxx.find_library('sigsegv',
		static: 'sigsegv' in staticLibs,
		required: get_option('with-sigsegv'),
		dirs: extraSearchPaths)

libraries += [buddy, sigsegv]

if readline.found()
	conf.set('USE_READLINE', 1, description: 'use GNU readline command line editing library')
endif

if sigsegv.found()
	conf.set('USE_LIBSIGSEGV', 1, description: 'use libsigsegv to handle segmentation faults')
endif

# Select which SMT solver to link with
smtOption = get_option('with-smt')

if smtOption == 'yices2'
	yices2 = cxx.find_library('yices',
			static: 'yices2' in staticLibs,
			dirs: extraSearchPaths)
	libraries += [yices2]
	conf.set('USE_YICES2', 1, description: 'use Yices2 SMT solver library')

elif smtOption == 'cvc4'
	cvc4 = cxx.find_library('cvc4',
			static: 'cvc4' in staticLibs,
			dirs: extraSearchPaths)
	cln = cxx.find_library('cln',
			dirs: extraSearchPaths,
			required: false)
	libraries += [cvc4, cln]
	conf.set('USE_CVC4', 1, description: 'use CVC4 SMT solver library')
endif

#
## Check for auxiliary programs
#

cat   = find_program('cat')
cp    = find_program('cp')
flex  = find_program('flex')
bison = find_program('bison')

configure_file(output: 'config.h', configuration: conf)


#
## Source files
#

# Parser

parser_includes = include_directories(
	'src/Parser',
	'src/Utility',
)

parser_source = [
	'src/Parser/parser.cc',
]

parser = static_library('parser', parser_source, include_directories: parser_includes)

# StrategyLanguage

strategylanguage_includes = include_directories(
	'src/StrategyLanguage',
	'src/Utility',
	'src/Interface',
	'src/Variable',
	'src/Core',
	'src/S_Theory',
	'src/NA_Theory',
	'src/BuiltIn',
	'src/Higher',
	'src/FullCompiler',
)

strategylanguage_source = [
	'src/StrategyLanguage/strategyExpression.cc',
	'src/StrategyLanguage/trivialStrategy.cc',
	'src/StrategyLanguage/applicationStrategy.cc',
	'src/StrategyLanguage/concatenationStrategy.cc',
	'src/StrategyLanguage/iterationStrategy.cc',
	'src/StrategyLanguage/branchStrategy.cc',
	'src/StrategyLanguage/unionStrategy.cc',
	'src/StrategyLanguage/testStrategy.cc',
	'src/StrategyLanguage/subtermStrategy.cc',
	'src/StrategyLanguage/callStrategy.cc',
	'src/StrategyLanguage/choiceStrategy.cc',
	'src/StrategyLanguage/sampleStrategy.cc',
	'src/StrategyLanguage/weightedSubtermStrategy.cc',
	'src/StrategyLanguage/strategicExecution.cc',
	'src/StrategyLanguage/strategicTask.cc',
	'src/StrategyLanguage/branchTask.cc',
	'src/StrategyLanguage/strategicProcess.cc',
	'src/StrategyLanguage/decompositionProcess.cc',
	'src/StrategyLanguage/applicationProcess.cc',
	'src/StrategyLanguage/strategicSearch.cc',
	'src/StrategyLanguage/fairStrategicSearch.cc',
	'src/StrategyLanguage/depthFirstStrategicSearch.cc',
	'src/StrategyLanguage/matchProcess.cc',
	'src/StrategyLanguage/subtermProcess.cc',
	'src/StrategyLanguage/rewriteTask.cc',
	'src/StrategyLanguage/subtermTask.cc',
	'src/StrategyLanguage/callTask.cc',
	'src/StrategyLanguage/callProcess.cc',
	'src/StrategyLanguage/strategyStackManager.cc',
	'src/StrategyLanguage/variableBindingsManager.cc',
	'src/StrategyLanguage/oneStrategy.cc',
	'src/StrategyLanguage/oneTask.cc',
	'src/StrategyLanguage/modelCheckerSubtermTask.cc',
	'src/StrategyLanguage/biasedSubtermTask.cc',
	'src/StrategyLanguage/fullSubtermTask.cc',
]

strategylanguage = static_library('strategylanguage', strategylanguage_source, include_directories: strategylanguage_includes)

# Temporal

temporal_includes = include_directories(
	'src/Temporal',
	'src/Utility',
)

temporal_source = [
	'src/Temporal/logicFormula.cc',
	'src/Temporal/buchiAutomaton2.cc',
	'src/Temporal/transitionSet.cc',
	'src/Temporal/veryWeakAlternatingAutomaton.cc',
	'src/Temporal/rawTransitionSet.cc',
	'src/Temporal/genBuchiAutomaton.cc',
	'src/Temporal/modelChecker2.cc',
]

temporal = static_library('temporal', temporal_source, include_directories: temporal_includes)

# Utility

utility_includes = include_directories(
	'src/Utility',
)

utility_source = [
	'src/Utility/macros.cc',
	'src/Utility/preVector.cc',
	'src/Utility/intSet.cc',
	'src/Utility/pointerSet.cc',
	'src/Utility/stringTable.cc',
	'src/Utility/graph.cc',
	'src/Utility/digraph.cc',
	'src/Utility/unionFind.cc',
	'src/Utility/diophantineSystem.cc',
	'src/Utility/natSet.cc',
	'src/Utility/pointerMap.cc',
	'src/Utility/sequencePartition.cc',
	'src/Utility/indent.cc',
	'src/Utility/binBuf.cc',
	'src/Utility/decBuf.cc',
	'src/Utility/bddUser.cc',
	'src/Utility/tty.cc',
	'src/Utility/bdd.cc',
	'src/Utility/timer.cc',
	'src/Utility/mpzSystem.cc',
	'src/Utility/intSystem.cc',
	'src/Utility/allSat.cc',
	'src/Utility/sequenceAssignment.cc',
	'src/Utility/pigPug.cc',
	'src/Utility/wordLevel.cc',
	'src/Utility/wordSystem.cc',
	'src/Utility/rope.cc',
	'src/Utility/variableConstraint.cc',
]

utility = static_library('utility', utility_source, include_directories: utility_includes)

# Mixfix

mixfix_includes = include_directories(
	'src/Mixfix',
	'src/Utility',
	'src/Temporal',
	'src/Interface',
	'src/Core',
	'src/Variable',
	'src/FullCompiler',
	'src/Higher',
	'src/CUI_Theory',
	'src/S_Theory',
	'src/NA_Theory',
	'src/FreeTheory',
	'src/ObjectSystem',
	'src/Mixfix',
	'src/BuiltIn',
	'src/Parser',
	'src/IO_Stuff',
	'src/ACU_Persistent',
	'src/ACU_Theory',
	'src/AU_Persistent',
	'src/AU_Theory',
	'src/Meta',
	'src/FullCompiler',
	'src/StrategyLanguage',
	'src/SMT',
)

mixfix_source = [
	'src/Mixfix/parameterDatabase.cc',
	'src/Mixfix/syntaxContainer.cc',
	'src/Mixfix/renaming.cc',
	'src/Mixfix/view.cc',
	'src/Mixfix/syntacticView.cc',
	'src/Mixfix/entity.cc',
	'src/Mixfix/moduleCache.cc',
	'src/Mixfix/moduleExpression.cc',
	'src/Mixfix/viewExpression.cc',
	'src/Mixfix/viewCache.cc',
	'src/Mixfix/enclosingObject.cc',
	'src/Mixfix/importModule.cc',
	'src/Mixfix/importTranslation.cc',
	'src/Mixfix/strategyTranslation.cc',
	'src/Mixfix/fileTable.cc',
	'src/Mixfix/loopSymbol.cc',
	'src/Mixfix/quotedIdentifierSymbol.cc',
	'src/Mixfix/quotedIdentifierDagNode.cc',
	'src/Mixfix/quotedIdentifierTerm.cc',
	'src/Mixfix/quotedIdentifierOpSymbol.cc',
	'src/Mixfix/mixfixModule.cc',
	'src/Mixfix/token.cc',
	'src/Mixfix/global.cc',
	'src/Mixfix/userLevelRewritingContext.cc',
	'src/Mixfix/preModule.cc',
	'src/Mixfix/syntacticPreModule.cc',
	'src/Mixfix/symbolType.cc',
	'src/Mixfix/xmlBuffer.cc',
	'src/Mixfix/maudemlBuffer.cc',
	'src/Mixfix/interpreter.cc',
	'src/Mixfix/moduleDatabase.cc',
	'src/Mixfix/viewDatabase.cc',
	'src/Mixfix/profileModule.cc',
	'src/Mixfix/mixfixParser.cc',
	'src/Mixfix/visibleModule.cc',
	'src/Mixfix/sharedTokens.cc',
	'src/Mixfix/metadataStore.cc',
	'src/Mixfix/printAttribute.cc',
	'src/Mixfix/banner.cc',
	'src/Mixfix/freshVariableSource.cc',
	'src/Mixfix/variableGenerator.cc',
	'src/Mixfix/objectConstructorSymbol.cc',
]

surfaceyy = custom_target('surfaceyy',
	input: ['src/Mixfix/top.yy', 'src/Mixfix/modules.yy', 'src/Mixfix/commands.yy', 'src/Mixfix/bottom.yy'],
	output: 'surface.yy',
	capture: true,
	command: [cat, '@INPUT@']
)

surfacec = custom_target('surfacec',
	input: surfaceyy,
	output: 'surface.c',
	command: [bison, '-dv', '@INPUT@', '-o', '@OUTPUT@']
)

surfacecc = custom_target('surfacecc',
	input: surfacec,
	output: 'surface.cc',
	command: [cp, '@INPUT@', '@OUTPUT@']
)

lexer = custom_target('lexer',
	input: 'src/Mixfix/lexer.ll',
	depends: surfacec,
	output: '@BASENAME@.cc',
	command: [flex, '-p', '-p', '-o', '@OUTPUT@', '@INPUT@'],
)

tokenizer = custom_target('tokenizer',
	input: 'src/Mixfix/tokenizer.ll',
	output: '@BASENAME@.cc',
	command: [flex, '-Pzz', '-p', '-p', '-o', '@OUTPUT@', '@INPUT@']
)

deserializer = custom_target('deserializer',
	input: 'src/Mixfix/deserializer.ll',
	output: '@BASENAME@.cc',
	command: [flex, '-Pxx', '-p', '-p', '-o', '@OUTPUT@', '@INPUT@']
)

mixfix_generators = [
	surfacecc,
	lexer,
	tokenizer,
	deserializer
]

mixfix = static_library('mixfix', mixfix_source, mixfix_generators, include_directories: mixfix_includes)

# Higher

higher_includes = include_directories(
	'src/Higher',
	'src/Utility',
	'src/Interface',
	'src/Core',
	'src/Variable',
	'src/FullCompiler',
	'src/Temporal',
	'src/FreeTheory',
	'src/NA_Theory',
	'src/BuiltIn',
	'src/Mixfix',
	'src/StrategyLanguage',
	'src/S_Theory',
)

higher_source = [
	'src/Higher/rewriteSearchState.cc',
	'src/Higher/matchSearchState.cc',
	'src/Higher/positionState.cc',
	'src/Higher/pattern.cc',
	'src/Higher/searchState.cc',
	'src/Higher/rewriteSequenceSearch.cc',
	'src/Higher/strategySequenceSearch.cc',
	'src/Higher/modelCheckerSymbol.cc',
	'src/Higher/stateTransitionGraph.cc',
	'src/Higher/rewriteConditionFragment.cc',
	'src/Higher/assignmentConditionFragment.cc',
	'src/Higher/sortTestConditionFragment.cc',
	'src/Higher/equalityConditionFragment.cc',
	'src/Higher/assignmentConditionState.cc',
	'src/Higher/rewriteConditionState.cc',
	'src/Higher/temporalSymbol.cc',
	'src/Higher/satSolverSymbol.cc',
	'src/Higher/unificationProblem.cc',
	'src/Higher/narrowingSearchState.cc',
	'src/Higher/narrowingUnificationProblem.cc',
	'src/Higher/narrowingSequenceSearch.cc',
	'src/Higher/unifierFilter.cc',
	'src/Higher/variantNarrowingSearchState.cc',
	'src/Higher/variantFolder.cc',
	'src/Higher/variantSearch.cc',
	'src/Higher/variantUnificationProblem.cc',
	'src/Higher/narrowingSearchState2.cc',
	'src/Higher/narrowingFolder.cc',
	'src/Higher/narrowingSearchState3.cc',
	'src/Higher/narrowingSequenceSearch3.cc',
	'src/Higher/irredundantUnificationProblem.cc',
	'src/Higher/variantUnifierFilter.cc',
	'src/Higher/filteredVariantUnifierSearch.cc',
	'src/Higher/variantMatchingProblem.cc',
	'src/Higher/strategyModelCheckerSymbol.cc',
	'src/Higher/strategyTransitionGraph.cc',
	'src/Higher/specialHubSymbol.cc',
]

higher = static_library('higher', higher_source, include_directories: higher_includes)

# ACU_Theory

acuTheory_includes = include_directories(
	'src/ACU_Theory',
	'src/Utility',
	'src/Interface',
	'src/Core',
	'src/Variable',
	'src/ACU_Persistent',
	'src/FullCompiler',
)

acuTheory_source = [
	'src/ACU_Theory/ACU_Symbol.cc',
	'src/ACU_Theory/ACU_Term.cc',
	'src/ACU_Theory/ACU_BaseDagNode.cc',
	'src/ACU_Theory/ACU_DagNode.cc',
	'src/ACU_Theory/ACU_TreeDagNode.cc',
	'src/ACU_Theory/ACU_RhsAutomaton.cc',
	'src/ACU_Theory/ACU_LhsAutomaton.cc',
	'src/ACU_Theory/ACU_Subproblem.cc',
	'src/ACU_Theory/ACU_ExtensionInfo.cc',
	'src/ACU_Theory/ACU_CollectorLhsAutomaton.cc',
	'src/ACU_Theory/ACU_NGA_LhsAutomaton.cc',
	'src/ACU_Theory/ACU_VarLhsAutomaton.cc',
	'src/ACU_Theory/ACU_GndLhsAutomaton.cc',
	'src/ACU_Theory/ACU_NonLinearLhsAutomaton.cc',
	'src/ACU_Theory/ACU_ArgumentIterator.cc',
	'src/ACU_Theory/ACU_DagArgumentIterator.cc',
	'src/ACU_Theory/ACU_TreeDagArgumentIterator.cc',
	'src/ACU_Theory/ACU_LazySubproblem.cc',
	'src/ACU_Theory/ACU_UnificationSubproblem2.cc',
	'src/ACU_Theory/ACU_BndVarLhsAutomaton.cc',
]

acuTheory = static_library('acuTheory', acuTheory_source, include_directories: acuTheory_includes)

# Interface

interface_includes = include_directories(
	'src/Interface',
	'src/Utility',
	'src/Core',
	'src/Variable',
	'src/FullCompiler',
)

interface_source = [
	'src/Interface/symbol.cc',
	'src/Interface/binarySymbol.cc',
	'src/Interface/associativeSymbol.cc',
	'src/Interface/term.cc',
	'src/Interface/dagNode.cc',
	'src/Interface/regularInstruction.cc',
	'src/Interface/nonFinalInstruction.cc',
	'src/Interface/nonFinalExtor.cc',
]

interface = static_library('interface', interface_source, include_directories: interface_includes)

# Variable

variable_includes = include_directories(
	'src/Variable',
	'src/Utility',
	'src/Interface',
	'src/Core',
	'src/FullCompiler',
)

variable_source = [
	'src/Variable/variableSymbol.cc',
	'src/Variable/variableTerm.cc',
	'src/Variable/variableDagNode.cc',
	'src/Variable/variableLhsAutomaton.cc',
]

variable = static_library('variable', variable_source, include_directories: variable_includes)

# NA_Theory

naTheory_includes = include_directories(
	'src/NA_Theory',
	'src/Utility',
	'src/Interface',
	'src/Core',
	'src/Variable',
	'src/FullCompiler',
)

naTheory_source = [
	'src/NA_Theory/NA_Symbol.cc',
	'src/NA_Theory/NA_Term.cc',
	'src/NA_Theory/NA_DagNode.cc',
	'src/NA_Theory/NA_LhsAutomaton.cc',
	'src/NA_Theory/NA_RhsAutomaton.cc',
]

naTheory = static_library('naTheory', naTheory_source, include_directories: naTheory_includes)

# FullCompiler

fullcompiler_includes = include_directories(
	'src/FullCompiler',
	'src/Utility',
	'src/Interface',
	'src/Core',
	'src/FullCompiler',
)

fullcompiler_source = [
	'src/FullCompiler/compilationContext.cc',
]

if get_option('enable-compiler')
	fullcompiler = static_library('fullcompiler', [], include_directories: fullcompiler_includes)
endif


# FreeTheory

freetheory_includes = include_directories(
	'src/FreeTheory',
	'src/Utility',
	'src/Interface',
	'src/Core',
	'src/Variable',
	'src/FullCompiler',
)

freetheory_source = [
	'src/FreeTheory/freeSymbol.cc',
	'src/FreeTheory/freeUnarySymbol.cc',
	'src/FreeTheory/freeNullarySymbol.cc',
	'src/FreeTheory/freeBinarySymbol.cc',
	'src/FreeTheory/freeTernarySymbol.cc',
	'src/FreeTheory/freeTerm.cc',
	'src/FreeTheory/freeArgumentIterator.cc',
	'src/FreeTheory/freeDagNode.cc',
	'src/FreeTheory/freeDagArgumentIterator.cc',
	'src/FreeTheory/freeLhsAutomaton.cc',
	'src/FreeTheory/freeRhsAutomaton.cc',
	'src/FreeTheory/freeNet.cc',
	'src/FreeTheory/freePreNet.cc',
	'src/FreeTheory/freeRemainder.cc',
	'src/FreeTheory/freePositionTable.cc',
	'src/FreeTheory/freeInstruction.cc',
	'src/FreeTheory/freeFastInstruction.cc',
	'src/FreeTheory/freeGeneralCtor.cc',
	'src/FreeTheory/freeGeneralCtorFinal.cc',
	'src/FreeTheory/freeGeneralExtor.cc',
	'src/FreeTheory/freeGeneralExtorFinal.cc',
	'src/FreeTheory/freeFast3RhsAutomaton.cc',
	'src/FreeTheory/freeFast2RhsAutomaton.cc',
	'src/FreeTheory/freeNullaryRhsAutomaton.cc',
	'src/FreeTheory/freeUnaryRhsAutomaton.cc',
	'src/FreeTheory/freeBinaryRhsAutomaton.cc',
	'src/FreeTheory/freeTernaryRhsAutomaton.cc',
]

freetheory = static_library('freetheory', freetheory_source, include_directories: freetheory_includes)

# CUI_Theory

cuiTheory_includes = include_directories(
	'src/CUI_Theory',
	'src/Utility',
	'src/Interface',
	'src/Core',
	'src/Variable',
	'src/FullCompiler',
)

cuiTheory_source = [
	'src/CUI_Theory/CUI_Symbol.cc',
	'src/CUI_Theory/CUI_DagNode.cc',
	'src/CUI_Theory/CUI_DagArgumentIterator.cc',
	'src/CUI_Theory/CUI_RhsAutomaton.cc',
	'src/CUI_Theory/CUI_Term.cc',
	'src/CUI_Theory/CUI_ArgumentIterator.cc',
	'src/CUI_Theory/CUI_UnificationSubproblem.cc',
	'src/CUI_Theory/CUI_UnificationSubproblem2.cc',
	'src/CUI_Theory/CUI_LhsAutomaton.cc',
]

cuiTheory = static_library('cuiTheory', cuiTheory_source, include_directories: cuiTheory_includes)

# S_Theory

sTheory_includes = include_directories(
	'src/S_Theory',
	'src/Utility',
	'src/Interface',
	'src/Core',
	'src/Variable',
	'src/FullCompiler',
)

sTheory_source = [
	'src/S_Theory/S_Symbol.cc',
	'src/S_Theory/S_DagNode.cc',
	'src/S_Theory/S_Term.cc',
	'src/S_Theory/S_ExtensionInfo.cc',
	'src/S_Theory/S_DagArgumentIterator.cc',
	'src/S_Theory/S_ArgumentIterator.cc',
	'src/S_Theory/S_LhsAutomaton.cc',
	'src/S_Theory/S_RhsAutomaton.cc',
	'src/S_Theory/S_Subproblem.cc',
]

sTheory = static_library('sTheory', sTheory_source, include_directories: sTheory_includes)

# IO_Stuff

ioStuff_includes = include_directories(
	'src/IO_Stuff',
	'src/Utility',
)

ioStuff_source = [
	'src/IO_Stuff/IO_Manager.cc',
	'src/IO_Stuff/autoWrapBuffer.cc',
	'src/IO_Stuff/directoryManager.cc',
]

ioStuff = static_library('ioStuff', ioStuff_source, include_directories: ioStuff_includes,
			 cpp_args: '-DLIBRARY_BUILD=_LB_LIBRARY')

# ObjectSystem

objectsystem_includes = include_directories(
	'src/ObjectSystem',
	'src/Utility',
	'src/Interface',
	'src/Core',
	'src/Variable',
	'src/FullCompiler',
	'src/ACU_Persistent',
	'src/ACU_Theory',
	'src/AU_Persistent',
	'src/AU_Theory',
	'src/FreeTheory',
	'src/NA_Theory',
	'src/S_Theory',
	'src/BuiltIn',
)

objectsystem_source = [
	'src/ObjectSystem/configSymbol.cc',
	'src/ObjectSystem/objectSystemRewritingContext.cc',
	'src/ObjectSystem/externalObjectManagerSymbol.cc',
	'src/ObjectSystem/socketManagerSymbol.cc',
	'src/ObjectSystem/pseudoThread.cc',
	'src/ObjectSystem/fileManagerSymbol.cc',
	'src/ObjectSystem/streamManagerSymbol.cc',
	'src/ObjectSystem/processManagerSymbol.cc',
	'src/ObjectSystem/timeManagerSymbol.cc',
	'src/ObjectSystem/directoryManagerSymbol.cc',
]

objectsystem = static_library('objectsystem', objectsystem_source, include_directories: objectsystem_includes)

# Core

core_includes = include_directories(
	'src/Core',
	'src/Utility',
	'src/Interface',
	'src/Variable',
	'src/FullCompiler',
	'src/StrategyLanguage',
)

core_source = [
	'src/Core/memoryCell.cc',
	'src/Core/rhsBuilder.cc',
	'src/Core/termBag.cc',
	'src/Core/bindingLhsAutomaton.cc',
	'src/Core/trivialRhsAutomaton.cc',
	'src/Core/copyRhsAutomaton.cc',
	'src/Core/variableInfo.cc',
	'src/Core/narrowingVariableInfo.cc',
	'src/Core/termSet.cc',
	'src/Core/strategy.cc',
	'src/Core/sortTable.cc',
	'src/Core/sortConstraintTable.cc',
	'src/Core/equationTable.cc',
	'src/Core/ruleTable.cc',
	'src/Core/sort.cc',
	'src/Core/connectedComponent.cc',
	'src/Core/module.cc',
	'src/Core/substitution.cc',
	'src/Core/localBinding.cc',
	'src/Core/subproblemSequence.cc',
	'src/Core/subproblemDisjunction.cc',
	'src/Core/sortCheckSubproblem.cc',
	'src/Core/disjunctiveSubproblemAccumulator.cc',
	'src/Core/preEquation.cc',
	'src/Core/equation.cc',
	'src/Core/rule.cc',
	'src/Core/sortConstraint.cc',
	'src/Core/rewritingContext.cc',
	'src/Core/variableAbstractionSubproblem.cc',
	'src/Core/equalitySubproblem.cc',
	'src/Core/dagRoot.cc',
	'src/Core/cachedDag.cc',
	'src/Core/extensionMatchSubproblem.cc',
	'src/Core/dagNodeSet.cc',
	'src/Core/hashConsSet.cc',
	'src/Core/memoTable.cc',
	'src/Core/memoMap.cc',
	'src/Core/rootContainer.cc',
	'src/Core/sortBdds.cc',
	'src/Core/unificationContext.cc',
	'src/Core/protectedDagNodeSet.cc',
	'src/Core/pendingUnificationStack.cc',
	'src/Core/unificationSubproblemDisjunction.cc',
	'src/Core/compoundCycleSubproblem.cc',
	'src/Core/stackMachine.cc',
	'src/Core/stackMachineRhsCompiler.cc',
	'src/Core/returnInstruction.cc',
	'src/Core/nullInstruction.cc',
	'src/Core/rewriteStrategy.cc',
	'src/Core/strategyDefinition.cc',
]

core = static_library('core', core_source, include_directories: core_includes)

# AU_Persistent

auPersistent_includes = include_directories(
	'src/AU_Persistent',
	'src/Utility',
	'src/Interface',
	'src/Core',
	'src/Variable',
	'src/FullCompiler',
)

auPersistent_source = [
	'src/AU_Persistent/AU_StackNode.cc',
	'src/AU_Persistent/AU_Deque.cc',
	'src/AU_Persistent/AU_DequeIter.cc',
]

auPersistent = static_library('auPersistent', auPersistent_source, include_directories: auPersistent_includes)

# Meta

meta_includes = include_directories(
	'src/Meta',
	'src/Utility',
	'src/Interface',
	'src/Core',
	'src/Variable',
	'src/FullCompiler',
	'src/Higher',
	'src/AU_Theory',
	'src/CUI_Theory',
	'src/S_Theory',
	'src/NA_Theory',
	'src/FreeTheory',
	'src/ObjectSystem',
	'src/Mixfix',
	'src/BuiltIn',
	'src/IO_Stuff',
	'src/StrategyLanguage',
	'src/SMT',
	'src/Parser',
)

meta_source = [
	'src/Meta/metaModuleCache.cc',
	'src/Meta/metaLevel.cc',
	'src/Meta/interpreterManagerSymbol.cc',
	'src/Meta/metaOpCache.cc',
	'src/Meta/metaModule.cc',
	'src/Meta/metaLevelOpSymbol.cc',
	'src/Meta/metaPreModule.cc',
	'src/Meta/metaView.cc',
]

meta = static_library('meta', meta_source, include_directories: meta_includes)

# AU_Theory

auTheory_includes = include_directories(
	'src/AU_Theory',
	'src/Utility',
	'src/Interface',
	'src/Core',
	'src/Variable',
	'src/AU_Persistent',
	'src/FullCompiler',
)

auTheory_source = [
	'src/AU_Theory/AU_Symbol.cc',
	'src/AU_Theory/AU_DagNode.cc',
	'src/AU_Theory/AU_DequeDagNode.cc',
	'src/AU_Theory/AU_Term.cc',
	'src/AU_Theory/AU_DagArgumentIterator.cc',
	'src/AU_Theory/AU_DequeDagArgumentIterator.cc',
	'src/AU_Theory/AU_ExtensionInfo.cc',
	'src/AU_Theory/AU_RhsAutomaton.cc',
	'src/AU_Theory/AU_LhsAutomaton.cc',
	'src/AU_Theory/AU_ArgumentIterator.cc',
	'src/AU_Theory/AU_Layer.cc',
	'src/AU_Theory/AU_Subproblem.cc',
	'src/AU_Theory/AU_UnificationSubproblem2.cc',
]

auTheory = static_library('auTheory', auTheory_source, include_directories: auTheory_includes)

# SMT

smt_includes = include_directories(
	'src/SMT',
	'src/Utility',
	'src/Interface',
	'src/Core',
	'src/Variable',
	'src/Higher',
	'src/FullCompiler',
	'src/NA_Theory',
	'src/FreeTheory',
	'src/BuiltIn',
	'src/Mixfix',
	'src/StrategyLanguage',
)

smt_source = [
	'src/SMT/SMT_Symbol.cc',
	'src/SMT/SMT_NumberSymbol.cc',
	'src/SMT/SMT_NumberDagNode.cc',
	'src/SMT/SMT_NumberTerm.cc',
	'src/SMT/SMT_RewriteSearchState.cc',
	'src/SMT/SMT_RewriteSequenceSearch.cc',
	'src/SMT/SMT_Info.cc',
	'src/SMT/folder.cc',
	'src/SMT/smtStateTransitionGraph.cc',
	'src/SMT/rewriteSmtSearchState.cc',
	'src/SMT/rewriteSmtSequenceSearch.cc',
]

smt = static_library('smt', smt_source, include_directories: smt_includes)

# Main

main_includes = include_directories(
	'src/Main',
	'src/Utility',
	'src/Temporal',
	'src/Interface',
	'src/Core',
	'src/Variable',
	'src/FullCompiler',
	'src/Higher',
	'src/CUI_Theory',
	'src/S_Theory',
	'src/NA_Theory',
	'src/FreeTheory',
	'src/ObjectSystem',
	'src/Mixfix',
	'src/BuiltIn',
	'src/SMT',
	'src/IO_Stuff',
	'src/ACU_Persistent',
	'src/ACU_Theory',
	'src/AU_Persistent',
	'src/AU_Theory',
	'src/Meta',
	'src/FullCompiler',
	'src/StrategyLanguage',
	'src/Mixfix',
)

main_source = [
	'src/Main/main.cc',
]

main = static_library('main', main_source, include_directories: main_includes)

# ACU_Persistent

acuPersistent_includes = include_directories(
	'src/ACU_Persistent',
	'src/Utility',
	'src/Interface',
	'src/Core',
	'src/Variable',
	'src/FullCompiler',
)

acuPersistent_source = [
	'src/ACU_Persistent/ACU_RedBlackNode.cc',
	'src/ACU_Persistent/ACU_Tree.cc',
]

acuPersistent = static_library('acuPersistent', acuPersistent_source, include_directories: acuPersistent_includes)

# BuiltIn

builtin_includes = include_directories(
	'src/BuiltIn',
	'src/Utility',
	'src/Interface',
	'src/Core',
	'src/Variable',
	'src/FullCompiler',
	'src/NA_Theory',
	'src/ACU_Persistent',
	'src/ACU_Theory',
	'src/CUI_Theory',
	'src/S_Theory',
	'src/FreeTheory',
)

builtin_source = [
	'src/BuiltIn/equalitySymbol.cc',
	'src/BuiltIn/sortTestSymbol.cc',
	'src/BuiltIn/branchSymbol.cc',
	'src/BuiltIn/stringSymbol.cc',
	'src/BuiltIn/stringTerm.cc',
	'src/BuiltIn/stringDagNode.cc',
	'src/BuiltIn/stringOpSymbol.cc',
	'src/BuiltIn/floatSymbol.cc',
	'src/BuiltIn/floatTerm.cc',
	'src/BuiltIn/floatDagNode.cc',
	'src/BuiltIn/floatOpSymbol.cc',
	'src/BuiltIn/succSymbol.cc',
	'src/BuiltIn/numberOpSymbol.cc',
	'src/BuiltIn/minusSymbol.cc',
	'src/BuiltIn/ACU_NumberOpSymbol.cc',
	'src/BuiltIn/CUI_NumberOpSymbol.cc',
	'src/BuiltIn/divisionSymbol.cc',
	'src/BuiltIn/randomOpSymbol.cc',
	'src/BuiltIn/counterSymbol.cc',
	'src/BuiltIn/matrixOpSymbol.cc',
	'src/BuiltIn/equalityExtor.cc',
	'src/BuiltIn/equalityExtorFinal.cc',
]

builtin = static_library('builtin', builtin_source, include_directories: builtin_includes)

#
## Final outcomes
#

maudeSubdirs = [
	higher,
	ioStuff,
	core,
	meta,
]

maudeSubsdirsInternal = [
	parser,
	temporal,
	acuTheory,
	variable,
	naTheory,
	freetheory,
	cuiTheory,
	sTheory,
	auPersistent,
	auTheory,
	acuPersistent,
	main,
	builtin,
	objectsystem,
	strategylanguage,
	utility,
	mixfix,
	interface,
	smt,
]

if get_option('enable-compiler')
	maudeSubdirsInternal += [fullCompiler]
endif

#
## Maude as a library

libmaude = shared_library('maude',
	link_whole: maudeSubdirs,
	link_with: maudeSubsdirsInternal,
	dependencies: libraries,
	install: true
)

libmaude_includes = include_directories(
	'src/BuiltIn',
	'src/Core',
	'src/FreeTheory',
	'src/FullCompiler',
	'src/Higher',
	'src/Interface',
	'src/IO_Stuff',
	'src/Meta',
	'src/Mixfix',
	'src/NA_Theory',
	'src/ObjectSystem',
	'src/Parser',
	'src/SMT',
	'src/S_Theory',
	'src/StrategyLanguage',
	'src/Temporal',
	'src/Utility',
	'src/Variable',
	'ltsmod',
)

libmaude_dep = declare_dependency(
	include_directories: libmaude_includes,
	link_with: libmaude
)

# Sets the RPATH so that maude can find libmaude in the same directory
if target_machine.system() == 'darwin'
	rpath_value = '@loader_path'
else
	rpath_value = '$ORIGIN'
endif

#
## The Maude interpreter using the library
#
# IO_Manager is compiled again with the _LB_EXCUTABLE flag to
# replace the default input functions with those using GNU
# readline, which should not be included in the library.

executable('maude',
	'src/IO_Stuff/IO_Manager.cc',
	include_directories: ioStuff_includes,
	link_with: main,
	dependencies: [libmaude_dep, readline],
	cpp_args: '-DLIBRARY_BUILD=_LB_EXECUTABLE',
	install: true,
	install_rpath: rpath_value
)

install_data(
	'src/Main/file.maude',
	'src/Main/linear.maude',
	'src/Main/machine-int.maude',
	'src/Main/metaInterpreter.maude',
	'src/Main/model-checker.maude',
	'src/Main/prelude.maude',
	'src/Main/process.maude',
	'src/Main/smt.maude',
	'src/Main/socket.maude',
	'src/Main/term-order.maude',
	'src/Main/time.maude',
)

#
## The model-checking plugin for LTSmin

if get_option('with-ltsmin').enabled()

	cxx.has_header('ltsmin/pins.h', args: extraIncludeArgs, required: true)
	dependency('popt', static: 'popt' in staticLibs)

	shared_module('maudemc',
		'ltsmod/maudemc.cc',
		dependencies: libmaude_dep,
		include_directories: include_directories('ltsmod'),
		override_options: ['cpp_std=c++17'],
		install_rpath: rpath_value,
		install: true
	)
endif

#
## The simulator tool

if get_option('with-simaude').enabled()
	popt = dependency('popt', static: 'popt' in staticLibs)

	simaude_source = [
		'simaude/simaude.cc',
		'simaude/strategicSimulation.cc',
		'simaude/maudeStuff.cc',
	]

	simaude_dependencies = [
		libmaude_dep,
		popt
	]

	if host_machine.system() == 'linux'
		dl = cxx.find_library('dl')
		simaude_dependencies += [dl]
	endif

	executable('simaude',
		simaude_source,
		dependencies: simaude_dependencies,
		override_options: ['cpp_std=c++17'],
		install_rpath: rpath_value,
		install: true
	)

endif
