%newobject dag2term;
%newobject term2dag;

EasyTerm* dag2term(PyObject* capsuleObj);
PyObject* term2dag(EasyTerm* term);

//
//	Interface to Maude terms and operations
//

%{
#include "rewriteSmtSequenceSearch.hh"
%}


/**
 * An iterator through the solutions of a search.
 */
class RewriteSmtSequenceSearch {
public:
	RewriteSmtSequenceSearch() = delete;

	%newobject getSubstitution;
	%newobject getStateTerm;
	%newobject __next;

	%extend {
		/**
		 * Get the number of rewrites until this term has been found.
		 */
		int getRewriteCount() {
			return $self->getContext()->getTotalCount();
		}

		/**
		 * Get the matching substitution of the solution into the pattern.
		 */
		EasySubstitution* getSubstitution() {
			return new EasySubstitution($self->getSubstitution(),
						    $self->getGoal(),
						    nullptr);
		}

		/**
		 * Get the rule leading to the given state.
		 * 
		 * @param stateNr The number of a state in the search graph
		 * or -1 for the current one.
		 */
		Rule* getRule(int stateNr = -1) {
			return $self->getStateRule(stateNr == -1
				? $self->getStateNr() : stateNr);
		}

		/**
		 * Get the term of a given state.
		 * 
		 * @param stateNr The number of a state in the search graph.
		 */
		EasyTerm* getStateTerm(int stateNr) {
			return new EasyTerm($self->getStateDag(stateNr));
		}


		/**
		 * Get the next match.
		 *
		 * @return A term or a null pointer if there is no more matches.
		 */
		EasyTerm* __next() {
			bool hasNext = $self->findNextMatch();
			return hasNext ? new EasyTerm($self->getStateDag($self->getStateNr())) : nullptr;
		}
	}

	/**
	 * Get an internal state number that allows reconstructing 
	 * the path to this term.
	 */
	int getStateNr() const;

	/**
	 * Get the parent state.
	 *
	 * @param stateNr The number of a state in the search graph.
	 *
	 * @return The number of the parent or -1 for the root.
	 */
	int getStateParent(int stateNr) const;

	%unprotectDestructor(RewriteSmtSequenceSearch);
};