%   Author: Robert F. Staerk <robert.staerk@unifr.ch> 
%  Created: Tue Mar 24 16:10:41 1998 
% Updated: Mon Feb 15 11:35:10 1999
% Filename: dep.pl 
% Abstract: Dependencies between formal proofs (the information flow)

% If the flag `write_dependencies' is set with the command
%
%    :- set(write_dependencies)
%
% then the dependencies between theorems, lemmas, corollaries and
% axioms are written on the `.thm' file.
%
% If the file is later used with the command `:- needs_thm(...)'
% the dependencies are added to the internal database.
%
% We can ask about the dependencies as follows:
%
%    ?- depends(theorem(_)).
%    ?- depends(lemma(_)).
%    ?- depends(corollary(_)).
%    ?- depends(definition_fun(_,_)).
%
% We can ask about unused facts:
%
%    ?- dep__unused(X).


%%d dep__print_dependencies(gr::in)

dep__print_dependencies(Fact) :-
	dep__depends(Fact,L1),
	dep__topological_ordering(L1,[],[],L2),
	io__tell_user,
	dep__print_facts(L2).

%% dep__write_dependencies(gr::in,gr::in,drv::in)

dep__write_fact(Kind,Ref,Deriv) :-
	(	db__flag(write_dependencies),
		db__is_open(thm) ->
		dep__derivation(Deriv,[],L),
		Fact =.. [Kind,Ref],
		io__tell(thm),
		write(':- '),
		writeq(assert(db__depends(Fact,L))),
		write('.'), nl
	;	true
	).

%%d dep__write_assert(gr::in,grL::in)

dep__write_assert(X,L) :-
	(	db__flag(write_dependencies),
		db__is_open(thm) ->
		io__tell(thm),
		write(':- '),
		writeq(assert(db__depends(X,L))),
		write('.'), nl
	;	true
	).

%%d dep__derivation(drv::in,grL::in,grL::out)

dep__derivation([],L,L).
dep__derivation([Step|Deriv],L1,L3) :-
	dep__derivation_step(Step,L1,L2),
	dep__derivation(Deriv,L2,L3).

%%d dep__derivation_step(dstp::in,grL::in,grL::out)

dep__derivation_step(by(_,X),L1,L2) :-
	(	dep__by(X,Y) ->
		lst__add_element(Y,L1,L2)
	;	L2 = L1
	).
dep__derivation_step([_|_],L,L).
dep__derivation_step(@(_,_,_),L,L).
dep__derivation_step(assume(_,Deriv,_),L1,L2) :-
	dep__derivation(Deriv,L1,L2).
dep__derivation_step(cases(CaseL,_),L1,L2) :-
	dep__caseL(CaseL,L1,L2).
dep__derivation_step(exist(_,_,Deriv,_),L1,L2) :-
	dep__derivation(Deriv,L1,L2).
dep__derivation_step(induction(_,StepL),L1,L2) :-
	dep__induction_stepL(StepL,L1,L2).
dep__derivation_step(contra(_,Deriv),L1,L2) :-
	dep__derivation(Deriv,L1,L2).
dep__derivation_step(indirect(_,Deriv),L1,L2) :-
	dep__derivation(Deriv,L1,L2).

%%d dep__caseL(casL::in,grL::in,grL::out)

dep__caseL([],L,L).
dep__caseL([case(_,Deriv)|CaseL],L1,L3) :-
	dep__derivation(Deriv,L1,L2),
	dep__caseL(CaseL,L2,L3).

%%d dep__induction_stepL(istpL::in,grL::in,grL::out)

dep__induction_stepL([],L,L).
dep__induction_stepL([step(_,_,Deriv,_)|StepL],L1,L3) :-
	dep__derivation(Deriv,L1,L2),
	dep__induction_stepL(StepL,L2,L3).

%%d dep_by(gr::in,gr::out)

dep__by(X,X) :- dep__fact_form(X).
dep__by(elimination(Name,N),definition_pred(Name,N)).
dep__by(introduction(Name,N),definition_pred(Name,N)).
dep__by(existence(Name,N),definition_fun(Name,N)).
dep__by(uniqueness(Name,N),definition_fun(Name,N)).

%%d dep__fact_form(any::in)

dep__fact_form(axiom(_)).
dep__fact_form(lemma(_)).
dep__fact_form(theorem(_)).
dep__fact_form(corollary(_)).

%%d dep__topological_ordering(grL::in,grL::in,grL::in,grL::out)

dep__topological_ordering([],_,WF,WF).
dep__topological_ordering([X|L1],Path,WF1,WF3) :-
	(	lst__member_check(X,Path) ->
		ctl__error([there,is,a,cycle,through,X])
	;	lst__member_check(X,WF1) ->
		dep__topological_ordering(L1,Path,WF1,WF3)
	;	dep__depends(X,L2),
		dep__topological_ordering(L2,[X|Path],WF1,WF2),
		dep__topological_ordering(L1,Path,[X|WF2],WF3)
	).

%%d dep__depends(gr::in,grL::out)

dep__depends(X,L) :-
	(	db__depends(X,L) ->
		true
	;	ctl__warning([no,dependencies,for,X]),
		L = []
	).

%%d dep__print_facts(grL::in)

dep__print_facts([]).
dep__print_facts([X|L]) :-
	write(X), nl,
	dep__print_facts(L).

%%d dep__used(gr::in)

dep__used(X) :-
	db__depends(_,L),
	lst__member_check(X,L).

%%d dep_unused(gr::in)

dep__unused(X) :-
	db__depends(X,_),
	\+ dep__used(X).

% dep.pl ends here
