/*   Author: Robert Staerk <staerk@math.stanford.edu> */
/*  Created: 8/11/95, 2:13 PM */
/* Updated: Sat Dec 26 15:12:10 1998 */
/* Filename: bi.pl */
/* Abstract: Built-in predicates. Library predicates. */

%%d bi__predicate(gr::out,int::out)

bi__predicate(atom,1).				% atom/1
bi__predicate(integer,1).			% integer/1
bi__predicate(atomic,1).			% atomic/1
bi__predicate(is,2).				% is/2
bi__predicate(<,2).				% </2
bi__predicate(=<,2).				% =</2
bi__predicate(current_op,3).			% current_op/3
bi__predicate(once,1).				% once/1
bi__predicate(call,_).				% call/n+1

%%d bi__arithmetic_constructor(gr::in)

bi__arithmetic_constructor(+,2).
bi__arithmetic_constructor(-,2).
bi__arithmetic_constructor(*,2).
bi__arithmetic_constructor(/,2).
bi__arithmetic_constructor(Name,0) :- integer(Name).

%%d bi__typed(atm::in)

bi__typed([n(atom,1),Term]) :-			% atom/1
	bi__ground(Term).
bi__typed([n(integer,1),Term]) :-		% integer/1
	bi__ground(Term).
bi__typed([n(atomic,1),Term]) :-		% atomic/1
	bi__ground(Term).
bi__typed([n(is,2),_,Term]) :-			% is/2
	bi__ground_arithmetic(Term).
bi__typed([n(<,2),Term1,Term2]) :-		% </2
	bi__ground_arithmetic(Term1),
	bi__ground_arithmetic(Term2).
bi__typed([n(=<,2),Term1,Term2]) :-		% =</2
	bi__ground_arithmetic(Term1),
	bi__ground_arithmetic(Term2).
bi__typed([n(current_op,3),_,_,[n(_,0)]]).	% current_op/3
bi__typed([n(once,1),Term]) :-			% once/1
	bi__ground(Term).
bi__typed([n(call,_),[n(_,0)]|_]).		% call/n+1

%%d bi__eval(atm::in,goal::out)

bi__eval([n(atom,1),Term],Goal) :-		% atom/1
	(	Term = [n(Name,0)],
		atom(Name) ->
		Goal = [&]
	;	Goal = [\/]
	).
bi__eval([n(integer,1),Term],Goal) :-		% integer/1
	(	Term = [n(Name,0)],
		integer(Name) ->
		Goal = [&]
	;	Goal = [\/]
	).
bi__eval([n(atomic,1),Term],Goal) :-		% atomic/1
	(	Term = [n(Name,0)],
		atomic(Name) ->
		Goal = [&]
	;	Goal = [\/]
	).
bi__eval([n(is,2),Term1,Term2],Goal) :-		% is/2
	bi__eval_arithm(Term2,Name),
	Goal = [=,Term1,[n(Name,0)]].
bi__eval([n(<,2),Term1,Term2],Goal) :-		% </2
	(	bi__eval_arithm(Term1,N1),
	 	bi__eval_arithm(Term2,N2),
	 	N1 < N2 ->
		Goal = [&]
	;	Goal = [\/]
	).
bi__eval([n(=<,2),Term1,Term2],Goal) :-		% </2
	(	bi__eval_arithm(Term1,N1),
	 	bi__eval_arithm(Term2,N2),
	 	N1 =< N2 ->
		Goal = [&]
	;	Goal = [\/]
	).
bi__eval([n(once,1),Term],Term).		% once/1
bi__eval([n(call,N1),[n(Name,0)]|TermL],Goal) :- % call/n+1
	N2 is N1 - 1,
	Goal = [n(Name,N2)|TermL].

%%d bi__ground(tm::in)

bi__ground([_|TermL]) :-
	bi__groundL(TermL).

%%d bi__groundL(tmL::in)

bi__groundL([]).
bi__groundL([Term|TermL]) :-
	bi__ground(Term),
	bi__groundL(TermL).

%%d bi__ground_arithmetic(tm::in)

bi__ground_arithmetic([n(Name,N)|TermL]) :-
	bi__arithmetic_constructor(Name,N),
	bi__ground_arithmeticL(TermL).

%%d bi__ground_arithmeticL(tmL::in)

bi__ground_arithmeticL([]).
bi__ground_arithmeticL([Term|TermL]) :-
	bi__ground_arithmetic(Term),
	bi__ground_arithmeticL(TermL).

%%d bi__eval_arithm(tm::in,gr::out)

bi__eval_arithm([n(+,2),Term1,Term2],N3) :-
	bi__eval_arithm(Term1,N1),
	bi__eval_arithm(Term2,N2),
	N3 is N1 + N2.
bi__eval_arithm([n(*,2),Term1,Term2],N3) :-
	bi__eval_arithm(Term1,N1),
	bi__eval_arithm(Term2,N2),
	N3 is N1 * N2.
bi__eval_arithm([n(-,2),Term1,Term2],N3) :-
	bi__eval_arithm(Term1,N1),
	bi__eval_arithm(Term2,N2),
	N3 is N1 - N2.
bi__eval_arithm([n(/,2),Term1,Term2],N3) :-
	bi__eval_arithm(Term1,N1),
	bi__eval_arithm(Term2,N2),
	N3 is N1 / N2.
bi__eval_arithm([n(N,0)],N) :-
	integer(N).

%%d bi__builtin_atom(atm::gr)

bi__builtin_atom([n(Name,N)|_]) :-
	bi__predicate(Name,N).

%%d bi__user_defined_atom(atm::int)

bi__user_defined_atom([Tag|_]) :-
	db__clauses(Tag,_).


%% Concatenation of lists

% The following predicates are only correct under the assumption that
% list/1 and **/2 have their standard definitions.
%
% Example: The list normal form of [?x|?l1 ** [] ** ?l2] ** (?l3 ** ?l4)
% is [ [?x|?l1],?l2,?l3,?l4 ].

%%d bi__list_form(tm::in)

bi__list_form([n([],0)]).
bi__list_form([n('.',2),_,_]).
bi__list_form([f(**,2),_,_]).

%%d bi__list_nf(tm::in,tmL::in,tmL::out)

bi__list_nf([f(**,2),Term1,Term2],L1,L3) :-
	bi__list_nf(Term2,L1,L2),
	bi__list_nf(Term1,L2,L3).
bi__list_nf([n('.',2),Term1,Term2],L1,L3) :-
	bi__list_nf(Term2,L1,L2),
	bi__list_cons(Term1,L2,L3).
bi__list_nf([n([],0)],L,L).
bi__list_nf(Term,L,[Term|L]) :-
 	\+ bi__list_form(Term).

%%d bi__list_cons(tm::in,tmL::in,tmL::out)

bi__list_cons(Term,[],[[n('.',2),Term,[n([],0)]]]).
bi__list_cons(Term1,[Term2|L],[[n('.',2),Term1,Term2]|L]).

%%d bi__list_definedL(tmL::in,fmlL::in)

bi__list_definedL([],_,_).	% [] = [] ** [] ** []
bi__list_definedL([_],_,_).	% The type of the last element is arbitrary
bi__list_definedL([Term1,Term2|L],V,Gamma) :-
	once(bi__list_defined(Term1,V,Gamma)),
	bi__list_definedL([Term2|L],V,Gamma).

%%d bi__list_defined(tm::in,fmlL::in)

bi__list_defined([n('.',2),_,Term],V,Gamma) :-
	bi__list_defined(Term,V,Gamma).
bi__list_defined(Term,V,Gamma) :-
	pr__derivable_once(V,Gamma,[succeeds,[n(list,1),Term]]).

%%d bi__concatenation(fmlL::in,fml::in)

% Term1 and Term2 have the same normal form.

bi__concatenation(V,Gamma,[=,Term1,Term2]) :-
	bi__list_nf(Term1,[],L),
	bi__list_definedL(L,V,Gamma),
	bi__list_nf(Term2,[],L).

%% Sums of natural numbers

% The following predicates are only correct under the assumption that
% nat/1 and @+/2 have their standard definitions.
%
% Example: The normal form of s(?m @+ s(?n) @+ 0) @+ ?i consists of
% [?m,?n,?i] and s(s(0)).

%%d bi__sum_form(tm::in)

bi__sum_form([n(0,0)]).
bi__sum_form([n(s,1),_]).
bi__sum_form([f(@+,2),_,_]).

%%d bi__sum_nf(tm::in,tmL::in,tmL::out)

bi__sum_nf([n(0,0)],L,L,N,N).
bi__sum_nf([n(s,1),Term],L1,L2,N1,s(N2)) :-
	bi__sum_nf(Term,L1,L2,N1,N2).
bi__sum_nf([f(@+,2),Term1,Term2],L1,L3,N1,N3) :-
	bi__sum_nf(Term2,L1,L2,N1,N2),
	bi__sum_nf(Term1,L2,L3,N2,N3).
bi__sum_nf(Term,L,[Term|L],N,N) :-
	\+ bi__sum_form(Term).

%%d bi__nat_defined(tm::in,varL::in,fmlL::in)

bi__nat_defined(Term,V,Gamma) :-
	pr__derivable_once(V,Gamma,[succeeds,[n(nat,1),Term]]).

bi__nat_definedL([],_,_).
bi__nat_definedL([Term|TermL],V,Gamma) :-
	bi__nat_defined(Term,V,Gamma),
	bi__nat_definedL(TermL,V,Gamma).

%%d bi__addition(varL::in,fmlL::in,fml::in)

bi__addition(V,Gamma,[=,Term1,Term2]) :-
	bi__sum_nf(Term1,[],L1,0,N),
	bi__nat_definedL(L1,V,Gamma),
	bi__sum_nf(Term2,[],L2,0,N),
	lst__permutation(L1,L2).

% bi.pl ends here

