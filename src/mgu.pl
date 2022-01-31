/*   Author: Robert Staerk <staerk@math.stanford.edu> */
/*  Created: Fri Dec  2 15:53:39 1994 */
/* Filename: mgu.pl */
/* Abstract: A union-find based, quadratic unification algorithm. */
%
% The algorithm uses equivalence relations on terms represented as
% lists of classes, called partitions.
%
% %%d mgu__class(gr::in)
% 
% mgu__class(cl(Term,Part)) :-
% 	obj__term(Term),
% 	mgu__partition(Part),
% 	\+ mgu__partition_member(Term,Part),
% 
% %%d mgu__partition(grL::in)
% 
% mgu__partition([]).
% mgu__partition([Class|Part]) :-
% 	mgu__class(Class),
% 	mgu__partition(Part),
% 	mgu__disjoint(Class,Part).
%
% %%d mgu__disjoint(cl::in,ptn::in)
% 
% mgu__disjoint(Class,Part) :- \+ mgu__not_disjoint(Class,Part).
% 
% %%d mgu__not_disjoint(cl::in,ptn::in)
% 
% mgu__not_disjoint(Class,Part) :-
% 	mgu__class_member(Term,Class),
% 	mgu__partition_member(Term,Part).
%
% %%d mgu__result(gr::in)
% 
% mgu__result(yes(Part)) :- mgu__partition(Part).
% mgu__result(no).

%%d mgu__class_member(gr::in,cl::in)

mgu__class_member(Term,cl(Term,_)).
mgu__class_member(Term,cl(_,Part)) :-
	mgu__partition_member(Term,Part).

%%d mgu__partition_member(gr::in,ptn::in)

mgu__partition_member(Term,[Class|_]) :-
	mgu__class_member(Term,Class).
mgu__partition_member(Term,[_|Part]) :-
	mgu__partition_member(Term,Part).

%%d mgu__find(ptn::in,gr::in,tm::out)

mgu__find([],Term,Term).
mgu__find([Class|Part],Term1,Term2) :-
	(	mgu__class_member(Term1,Class) ->
		Class = cl(Term2,_)
	;	mgu__find(Part,Term1,Term2)
	).

%%d mgu__find_delete(ptn::in,tm::in,ptn::out,cl::out)

mgu__find_delete([],Term,[],cl(Term,[])).
mgu__find_delete([Class1|Part1],Term,Part3,Class2) :-
	(	mgu__class_member(Term,Class1) -> 
		Class2 = Class1,
		Part3 = Part1
	;	mgu__find_delete(Part1,Term,Part2,Class2),
		Part3 = [Class1|Part2]
	).

%%d mgu__union_find(tm::in,tm::in,ptn::in,ptn::out)

mgu__union_find(Term1,Term2,Part1,Part4) :-
	mgu__find_delete(Part1,Term1,Part2,Class1),
	(	mgu__class_member(Term2,Class1) -> 
		Part4 = Part1
	;	mgu__find_delete(Part2,Term2,Part3,Class2),
		Class1 = cl(Term3,Q1),
		Class2 = cl(Term4,Q2),
		(	obj__var_form(Term3) ->
			Part4 = [cl(Term4,[Class1|Q2])|Part3]
		;	obj__var_form(Term4) ->
			Part4 = [cl(Term3,[Class2|Q1])|Part3]
		;	Term3 = [Tag|Term1L], 
			Term4 = [Tag|Term2L],
			mgu__union_findL(Term1L,Term2L,
				[cl(Term4,[Class1|Q2])|Part3],Part4)
	    	)
	).

%%d mgu__union_findL(tmL::in,tmL::in,ptn::in,ptn::out)

mgu__union_findL([],[],Part,Part).
mgu__union_findL([Term1|Term1L],[Term2|Term2L],Part1,Part3) :-
	mgu__union_find(Term1,Term2,Part1,Part2),
	mgu__union_findL(Term1L,Term2L,Part2,Part3).

%%d mgu__cycle_free(ptn::in)

mgu__cycle_free(Part) :-
	mgu__roots(Part,TermL),
	mgu__cycle_freeL(TermL,Part,[],[],_).

%%d mgu__roots(ptn::in,tmL::out)

mgu__roots([],[]).
mgu__roots([cl(Term,_)|Part],[Term|TermL]) :-
	mgu__roots(Part,TermL).

%%d mgu__cycle_freeL(tmL::in,ptn::in,tmL::in,tmL::in,tmL::out)

mgu__cycle_freeL([],_,_,TermL,TermL).
mgu__cycle_freeL([Term1|Term1L],Part,Term2L,Term3L,TermL) :-
	mgu__find(Part,Term1,Term2),
	(	lst__member_check(Term2,Term2L) ->
		fail
	;	lst__member_check(Term2,Term3L) ->
		mgu__cycle_freeL(Term1L,Part,Term2L,Term3L,TermL)
	;	obj__var_form(Term2) ->
		mgu__cycle_freeL(Term1L,Part,Term2L,[Term2|Term3L],TermL)
	;	Term2 = [_|Term4L],
		mgu__cycle_freeL(Term4L,Part,[Term2|Term2L],Term3L,Term5L),
		mgu__cycle_freeL(Term1L,Part,Term2L,[Term2|Term5L],TermL)
	).

%%d mgu__unify_terms_part(tm::in,tm::in,ptn::out)

mgu__unify_terms_part(Term1,Term2,Part) :- 
	mgu__union_find(Term1,Term2,[],Part),
	mgu__cycle_free(Part).

%%d mgu__unifiable_terms(tm::in,tm::in)

mgu__unifiable_terms(Term1,Term2) :- mgu__unify_terms_part(Term1,Term2,_).

%%d mgu__unify_terms_sub(tm::in,tm::in,sub::out)

mgu__unify_terms_sub(Term1,Term2,Sub) :-
	mgu__unify_terms_part(Term1,Term2,Part),
	mgu__partition_sub(Part,Part,[],Sub).

%%d mgu__unify_termL_sub(tmL::in,tmL::in,sub::out)

mgu__unify_termL_sub(Term1L,Term2L,Sub) :-
	mgu__union_findL(Term1L,Term2L,[],Part),
	mgu__cycle_free(Part),
	mgu__partition_sub(Part,Part,[],Sub).

%%d mgu__partition_sub(ptn::in,ptn::in,sub::in,sub::out)

mgu__partition_sub([],_,Sub,Sub).
mgu__partition_sub([Class|Part1],Part2,Sub1,Sub3) :-
	mgu__class_sub(Class,Part2,Sub1,Sub2),
	mgu__partition_sub(Part1,Part2,Sub2,Sub3).

%%d mgu__class_sub(cl::in,ptn::in,sub::in,sub::out)

mgu__class_sub(cl($(X),Part1),Part2,Sub1,Sub2) :-
	mgu__partition_term($(X),Part2,Term),
	mgu__partition_sub(Part1,Part2,[X => Term|Sub1],Sub2).
mgu__class_sub(cl([_|_],Part1),Part2,Sub1,Sub2) :-
	mgu__partition_sub(Part1,Part2,Sub1,Sub2).

%%d mgu__partition_term(tm::in,ptn::in,tm::out)

mgu__partition_term(Term1,Part,Term3) :-
	mgu__find(Part,Term1,Term2),
	(	obj__var_form(Term2) ->
		Term3 = Term2
	;	Term2 = [Tag|Term1L],
		mgu__partition_termL(Term1L,Part,Term2L),
		Term3 = [Tag|Term2L]
	).

%%d mgu__partition_termL(tmL::in,ptn::in,tmL::out)

mgu__partition_termL([],_,[]).
mgu__partition_termL([Term1|Term1L],Part,[Term2|Term2L]) :-
	mgu__partition_term(Term1,Part,Term2),
	mgu__partition_termL(Term1L,Part,Term2L).

%%d mgu__unify_gamma(fmlL::in,mgu::out)

mgu__unify_gamma(Gamma,X) :-
	mgu__filter_equations(Gamma,[],TermLL),
	(	mgu__unify_termLL(TermLL,[],Part), 
		mgu__cycle_free(Part) ->
		X = yes(Part)
	;	X = no
	).

%%d mgu__filter_equations(fmlL::in,tmLL::out)

mgu__filter_equations([],TermLL,TermLL).
mgu__filter_equations([Form|Gamma],Term1LL,Term3LL) :-
	(	Form = [=|TermL],
		obj__pure_termL(TermL) ->
		mgu__filter_equations(Gamma,[TermL|Term1LL],Term3LL)
	;	Form = [&|FormL] ->
		mgu__filter_equations(FormL,Term1LL,Term2LL),
		mgu__filter_equations(Gamma,Term2LL,Term3LL)
	;	mgu__filter_equations(Gamma,Term1LL,Term3LL)
	).

%%d mgu__unify_termLL(tmLL::in,ptn::in,ptn::out)

mgu__unify_termLL([],Part,Part).
mgu__unify_termLL([TermL|TermLL],Part1,Part3) :-
	mgu__unify_termL(TermL,Part1,Part2),
	mgu__unify_termLL(TermLL,Part2,Part3).

%%d mgu__unify_termL(tmL::in,ptn::in,ptn::out)

mgu__unify_termL([],Part,Part).
mgu__unify_termL([Term|TermL],Part1,Part2) :-
	mgu__unify_term_termL(TermL,Term,Part1,Part2).

%%d mgu__unify_term_termL(tmL::in,tm::in,ptn::in,ptn::out)

mgu__unify_term_termL([],_,Part,Part).
mgu__unify_term_termL([Term1|TermL],Term2,Part1,Part3) :-
	mgu__union_find(Term1,Term2,Part1,Part2),
	mgu__unify_term_termL(TermL,Term2,Part2,Part3).

%%d mgu__term_eq(tm::in,tm::in,ptn::in)

mgu__term_eq(Term1,Term2,Part) :-
	mgu__term_eq(Term1,Term2,Part,_).

%%d mgu__term_eq(tm::in,tm::in,ptn::in,ptn::out)

mgu__term_eq(Term1,Term2,Part1,Part5) :-
	mgu__find_delete(Part1,Term1,Part2,Class1),
	(	mgu__class_member(Term2,Class1) ->
		Part5 = Part1
	;	mgu__find_delete(Part2,Term2,Part3,Class2),
		Class1 = cl(Term3,_),
		Class2 = cl(Term4,Q2),
		(	Term3 = [Tag|Term1L], Term4 = [Tag|Term2L] -> 
			mgu__term_eqL(Term1L,Term2L,Part3,Part4),
			Part5 = [cl(Term4,[Class1|Q2])|Part4]
		;	fail
		)
	).

%%d mgu__term_eqL(tmL::in,tmL::in,ptn::in,ptn::out)

mgu__term_eqL([],[],Part,Part).
mgu__term_eqL([Term1|Term1L],[Term2|Term2L],Part1,Part3) :-
	mgu__term_eq(Term1,Term2,Part1,Part2),
	mgu__term_eqL(Term1L,Term2L,Part2,Part3).

%%d mgu__expr_eq(exp::in,exp::in,ptn::in)

mgu__expr_eq(Exp1,Exp2,Part) :- mgu__expr_bound_eq(Exp1,Exp2,[],[],[],Part).

%%d mgu__expr_bound_eq(exp::in,exp::in,varL::in,varL::in,ass::in,ptn::in)

mgu__expr_bound_eq($(X1),Term,Bnd1L,Bnd2L,Ass,Part) :-
	(	lst__member_check(X1,Bnd1L) -> 
		Term = $(X2),
		eq__assoc(Ass,X1,X2)
	;	eq__free_qf(Term,Bnd2L),
		mgu__term_eq($(X1),Term,Part)
	).
mgu__expr_bound_eq([Tag|TermL],$(X),Bnd1L,Bnd2L,_,Part) :-
	\+ lst__member_check(X,Bnd2L),
	eq__free_qf([Tag|TermL],Bnd1L),
	mgu__term_eq([Tag|TermL],$(X),Part).
mgu__expr_bound_eq([Tag|Expr1L],[Tag|Expr2L],Bnd1L,Bnd2L,Ass,Part) :-
	mgu__expr_bound_eqL(Expr1L,Expr2L,Bnd1L,Bnd2L,Ass,Part).
mgu__expr_bound_eq(@(TAG,Bnd1L,Expr1),@(TAG,Bnd2L,Expr2),
		Bnd3L,Bnd4L,Ass1,Part) :-
	eq__alpha_extend(Bnd1L,Bnd2L,Ass1,Ass2),
	lst__append_set(Bnd1L,Bnd3L,Bnd5L),
	lst__append_set(Bnd2L,Bnd4L,Bnd6L),
	mgu__expr_bound_eq(Expr1,Expr2,Bnd5L,Bnd6L,Ass2,Part).

%%d mgu__expr_bound_eqL(expL::in,expL::in,varL::in,varL::in,ass::in,ptn::in)

mgu__expr_bound_eqL([],[],_,_,_,_).
mgu__expr_bound_eqL([Expr1|Expr1L],[Expr2|Expr2L],Bnd1L,Bnd2L,Ass,Part) :-
	mgu__expr_bound_eq(Expr1,Expr2,Bnd1L,Bnd2L,Ass,Part),
	mgu__expr_bound_eqL(Expr1L,Expr2L,Bnd1L,Bnd2L,Ass,Part).

% mgu.pl ends here

