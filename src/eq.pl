/*   Author: Robert Staerk <staerk@math.stanford.edu> */
/*  Created: Fri Dec  2 15:52:06 1994 */
/* Updated: Tue Feb 16 10:46:46 1999 */
/* Filename: eq.pl */
/* Abstract: Equality predicates for terms with abstractions. */



%%% alpha equality between expressions 



%%d eq__alpha(exp::in,exp::in)

eq__alpha(Expr1,Expr2) :- eq__alpha_bound(Expr1,Expr2,[]).

%%d eq__alpha_bound(exp::in,exp::in,ass::in)

eq__alpha_bound($(X1),$(X2),Ass) :-		% Ass is a list of pairs of
	eq__alpha_correspond(Ass,X1,X2).	% the form X1 - X2
eq__alpha_bound([Tag|Expr1L],[Tag|Expr2L],Ass) :-
	eq__alpha_boundL(Expr1L,Expr2L,Ass).
eq__alpha_bound(@(Tag,V1,Expr1),@(Tag,V2,Expr2),Ass1) :-
	eq__alpha_extend(V1,V2,Ass1,Ass2),
	eq__alpha_bound(Expr1,Expr2,Ass2).

%%d eq__alpha_extend(varL::in,varL::in,ass::in,ass::out)

eq__alpha_extend([],[],Ass,Ass).
eq__alpha_extend([X1|V1],[X2|V2],A1L,[X1 - X2|A2L]) :-
	eq__alpha_extend(V1,V2,A1L,A2L).

%%d eq__alpha_boundL(expL::in,expL::in,ass::in)

eq__alpha_boundL([],[],_).
eq__alpha_boundL([Expr1|Expr1L],[Expr2|Expr2L],Ass) :-
	eq__alpha_bound(Expr1,Expr2,Ass),
	eq__alpha_boundL(Expr1L,Expr2L,Ass).

%%d eq__alpha_correspond(ass::in,gr::in,gr::in)

eq__alpha_correspond([X - Y|_],X,Y).
eq__alpha_correspond([U - V|Ass],X,Y) :-
	\+ (X = U),
	\+ (Y = V),
	eq__alpha_correspond(Ass,X,Y).
eq__alpha_correspond([],X,X).



%%% maximum integer variable of an expression



%%d eq__max(exp::in,int::in,int::out)

% eq__max(Expr,N1,N2) => 
%   N2 = max( {N1} union {M +1 | $(M) free in Expr, integer(M)} )

eq__max(Expr,N1,N2) :-
	eq__max_bound(Expr,[],N1,N2).

%%d eq__max_bound(exp::in,varL::in,int::in,int::out)

eq__max_bound($(X),BV,N1,N2) :-
	(	lst__member_check(X,BV) -> 
		N2 = N1
	; 	eq__max_var(X,N1,N2)
	).
eq__max_bound([_|ExprL],BV,N1,N2) :-
	eq__max_boundL(ExprL,BV,N1,N2).
eq__max_bound(@(_,BV1,Expr),BV2,N1,N2) :-
	lst__append_set(BV1,BV2,BV3),
	eq__max_bound(Expr,BV3,N1,N2).

%%d eq__max_boundL(expL::in,varL::in,int::in,int::out)

eq__max_boundL([],_,N,N).
eq__max_boundL([Expr|ExprL],BV,N1,N3) :-
	eq__max_bound(Expr,BV,N1,N2),
	eq__max_boundL(ExprL,BV,N2,N3).

%%d eq__max_var(gr::in,int::in,int::out)

eq__max_var(X,N,N) :-
	atom(X).
eq__max_var(X,N1,N2) :-
	integer(X),
	(	X < N1 -> 
		N2 = N1
	; 	N2 is X + 1
	).

%%d eq__max_varL(varL::in,int::in,int::out)

eq__max_varL([],N,N).
eq__max_varL([X|XL],N1,N3) :-
	eq__max_var(X,N1,N2),
	eq__max_varL(XL,N2,N3).

%%d eq__max_qf(exp::in,int::in,int::out)

eq__max_qf($(X),N1,N2) :-
	eq__max_var(X,N1,N2).
eq__max_qf([_|ExprL],N1,N2) :-
	eq__max_qfL(ExprL,N1,N2).

%%d eq__max_qfL(expL::in,int::in,int::out)

eq__max_qfL([],N,N).
eq__max_qfL([Expr|ExprL],N1,N3) :-
	eq__max_qf(Expr,N1,N2),
	eq__max_qfL(ExprL,N2,N3).



%%% alpha norm of an expression



%%d eq__norm(exp::in,exp::out)

eq__norm(Expr1,Expr2) :-
	eq__max(Expr1,0,N),
	eq__norm_bound(Expr1,N,[],Expr2).

%%d eq__norm_bound(exp::in,int::in,ass::in,exp::out)

eq__norm_bound($(V1),_,Ass,$(V2)) :-
	eq__assoc(Ass,V1,V2).
eq__norm_bound([Tag|Expr1L],N,Ass,[Tag|Expr2L]) :-
	eq__norm_boundL(Expr1L,N,Ass,Expr2L).
eq__norm_bound(@(Tag,V,Expr1),N1,Ass1,@(Tag,NL,Expr2)) :-
	eq__norm_extend(V,N1,Ass1,N2,Ass2,NL),
	eq__norm_bound(Expr1,N2,Ass2,Expr2).

%%d eq__norm_extend(varL::in,int::in,ass::in,int::out,ass::out,intL::out)

eq__norm_extend([],N,Ass,N,Ass,[]).
eq__norm_extend([X|V],N1,Ass1,N3,[X - N1|Ass2],[N1|NL]) :-
	N2 is N1 + 1,
	eq__norm_extend(V,N2,Ass1,N3,Ass2,NL).

%%d eq__norm_boundL(expL::in,int::in,ass::in,expL::out)

eq__norm_boundL([],_,_,[]).
eq__norm_boundL([Expr1|Expr1L],N,Ass,[Expr2|Expr2L]) :-
	eq__norm_bound(Expr1,N,Ass,Expr2),
	eq__norm_boundL(Expr1L,N,Ass,Expr2L).

%%d eq__assoc(ass::in,gr::in,gr::out)

eq__assoc([],X,X).
eq__assoc([X1 - Y1|Ass],X2,Y2) :-
	(	X1 = X2 -> 
		Y2 = Y1
	; 	eq__assoc(Ass,X2,Y2)
	).

%%d eq__norm_equal(exp::in,exp::in)

eq__norm_equal(Expr1,Expr2) :-			% alpha equality
	eq__norm(Expr1,Expr3),
	eq__norm(Expr2,Expr3).



%%% free variables of an expression



%%d eq__occurs_qf(tm::in,gr::in)

eq__occurs_qf($(X),X).
eq__occurs_qf([_|TermL],X) :-
	lst__member(Term,TermL),
	eq__occurs_qf(Term,X).

%%d eq__free_qf(exp::in,varL::in)

eq__free_qf($(X),V) :-
	\+ lst__member_check(X,V).
eq__free_qf([_|ExprL],V) :-
	eq__free_qfL(ExprL,V).

%%d eq__free_qfL(expL::in,varL::in)

eq__free_qfL([],_).
eq__free_qfL([Expr|ExprL],V) :-
	eq__free_qf(Expr,V),
	eq__free_qfL(ExprL,V).

%%d eq__free(exp::in,varL::in)

eq__free(Expr,V) :- eq__free_bound(Expr,V,[]).

%%d eq__free_bound(exp::in,varL::in,varL::in)

eq__free_bound($(X),V,BV) :-
	(	lst__member_check(X,BV) ->
		true
	; 	\+ lst__member_check(X,V)
	).
eq__free_bound([_|ExprL],V,BV) :-
	eq__free_boundL(ExprL,V,BV).
eq__free_bound(@(_,BV1,Expr),V,BV2) :-
	lst__append_set(BV1,BV2,BV3),
	eq__free_bound(Expr,V,BV3).

%%d eq__free_boundL(expL::in,varL::in,varL::in)

eq__free_boundL([],_,_).
eq__free_boundL([Expr|ExprL],V,BV) :-
	eq__free_bound(Expr,V,BV),
	eq__free_boundL(ExprL,V,BV).

%%d eq__add_free_qf(exp::in,varL::in,varL::out)

eq__add_free_qf($(X),V1,V2) :-
	lst__add_element(X,V1,V2).
eq__add_free_qf([_|ExprL],V1,V2) :-
	eq__add_free_qfL(ExprL,V1,V2).

%%d eq__add_free_qfL(expL::in,varL::in,varL::out)

eq__add_free_qfL([],V,V).
eq__add_free_qfL([Expr|ExprL],V1,V3) :-
	eq__add_free_qf(Expr,V1,V2),
	eq__add_free_qfL(ExprL,V2,V3).

%%d eq__add_free(exp::in,varL::in,varL::out)

eq__add_free(Expr,V1,V2) :-
	eq__add_free_bound(Expr,[],V1,V2).

%%d eq__add_free_bound(exp::in,varL::in,varL::in,varL::out)

eq__add_free_bound($(X),BV,V1,V2) :-
	(	lst__member_check(X,BV) -> 
		V2 = V1 
	; 	lst__add_element(X,V1,V2)
	).
eq__add_free_bound([_|ExprL],BV,V1,V2) :-
	eq__add_free_boundL(ExprL,BV,V1,V2).
eq__add_free_bound(@(_,BV1,Expr),BV2,V1,V2) :-
	lst__append_set(BV1,BV2,BV3),
	eq__add_free_bound(Expr,BV3,V1,V2).

%%d eq__add_free_boundL(expL::in,varL::in,varL::in,varL::out)

eq__add_free_boundL([],_,V,V).
eq__add_free_boundL([Expr|ExprL],BV,V1,V3) :-
	eq__add_free_bound(Expr,BV,V1,V2),
	eq__add_free_boundL(ExprL,BV,V2,V3).

%%d eq__add_max_free_qf(exp::in,int::in,varL::in,int::out,varL::out)

eq__add_max_free_qf($(X),N1,V1,N2,V2) :-
	eq__max_var(X,N1,N2),
	lst__add_element(X,V1,V2).
eq__add_max_free_qf([_|ExprL],N1,V1,N2,V2) :-
	eq__add_max_free_qfL(ExprL,N1,V1,N2,V2).

%%d eq__add_max_free_qfL(expL::in,int::in,varL::in,int::out,varL::out)

eq__add_max_free_qfL([],N,V,N,V).
eq__add_max_free_qfL([Expr|ExprL],N1,V1,N3,V3) :-
	eq__add_max_free_qf(Expr,N1,V1,N2,V2),
	eq__add_max_free_qfL(ExprL,N2,V2,N3,V3).

%%d eq__add__free_max(exp::in,int::in,varL::in,int::out,varL::out)

eq__add_max_free(Expr,N1,V1,N2,V2) :-
	eq__add_max_free_bound(Expr,[],N1,V1,N2,V2).

%%d eq__add_max_free_bound(exp::in,varL::in,int::in,varL::in,int::out,varL::out)

eq__add_max_free_bound($(X),BV,N1,V1,N2,V2) :-
	(	lst__member_check(X,BV) ->
		N2 = N1,
		V2 = V1
	;	lst__add_element(X,V1,V2),
		eq__max_var(X,N1,N2)
	).
eq__add_max_free_bound([_|ExprL],BV,N1,V1,N2,V2) :-
	eq__add_max_free_boundL(ExprL,BV,N1,V1,N2,V2).
eq__add_max_free_bound(@(_,BV1,Expr),BV2,N1,V1,N2,V2) :-
	lst__append_set(BV1,BV2,BV3),
	eq__add_max_free_bound(Expr,BV3,N1,V1,N2,V2).

%%d eq__add_max_free_boundL(expL::in,varL::in,int::in,varL::in,int::out,varL::out)

eq__add_max_free_boundL([],_,N,V,N,V).
eq__add_max_free_boundL([Expr|ExprL],BV,N1,V1,N3,V3) :-
	eq__add_max_free_bound(Expr,BV,N1,V1,N2,V2),
	eq__add_max_free_boundL(ExprL,BV,N2,V2,N3,V3).




%%% matching of expressions




%%d eq__match_extend(gr::in,tm::in,sub::in,sub::out)

eq__match_extend(X,Term1,Sub1,Sub2) :-
	(	lst__member(X => Term2,Sub1) ->
			Term1 = Term2, 
			Sub2 = Sub1
	; 	Sub2 = [X => Term1|Sub1]
	).

%%d eq__match_qf(exp::in,exp::in,sub::in,sub::out)

eq__match_qf($(X),Term,Sub1,Sub2) :-
	eq__match_extend(X,Term,Sub1,Sub2).
eq__match_qf([Tag|Expr1L],[Tag|Expr2L],Sub1,Sub2) :-
	eq__match_qfL(Expr1L,Expr2L,Sub1,Sub2).

%%d eq__match_qfL(expL::in,expL::in,sub::in,sub::out)

eq__match_qfL([],[],Sub,Sub).
eq__match_qfL([Expr1|Expr1L],[Expr2|Expr2L],Sub1,Sub3) :-
	eq__match_qf(Expr1,Expr2,Sub1,Sub2),
	eq__match_qfL(Expr1L,Expr2L,Sub2,Sub3).

%%d eq__match(exp::in,exp::in,sub::out)

eq__match(Expr1,Expr2,Sub) :-
	eq__match_bound(Expr1,Expr2,[],[],[],[],Sub).

%%d eq__match_bound(exp::in,exp::in,varL::in,varL::in,ass::in,sub::in,sub::out)

eq__match_bound($(X1),Term,BV1,BV2,Ass,Sub1,Sub2) :-
	(	lst__member_check(X1,BV1) -> 
		Term = $(X2),
		eq__assoc(Ass,X1,X2),
		Sub2 = Sub1
	;	eq__free_qf(Term,BV2),
		eq__match_extend(X1,Term,Sub1,Sub2)
	).
eq__match_bound([Tag|Expr1L],[Tag|Expr2L],BV1,BV2,Ass,Sub1,Sub2) :-
	eq__match_boundL(Expr1L,Expr2L,BV1,BV2,Ass,Sub1,Sub2).
eq__match_bound(@(Tag,V1,Expr1),@(Tag,V2,Expr2),
	BV1,BV2,Ass1,Sub1,Sub2) :-
	eq__alpha_extend(V1,V2,Ass1,Ass2),
	lst__append_set(V1,BV1,BV3),
	lst__append_set(V2,BV2,BV4),
	eq__match_bound(Expr1,Expr2,BV3,BV4,Ass2,Sub1,Sub2).

%%d eq__match_boundL(expL::in,expL::in,varL::in,varL::in,ass::in,sub::in,sub::out)

eq__match_boundL([],[],_,_,_,Sub,Sub).
eq__match_boundL([Expr1|Expr1L],[Expr2|Expr2L],BV1,BV2,Ass,Sub1,Sub3) :-
	eq__match_bound(Expr1,Expr2,BV1,BV2,Ass,Sub1,Sub2),
	eq__match_boundL(Expr1L,Expr2L,BV1,BV2,Ass,Sub2,Sub3).

%%d eq__match_constrained(exp::in,exp::in,varL::in,sub::in,sub::out)

eq__match_constrained(Expr1,Expr2,XL,Sub1,Sub2) :-
	(eq__match_constrained_bound(Expr1,Expr2,[],[],[],XL,Sub1,Sub2) ->
		true
	;	fail
	).

%%d eq__match_constrained_bound(exp::in,exp::in,varL::in,varL::in,ass::in,varL::in,sub::in,sub::out)

eq__match_constrained_bound($(X1),Term,BV1,BV2,Ass,XL,Sub1,Sub2) :-
	(	lst__member_check(X1,BV1) -> 
		Term = $(X2),
		eq__assoc(Ass,X1,X2),
		Sub2 = Sub1
	;	(	Term = $(X1) ->
			true
		; 	lst__member_check(X1,XL)
		),
		eq__free_qf(Term,BV2),
		eq__match_extend(X1,Term,Sub1,Sub2)
	).
eq__match_constrained_bound([Tag|Expr1L],[Tag|Expr2L],
	BV1,BV2,Ass,XL,Sub1,Sub2) :-
	eq__match_constrained_boundL(Expr1L,Expr2L,BV1,BV2,Ass,XL,Sub1,Sub2).
eq__match_constrained_bound(@(Tag,V1,Expr1),@(Tag,V2,Expr2),
	BV1,BV2,Ass1,XL,Sub1,Sub2) :-
	eq__alpha_extend(V1,V2,Ass1,Ass2),
	lst__append_set(V1,BV1,BV3),
	lst__append_set(V2,BV2,BV4),
	eq__match_constrained_bound(Expr1,Expr2,BV3,BV4,Ass2,XL,Sub1,Sub2).

%%d eq__match_constrained_boundL(expL::in,expL::in,varL::in,varL::in,ass::in,varL::in,sub::in,sub::out)

eq__match_constrained_boundL([],[],_,_,_,_,Sub,Sub).
eq__match_constrained_boundL([Expr1|Expr1L],[Expr2|Expr2L],
	BV1,BV2,Ass,XL,Sub1,Sub3) :-
	eq__match_constrained_bound(Expr1,Expr2,BV1,BV2,Ass,XL,Sub1,Sub2),
	eq__match_constrained_boundL(Expr1L,Expr2L,BV1,BV2,Ass,XL,Sub2,Sub3).



%%% application of substitutions to expressions



%%d eq__apply(exp::in,varL::in,sub::in,int::in,exp::out)

% Preconditions for eq__apply(Expr1,V,Sub,N,Expr2):
%
%  o If $(K) is free in Expr1 then K < N.
%  o If X => Term is in Sub, $(X) <> Term and $(Y) is in Term then
%    Y is in V.
%  o If X => Term is in Sub and $(K) is in Term then K < N.

eq__apply($(X),_,Sub,_,Term) :-
	eq__apply_var(Sub,X,Term).
eq__apply([Tag|Expr1L],V,Sub,N,[Tag|Expr2L]) :-
	eq__applyL(Expr1L,V,Sub,N,Expr2L).
eq__apply(@(Tag,BV1,Expr1),V1,Sub1,N1,@(Tag,BV2,Expr2)) :-
	eq__apply_extend(BV1,V1,Sub1,N1,BV2,V2,Sub2,N2),
	eq__apply(Expr1,V2,Sub2,N2,Expr2).

%%d eq__applyL(expL::in,varL::in,sub::in,int::in,expL::out)

eq__applyL([],_,_,_,[]).
eq__applyL([Expr1|Expr1L],V,Sub,N,[Expr2|Expr2L]) :-
	eq__apply(Expr1,V,Sub,N,Expr2),
	eq__applyL(Expr1L,V,Sub,N,Expr2L).

%%d eq__apply_extend(varL::in,varL::in,sub::in,int::in,varL::out,varL::out,sub::out,int::out)

eq__apply_extend([],V,Sub,N,[],V,Sub,N).
eq__apply_extend([X|BV1],V1,Sub1,N1,BV3,V3,Sub3,N3) :-
	(	lst__member_check(X,V1) -> 
		N2 is N1 + 1,
		BV3 = [N1|BV2],
		V3 = [N1|V2],
		Sub3 = [X => $(N1)|Sub2],
		eq__apply_extend(BV1,V1,Sub1,N2,BV2,V2,Sub2,N3)
	;	BV3 = [X|BV2],
		Sub3 = [X => $(X)|Sub2],
		eq__max_var(X,N1,N2),
		eq__apply_extend(BV1,V1,Sub1,N2,BV2,V3,Sub2,N3)
	).

%%d eq__apply_var(sub::in,gr::in,tm::out)

eq__apply_var([],X,$(X)).
eq__apply_var([Y => Term1|Sub],X,Term2) :-
	(	X = Y -> 
		Term2 = Term1 
	; 	eq__apply_var(Sub,X,Term2)
	).

%%d eq__apply_sub_qf(exp::in,sub::in,exp::in)

eq__apply_sub_qf(Expr1,Sub,Expr2) :-
	(	Sub = [] ->
		Expr2 = Expr1
	;	eq__apply_qf(Expr1,Sub,Expr2)
	).

%%d eq__apply_sub_qfL(exp::in,sub::in,exp::in)

eq__apply_sub_qfL(Expr1L,Sub,Expr2L) :-
	(	Sub = [] ->
		Expr2L = Expr1L
	;	eq__apply_qfL(Expr1L,Sub,Expr2L)
	).

%%d eq__apply_qf(exp::in,sub::in,exp::in)

eq__apply_qf($(X),Sub,Term) :-
	eq__apply_var(Sub,X,Term).
eq__apply_qf([Tag|Expr1L],Sub,[Tag|Expr2L]) :-
	eq__apply_qfL(Expr1L,Sub,Expr2L).

%%d eq__apply_qfL(tmL::in,sub::in,tmL::in)

eq__apply_qfL([],_,[]).
eq__apply_qfL([Expr1|Expr1L],Sub,[Expr2|Expr2L]) :-
	eq__apply_qf(Expr1,Sub,Expr2),
	eq__apply_qfL(Expr1L,Sub,Expr2L).

%%d eq__apply_plain(exp::in,sub::in,exp::out)

eq__apply_plain(Expr1,Sub,Expr2) :-
	(	Sub = [] ->
		Expr2 = Expr1
	;	eq__max(Expr1,0,N1),
		eq__max_free_sub(Sub,N1,[],N2,V),
		eq__apply(Expr1,V,Sub,N2,Expr2)
	).

%%d eq__max_free_sub(sub::in,int::in,varL::in,int::out,varL::out)

eq__max_free_sub([],N,V,N,V).
eq__max_free_sub([_ => Term|Sub],N1,V1,N3,V3) :-
	eq__add_max_free_qf(Term,N1,V1,N2,V2),
	eq__max_free_sub(Sub,N2,V2,N3,V3).




%%% Predicates used in other files




%%d eq__make_sub(varL::in,tmL::in,varL::out,sub::out)

eq__make_sub([],[],[],[]).
eq__make_sub([X|XL],[Term|TermL],V2,[X => Term|Sub]) :-
	eq__make_sub(XL,TermL,V1,Sub),
	eq__add_free_qf(Term,V1,V2).

%%d eq__term_eq(tm::in,tm::in,tmLL::in)

eq__term_eq(Term1,Term2,TermLL) :-
	lst__member(TermL,TermLL),
	lst__member_check(Term1,TermL),
	lst__member_check(Term2,TermL).
eq__term_eq($(X),$(X),_).
eq__term_eq([Tag|Term1L],[Tag|Term2L],TermLL) :-
	eq__term_eqL(Term1L,Term2L,TermLL).

%%d eq__term_eqL(tmL::in,tmL::in,tmLL::in)

eq__term_eqL([],[],_).
eq__term_eqL([Term1|Term1L],[Term2|Term2L],TermLL) :-
	once(eq__term_eq(Term1,Term2,TermLL)),
	eq__term_eqL(Term1L,Term2L,TermLL).

%%d eq__termL_eq(tmLL::in,tmLL::in)

eq__termL_eq([_],_).
eq__termL_eq([Term1,Term2|TermL],TermLL) :-
	once(eq__term_eq(Term1,Term2,TermLL)),
	eq__termL_eq([Term2|TermL],TermLL).

%%d eq__expr_eq(exp::in,exp::in,tmLL::in)

eq__expr_eq(Expr1,Expr2,TermLL) :-
	once(eq__expr_eq_bound(Expr1,Expr2,[],[],[],TermLL)).

%%d eq__expr_eq_bound(exp::in,exp::in,varL::in,varL::in,ass::in,tmLL::in)

eq__expr_eq_bound($(X1),$(X2),_,_,Ass,_) :-
	eq__alpha_correspond(Ass,X1,X2).
eq__expr_eq_bound(Term1,Term2,BV1,BV2,_,TermLL) :-
	obj__term_form(Term1),
	obj__term_form(Term2),
	(	eq__free_qf(Term1,BV1), 
		eq__free_qf(Term2,BV2) ->
		once(eq__term_eq(Term1,Term2,TermLL))
	; 	fail
	).
eq__expr_eq_bound([Tag|Form1L],[Tag|Form2L],BV1,BV2,Ass,TermLL) :-
	eq__expr_eq_boundL(Form1L,Form2L,BV1,BV2,Ass,TermLL).
eq__expr_eq_bound(@(Tag,BV1,Form1),@(Tag,BV2,Form2),
	BV3,BV4,Ass1,TermLL) :-
	eq__alpha_extend(BV1,BV2,Ass1,Ass2),
	lst__append_set(BV1,BV3,BV5),
	lst__append_set(BV2,BV4,BV6),
	once(eq__expr_eq_bound(Form1,Form2,BV5,BV6,Ass2,TermLL)).

%%d eq__expr_eq_boundL(expL::in,expL::in,varL::in,varL::in,ass::in,tmLL::in)

eq__expr_eq_boundL([],[],_,_,_,_).
eq__expr_eq_boundL([Form1|Form1L],[Form2|Form2L],BV1,BV2,Ass,TermLL) :-
	once(eq__expr_eq_bound(Form1,Form2,BV1,BV2,Ass,TermLL)),
	eq__expr_eq_boundL(Form1L,Form2L,BV1,BV2,Ass,TermLL).

%%d eq__sub_forall(sub::in,varL::in,varL::in,varL::in)

eq__sub_forall(Sub,V,BV1,BV2) :-
	\+ eq__sub_forall_not(Sub,V,BV1,BV2).

%%d eq__sub_forall_not(sub::in,varL::in,varL::in,varL::in)

eq__sub_forall_not(Sub,V,BV1,BV2) :-
	lst__member(X => Term,Sub),
	\+ lst__member_check(X,BV2),
	lst__member_check(X,V),
	(	Term = $(X) -> 
		lst__member_check(X,BV1)
	;	 true
	).

% eq.pl ends here

