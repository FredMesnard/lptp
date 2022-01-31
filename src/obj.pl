/*   Author: Robert Staerk <staerk@math.stanford.edu> */
/*  Created: Fri Dec  2 15:54:26 1994 */
/* Updated: Tue Feb 16 14:38:24 1999 */
/* Filename: obj.pl */
/* Abstract: Data types for the object logic. The internal representation of
   expressions, terms, atomic goals, queries, formulas, clauses, derivations,
   derivation steps, substitutions, and second order substitutions. */

%%c
%%c Expressions are Prolog terms of the following form:
%%c
%%c   $(Name)				variables
%%c   [Tag,Expr,...,Expr]		applications
%%c   @(Tag,[Name,...,Name],Expr)	abstractions
%%c
%%c Terms, atomic goals, queries and formulas are all expressions.
%%c
%%c Terms are Prolog terms of the following form:
%%c
%%c   $(Name)
%%c   [n(Name,N),Term,...,Term]
%%c   [f(Name,N),Term,...,Term]
%%c
%%c Atomic goals are Prolog terms of the following form:
%%c
%%c   [n(Name,N),Term,...,Term]
%%c
%%c Goals are Prolog terms of the following form:
%%c
%%c   Atom
%%c   [=,Term,Term]
%%c   [~,Goal]
%%c   [&,Goal,...,Goal]
%%c   [\/,Goal,...,Goal]
%%c 
%%c Formulas are Prolog terms of the following form:
%%c
%%c   [d(Name,N),Term,...,Term]
%%c   [n(Name,N),Term,...,Term]
%%c   [=,Term,...,Term]
%%c   [<>,Term,Term]
%%c   gr(Term)
%%c   [succeeds,Atom]
%%c   [fails,Atom]
%%c   [terminates,Goal]
%%c   [def,Form]
%%c   [&,Form,...,Form]
%%c   [\/,Form,...,Form]
%%c   [~,Form]
%%c   [=>,Form,Form]
%%c   [<=>,Form,Form]
%%c   @(all,[Name,...,Name],Form)
%%c   @(ex,[Name,...,Name],Form)
%%c
%%c Clauses are Prolog terms of the following form:
%%c
%%c   clause(Atom,Goal,VarL/N) 
%%c
%%c Condition: The variables of Atom and Goal are in VarL or among 
%%c $(0), $(1),...,$(N - 1).
%%c
%%c Program predicate definitions are Prolog facts of the following form:
%%c
%%c   db__clauses(n(Name,N),[Clause,...,Clause]).
%%c
%%c Defined predicate definitions are Prolog facts of the following form:
%%c
%%c   db__pred([d(Name,N),$(1),...,$(n)],Form).
%%c
%%c Defined function definitions are Prolog facts of the following form:
%%c
%%c   db__fun([f(Name,N),$(1),...,$(n)],Form,Form).
%%c

% %%d obj__expression(gr::in)
% 
% obj__expression($(Name)) :-			% variable
% 	atomic(Name).
% obj__expression([_|ExprL]) :-			% compound expression
% 	obj__expressionL(ExprL).
% obj__expression(@(_,VarL,Expr)) :-		% abstraction
% 	obj__varL(VarL),
% 	obj__expression(Expr).
% 
% %%d obj__expressionL(grL::in)
% 
% obj__expressionL([]).				% lists of expressions
% obj__expressionL([Expr|ExprL]) :-
% 	obj__expression(Expr),
% 	obj__expressionL(ExprL).

%%d obj__varL(grL::in)

obj__varL([]).					% lists of variables
obj__varL([Name|NameL]) :-
	atomic(Name),
	obj__varL(NameL),
	\+ lst__member_check(Name,NameL).

%%d obj__term(gr::in)

obj__term($(Name)) :-				% variables
	atomic(Name).
obj__term([n(Name,N)|TermL]) :-			% constructor
	atomic(Name),
	integer(N),
	obj__termL(TermL).
obj__term([f(Name,N)|TermL]) :-			% defined function symbol
	atomic(Name),
	integer(N),
	obj__termL(TermL).

%%d obj__termL(grL::in)

obj__termL([]).					% lists of terms
obj__termL([Term|TermL]) :-
	obj__term(Term),
	obj__termL(TermL).

%%d obj__pure_term(gr::in)

obj__pure_term($(_)).				% functions symbols
obj__pure_term([n(_,_)|TermL]) :-	
	obj__pure_termL(TermL).

%%d obj__pure_termL(grL::in)

obj__pure_termL([]).				% lists of pure terms
obj__pure_termL([Term|TermL]) :-
	obj__pure_term(Term),
	obj__pure_termL(TermL).

%%d obj__atomic_goal(gr::in)

obj__atomic_goal([n(Name,N)|TermL]) :-		% atomic goals
	atomic(Name),
	integer(N),
	obj__termL(TermL).

%%d obj__goal(gr::in)

obj__goal([=,Term1,Term2]) :-			% equations
	obj__term(Term1),
	obj__term(Term2).
obj__goal([n(Name,N)|TermL]) :-			% atomic goals
	atomic(Name),
	integer(N),
	obj__termL(TermL).
obj__goal([~,Goal]) :-				% negated goal: \+ Goal
	obj__goal(Goal).
obj__goal([&|GoalL]) :-				% conjunction: (Goal1, Goal2)
	obj__goalL(GoalL).			% [&] is true
obj__goal([\/|GoalL]) :-			% disjunction: (Goal1; Goal2)
	obj__goalL(GoalL).			% [\/] is fail

%%d obj__goalL(grL::in)

obj__goalL([]).					% lists of goals
obj__goalL([Goal|GoalL]) :-
	obj__goal(Goal),
	obj__goalL(GoalL).

%%d obj__sft_atom(gr::in)

obj__sft_atom([succeeds,Atom]) :-
	obj__atomic_goal(Atom).
obj__sft_atom([fails,Atom]) :-
	obj__atomic_goal(Atom).
obj__sft_atom([terminates,Atom]) :-
	obj__atomic_goal(Atom).

%%d obj__formula(gr::in)

obj__formula([n(Name,N)|TermL]) :-		% atomic formulas
	atomic(Name),
	integer(N),
	obj__termL(TermL).
obj__formula([d(Name,N)|TermL]) :-		% atomic formulas
	atomic(Name),
	integer(N),
	obj__termL(TermL).
obj__formula([=|TermL]) :-			% equations
	obj__termL(TermL).
obj__formula([<>,Term1,Term2]) :-		% inequations
	obj__term(Term1),
	obj__term(Term2).
obj__formula([gr,Term]) :-			% gr
	obj__term(Term).
obj__formula([succeeds,Atom]) :-		% sft formulas, operator S
	obj__atomic_goal(Atom).
obj__formula([fails,Atom]) :-			% sft formulas, operator F
	obj__atomic_goal(Atom).
obj__formula([terminates,Goal]) :-		% sft formulas, operator T
	obj__goal(Goal).	
obj__formula([def,Form]) :-			% def, the definition form
	obj__sft_atom(Form).
obj__formula([~,Form]) :-			% negation
	obj__formula(Form).
obj__formula([&|FormL]) :-			% conjunction, [&] ~~ true
	obj__formulaL(FormL).
obj__formula([\/|FormL]) :-			% disjunction, [\/] ~~ false
	obj__formulaL(FormL).
obj__formula([=>,Form1,Form2]) :-		% implication
	obj__formula(Form1),
	obj__formula(Form2).
obj__formula([<=>,Form1,Form2]) :-		% equivalence
	obj__formula(Form1),
	obj__formula(Form2).
obj__formula(@(all,NameL,Form)) :-		% universial quantifier
	obj__varL(NameL),
	obj__formula(Form).
obj__formula(@(ex,NameL,Form)) :-		% existential quantifier
	obj__varL(NameL),
	obj__formula(Form).

%%d obj__formulaL(grL::in)

obj__formulaL([]).				% lists of formulas
obj__formulaL([Form|FormL]) :-
	obj__formula(Form),
	obj__formulaL(FormL).

%%d obj__sft_op(gr::out)

obj__sft_op(succeeds).
obj__sft_op(fails).
obj__sft_op(terminates).

%%d obj__var_form(gr::in)
%%d obj__equation_form(gr::in)
%%d obj__negation_form(gr::in)
%%d obj__conjunction_form(gr::in)
%%d obj__disjunction_form(gr::in)
%%d obj__implication_form(gr::in)
%%d obj__equivalence_form(gr::in)
%%d obj__forall_form(gr::in)
%%d obj__exists_form(gr::in)

obj__var_form($(_)).
obj__equation_form([=|_]).
obj__negation_form([~,_]).
obj__conjunction_form([&|_]).
obj__disjunction_form([\/|_]).
obj__implication_form([=>,_,_]).
obj__equivalence_form([<=>,_,_]).
obj__forall_form(@(all,_,_)).
obj__exists_form(@(ex,_,_)).

%%d obj__term_form(gr::in)

obj__term_form($(_)).
obj__term_form([n(_,_)|_]).
obj__term_form([f(_,_)|_]).

%%d obj__clause(gr::in)

obj__clause(clause(Head,Body,U)) :-
	obj__atomic_goal(Head),
	obj__goal(Body),
	obj__free_vars(U).

%%d obj__free_vars(gr::in)

obj__free_vars(NameL/N) :-
	obj__varL(NameL),
	integer(N).

%%d obj__clauseL(grL::in)

obj__clauseL([]).
obj__clauseL([Clause|ClauseL]) :-
	obj__clause(Clause),
	obj__clauseL(ClauseL).

%%d obj__derivation(grL::in)

obj__derivation([]).
obj__derivation([Step|Deriv]) :-
	obj__derivation_step(Step),
	obj__derivation(Deriv).

%%d obj__derivation_step(gr::in)

obj__derivation_step(by(Form,_)) :-
	obj__formula(Form).
obj__derivation_step([Tag|FormL]) :-
	obj__formula([Tag|FormL]).
obj__derivation_step(@(Tag,VL,Form)) :-
	obj__formula(@(Tag,VL,Form)).
obj__derivation_step(assume(Form1,Deriv,Form2)) :-
	obj__formula(Form1),
	obj__derivation(Deriv),
	obj__formula(Form2).
obj__derivation_step(cases(CaseL,Form)) :-
	obj__caseL(CaseL),
	obj__formula(Form).
obj__derivation_step(exist(NameL,Form1,Deriv,Form2)) :-
	obj__varL(NameL),
	obj__formula(Form1),
	obj__derivation(Deriv),
	obj__formula(Form2).
obj__derivation_step(induction(FormL,StepL)) :-
	obj__formulaL(FormL),
	obj__induction_stepL(StepL).
obj__derivation_step(contra(Form,Deriv)) :-
	obj__formula(Form),
	obj__derivation(Deriv).
obj__derivation_step(indirect([~,Form],Deriv)) :-
	obj__formula(Form),
	obj__derivation(Deriv).

%%d obj__caseL(grL::in)

obj__caseL([]).
obj__caseL([case(Form,Deriv)|CaseL]) :-
	obj__formula(Form),
	obj__derivation(Deriv),
	obj__caseL(CaseL).

%%d obj__induction_step(gr::in)

obj__induction_step(step(NameL,FormL,Deriv,Form)) :-
	obj__varL(NameL),
	obj__formulaL(FormL),
	obj__derivation(Deriv),
	obj__formula(Form).
	
%%d obj__induction_stepL(grL::in)

obj__induction_stepL([]).
obj__induction_stepL([Step|StepL]) :-
	obj__induction_step(Step),
	obj__induction_stepL(StepL).

%%d obj__substitution(gr::in)

obj__substitution([]).
obj__substitution([Name => Term|Sub]) :-
	atomic(Name),
	obj__term(Term),
	\+ obj__domain(Name,Sub),
	obj__substitution(Sub).

%%d obj__domain(gr::in,grL::in)

obj__domain(Name,Sub) :- lst__member(Name => _,Sub).

%%d obj__substitution2(grL::in)

obj__substitution2([]).
obj__substitution2([sub(Name,N,VarL,Form)|U]) :-
	atomic(Name),
	integer(N),
	obj__varL(VarL),
	obj__formula(Form), 
	\+ obj__domain2(Name,N,U),
	obj__substitution2(U).

%%d obj__domain2(gr::in,gr::in,grL::in)

obj__domain2(Name,N,U) :- lst__member(sub(Name,N,_,_),U).

%%d obj__make_varL(varL::in,tmL::out)
%%d obj__make_varL(varL::out,tmL::in)

obj__make_varL([],[]).
obj__make_varL([Name|NameL],[$(Name)|TermL]) :-
	obj__make_varL(NameL,TermL).

%%d obj__theorem(gr::in,gr::in,gr::in)

% obj__theorem(theorem(Ref,Form,Deriv)) :-
%	ctl__reference(Ref),
% 	obj__formula(Form),
% 	obj__derivation(Deriv).
% obj__theorem(lemma(Ref,Form,Deriv)) :-
%	ctl__reference(Ref),
% 	obj__formula(Form),
% 	obj__derivation(Deriv).
% obj__theorem(corollary(Ref,Form,Deriv)) :-
%	ctl__reference(Ref),
% 	obj__formula(Form),
% 	obj__derivation(Deriv).

% obj.pl ends here

