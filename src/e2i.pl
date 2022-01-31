/*   Author: Robert Staerk <staerk@math.stanford.edu> */
/*  Created: 6/11/95, 9:11 PM */
/* Updated: Tue Feb 16 14:38:50 1999 */
/* Filename: e2i.pl */
/* Abstract: From the external to the internal representation. */

%%c
%%c External representations:
%%c
%%c We use the following meta symbols:
%%c
%%c <c> <x> <x1> ... <xn>	for arbitrary Prolog constants.
%%c <f>				for Prolog constants different from
%%c				= <> ~ & \/ => <=> ? all ex tt ff
%%c				succeeds fails terminates def by gr
%%c
%%c External terms are Prolog terms of the following form:
%%c
%%c <c>				[n(<c>,0)]
%%c ?<x>			$(<x>)
%%c <f>(ETerm,...,ETerm)	[n(<f>,n),ETerm^,...,ETerm^]
%%c
%%c External atomic goals are Prolog terms of the following form:
%%c
%%c <c>				[n(<c>,0)]
%%c <f>(ETerm,...,ETerm)	[n(<f>,n),ETerm^,...,ETerm^]
%%c
%%c External goals are Prolog terms of the following form:
%%c
%%c ETerm = ETerm		[=,ETerm^,ETerm^]
%%c EAtom		        EAtom^
%%c ~ EGoal			[~,EGoal^]
%%c EGoal & ... & EGoal		[&,EGoal^,...,EGoal^]
%%c EGoal \/ ... \/ EGoal	[\/,EGoal^,...,EGoal^]
%%c
%%c External formulas are Prolog terms of the following form:
%%c
%%c tt				[&]
%%c ff				[\/]
%%c <c>				[n(<c>,0)]
%%c ETerm = ... = ETerm		[=,ETerm^,...,Eterm^]
%%c Eterm <> Eterm		[<>,ETerm^,ETerm^]
%%c EAtom		        EAtom^
%%c succeeds EAtom		[succeeds,EAtom^]
%%c fails EAtom			[fails,EAtom^]
%%c terminates EGoal		[terminates,EGoal^]
%%c def succeeds EAtom		[def,[succeeds,EAtom^]]
%%c def fails EAtom 		[def,[fails,EAtom^]]
%%c def terminates EGoal	[def,[terminates,EGoal^]]
%%c ~ EForm			[~,EForm^]
%%c EForm & ... & EForm		[&,EForm^,...,EForm^]
%%c EForm \/ ... \/ EForm	[\/,EForm^,...,EForm^]
%%c EForm => EForm		[=>,EForm^,EForm^]
%%c EForm <=> EForm		[<=>,EForm^,EForm^]
%%c all <x>: EForm		@(all,[<x>],EForm^)
%%c ex <x>: EForm		@(ex,[<x>],EForm^)
%%c all[<x1>,...,<xn>]: EForm	@(all,[<x1>,...,<xn>],EForm^)
%%c ex[<x1>,...,<xn>]: EForm	@(ex,[<x1>,...,<xn>],EForm^)
%%c
%%c External derivations are Prolog terms of the following form:
%%c
%%c EStep
%%c [EStep,...,EStep]
%%c
%%c External derivation steps are Prolog terms:
%%c 
%%c EForm
%%c
%%c assume(EForm,
%%c  EDeriv,
%%c  EForm)
%%c
%%c contra(EForm,
%%c  EDeriv)
%%c
%%c indirect(~ EFform,
%%c  EDeriv)
%%c
%%c cases(EForm,
%%c  EDeriv,
%%c  EForm,
%%c  EDeriv,
%%c  EForm)
%%c
%%c cases([
%%c  case(EForm,
%%c   EDeriv),
%%c  ...,
%%c  case(EForm,
%%c   EDeriv)],
%%c  EForm)
%%c
%%c exist([<x1>,...,<xn>],EForm,
%%c  EDeriv,
%%c  EForm)
%%c
%%c exist(<x>,EForm,
%%c  EDeriv,
%%c  EForm)
%%c
%%c induction([EForm,..,EForm],
%%c  [step([<x1>,...,<xn>],[EForm,...,EForm],
%%c    EDerv,
%%c    EForm),
%%c   ...,
%%c   step([<x1>,...,<xn>],[EForm,...,EForm],
%%c    EDerv,
%%c    EForm)])
%%c
%%c EForm by lemma(Ref)
%%c EForm by theorem(Ref)
%%c EForm by corollary(Ref)
%%c EForm by axiom(Ref)
%%c EForm by completion
%%c EForm by sld
%%c EForm by introduction(Name,N)
%%c EForm by elimination(Name,N)
%%c EForm by existence(Name,N)
%%c EForm by uniqueness(Name,N)
%%c EForm by concatenation
%%c EForm by builtin
%%c EForm by addition
%%c EForm by gap
%%c EForm by because
%%c EForm by comment(_)
%%c EForm by new(Ref)
%%c EForm by [debug,fact,ind,indqf,unfold,case,ex,elim,tot,comp,auto(N)]
%%c


%%d e2i__formula_tag(gr::out)

e2i__formula_tag(=>).
e2i__formula_tag(~).
e2i__formula_tag(succeeds).
e2i__formula_tag(fails).
e2i__formula_tag(terminates).
e2i__formula_tag(gr).
e2i__formula_tag(def).
e2i__formula_tag(<>).
e2i__formula_tag(<=>).

%%d e2i__flat_op(gr::out)

e2i__flat_op(&).
e2i__flat_op(\/).
e2i__flat_op(=).

%%d e2i__keyword(gr::out)

e2i__keyword(?).
e2i__keyword(tt).
e2i__keyword(ff).
e2i__keyword(all).
e2i__keyword(ex).
e2i__keyword(assume).
e2i__keyword(contra).
e2i__keyword(cases).
e2i__keyword(case).
e2i__keyword(indirect).
e2i__keyword(exist).
e2i__keyword(by).
e2i__keyword(induction).
e2i__keyword(step).


% The predicate `e2i__expression(X,Expr)' transforms a Prolog term `X'
% into an expression `Expr' of the following kind:
%
%     $(_)
%     [Tag,Expr,...,Expr]
%     @(all,_,Expr)
%     @(ex,_,Expr)
%
% `Tag' satisfies:
%
%     `e2i__formula(Tag)' or 
%     `e2i__flat_op(Tag)' or
%     `Tag = n(_,_)' or 
%     `Tag = d(_,_)' or
%     `Tag = f(_,_)'.
%
% The predicate `e2i__expression(X,Expr)' checks whether `X' is a ground
% term, i.e., does not contain Prolog variables.
%
% Conjunctions `&', disjunctions `\/' and equations `=' are flattened.
%
% Nested quantifiers of the same kind are flattened, too.

%%d e2i__expression(gr:in,exp::out)

e2i__expression(X,Result) :-
	(	var(X) ->
		ctl__syntax([prolog,variable,in,formula]),
		Result = [n(undef,0)]
	;	X = (? Y) ->
		Result = $(Y)
	;	X = (A & B) ->
		e2i__con(B,[],Expr1L),
		e2i__con(A,Expr1L,Expr2L),
		e2i__add_op(Expr2L,&,Result)
	;	X = (A \/ B) ->
		e2i__dis(B,[],Expr1L),
		e2i__dis(A,Expr1L,Expr2L),
		e2i__add_op(Expr2L,\/,Result)
	;	X = (A = B) ->
		e2i__eq(B,[],Expr1L),
		e2i__eq(A,Expr1L,Expr2L),
		Result = [=|Expr2L]
	;	X = (all Y: A) ->
		e2i__forall(A,Var1L,Expr),
		e2i__concat_variables(Y,Var1L,Var2L),
		Result = @(all,Var2L,Expr)
	;	X = (ex Y: A) ->
		e2i__exists(A,Var1L,Expr),
		e2i__concat_variables(Y,Var1L,Var2L),
		Result = @(ex,Var2L,Expr)
	;	X = ff ->
		Result = [\/]
	;	X = tt ->
		Result = [&]
	;	functor(X,Name,N),
		(	e2i__formula_tag(Name) ->
			Tag = Name
		;	def__defined_fun(Name,N) -> 
			Tag = f(Name,N)
		;	def__defined_pred(Name,N) ->
			Tag = d(Name,N)
		; 	Tag = n(Name,N)
		),
		X =.. [Name|XL],
		e2i__expressionL(XL,ExprL),
		Result = [Tag|ExprL]
	).

%%d e2i__expressionL(grL::in,expL::out)

e2i__expressionL([],[]).
e2i__expressionL([X|XL],[Expr|ExprL]) :-
	e2i__expression(X,Expr),
	e2i__expressionL(XL,ExprL).

%%d e2i__con(gr::in,expL::in,expL::out)

e2i__con(X,Expr1L,Expr3L) :-
	(	var(X) ->
		ctl__syntax([prolog,variable,in,formula]),
		Expr3L = []
	;	X = (A & B) ->
		e2i__con(B,Expr1L,Expr2L),
		e2i__con(A,Expr2L,Expr3L)
	;	X = tt ->
		Expr3L = Expr1L
	;	e2i__expression(X,Expr),
		Expr3L = [Expr|Expr1L]
	).

%%d e2i__dis(gr::in,expL::in,expL::out)
 
e2i__dis(X,Expr1L,Expr3L) :-
	(	var(X) ->
		ctl__syntax([prolog,variable,in,formula]),
		Expr3L = []
	;	X = (A \/ B) ->
		e2i__dis(B,Expr1L,Expr2L),
		e2i__dis(A,Expr2L,Expr3L)
	;	X = ff ->
		Expr3L = Expr1L
	;	e2i__expression(X,Expr),
		Expr3L = [Expr|Expr1L]
	).

%%d e2i__add_op(expL::in,gr::in,exp::out)

e2i__add_op(ExprL,Op,Expr) :-
	(	ExprL = [Expr] -> 
		true
	; 	Expr = [Op|ExprL]
	).

%%d e2i__forall(gr::in,varL::out,exp::out)

e2i__forall(X,Var2L,Expr) :-
	(	var(X) ->
		ctl__syntax([prolog,variable,in,formula]),
		Expr = [&]
	;	X = (all Y: A) ->
		e2i__forall(A,Var1L,Expr),
		e2i__concat_variables(Y,Var1L,Var2L)
	;	Var2L = [],
		e2i__expression(X,Expr)
	).

%%d e2i__exists(gr::in,varL::out,exp::out)

e2i__exists(X,Var2L,Expr) :-
	(	var(X) ->
		ctl__syntax([prolog,variable,in,formula]),
		Expr = [&]
	;	X = (ex Y: A) ->
		e2i__exists(A,Var1L,Expr),
		e2i__concat_variables(Y,Var1L,Var2L)
	;	Var2L = [],
		e2i__expression(X,Expr)
	).

%%d e2i__concat_variables(gr::in,grL::in,grL::out)

e2i__concat_variables(X,L1,L2) :-
	(	var(X) ->
		ctl__syntax([prolog,variable,as,bound,variable]),
		L2 = []
	;	lst__append(X,L1,L2) ->
		true
	;	L2 = [X|L1]
	).


%%d e2i__eq(gr::in,expL::in,expL::out)

e2i__eq(X,Expr1L,Expr3L) :-
	(	var(X) ->
		ctl__syntax([prolog,variable,in,formula]),
		Expr3L = []
	;	X = (A = B) ->
		e2i__eq(B,Expr1L,Expr2L),
		e2i__eq(A,Expr2L,Expr3L)
	;	e2i__expression(X,Expr),
		Expr3L = [Expr|Expr1L]	
	).

%%d e2i__check_name(gr::in)

e2i__check_name(Name) :-
	(	e2i__keyword(Name) ->
		ctl__syntax([keyword,q(Name),at,wrong,place])
	;	true
	).

%%d e2i__check_term(gr::in)

e2i__check_term($(Name)) :-
	(	var(Name) ->
		ctl__syntax([prolog,variable,in,term])
	;	atomic(Name),
		e2i__check_name(Name)
	).
e2i__check_term([n(Name,_)|TermL]) :-
	e2i__check_name(Name),
	e2i__check_termL(TermL).
e2i__check_term([f(_,_)|TermL]) :-
	e2i__check_termL(TermL).
e2i__check_term($(Name)) :-
	\+ atomic(Name),
	ctl__syntax([q(Name),is,not,an,atomic,variable,name]).
e2i__check_term([d(Name,N)|_]) :-
	ctl__syntax([defined,predicate,Name/N,not,allowed,in,term]).
e2i__check_term(@(Quant,_,_)) :-
	ctl__syntax([quantifier,q(Quant),not,allowed,in,term]).
e2i__check_term([Tag|_]) :-
	atomic(Tag),
	ctl__syntax([q(Tag),not,allowed,in,term]).

%%d e2i__check_termL(grL::in)

e2i__check_termL([]).
e2i__check_termL([Term|TermL]) :-
	e2i__check_term(Term),
	e2i__check_termL(TermL).

%%d e2i__check_atomic_goal(gr::in)

e2i__check_atomic_goal([n(Name,_)|TermL]) :-
	e2i__check_name(Name),
	e2i__check_termL(TermL).
e2i__check_atomic_goal([d(Name,N)|_]) :-
	ctl__syntax([defined,predicate,Name/N,not,allowed,as,atomic,goal]).
e2i__check_atomic_goal([f(Name,N)|_]) :-
	ctl__syntax([defined,function,Name/N,not,allowed,as,atomic,goal]).
e2i__check_atomic_goal($(Name)) :-
	ctl__syntax([variable,q(? Name),not,allowed,as,atomic,goal]).
e2i__check_atomic_goal(@(Quant,_,_)) :-
	ctl__syntax([quantifier,q(Quant),not,allowed,in,atomic,goal]).
e2i__check_atomic_goal([Tag|_]) :-
	atomic(Tag),
	ctl__syntax([q(Tag),not,allowed,as,atomic,goal]).

%%d e2i__check_goal(gr::in)

e2i__check_goal([=,Term1,Term2]) :-		% equations
	e2i__check_term(Term1),
	e2i__check_term(Term2).
e2i__check_goal([n(Name,_)|TermL]) :-		% atomic goals
	e2i__check_name(Name),
	e2i__check_termL(TermL).
e2i__check_goal([~,Goal]) :-			% negated goals
	e2i__check_goal(Goal).
e2i__check_goal([&|GoalL]) :-			% conjunction: `true' is [&]
	e2i__check_goalL(GoalL).
e2i__check_goal([\/|GoalL]) :-			% disjunctions: `fail' is [\/]
	e2i__check_goalL(GoalL).
e2i__check_goal([d(Name,N)|_]) :-		% no defined predicates
	ctl__syntax([defined,predicate,Name/N,not,allowed,as,goal]).
e2i__check_goal([f(Name,N)|_]) :-		% no defined functions
	ctl__syntax([defined,function,Name/N,not,allowed,as,goal]).
e2i__check_goal($(Name)) :-			% no variables
	ctl__syntax([variable,q(? Name),not,allowed,as,goal]).
e2i__check_goal(@(Quant,_,_)) :-		% no quantifiers
	ctl__syntax([quantifier,q(Quant),not,allowed,in,goal]).
e2i__check_goal([=|ExprL]) :-			% `=' is binary
	\+ lst__two_elements(ExprL),
	ctl__syntax([q(=),is,binary,in,goals]).
e2i__check_goal([~|ExprL]) :-			% `~' is unary
	\+ lst__singleton(ExprL),
	ctl__syntax([q(~),is,unary]).
e2i__check_goal([Tag|_]) :-			% unknown tags
	atomic(Tag),
	\+ lst__member(Tag,[=,~,&,\/]),
	ctl__syntax([q(Tag),not,allowed,as,goal]).

%%d e2i__check_goalL(grL::in)

e2i__check_goalL([]).
e2i__check_goalL([Goal|GoalL]) :-
	e2i__check_goal(Goal),
	e2i__check_goalL(GoalL).

%%d e2i__check_sft_atom(gr::in)

e2i__check_sft_atom([succeeds,Atom]) :-		% succeeds
	e2i__check_atomic_goal(Atom).
e2i__check_sft_atom([fails,Atom]) :-		% fails
	e2i__check_atomic_goal(Atom).
e2i__check_sft_atom([terminates,Atom]) :-	% terminates
	e2i__check_atomic_goal(Atom).
e2i__check_sft_atom($(Name)) :-			% no variables
	ctl__syntax([variable,q(? Name),not,allowed,after,q(def)]).
e2i__check_sft_atom(@(Quant,_,_)) :-		% no quantifiers
	ctl__syntax([quantifier,q(Quant),not,allowed,after,q(def)]).
e2i__check_sft_atom([succeeds|ExprL]) :-	% `succeeds' is unary
	\+ lst__singleton(ExprL),
	ctl__syntax([q(succeeds),is,unary]).
e2i__check_sft_atom([fails|ExprL]) :-		% `fails' is unary
	\+ lst__singleton(ExprL),
	ctl__syntax([q(fails),is,unary]).
e2i__check_sft_atom([terminates|ExprL]) :-	% `terminates' is unary
	\+ lst__singleton(ExprL),
	ctl__syntax([q(terminates),is,unary]).
e2i__check_sft_atom([Tag|_]) :-			% unknown tags
	\+ lst__member(Tag,[succeeds,fails,terminates]),
	ctl__syntax([q(Tag),not,allowed,after,q(def)]).

%%d e2i__check_formula(gr::in)

e2i__check_formula([n(Name,_)|TermL]) :-	% predicate with clauses
	e2i__check_name(Name),
	e2i__check_termL(TermL).
e2i__check_formula([d(_,_)|TermL]) :-		% predicate as abbreviation
	e2i__check_termL(TermL).
e2i__check_formula([=|TermL]) :-		% equation
	e2i__check_termL(TermL).
e2i__check_formula([<>,Term1,Term2]) :-		% inequation
	e2i__check_term(Term1),
	e2i__check_term(Term2).
e2i__check_formula([gr,Term]) :-		% gr
	e2i__check_term(Term).
e2i__check_formula([succeeds,Atom]) :-		% succeeds
	e2i__check_atomic_goal(Atom).
e2i__check_formula([fails,Atom]) :-		% fails
	e2i__check_atomic_goal(Atom).
e2i__check_formula([terminates,Goal]) :-	% terminates
	e2i__check_goal(Goal).
e2i__check_formula([def,Form]) :-		% def
	e2i__check_sft_atom(Form).
e2i__check_formula([~,Form]) :-			% negation
	e2i__check_formula(Form).
e2i__check_formula([&|FormL]) :-		% conjunction
	e2i__check_formulaL(FormL).
e2i__check_formula([\/|FormL]) :-		% disjunction
	e2i__check_formulaL(FormL).
e2i__check_formula([=>,Form1,Form2]) :-		% implication
	e2i__check_formula(Form1),
	e2i__check_formula(Form2).
e2i__check_formula([<=>,Form1,Form2]) :-	% equivalence
	e2i__check_formula(Form1),
	e2i__check_formula(Form2).
e2i__check_formula(@(all,NameL,Form)) :-	% universial quantifier
	e2i__check_formula(Form),
	obj__varL(NameL).
e2i__check_formula(@(ex,NameL,Form)) :-		% existential quantifier
	e2i__check_formula(Form),
	obj__varL(NameL).
e2i__check_formula($(Name)) :-			% no variables
	ctl__syntax([variable,q(? Name),not,allowed,as,formula]).
e2i__check_formula([f(Name,N)|_]) :-		% no defined functions
	ctl__syntax([defined,function,Name/N,not,allowed,as,predicate]).
e2i__check_formula([<>|ExprL]) :-		% `<>' is binary
	\+ lst__two_elements(ExprL),
	ctl__syntax([q(<>),is,binary]).
e2i__check_formula([gr|ExprL]) :-		% `gr' is unary
	\+ lst__singleton(ExprL),
	ctl__syntax([q(gr),is,unary]).
e2i__check_formula([succeeds|ExprL]) :-		% `succeeds' is unary
	\+ lst__singleton(ExprL),
	ctl__syntax([q(succeeds),is,unary]).
e2i__check_formula([fails|ExprL]) :-		% `fails' is unary
	\+ lst__singleton(ExprL),
	ctl__syntax([q(fails),is,unary]).
e2i__check_formula([terminates|ExprL]) :-	% `terminates' is unary
	\+ lst__singleton(ExprL),
	ctl__syntax([q(terminates),is,unary]).
e2i__check_formula([def|ExprL]) :-		% `def' is unary
	\+ lst__singleton(ExprL),
	ctl__syntax([q(def),is,unary]).
e2i__check_formula([~|ExprL]) :-		% `~' is unary
	\+ lst__singleton(ExprL),
	ctl__syntax([q(~),is,unary]).
e2i__check_formula([=>|ExprL]) :-		% `=>' is binary
	\+ lst__two_elements(ExprL),
	ctl__syntax([q(=>),is,binary]).
e2i__check_formula([<=>|ExprL]) :-		% `<=>' is binary
	\+ lst__two_elements(ExprL),
	ctl__syntax([q(<=>),is,binary]).
e2i__check_formula(@(all,NameL,_)) :-		% bound variables
	\+ obj__varL(NameL),
	ctl__syntax([NameL,is,not,a,list,of,bound,variables]).
e2i__check_formula(@(ex,NameL,_)) :-		% bound variables
	\+ obj__varL(NameL),
	ctl__syntax([NameL,is,not,a,list,of,bound,variables]).
e2i__check_formula([Tag|_]) :-			% unknown tags
	atomic(Tag),
	\+ e2i__formula_tag(Tag),
	\+ e2i__flat_op(Tag),
	ctl__syntax([q(Tag),cannot,be,used,as,a,formula]).

%%d e2i__check_formulaL(grL::in)

e2i__check_formulaL([]).
e2i__check_formulaL([Form|FormL]) :-
	e2i__check_formula(Form),
	e2i__check_formulaL(FormL).

%%d e2i__formula(gr::in,fml::out)

e2i__formula(X,Form) :-
	(	e2i__expression(X,Form),
		(	\+ db__flag(check_everything)
		;	e2i__check_formula(Form)
		) -> true
	;	ctl__syntax([p(X),cannot,be,parsed]),
		Form = [&]
	).

%%d e2i__formulaL(gr::in,fmlL::out)

e2i__formulaL(X,Result) :-
	(	var(X) ->
		ctl__syntax([prolog,variable,in,formula]),
		Result = []
	;	X = [] ->
		Result = []
	;	X = [Y|YL] ->
		e2i__formula(Y,Form),
		e2i__formulaL(YL,FormL),
		Result = [Form|FormL]
	).


%%d e2i__derivation(gr::in,drv::out)

e2i__derivation(X,Deriv) :-
	(	e2i__derivation_steps(X,Deriv) ->
		true
	;	ctl__syntax([p(X),cannot,be,parsed])
	).


%%d e2i__derivation_steps(gr::in,drv::out)

e2i__derivation_steps(X,Result) :-
	(	var(X) ->
		ctl__syntax([prolog,variable,in,derivation]),
		Result = []
	;	lst__list_form(X) ->
		e2i__derivation_list(X,Result)
	;	e2i__derivation_step(X,Step),
		Result = [Step]
	).

%%d e2i__derivation_steps(grL::in,drv::out)

e2i__derivation_list(X,Result) :-
	(	var(X) ->
		ctl__syntax([prolog,variable,in,derivation]),
		Result = []
	;	X = [] ->
		Result = []
	;	X = [Y|YL] ->
		e2i__derivation_step(Y,Step),
		e2i__derivation_list(YL,Deriv),
		Result = [Step|Deriv]
	;	ctl__syntax([p(X),is,not,a,list,of,derivation,steps]),
		Result = []
	).

%%d e2i__derivation_step(gr::in,dstp::out)

e2i__derivation_step(S,Result) :-
	(	var(S) ->
		ctl__syntax([prolog,variable,in,derivation]),
		Result = [&]
	;	S = assume(X,Y,Z) ->
		e2i__formula(X,Form1),
		e2i__derivation(Y,Deriv),
		e2i__formula(Z,Form2),
		Result = assume(Form1,Deriv,Form2)
	;	S = contra(X,Y) ->
		e2i__formula(X,Form1),
		e2i__derivation(Y,Deriv),
		Result = contra(Form1,Deriv)
	;	S = cases(X1,Y1,X2,Y2,X) ->
	 	e2i__formula(X1,Form1),
		e2i__derivation(Y1,Deriv1),
		e2i__formula(X2,Form2),
		e2i__derivation(Y2,Deriv2),
		e2i__formula(X,Form),
		Result = cases([case(Form1,Deriv1),case(Form2,Deriv2)],Form)
	;	S = cases(XL,X) ->
		e2i__cases(XL,CaseL),
		e2i__formula(X,Form),
		Result = cases(CaseL,Form)
	; 	S = indirect(X,Y) ->
		e2i__formula(X,Form),
		e2i__derivation(Y,Deriv),
		Result = indirect(Form,Deriv)
	; 	S = exist(X,X1,Y,X2) ->
		e2i__bound_variables(X,VL),
		e2i__formula(X1,Form1),
		e2i__derivation(Y,Deriv),
		e2i__formula(X2,Form2),
		Result = exist(VL,Form1,Deriv,Form2)
	;	S = by(X,Y) ->
		e2i__formula(X,Form),
		Result = by(Form,Y)
	;	S = induction(XL,YL) ->
		e2i__formulaL(XL,FormL),
		e2i__inductionL(YL,StepL),
		Result = induction(FormL,StepL)
	; 	e2i__formula(S,Result)
	).

%%d e2i__bound_variables(gr::in,varL::out)

e2i__bound_variables(X,VarL) :-
	(	var(X) ->
		ctl__syntax([prolog,variable,in,derivation]),
		VarL = []
	;	atomic(X) ->
		VarL = [X]
	;	obj__varL(X) ->
		VarL = X
	;	ctl__syntax([X,is,not,a,list,of,bound,variables]),
		VarL = []
	).
	
%%d e2i__cases(grL::in,casL::out)

e2i__cases(C,Result) :-
	(	var(C) ->
		ctl__syntax([prolog,variable,in,derivation]),
		Result = []
	;	C = [] ->
		Result = []
	; 	C = [case(X,Y)|XL] ->
		e2i__formula(X,Form),
		e2i__derivation(Y,Deriv),
		e2i__cases(XL,CaseL),
		Result = [case(Form,Deriv)|CaseL]
	;	ctl__syntax([p(C),is,not,a,case,list]),
		Result = []
	).

%%d e2i__inductionL(grL::in,istpL::out)

e2i__inductionL(X,Result) :-
	(	var(X) ->
		ctl__syntax([prolog,variable,in,derivation]),
		Result = []
	;	X = [] ->
		Result = []
	;	X = [step(VL,YL,Y,Z)|XL] ->
		e2i__formulaL(YL,FormL),
		e2i__derivation(Y,Deriv),
		e2i__formula(Z,Form),
		e2i__inductionL(XL,StepL),
		Result = [step(VL,FormL,Deriv,Form)|StepL]
	;	ctl__syntax([p(X),is,not,a,list,of,induction,steps]),
		Result = []
	).

% e2i.pl ends here
