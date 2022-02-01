/*   Author: Robert Staerk <staerk@saul.cis.upenn.edu> */
/*  Created: Fri Jan 19 12:01:32 1996 */
/* Updated: Mon Feb 15 16:10:13 1999 */
/* Filename: ctl.pl */
/* Abstract: Flags, warnings, error messages, initialization, theorems,
   lemmas, corollaries, axioms. */

%%c
%%c The proof files (.pr) contain the following commands:
%%c
%%c :- initialize.
%%c
%%c :- needs_thm(Path).
%%c :- needs_gr(Path).
%%c
%%c :- thm_file(Path).
%%c :- tex_file(Path).
%%c :- prt_file(Path).
%%c :- ma_file(Path).
%%c
%%c :- axiom(Ref,EForm).
%%c
%%c :- theorem(Ref,EForm,EDeriv).
%%c :- lemma(Ref,EForm,EDeriv).
%%c :- corollary(Ref,EForm,EDeriv).
%%c
%%c :- definition_pred(<r>,n,
%%c  all [<x1>,...,<xn>]: <r>(?<x1>,...,?<xn>) <=> Eform).
%%c
%%c :- definition_fun(<f>,n,
%%c  all [<x1>,...,<xn>,<y>]: EForm1 =>
%%c   (<f>(?<x1>,...,?<xn>) = ?<y> <=> EForm2),
%%c  existence by <Thm>(Ref1),
%%c  uniqueness by <Thm>(Ref2)
%%c ).
%%c
%%c :- bye(File).
%%c
%%c The theorem files (.thm) contain the following commands:
%%c
%%c :- assert_fact(theorem,Ref,Form).
%%c :- assert_fact(lemma,Ref,Form).
%%c :- assert_fact(corollary,Ref,Form).
%%c :- assert_fact(axiom,Ref,Form).
%%c
%%c :- assert_pred(Atom,Form).
%%c :- assert_fun(Term,Form,Form).
%%c
%%c The program files (.gr) contain the following commands:
%%c
%%c :- assert_clauses(Pred,ClauseL)
%%c
%%c The internal database contains the following facts:
%%c
%%c db__theorem(Ref,Form).
%%c db__lemma(Ref,Form).
%%c db__corollary(Ref,Form).
%%c db__axiom(Ref,Form).
%%c db__pred(Atom,Form).
%%c db__fun(Term,Form,Form).
%%c db__clauses(Pred,ClauseL).
%%c


%% Flags

%%d db__flag(gr::out)

:- dynamic db__flag/1.

db__flag('DUMMY').
db__flag(check_everything).			% cautious
db__flag(fail_on_error).			% fail in case of an error
db__flag(unique_names).				% unique names in theorems
db__flag(assert_facts).				% assert facts
db__flag(report_because).			% report "because"
db__flag(tex_output).				% create TeX output
db__flag(thm_output).				% write the .thm files

%db__flag(print_names).				% print names of theorems
%db__flag(debug).				% debug mode
%db__flag(write_dependencies).			% write dependencies on .thm

% The following flags are set by the system. Do not change them.

%db__flag(global_error).			% there is a global error

%%d ctl__set_flag(gr::in)

ctl__set_flag(Flag) :-
	(	db__flag(Flag) -> 
		true
	; 	assert(db__flag(Flag))
	).

%%d ctl__unset_flag(gr::in)

ctl__unset_flag(Flag) :-
	(	db__flag(Flag) -> 
		retract(db__flag(Flag))
	; 	true
	).

%%d ctl__plain
%%d ctl__pedantic
%%d ctl__draft
%%d ctl__show

ctl__pedantic :-
	ctl__set_flag(check_everything),
	ctl__set_flag(fail_on_error),
	ctl__set_flag(unique_names),
	ctl__set_flag(assert_facts),
	ctl__set_flag(report_because),
	ctl__set_flag(tex_output),
	ctl__set_flag(thm_output),
	ctl__unset_flag(print_names).

ctl__plain :-
	ctl__unset_flag(check_everything),
	ctl__set_flag(fail_on_error),
	ctl__unset_flag(unique_names),
	ctl__set_flag(assert_facts),
	ctl__unset_flag(report_because),
	ctl__unset_flag(tex_output),
	ctl__set_flag(thm_output),
	ctl__unset_flag(print_names).

ctl__draft :-
	ctl__set_flag(check_everything),
	ctl__unset_flag(fail_on_error),
	ctl__unset_flag(unique_names),
	ctl__unset_flag(assert_facts),
	ctl__unset_flag(report_because),
	ctl__unset_flag(tex_output),
	ctl__unset_flag(thm_output),
	ctl__unset_flag(print_names).

ctl__show :-
	ctl__unset_flag(check_everything),
	ctl__unset_flag(fail_on_error),
	ctl__set_flag(unique_names),
	ctl__set_flag(assert_facts),
	ctl__unset_flag(report_because),
	ctl__unset_flag(tex_output),
	ctl__unset_flag(thm_output),
	ctl__set_flag(print_names).

%%d ctl__warning(grL::in)

ctl__warning(L) :-
	io__tell_user,
	write('! LPTP-Warning:'),
	ctl__write_phrase(L).

%%d ctl__message(grL::in)

ctl__message(L) :-
	io__tell_user,
	write('! LPTP-Message:'),
	ctl__write_phrase(L).

%%d ctl__syntax(grL::in)

ctl__syntax(L) :-
	ctl__set_flag(global_error),
	io__tell_user,
	write('! LPTP-Syntax:'),
	ctl__write_phrase(L).

%%d ctl__error(grL::in)

ctl__error(L) :-
	(	db__flag(global_error) ->
		true
	;	ctl__set_flag(global_error),
		io__tell_user,
		write('! LPTP-Error:'),
		ctl__write_phrase(L)	
	),
	\+ db__flag(fail_on_error).

%%d ctl__write_phrase(grL::in)

ctl__write_phrase([]) :-
	write('.'), nl.
ctl__write_phrase([X|L]) :-
	write(' '), 
	(	var(X) ->
		write(X)
	;	X = p(Y) ->
		nl, prt__write(Y)
	;	X = q(Y) ->
		write('`'), write(Y), write('\'')
	;	X = e(Expr) ->
		i2e__expression(Expr,Y), nl, prt__write(Y)
	;	write(X)
	),
	ctl__write_phrase(L).

%% Theorems, lemmas, corollaries, axioms

%%d db__theorem(gr::out,fml::out)
%%d db__lemma(gr::out,fml::out)
%%d db__corollary(gr::out,fml::out)
%%d db__axiom(gr::out,fml::out)

:- dynamic db__theorem/2.
:- dynamic db__lemma/2.
:- dynamic db__corollary/2.
:- dynamic db__axiom/2.

db__theorem('DUMMY',[&]).
db__lemma('DUMMY',[&]).
db__corollary('DUMMY',[&]).
db__axiom('DUMMY',[&]).

%%d theorem(gr::in,gr::in,gr::in)
%%d lemma(gr::in,gr::in,gr::in)
%%d corollary(gr::in,gr::in,gr::in)

theorem(X,Y,Z)   :- ctl__module(theorem,X,Y,Z).
lemma(X,Y,Z)     :- ctl__module(lemma,X,Y,Z).
corollary(X,Y,Z) :- ctl__module(corollary,X,Y,Z).

%%d axiom(gr::in,gr::in)

axiom(Ref,X) :-
	ctl__unset_flag(global_error),
	ctl__reference_err(Ref),
	e2i__formula(X,Form),
	ctl__assert_and_print_fact(axiom,Ref,Form,[],X,'DUMMY').

%%d ctl__exists_fact(gr::in,gr::in)

ctl__exists_fact(theorem,Ref)   :- db__theorem(Ref,_).
ctl__exists_fact(lemma,Ref)     :- db__lemma(Ref,_).
ctl__exists_fact(corollary,Ref) :- db__corollary(Ref,_).
ctl__exists_fact(axiom,Ref)     :- db__axiom(Ref,_).

%%d ctl__do_assert(gr::in,gr::in,fml::in)

ctl__do_assert(theorem,Ref,Form)   :- assert(db__theorem(Ref,Form)).
ctl__do_assert(lemma,Ref,Form)     :- assert(db__lemma(Ref,Form)).
ctl__do_assert(corollary,Ref,Form) :- assert(db__corollary(Ref,Form)).
ctl__do_assert(axiom,Ref,Form)     :- assert(db__axiom(Ref,Form)).

%%d ctl__module(gr::in,gr::in,gr::in,gr::in)

ctl__module(Kind,Ref,X,Y) :-
	ctl__unset_flag(global_error),
	ctl__reference_err(Ref),
	(	db__flag(print_names) ->
		io__tell_user,
		write(Kind), write(' '), write(Ref), nl
	;	true
	),
	e2i__formula(X,Form),
	e2i__derivation(Y,Deriv),
	(	db__flag(global_error) ->
		Fact =.. [Kind,Ref],
		ctl__warning([Fact,is,not,checked])
	;	pr__proof(Deriv,[],[],Gamma),
		pr__derivable_err([],Gamma,Form),
		ctl__assert_and_print_fact(Kind,Ref,Form,Deriv,X,Y),
		dep__write_fact(Kind,Ref,Deriv)
	).

%%d ctl__assert_and_print_fact(gr::in,gr::in,fml::in,drv::in,gr::in,gr::in)

ctl__assert_and_print_fact(Kind,Ref,Form,Deriv,X,Y) :-
	(	db__flag(global__error) ->
		Fact =.. [Kind,Ref],
		ctl__warning([Fact,is,not,asserted])
	;	ctl__assert_new_fact(Kind,Ref,Form),
		eq__add_free(Form,[],VarL),
		(	VarL = [] ->
			true
		;	Fact = [Kind,Ref],
			ctl__warning([free,variables,VarL,in,Fact])
		),
		ctl__write_tex(Kind,Ref,Form,Deriv),
		ctl__write_thm(Kind,Ref,Form),
		(	db__is_open(prt) ->
			io__tell(prt),
			prt__fact(Kind,Ref,X,Y)
		;	true
		)
	).

%% ctl__write_tex(gr::in,gr::in,fml::in,drv::in)

ctl__write_tex(Kind,Ref,Form,Deriv) :-
	(	db__is_open(tex), 
		db__flag(tex_output) ->
		io__tell(tex),
		'TeX__write_fact'(Kind,Ref,Form,Deriv)
	; 	true
	).

%%d ctl__write_thm(gr::in,gr::in,fml::in)

ctl__write_thm(Kind,Ref,Form) :-
	(	db__is_open(thm), 
		\+ ctl__tmp_name(Ref),
		db__flag(thm_output) -> 
		io__tell(thm),
		write(':- '),
		writeq(assert_fact(Kind,Ref,Form)),
		write('.'), nl
	; 	true
	).

%%d ctl__tmp_name(gr::in)

ctl__tmp_name(tmp:_).

%%d assert_fact(gr::in,gr::in,fml::in)

assert_fact(Kind,Ref,Form) :- 
	(	db__flag(check_everything) ->
		(	obj__formula(Form) ->
			true
		;	Fact =.. [Kind,Ref],
			ctl__warning([corrupted,formula,in,Kind,Fact])
		)
	;	true),
	ctl__assert_new_fact(Kind,Ref,Form).

%%d ctl__assert_new_fact(gr::in,gr::in,fml::in)

ctl__assert_new_fact(Kind,Ref,Form) :-
	(	db__flag(unique_names),
		ctl__exists_fact(Kind,Ref) ->
		Fact =.. [Kind,Ref],
		ctl__warning([Fact,already,exists])
	;	db__flag(assert_facts) ->
		ctl__do_assert(Kind,Ref,Form)
	;	true
	).

%%d initialize

initialize :-
	abolish(db__theorem/2),
	abolish(db__lemma/2),
	abolish(db__corollary/2),
	abolish(db__axiom/2),
	abolish(db__pred/2),
	abolish(db__fun/3),
	abolish(db__clauses/2),
	abolish(db__depends/2),
	assert(db__theorem('DUMMY',[&])),
	assert(db__lemma('DUMMY',[&])),
	assert(db__corollary('DUMMY',[&])),
	assert(db__axiom('DUMMY',[&])),
	assert(db__pred([d('DUMMY',0)],[&])),
	assert(db__fun([f('DUMMY',0)],[&],[&])),
	assert(db__clauses(n(fail,0),[])),
	assert(db__depends('DUMMY',[])).

%% Print all theorems, lemmas, corollaries and axioms

%%d ctl__print_facts(gr::in)

ctl__print_facts(Ref) :-
	io__tell_user,
	ctl__unset_flag(global_error),
	ctl__reference_err(Ref),
	\+ ctl__print_all_facts(Ref).

%%d ctl__print_all_factss(gr::in)

ctl__print_all_facts(Ref1) :-
	db__theorem(Ref2,Form),
	ctl__print_fact(theorem,Ref1,Ref2,Form),
	fail.
ctl__print_all_facts(Ref1) :-
	db__lemma(Ref2,Form),
	ctl__print_fact(lemma,Ref1,Ref2,Form),
	fail.
ctl__print_all_facts(Ref1) :-
	db__corollary(Ref2,Form),
	ctl__print_fact(corollary,Ref1,Ref2,Form),
	fail.
ctl__print_all_facts(Ref1) :-
	db__axiom(Ref2,Form),
	ctl__print_fact(axiom,Ref1,Ref2,Form),
	fail.

%%d ctl__print_fact(gr::in,gr::in,gr::in,fml::in)

ctl__print_fact(Kind,Ref1,Ref2,Form) :-
	ctl__reference_subset(Ref1,Ref2),
	nl, write(Kind), 
	write('('),
	write(Ref2),
	write(')'), nl,
	i2e__expression(Form,Y),
	prt__write(Y),
	write('.'), nl.

%%d ctl__prt_definition(gr::in)

ctl__prt_definition(X1) :-
	io__tell_user,
	ctl__unset_flag(global_error),
	e2i__formula(X1,Form1),
	e2i__check_sft_atom(Form1),
	(	Form1 = [Op,Atom], 
		obj__sft_op(Op),
		bi__user_defined_atom(Atom) ->
		cmp__sft_formula(Op,Atom,Form2)
	;	Form1 = [Op,Atom], 
		obj__sft_op(Op),
		bi__typed(Atom) ->
		bi__eval(Atom,Goal),
		cmp__op_goal(Op,Goal,Form2)
	;	Form1 = [d(_,_)|_] ->
		def__pred_formula(Form1,Form2)
	),
	i2e__expression(Form2,X2),
	nl, prt__write(X2), nl.

%%d ctl__reference_err(gr::in)

ctl__reference_err(Ref) :-
	(	ctl__reference(Ref) ->
		true
	;	ctl__syntax([q(Ref),is,not,a,correct,reference])
	).
%%d ctl__reference(gr::in)

ctl__reference(X) :-
	(	var(X) ->
		ctl__syntax([prolog,variable,in,reference])
	;	X = (Y:Z) ->
		atomic(Y),
		ctl__reference(Z)
	;	atomic(X)
	).

%%d ctl__reference_member(gr::out,gr:;in)
%%d ctl__reference_member(gr::in,gr:;in)

ctl__reference_member(Ref,Ref) :-
	atomic(Ref).
ctl__reference_member(Ref,Ref:_).
ctl__reference_member(Ref1,_:Ref2) :-
	ctl__reference_member(Ref1,Ref2).

%%d ctl__reference_subset(gr::in,gr::in)

ctl__reference_subset(Ref1,Ref2) :-
	\+ ctl__reference_subset_not(Ref1,Ref2).

%%d ctl__reference_subset_not(gr::in,gr::in)

ctl__reference_subset_not(Ref1,Ref2) :-
	ctl__reference_member(Ref,Ref1),
	\+ ctl__reference_member(Ref,Ref2).

%%d db__marked_assumption(gr::out)

:- dynamic db__marked_assumption/1.

db__marked_assumption([&]).

%%d ctl__assert_marked_assumption(gr::in)

ctl__assert_marked_assumption(X) :-
	e2i__formula(X,Form),
	retract(db__marked_assumption(_)),
	assert(db__marked_assumption(Form)),
	io__tell_user,
	nl,
	ctl__message([X,is,marked]).

%%d db__depends(gr::out,grL::out)

:- dynamic db__depends/2.

db__depends('DUMMY',[]).

% ctl.pl ends here

