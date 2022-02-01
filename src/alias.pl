/*   Author: Robert Staerk <staerk@math.stanford.edu> */
/*  Created: Fri Dec  2 15:51:07 1994 */
/*  Updated: Wed Jul 21 14:06:12 1999 */
/* Filename: alias.pl */
/* Abstract: Some handy abbreviations. */

draft :-		ctl__draft.
pedantic :-		ctl__pedantic.
plain :-		ctl__plain.
show :-			ctl__show.

set(Flag) :-		ctl__set_flag(Flag).
unset(Flag) :-		ctl__unset_flag(Flag).

bye :- 			io__close_output.
bye(File) :- 		io__close_output(File).
needs_gr(Path) :- 	io__consult(Path,gr).
needs_thm(Path) :- 	io__consult_thm(Path).
prt_file(Path) :- 	io__open(prt,Path).
tex_file(Path) :- 	io__open(tex,Path).
thm_file(Path) :- 	io__open(thm,Path).
set(Alias,Path) :-	io__set_alias(Alias,Path).
exec(File) :-		io__exec_file(File).
check(Path) :-		once(io__consult(Path,pr)).

def(EForm) :-		once(ctl__prt_definition(EForm)).
facts(PTerm) :- 	ctl__print_facts(PTerm).
by(EForm,Opt) :-	tac__by(EForm,Opt).
compile_gr(Path) :- 	once(gnd__compile(Path)).
mark(EForm) :-          ctl__assert_marked_assumption(EForm).

e2i(EForm,Form) :- 	e2i__formula(EForm,Form).
e2id(EDeriv,Deriv) :- 	e2i__derivation(EDeriv,Deriv).
i2e(Form,EForm) :- 	i2e__expression(Form,EForm).
ipp(Form) :-		i2e__expression(Form,X), prt__write(X), nl.
pp(PTerm) :- 		prt__write(PTerm).

depends(Fact) :-	dep__print_dependencies(Fact).

banner :- 
	write('LPTP, Version 1.06, July 21, 1999.'), nl,
	write('Copyright (C) 1999 by Robert F. Staerk'), nl.

:- initialization(banner).

% alias.pl ends here

