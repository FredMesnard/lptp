/*   Author: Robert Staerk <staerk@math.stanford.edu> */
/*  Created: Fri Dec  2 15:53:06 1994 */
/* Updated: Wed Jul 21 10:11:11 1999 */
/* Filename: io.pl */
/* Abstract: Input and output. */

% For every suffix X in [thm,tex,err,gr], a stream can be generated with
% 
% 	io__open(X,Path)	side effect: io__preamble(X,Path)
% 	
% Then, the following predicates are available:
% 
% 	db__is_open(X)
% 	io__tell(X)
% 	io__close(X)		side effect: io__postamble(X)


%%d db__is_open(gr::in)
%%d db__stream(gr::in,gr::out)

:- dynamic db__is_open/1.
:- dynamic db__stream/2.

db__is_open('DUMMY').
db__stream('DUMMY','DUMMY').

%%d io__open(gr::in,gr::in)

io__open(Suffix,Path) :-
	(	db__is_open(Suffix) ->
		io__close(Suffix)
	;	true
	),
	(	Suffix = tex,
		\+ db__flag(tex_output) ->
		true
	;	Suffix = thm,
		\+ db__flag(thm_output) ->
		true
	;	io__expand(Path,File),
		concat_atom([File,'.',Suffix],File_Suffix),
		io__get_stream(File_Suffix,write,Stream),
		assert(db__stream(Suffix,Stream)),
		assert(db__is_open(Suffix)),
		io__set_output(Stream),
		io__preamble(Suffix,Path)
	).

%%d io__tell(gr::in)

io__tell(Suffix) :-
	db__stream(Suffix,Stream),
	io__set_output(Stream).

%%d io__close(gr::in)

io__close(Suffix) :-
	(	db__is_open(Suffix) ->
		db__stream(Suffix,Stream),
		io__set_output(Stream),
		io__postamble(Suffix),
		close(Stream),
		retract(db__is_open(Suffix)),
		retract(db__stream(Suffix,Stream))
	;	true
	).

%%d io__closeL(grL::in)

io__closeL([]).
io__closeL([Suffix|SuffixL]) :-
	io__close(Suffix),
	io__closeL(SuffixL).

%%d io__close_output(gr::in)

io__close_output(File) :-
	io__close_output,
	ctl__message([File,'o.k']).

%%d io__close_output

io__close_output :-
	(	bagof(Suffix,
			(db__is_open(Suffix), \+ Suffix = 'DUMMY'),
			SuffixL) ->
		io__closeL(SuffixL)
	;	true
	).

%%d db__alias(gr::out,gr::out)

:- dynamic db__alias/2.

db__alias(lptp,Path) :- io__lptp_home(Path).
db__alias(lib,$(lptp)/lib).
db__alias(tmp,$(lptp)/tmp).
db__alias(tex,$(lptp)/tex).
db__alias(test,$(lptp)/test).
db__alias(examples,$(lptp)/examples).
db__alias(parser,$(lptp)/examples/parser).

%%d io__defined_alias(gr::in)

io__defined_alias(Alias) :- db__alias(Alias,_).

%%d io__set_alias(gr::in,gr::in)

io__set_alias(Alias,Path) :-
	(	io__defined_alias(Alias) ->
		ctl__warning([alias,q(Alias),is,redefined]),
		retract(db__alias(Alias,_)),
		assert(db__alias(Alias,Path))
	;	atomic(Alias) ->
		assert(db__alias(Alias,Path))
	;	ctl__error([q(Alias),is,not,atomic])
	).

%%d io__expand(gr::in,gr::out)

io__expand(Path1,Name) :-
	(	io__substitute(Path1,Path2) ->
		io__insert_sep(Path2,NameL),
		concat_atom(NameL,Name)
	;	ctl__error([cannot,expand,q(Path1),into,a,filename])
	).

%%d io__substitute(gr::in,gr::out)

io__substitute(Name,Name) :-
	atom(Name).
io__substitute(Path1/Name,Path2/Name) :-
	atom(Name),
	io__substitute(Path1,Path2).
io__substitute(Path1/ $(Alias),Path4/Path3) :-
	db__alias(Alias,Path2),
	io__expand(Path2,Path3),
	io__substitute(Path1,Path4).
io__substitute($(Alias),Path2) :-
	db__alias(Alias,Path1),
	io__expand(Path1,Path2).

%%d io__insert_sep(gr::in,grL::out).

io__insert_sep(Path/Name,NameL) :-
	io__insert_sep(Path,[Name],NameL).
io__insert_sep(Name,[Name]) :-
	atom(Name).

%%d io__insert_sep(gr::in,grL::in,grL::out)

io__insert_sep(Name,NameL,[Name,Sep|NameL]) :-
	atom(Name),
	io__path_sep(Sep).
io__insert_sep(Path/Name,Name1L,Name2L) :-
	io__path_sep(Sep),
	io__insert_sep(Path,[Name,Sep|Name1L],Name2L).

%%d io__path_last(gr::in,gr::in)

io__path_last(Name,Name) :-
	atom(Name).
io__path_last(_/Name,Name).

%%d io__preamble(gr::in,gr::in)

io__preamble(Suffix,Path) :-
	(	Suffix = tex -> 
		'TeX__preamble'(Path)
	;	true
	).

%%d io__postamble(gr::in)

io__postamble(Suffix) :-
	(	Suffix = tex ->
		'TeX__postamble'
	;	true
	).

% the user stream is treated differently


%%d io__open_user(gr::in)

io__open_user(Path) :-
	io__expand(Path,File),
	abolish(db__user_stream/1),
	concat_atom([File,'.err'],File_err),
	io__get_stream(File_err,write,Stream),
	assert(db__user_stream(Stream)).

%%d io__tell_user

io__tell_user :-
	db__user_stream(Stream),
	io__set_output(Stream).

%%d io__close_user

io__close_user :-
	db__user_stream(Stream),
	close(Stream),
	abolish(db__user_stream/1),
	io__original_user(User),
	assert(db__user_stream(User)).

%%d io__consult(gr::in,gr::in)

io__consult(Path,Suffix) :-
	io__expand(Path,File1),
	concat_atom([File1,'.',Suffix],File2),
	io__exec_file(File2).

%%d io__consult_thm(gr::in)

io__consult_thm(Path) :-
	io__consult(Path,thm),
	(	db__is_open(tex) ->
		io__tell(tex),
		write('!inputaux{'),
		io__path_last(Path,Name),
		write(Name), write('.aux}'), nl
	;	true
	).

% io.pl ends here

