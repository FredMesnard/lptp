:- compile_gr(test/gr/clauses1).
:- compile_gr(test/gr/clauses2).
:- needs_gr(test/gr/clauses1).
:- needs_gr(test/gr/clauses2).

:- db__clauses(n(a,0),[
 clause([n(a,0)],
  [&],
  []/0),
 clause([n(a,0)],
  [&,[n(b,0)],[n(c,0)],[n(d,0)]],
  []/0),
 clause([n(a,0)],
  [&],
  []/0),
 clause([n(a,0)],
  [&,[\/,[&,[n(b,0)],[n(c,0)],[n(d,0)]],[&,[~,[&,[n(b,0)],[n(c,0)]]],[n(e,0)]]],[n(f,0)]],
  []/0),
 clause([n(a,0)],
  [&,[n(b,0)],[\/,[n(c,0)],[n(d,0)],[n(e,0)]],[~,[n(f,0)]]],
  []/0),
 clause([n(a,0)],
  [&,[~,[&,[n(b,0)],[n(c,0)],[n(d,0)]]],[~,[n(e,0)]]],
  []/0)
]).

:- db__clauses(n(member,2),[
 clause([n(member,2),var(x),[n('.',2),var(x),var(0)]],
  [&],
  [x,0]/1),
 clause([n(member,2),var(x),[n('.',2),var(0),var(l)]],
  [n(member,2),var(x),var(l)],
  [x,0,l]/1)
]).

:- db__clauses(n(member_check,2),[
 clause([n(member_check,2),var(x),[n('.',2),var(y),var(l)]],
  [\/,[&,[=,var(x),var(y)]],[&,[~,[=,var(x),var(y)]],[n(member_check,2),var(x),var(l)]]],
  [x,y,l]/0)
]).

:- bye(test_gr).

    
