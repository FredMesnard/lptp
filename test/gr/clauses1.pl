a.
a :- b, c, d.
a :- true.
a :- (b, c -> d; e), f.
a :- b, (c; d; e), not f.
a :- not (b, c, d), not e.

