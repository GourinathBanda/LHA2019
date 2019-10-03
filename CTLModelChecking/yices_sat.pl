:- module(yices_sat,_).

:- use_module(ciao_yices).
:- use_module(library(lists)).
:- use_module(library(strings)).

yices_sat(E,Vars) :-
	expr2yices(E,S),
	% write_string(S),nl,nl,
	yicesl_mk_context(Ctx),
	yicesl_set_output_file("yikes.log"),
	defineVars(Ctx,Vars),
	concatStrings(["(assert ",S,")"],Expr),
	yicesl_read(Ctx,Expr,_),
	yicesl_read(Ctx,"(check)",_),
	!,
	yicesl_inconsistent(Ctx,Sat),
	yicesl_del_context(Ctx),
	Sat==0.
	
expr2yices((X;Y),S) :-
	expr2yices(X,S1),
	expr2yices(Y,S2),
	concatStrings(["(","or ",S1," ",S2,")"],S).
expr2yices((X,Y),S) :-
	expr2yices(X,S1),
	expr2yices(Y,S2),
	concatStrings(["(","and ",S1," ",S2,")"],S).
expr2yices((X<Y),S) :-
	expr2yices(X,S1),
	expr2yices(Y,S2),
	concatStrings(["(","< ",S1," ",S2,")"],S).
expr2yices((X>Y),S) :-
	expr2yices(X,S1),
	expr2yices(Y,S2),
	concatStrings(["(","> ",S1," ",S2,")"],S).
expr2yices((X=<Y),S) :-
	expr2yices(X,S1),
	expr2yices(Y,S2),
	concatStrings(["(","<= ",S1," ",S2,")"],S).
expr2yices((X>=Y),S) :-
	expr2yices(X,S1),
	expr2yices(Y,S2),
	concatStrings(["(",">= ",S1," ",S2,")"],S).
expr2yices((X*Y),S) :-
	expr2yices(X,S1),
	expr2yices(Y,S2),
	concatStrings(["(","* ",S1," ",S2,")"],S).
expr2yices((X+Y),S) :-
	expr2yices(X,S1),
	expr2yices(Y,S2),
	concatStrings(["(","+ ",S1," ",S2,")"],S).
expr2yices((X=Y),S) :-
	expr2yices(X,S1),
	expr2yices(Y,S2),
	concatStrings(["(","= ",S1," ",S2,")"],S).
expr2yices(neg(X),S) :-
	expr2yices(X,S1),
	concatStrings(["(","not ",S1,")"],S).
expr2yices('$VAR'(N),S) :-
	name(N,I),
	append("x",I,S).
expr2yices(A,S) :-
	atomic(A),
	name(A,S).
expr2yices(A,"") :-
	write('problem with '),
	write(A),
	nl.
	
	
defineVars(Ctx,[V|Vs]) :-
	expr2yices(V,S),
	concatStrings(["(define ",S,"::real)"],Decl),
	yicesl_read(Ctx,Decl,_),
	defineVars(Ctx,Vs).
defineVars(_,[]).

concatStrings([],"").
concatStrings([S|Ss],R) :-
	concatStrings(Ss,R1),
	append(S,R1,R).