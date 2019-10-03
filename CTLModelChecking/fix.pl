:- module(fix, _).

:- use_module(predExists_predForall2).
:- use_module(setops).


lfp(Z,E, S1) :-
	lfp_iteration([], Z, E, S1).

lfp_iteration(Prev, Z, E, Fix) :-
	apply_arg(Z,Prev,E,E1),	
	evalExpr(E1,Next),
	lfp_check_fix(Next,Prev,Z,E,Fix).

lfp_check_fix(E1,Prev,_,_,Fix) :-
	subset(E1,Prev),
	!,
	return_fixpoint(E1,Fix).
lfp_check_fix(E1,_,Z,E,Fix) :-
	lfp_iteration(E1, Z, E, Fix).


gfp(Z,E, S1) :-
	allStates(S),
	gfp_iteration(S, Z, E, S1).

gfp_iteration(Prev, Z, E, Fix) :-
	apply_arg(Z,Prev,E,E1),	
	evalExpr(E1,Next),
	gfp_check_fix(Next,Prev,Z,E,Fix).

gfp_check_fix(E1,Prev,_,_,Fix) :-
	subset(E1,Prev),
	!,
	return_fixpoint(E1,Fix).
gfp_check_fix(E1,_,Z,E,Fix) :-
	gfp_iteration(E1, Z, E, Fix).
	
return_fixpoint(X,X).


apply_arg(V,X,T,X) :-
        T == V,
        !.
apply_arg(_,_,T,T) :-
        var(T),
        !.
apply_arg(V,X,T,T1) :-
        nonvar(T),
        T =.. [F|Us],
        apply_all(Us,V,X,Vs),
        T1 =.. [F|Vs].

apply_all([U|Us],V,X,[W|Ws]) :-
        apply_arg(V,X,U,W),
        apply_all(Us,V,X,Ws).
apply_all([],_,_,[]).


%---------------------------------
	
evalExpr(union(S1,S2),S3) :-
	setunion(S1,S2,S3).
evalExpr(intersect(S1,S2),S3) :-
	setintersect(S1,S2,S3).
evalExpr(predExists(S1),S2) :-
	predExists(S1,S2).
evalExpr(predForall(S1),S2) :-
	predForall(S1,S2).
	
	
predExists(S1,S2) :-
	gamma(S1,Cs),
	getVars(Cs,Xs),
	predExists(Cs,Xs,Ds),
	alpha(Ds,S2).
	
predForall(S1,S2) :-
	gamma(S1,Cs),
	getVars(Cs,Xs),
	predForall(Cs,Xs,Ds),
	alpha(Ds,S2).
	