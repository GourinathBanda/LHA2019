%:- module(dmbdd, [dmbdd/3]).
:- module(duplVar, _).


:- use_module(chclibs(canonical)).
:- use_module(library(lists)).

%?- writeAtomEq(p(U,U,V,U,V,W),A,Es,0,K).

%A = p(U,_A,V,_B,_C,W),
%Es = [U=_A,U=_B,V=_C],
%K = 3 ? 


	
writeAtomEq(A,A1,Eqs,K0,K1) :-
	A =.. [P|Xs],
	removeDupls(Xs,Xs1,Eqs,K0,K1),
	A1 =.. [P|Xs1].
	
removeDupls([],[],[],K,K).
removeDupls([X|Xs],Xs2,[X=Y|Eqs],K0,K2) :-
	replaceDupl(X,Xs,K0,Y,Xs1),
	!,
	K1 is K0+1,
	removeDupls([X|Xs1],Xs2,Eqs,K1,K2).
removeDupls([X|Xs],[X|Xs1],Eqs,K0,K1) :-
	removeDupls(Xs,Xs1,Eqs,K0,K1).
	
	
newVar(K,VK) :-
	name('NewVar',Pre),
	name(K,Suff),
	append(Pre,Suff,Y),
	name(VK,Y).
	

replaceDupl(X1,[X2|Xs],K,XK,[XK|Xs]) :-
	X1 == X2,
	!,
	newVar(K,VK),
	melt('$VAR'(VK), XK).
replaceDupl(X,[X1|Xs],K,Y,[X1|Xs1]) :-
	replaceDupl(X,Xs,K,Y,Xs1).
