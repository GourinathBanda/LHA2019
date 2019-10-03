:- module(negatedNormalForm_CTL,_).

nnf(true, true).

nnf(false, false).

nnf(neg(true),false).

nnf(neg(false),true).

nnf(prop(P),prop(P)).

nnf(neg(prop(P)),neg(prop(P))).

%nnf(neg(neg(prop(P))),prop(P)).

nnf(ax(F),ax(F_nnf)) :-
	nnf(F,F_nnf).

nnf(neg(ax(F)),ex(NegF_nnf)) :-
	nnf(neg(F),NegF_nnf).
	
nnf(ex(F),ex(F_nnf)) :-
	nnf(F,F_nnf).

nnf(neg(ex(F)),ax(NegF_nnf)) :-
	nnf(neg(F),NegF_nnf).
	

nnf(af(F), af(F_nnf)) :-
	nnf(F,F_nnf).
	
nnf(neg(af(F)), eg(NegF_nnf)) :-
	nnf(neg(F),NegF_nnf).

nnf(ag(F), ag(F_nnf)) :-
	nnf(F,F_nnf).
	
nnf(neg(ag(F)), ef(NegF_nnf)) :-
	nnf(neg(F),NegF_nnf).

nnf(ar(F1,F2), ar(F1_nnf,F2_nnf)) :-
	nnf(F1,F1_nnf),
	nnf(F2,F2_nnf).
	
nnf(neg(ar(F1,F2)), eu(NegF1_nnf,NegF2_nnf)) :-
	nnf(neg(F1),NegF1_nnf),
	nnf(neg(F2),NegF2_nnf).

nnf(au(F1,F2), au(F1_nnf,F2_nnf)) :-
	nnf(F1,F1_nnf),
	nnf(F2,F2_nnf).
	
nnf(neg(au(F1,F2)), er(NegF1_nnf,NegF2_nnf)) :-
	nnf(neg(F1),NegF1_nnf),
	nnf(neg(F2),NegF2_nnf).

nnf(ef(F), ef(F_nnf)) :-
	nnf(F,F_nnf).
	
nnf(neg(ef(F)), ag(NegF_nnf)) :-
	nnf(neg(F),NegF_nnf).

nnf(eg(F), eg(F_nnf)) :-
	nnf(F,F_nnf).
	
nnf(neg(eg(F)), af(NegF_nnf)) :-
	nnf(neg(F),NegF_nnf).

nnf(er(F1,F2), er(F1_nnf,F2_nnf)) :-
	nnf(F1,F1_nnf),
	nnf(F2,F2_nnf).
	
nnf(neg(er(F1,F2)), au(NegF1_nnf,NegF2_nnf)) :-
	nnf(neg(F1),NegF1_nnf),
	nnf(neg(F2),NegF2_nnf).

nnf(eu(F1,F2), eu(F1_nnf,F2_nnf)) :-
	nnf(F1,F1_nnf),
	nnf(F2,F2_nnf).
	
nnf(neg(eu(F1,F2)), ar(NegF1_nnf,NegF2_nnf)) :-
	nnf(neg(F1),NegF1_nnf),
	nnf(neg(F2),NegF2_nnf).


nnf(and(F,G), and(F_nnf,G_nnf)) :-
	nnf(F,F_nnf),
	nnf(G,G_nnf).
	
nnf(neg(and(F,G)), or(NegF_nnf,NegG_nnf)) :-
	nnf(neg(F),NegF_nnf),
	nnf(neg(G),NegG_nnf).

	
nnf(or(F,G), or(F_nnf,G_nnf)) :-
	nnf(F,F_nnf),
	nnf(G,G_nnf).
	
nnf(neg(or(F,G)), and(NegF_nnf,NegG_nnf)) :-
	nnf(neg(F),NegF_nnf),
	nnf(neg(G),NegG_nnf).


nnf(implies(F,G), or(NegF_nnf,G_nnf)) :-
	nnf(neg(F),NegF_nnf),
	nnf(G,G_nnf).
	
nnf(neg(implies(F,G)), NegImplies_F_G) :-
	nnf(implies(F,G),Implies_F_G_nnf),
	nnf(neg(Implies_F_G_nnf),NegImplies_F_G).
	
nnf(neg(neg(F)),F_nnf) :-
	nnf(F,F_nnf),!.