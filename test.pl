:- op(600, xfy, <->).
:- op(575, xfy, ->).    
:- op(550, xfy, \/).
:- op(525, xfy, /\).
:- op(500, fy,  ¬).

binaryOperatorp((/\)).
binaryOperatorp((\/)).
binaryOperatorp((->)).
binaryOperatorp((<->)).

unaryOperatorp((¬)).

% Propositional constants: any atom that isn't a connective symbol
constantp(P) :-
    atom(P),
    \+ binaryOperatorp(P),
    \+ unaryOperatorp(P).

% Well-formed formulas
propositionp(P) :- var(P), !, fail.
propositionp(P) :- constantp(P), !.
propositionp(P) :-
    P =.. [Op, P1],
    unaryOperatorp(Op), !,
    propositionp(P1).
propositionp(P) :-
    P =.. [Op, P1, P2],
    binaryOperatorp(Op),
    propositionp(P1),
    propositionp(P2).


formula2cnf(P, _) :-
    \+ propositionp(P), !,
    domain_error(proposition, P).
formula2cnf(P, L) :-
    cnf(P, CNF),
    conj_list(CNF, Conjuncts),        % split on /\
    maplist(disj_list, Conjuncts, Ls),% split each conjunct on \/
    maplist(sort, Ls, Sets),          % each clause as a set of literals
    exclude(tautology, Sets, Clauses0),
    sort(Clauses0, Clauses),          % remove duplicate clauses
    findall(I-C, nth1(I, Clauses, C), L).

% cnf(+Formula, -CNF): CNF as a formula built from /\, \/ and ¬
cnf(P, CNF) :-
    elim(P, P1),     % 1. remove <-> and ->
    nnf(P1, P2),     % 2. push ¬ down to the atoms
    dist(P2, CNF).   % 3. distribute \/ over /\

/* Step 1: eliminate biconditional and implication */
elim(P <-> Q, (¬P1 \/ Q1) /\ (¬Q1 \/ P1)) :- !, 
    elim(P, P1), 
    elim(Q, Q1).
elim(P -> Q,  ¬P1 \/ Q1)                  :- !, 
    elim(P, P1), 
    elim(Q, Q1).
elim(P /\ Q,  P1 /\ Q1)                   :- !, 
    elim(P, P1), 
    elim(Q, Q1).
elim(P \/ Q,  P1 \/ Q1)                   :- !, 
    elim(P, P1), 
    elim(Q, Q1).
elim(¬P,      ¬P1)                        :- !, 
    elim(P, P1).
elim(A, A).

/* Step 2: negation normal form */
nnf(¬(¬P),     R)        :- !, 
    nnf(P, R).                  % ¬¬P ≡ P
nnf(¬(P /\ Q), R1 \/ R2) :- !, 
    nnf(¬P, R1), 
    nnf(¬Q, R2).   % De Morgan
nnf(¬(P \/ Q), R1 /\ R2) :- !, 
    nnf(¬P, R1), 
    nnf(¬Q, R2).   % De Morgan
nnf(P /\ Q,    R1 /\ R2) :- !, 
    nnf(P, R1), 
    nnf(Q, R2).
nnf(P \/ Q,    R1 \/ R2) :- !, 
    nnf(P, R1), 
    nnf(Q, R2).
nnf(L, L).                                                 % literal

/* Step 3: distribute \/ over /\ */
dist(P /\ Q, R1 /\ R2) :- !, 
    dist(P, R1), 
    dist(Q, R2).
dist(P \/ Q, R)        :- !, 
    dist(P, P1), 
    dist(Q, Q1), 
    dist_or(P1, Q1, R).
dist(L, L).

dist_or(A /\ B, C, R1 /\ R2) :- !, 
    dist_or(A, C, R1), 
    dist_or(B, C, R2).  % (A∧B)∨C
dist_or(A, B /\ C, R1 /\ R2) :- !, 
    dist_or(A, B, R1), 
    dist_or(A, C, R2).  % A∨(B∧C)
dist_or(A, B, A \/ B).

/* Helpers: flatten a CNF formula into lists */
conj_list(A /\ B, L) :- !, 
    conj_list(A, LA), 
    conj_list(B, LB), 
    append(LA, LB, L).
conj_list(A, [A]).

disj_list(A \/ B, L) :- !, 
    disj_list(A, LA), 
    disj_list(B, LB), 
    append(LA, LB, L).
disj_list(A, [A]).

% A clause containing both p and ¬p is always true
tautology(Clause) :- member(L, Clause), member(¬L, Clause), !.

