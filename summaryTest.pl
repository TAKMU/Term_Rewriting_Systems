:- encoding(utf8).

:- op(600, xfy, <->).
:- op(575, xfy, ->).    
:- op(550, xfy, \/).
:- op(525, xfy, /\).
:- op(500, fy,  ¬).

:- ensure_loaded('test.pl').

% ============================================================================
% Semantic Verification Engine (Exhaustive Truth-Table Equivalence)
% ============================================================================

% Collect all unique propositional constants appearing in a formula
vars_in_formula(P, Vars) :-
    vars_f(P, Raw),
    sort(Raw, Vars).

vars_f(P, [P]) :-
    constantp(P), !.
vars_f(P, Vars) :-
    P =.. [Op, P1],
    unaryOperatorp(Op), !,
    vars_f(P1, Vars).
vars_f(P, Vars) :-
    P =.. [Op, P1, P2],
    binaryOperatorp(Op),
    vars_f(P1, V1),
    vars_f(P2, V2),
    append(V1, V2, Vars).

% Collect all unique propositional constants appearing in an indexed CNF list
vars_in_cnf(CNFList, Vars) :-
    findall(Atom, (
        member(_-Clause, CNFList),
        member(Lit, Clause),
        (   Lit =.. [Op, Atom], unaryOperatorp(Op)
        ->  true
        ;   Atom = Lit
        )
    ), Raw),
    sort(Raw, Vars).

% Generate all 2^N truth assignments (Valuations as lists of Var-Bool pairs)
all_valuations([], [[]]).
all_valuations([V|Vs], Valuations) :-
    all_valuations(Vs, Rest),
    findall([V-true|R],  member(R, Rest), TBranch),
    findall([V-false|R], member(R, Rest), FBranch),
    append(TBranch, FBranch, Valuations).

% Evaluate a propositional formula under a given Valuation
eval_formula(P, Val, Bool) :-
    constantp(P), !,
    memberchk(P-Bool, Val).
eval_formula(¬P, Val, Bool) :- !,
    eval_formula(P, Val, B1),
    bool_not(B1, Bool).
eval_formula(P /\ Q, Val, Bool) :- !,
    eval_formula(P, Val, B1),
    eval_formula(Q, Val, B2),
    bool_and(B1, B2, Bool).
eval_formula(P \/ Q, Val, Bool) :- !,
    eval_formula(P, Val, B1),
    eval_formula(Q, Val, B2),
    bool_or(B1, B2, Bool).
eval_formula(P -> Q, Val, Bool) :- !,
    eval_formula(P, Val, B1),
    eval_formula(Q, Val, B2),
    bool_imp(B1, B2, Bool).
eval_formula(P <-> Q, Val, Bool) :- !,
    eval_formula(P, Val, B1),
    eval_formula(Q, Val, B2),
    bool_iff(B1, B2, Bool).

bool_not(true,  false).
bool_not(false, true).

bool_and(true,  true,  true)  :- !.
bool_and(_,     _,     false).

bool_or(false, false, false) :- !.
bool_or(_,     _,     true).

bool_imp(true,  false, false) :- !.
bool_imp(_,     _,     true).

bool_iff(X, X, true)  :- !.
bool_iff(_, _, false).

% Evaluate an indexed CNF list (conjunction of disjunctive clauses)
% Note: Empty list [] represents empty conjunction (verum / true).
%       A list containing _-[] represents an empty clause (falsum / false).
eval_cnf([], _, true) :- !.
eval_cnf([_-Clause | Rest], Val, Bool) :-
    eval_clause(Clause, Val, B1),
    (   (B1 == false)
->  (Bool = false)
    ;   eval_cnf(Rest, Val, Bool)
    ).

eval_clause([], _, false) :- !.
eval_clause([Lit | Rest], Val, Bool) :-
    eval_literal(Lit, Val, B1),
    (   (B1 == true)
->  (Bool = true)
    ;   eval_clause(Rest, Val, Bool)
    ).

eval_literal(Lit, Val, Bool) :-
    Lit =.. [Op, Atom],
    unaryOperatorp(Op), !,
    memberchk(Atom-B1, Val),
    bool_not(B1, Bool).
eval_literal(Atom, Val, Bool) :-
    constantp(Atom),
    memberchk(Atom-Bool, Val).

% Check whether Formula and CNFList agree on every row of the truth table
semantically_equivalent(Formula, CNFList) :-
    vars_in_formula(Formula, V1),
    vars_in_cnf(CNFList, V2),
    append(V1, V2, VAll),
    sort(VAll, Vars),
    all_valuations(Vars, Valuations),
    forall(member(Val, Valuations), (
        eval_formula(Formula, Val, B1),
        eval_cnf(CNFList, Val, B2),
        B1 == B2
    )).

% ============================================================================
% Documented Test Cases for formula2cnf/2
% ============================================================================

% test_case(?ID, ?Category, ?Description, ?InputFormula)

test_case(1, atom,
    "Single propositional atom p converts to a single unit clause [[p]].",
    p).

test_case(2, negated_atom,
    "Single negated atom ¬p converts to a single negative unit clause [[¬p]].",
    ¬p).

test_case(3, implication,
    "Material implication (p -> q) eliminates -> into disjunctive clause [¬p, q].",
    p -> q).

test_case(4, equivalence,
    "Biconditional (p <-> q) expands into two clauses: [¬p, q] and [¬q, p].",
    p <-> q).

test_case(5, nested_negation,
    "Nested negation ¬(¬(p \\/ ¬q)) applies double-negation elimination and De Morgan's laws.",
    ¬(¬(p \/ ¬q))).

test_case(6, distribution,
    "Disjunction over conjunction (p \\/ (q /\\ r)) distributes \\/ over /\\ into [p, q] and [p, r].",
    p \/ (q /\ r)).

test_case(7, tautology,
    "Excluded middle (p \\/ ¬p) produces only tautological clauses, simplifying to empty conjunction [].",
    p \/ ¬p).

test_case(8, contradiction,
    "Contradiction (p /\\ ¬p) produces two complementary unit clauses [[p], [¬p]], unsatisfiable under all valuations.",
    p /\ ¬p).

% ============================================================================
% Test Runner
% ============================================================================

run_tests :-
    format('~n=== Running formula2cnf/2 Semantic Equivalence Test Suite ===~n~n'),
    findall(ID, test_case(ID, _, _, _), IDs),
    run_all(IDs, 0, 0).

run_all([], Passed, Failed) :-
    Total is Passed + Failed,
    format('=== Summary: ~w/~w passed (~w failed) ===~n', [Passed, Total, Failed]).
run_all([ID|Rest], PIn, FIn) :-
    test_case(ID, Cat, Desc, Formula),
    format('[Test ~w - ~w] ~s~n', [ID, Cat, Desc]),
    format('  Input : ~w~n', [Formula]),
    (   catch(formula2cnf(Formula, CNF), Err, (format('  ERROR : ~w~n', [Err]), fail))
    ->  format('  Output: ~w~n', [CNF]),
        (   semantically_equivalent(Formula, CNF)
        ->  format('  Status: PASS (Truth-table equivalent)~n~n'),
            POut is PIn + 1, FOut = FIn
        ;   format('  Status: FAIL (Semantic mismatch!)~n~n'),
            POut = PIn, FOut is FIn + 1
        )
    ;   format('  Status: FAIL (Exception or failure)~n~n'),
        POut = PIn, FOut is FIn + 1
    ),
    run_all(Rest, POut, FOut).