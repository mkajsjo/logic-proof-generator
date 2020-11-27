-module(proof_SUITE).

-export(
    [
        all/0,
        groups/0,

        law_of_excluded_middle/1,
        law_of_non_contradiction/1,
        self_implication/1,
        idempotent_law1/1,
        idempotent_law2/1,
        double_negation/1,
        commutative_conjunction/1,
        commutative_disjunction/1,
        associative_conjunction/1,
        associative_disjunction/1,
        distributive_law1/1,
        distributive_law2/1,
        de_morgans_law1/1,
        de_morgans_law2/1,
        contrapositive/1,
        reduction_ad_absurdum/1,
        implication_distributive_law1/1,
        implication_distributive_law2/1,
        implication_distributive_law3/1,
        exportation_law/1,
        addition/1,
        simplification/1,
        modus_ponens/1,
        modus_tollens/1,
        hypothetical_syllogism/1,
        disjunctive_syllogism/1,
        duns_scotus/1,
        clavius/1,
        frege/1,
        implication_language_equivalence1/1,
        implication_language_equivalence2/1,
        disjunction_language_equivalence1/1,
        disjunction_language_equivalence2/1,
        conjunction_language_equivalence1/1,
        conjunction_language_equivalence2/1
    ]
).


-include_lib("eunit/include/eunit.hrl").


all() ->
    [
        {group, group1}
    ].


groups() ->
    [
        {
            group1,
            [sequence],
            [
                law_of_excluded_middle,
                law_of_non_contradiction,
                self_implication,
                idempotent_law1,
                idempotent_law2,
                double_negation,
                commutative_conjunction,
                commutative_disjunction,
                associative_conjunction,
                associative_disjunction,
                distributive_law1,
                distributive_law2,
                de_morgans_law1,
                de_morgans_law2,
                contrapositive,
                reduction_ad_absurdum,
                implication_distributive_law1,
                implication_distributive_law2,
                implication_distributive_law3,
                exportation_law,
                addition,
                simplification,
                modus_ponens,
                modus_tollens,
                hypothetical_syllogism,
                disjunctive_syllogism,
                duns_scotus,
                clavius,
                frege,
                implication_language_equivalence1,
                implication_language_equivalence2,
                disjunction_language_equivalence1,
                disjunction_language_equivalence2,
                conjunction_language_equivalence1,
                conjunction_language_equivalence2
            ]
        }
    ].


law_of_excluded_middle(_Config) ->
    {ok, Sequent} = parse:sequent(<<"|- p | !p">>),
    {proof_found, _} = proof:find(Sequent).


law_of_non_contradiction(_Config) ->
    {ok, Sequent} = parse:sequent(<<"|- !(p & !p)">>),
    {proof_found, _} = proof:find(Sequent).


self_implication(_Config) ->
    {ok, Sequent} = parse:sequent(<<"|- p -> p">>),
    {proof_found, _} = proof:find(Sequent).


idempotent_law1(_Config) ->
    {ok, Sequent} = parse:sequent(<<"p |- p | p">>),
    {proof_found, _} = proof:find(Sequent),
    {ok, Sequent2} = parse:sequent(<<"p | p |- p">>),
    {proof_found, _} = proof:find(Sequent2).


idempotent_law2(_Config) ->
    {ok, Sequent} = parse:sequent(<<"p |- p & p">>),
    {proof_found, _} = proof:find(Sequent),
    {ok, Sequent2} = parse:sequent(<<"p & p |- p">>),
    {proof_found, _} = proof:find(Sequent2).


double_negation(_Config) ->
    {ok, Sequent} = parse:sequent(<<"p |- !!p">>),
    {proof_found, _} = proof:find(Sequent),
    {ok, Sequent2} = parse:sequent(<<"!!p |- p">>),
    {proof_found, _} = proof:find(Sequent2).


commutative_conjunction(_Config) ->
    {ok, Sequent} = parse:sequent(<<"p & q |- q & p">>),
    {proof_found, _} = proof:find(Sequent).


commutative_disjunction(_Config) ->
    {ok, Sequent} = parse:sequent(<<"p | q |- q | p">>),
    {proof_found, _} = proof:find(Sequent).


associative_conjunction(_Config) ->
    {ok, Sequent} = parse:sequent(<<"(p & q) & r |- p & (q & r)">>),
    {proof_found, _} = proof:find(Sequent),
    {ok, Sequent2} = parse:sequent(<<"p & (q & r) |- (p & q) & r">>),
    {proof_found, _} = proof:find(Sequent2).


associative_disjunction(_Config) ->
    {ok, Sequent} = parse:sequent(<<"(p | q) | r |- p | (q | r)">>),
    {proof_found, _} = proof:find(Sequent),
    {ok, Sequent2} = parse:sequent(<<"p | (q | r) |- (p | q) | r">>),
    {proof_found, _} = proof:find(Sequent2).


distributive_law1(_Config) ->
    {ok, Sequent} = parse:sequent(<<"p & (q | r) |- (p & q) | (p & r)">>),
    {proof_found, _} = proof:find(Sequent),
    {ok, Sequent2} = parse:sequent(<<"(p & q) | (p & r) |- p & (q | r)">>),
    {proof_found, _} = proof:find(Sequent2).


distributive_law2(_Config) ->
    {ok, Sequent} = parse:sequent(<<"p | (q & r) |- (p | q) & (p | r)">>),
    {proof_found, _} = proof:find(Sequent),
    {ok, Sequent2} = parse:sequent(<<"(p | q) & (p | r) |- p | (q & r)">>),
    {proof_found, _} = proof:find(Sequent2).


de_morgans_law1(_Config) ->
    {ok, Sequent} = parse:sequent(<<"!(p & q) |- !p | !q">>),
    {proof_found, _} = proof:find(Sequent),
    {ok, Sequent2} = parse:sequent(<<"!p | !q |- !(p & q)">>),
    {proof_found, _} = proof:find(Sequent2).


de_morgans_law2(_Config) ->
    {ok, Sequent} = parse:sequent(<<"!(p | q) |- !p & !q">>),
    {proof_found, _} = proof:find(Sequent),
    {ok, Sequent2} = parse:sequent(<<"!p & !q |- !(p | q)">>),
    {proof_found, _} = proof:find(Sequent2).


contrapositive(_Config) ->
    {ok, Sequent} = parse:sequent(<<"p -> q |- !q -> !p">>),
    {proof_found, _} = proof:find(Sequent),
    {ok, Sequent2} = parse:sequent(<<"!q -> !p |- p -> q">>),
    {proof_found, _} = proof:find(Sequent2).


reduction_ad_absurdum(_Config) ->
    {ok, Sequent} = parse:sequent(<<"p -> q & !q |- !p">>),
    {proof_found, _} = proof:find(Sequent),
    {ok, Sequent2} = parse:sequent(<<"!p |- p -> q & !q">>),
    {proof_found, _} = proof:find(Sequent2).


implication_distributive_law1(_Config) ->
    {ok, Sequent} = parse:sequent(<<"(p -> r) & (q -> r) |- p | q -> r">>),
    {proof_found, _} = proof:find(Sequent),
    {ok, Sequent2} = parse:sequent(<<"p | q -> r |- (p -> r) & (q -> r)">>),
    {proof_found, _} = proof:find(Sequent2).


implication_distributive_law2(_Config) ->
    {ok, Sequent} = parse:sequent(<<"(p -> q) & (p -> r) |- p -> q & r">>),
    {proof_found, _} = proof:find(Sequent),
    {ok, Sequent2} = parse:sequent(<<"p -> q & r |- (p -> q) & (p -> r)">>),
    {proof_found, _} = proof:find(Sequent2).


implication_distributive_law3(_Config) ->
    {ok, Sequent} = parse:sequent(<<"(p -> q) | (p -> r) |- p -> q | r">>),
    {proof_found, _} = proof:find(Sequent),
    {ok, Sequent2} = parse:sequent(<<"p -> q | r |- (p -> q) | (p -> r)">>),
    {proof_found, _} = proof:find(Sequent2).


exportation_law(_Config) ->
    {ok, Sequent} = parse:sequent(<<"p & q -> r |- p -> q -> r">>),
    {proof_found, _} = proof:find(Sequent),
    {ok, Sequent2} = parse:sequent(<<"p -> q -> r |- p & q -> r">>),
    {proof_found, _} = proof:find(Sequent2).


addition(_Config) ->
    {ok, Sequent} = parse:sequent(<<"|- p -> p | q">>),
    {proof_found, _} = proof:find(Sequent).


simplification(_Config) ->
    {ok, Sequent} = parse:sequent(<<"|- p & q -> p">>),
    {proof_found, _} = proof:find(Sequent).


modus_ponens(_Config) ->
    {ok, Sequent} = parse:sequent(<<"p, p -> q |- q">>),
    {proof_found, _} = proof:find(Sequent).


modus_tollens(_Config) ->
    {ok, Sequent} = parse:sequent(<<"p -> q, !q |- !p">>),
    {proof_found, _} = proof:find(Sequent).


hypothetical_syllogism(_Config) ->
    {ok, Sequent} = parse:sequent(<<"(p -> q) & (q -> r) |- p -> r">>),
    {proof_found, _} = proof:find(Sequent).


disjunctive_syllogism(_Config) ->
    {ok, Sequent} = parse:sequent(<<"p | q, !p |- q">>),
    {proof_found, _} = proof:find(Sequent).


duns_scotus(_Config) ->
    {ok, Sequent} = parse:sequent(<<"!p |- p -> q">>),
    {proof_found, _} = proof:find(Sequent).


clavius(_Config) ->
    {ok, Sequent} = parse:sequent(<<"!p -> p |- p">>),
    {proof_found, _} = proof:find(Sequent).


frege(_Config) ->
    {ok, Sequent} = parse:sequent(<<"p -> (q -> r), p -> q |- p -> r">>),
    {proof_found, _} = proof:find(Sequent).


implication_language_equivalence1(_Config) ->
    {ok, Sequent} = parse:sequent(<<"p -> q |- !p | q">>),
    {proof_found, _} = proof:find(Sequent),
    {ok, Sequent2} = parse:sequent(<<"!p | q |- p -> q">>),
    {proof_found, _} = proof:find(Sequent2).


implication_language_equivalence2(_Config) ->
    {ok, Sequent3} = parse:sequent(<<"p -> q |- !(p & !q)">>),
    {proof_found, _} = proof:find(Sequent3),
    {ok, Sequent4} = parse:sequent(<<"!(p & !q) |- p -> q">>),
    {proof_found, _} = proof:find(Sequent4).


disjunction_language_equivalence1(_Config) ->
    {ok, Sequent5} = parse:sequent(<<"p | q |- !p -> q">>),
    {proof_found, _} = proof:find(Sequent5),
    {ok, Sequent6} = parse:sequent(<<"!p -> q |- p | q">>),
    {proof_found, _} = proof:find(Sequent6).


disjunction_language_equivalence2(_Config) ->
    {ok, Sequent7} = parse:sequent(<<"p | q |- !(!p & !q)">>),
    {proof_found, _} = proof:find(Sequent7),
    {ok, Sequent8} = parse:sequent(<<"!(!p & !q) |- p | q">>),
    {proof_found, _} = proof:find(Sequent8).


conjunction_language_equivalence1(_Config) ->
    {ok, Sequent9} = parse:sequent(<<"p & q |- !(p -> !q)">>),
    {proof_found, _} = proof:find(Sequent9),
    {ok, Sequent10} = parse:sequent(<<"!(p -> !q) |- p & q">>),
    {proof_found, _} = proof:find(Sequent10).


conjunction_language_equivalence2(_Config) ->
    {ok, Sequent11} = parse:sequent(<<"p & q |- !(!p | !q)">>),
    {proof_found, _} = proof:find(Sequent11),
    {ok, Sequent12} = parse:sequent(<<"!(!p | !q) |- p & q">>),
    {proof_found, _} = proof:find(Sequent12).


