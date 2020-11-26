-module(parse_SUITE).

-export(
    [
        all/0,
        groups/0,

        proposition/1,
        implication/1,
        conjunction/1,
        disjunction/1,
        negation/1,
        parenthesis/1,
        bottom/1,
        implication_right_associative/1,
        conjunction_left_associative/1,
        disjunction_left_associative/1,
        implication_before_conjunction/1,
        implication_before_disjunction/1,
        implication_before_negation/1,
        conjunction_before_disjunction/1,
        conjunction_before_negation/1,
        disjunction_before_negation/1,
        parenthesis_changes_order/1,
        negated_parenthesis/1,
        sequent/1,
        parenthesis_mismatch/1,
        proposition_no_multi_letter/1,
        implication_missing_operand/1,
        conjunction_missing_operand/1,
        disjunction_missing_operand/1,
        negation_missing_operand/1,
        sequent_no_premises/1,
        sequent_missing_premises/1,
        sequent_missing_conclusion/1,
        implication_with_parenthesis/1,
        disjunction_with_parenthesis/1,
        conjunction_with_parenthesis/1
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
            [parallel],
            [
                proposition,
                implication,
                conjunction,
                disjunction,
                negation,
                parenthesis,
                bottom,
                implication_right_associative,
                conjunction_left_associative,
                disjunction_left_associative,
                implication_before_conjunction,
                implication_before_disjunction,
                implication_before_negation,
                conjunction_before_disjunction,
                conjunction_before_negation,
                disjunction_before_negation,
                parenthesis_changes_order,
                negated_parenthesis,
                sequent,
                parenthesis_mismatch,
                proposition_no_multi_letter,
                implication_missing_operand,
                conjunction_missing_operand,
                disjunction_missing_operand,
                negation_missing_operand,
                sequent_no_premises,
                sequent_missing_premises,
                sequent_missing_conclusion,
                implication_with_parenthesis,
                disjunction_with_parenthesis,
                conjunction_with_parenthesis
            ]
        }
    ].

proposition(_Config) ->
    ?assertEqual(
        {ok, <<"p">>},
        parse:expr(<<"p">>)
    ).


implication(_Config) ->
    ?assertEqual(
        {ok, {<<"p">>, '->', <<"q">>}},
        parse:expr(<<"p -> q">>)
    ).


conjunction(_Config) ->
    ?assertEqual(
        {ok, {<<"p">>, '&', <<"q">>}},
        parse:expr(<<"p & q">>)
    ).


disjunction(_Config) ->
    ?assertEqual(
        {ok, {<<"p">>, '|', <<"q">>}},
        parse:expr(<<"p | q">>)
    ).


negation(_Config) ->
    ?assertEqual(
        {ok, {'!', <<"p">>}},
        parse:expr(<<"!p">>)
    ).


parenthesis(_Config) ->
    ?assertEqual(
        {ok, {<<"p">>, '&', <<"q">>}},
        parse:expr(<<"(((p)) & q)">>)
    ).


bottom(_Config) ->
    ?assertEqual(
        {ok, false},
        parse:expr(<<"false">>)
    ).


implication_right_associative(_Config) ->
    ?assertEqual(
        {ok, {<<"p">>, '->', {<<"q">>, '->', <<"r">>}}},
        parse:expr(<<"p -> q -> r">>)
    ).


conjunction_left_associative(_Config) ->
    ?assertEqual(
        {ok, {{<<"p">>, '&', <<"q">>}, '&', <<"r">>}},
        parse:expr(<<"p & q & r">>)
    ).


disjunction_left_associative(_Config) ->
    ?assertEqual(
        {ok, {{<<"p">>, '|', <<"q">>}, '|', <<"r">>}},
        parse:expr(<<"p | q | r">>)
    ).


implication_before_conjunction(_Config) ->
    ?assertEqual(
        {ok, {{<<"p">>, '&', <<"q">>}, '->', {<<"q">>, '&', <<"r">>}}},
        parse:expr(<<"p & q -> q & r">>)
    ).


implication_before_disjunction(_Config) ->
    ?assertEqual(
        {ok, {{<<"p">>, '|', <<"q">>}, '->', {<<"q">>, '|', <<"r">>}}},
        parse:expr(<<"p | q -> q | r">>)
    ).


implication_before_negation(_Config) ->
    ?assertEqual(
        {ok, {{'!', <<"p">>}, '->', {'!', <<"q">>}}},
        parse:expr(<<"!p -> !q">>)
    ).


conjunction_before_disjunction(_Config) ->
    ?assertEqual(
        {ok, {{<<"p">>, '&', <<"q">>}, '|', {<<"q">>, '&', <<"r">>}}},
        parse:expr(<<"p & q | q & r">>)
    ).


conjunction_before_negation(_Config) ->
    ?assertEqual(
        {ok, {{'!', <<"p">>}, '&', {'!', <<"q">>}}},
        parse:expr(<<"!p & !q">>)
    ).


disjunction_before_negation(_Config) ->
    ?assertEqual(
        {ok, {{'!', <<"p">>}, '|', {'!', <<"q">>}}},
        parse:expr(<<"!p | !q">>)
    ).


parenthesis_changes_order(_Config) ->
    ?assertEqual(
        {ok, {{<<"p">>, '&', {<<"q">>, '|', <<"q">>}}, '&', <<"r">>}},
        parse:expr(<<"(p & (q | q)) & r">>)
    ).


negated_parenthesis(_Config) ->
    ?assertEqual(
        {ok, {'!', {<<"p">>, '&', <<"q">>}}},
        parse:expr(<<"!(p & q)">>)
    ).


parenthesis_mismatch(_Config) ->
    ?assertEqual(
        {error, <<"p&(q">>},
        parse:expr(<<"p & (q">>)
    ),
    ?assertEqual(
        {error, <<"p&q)">>},
        parse:expr(<<"p & q)">>)
    ),
    ?assertEqual(
        {error, <<"!(p&!(q)">>},
        parse:expr(<<"!(p & !(q)">>)
    ).


sequent(_Config) ->
    ?assertEqual(
        {ok, {[{<<"p">>, '->', <<"q">>}, <<"p">>], '|-', <<"q">>}},
        parse:sequent(<<"p -> q, p |- q">>)
    ).


proposition_no_multi_letter(_Config) ->
    ?assertEqual(
        {error, <<"pq">>},
        parse:expr(<<"pq">>)
    ).


implication_missing_operand(_Config) ->
    ?assertEqual(
        {error, <<"p->">>},
        parse:expr(<<"p ->">>)
    ),
    ?assertEqual(
        {error, <<"->q">>},
        parse:expr(<<" -> q">>)
    ).


conjunction_missing_operand(_Config) ->
    ?assertEqual(
        {error, <<"p&">>},
        parse:expr(<<"p &">>)
    ),
    ?assertEqual(
        {error, <<"&q">>},
        parse:expr(<<" & q">>)
    ).


disjunction_missing_operand(_Config) ->
    ?assertEqual(
        {error, <<"p|">>},
        parse:expr(<<"p |">>)
    ),
    ?assertEqual(
        {error, <<"|q">>},
        parse:expr(<<" | q">>)
    ).


negation_missing_operand(_Config) ->
    ?assertEqual(
        {error, <<"!">>},
        parse:expr(<<"!">>)
    ).


sequent_no_premises(_Config) ->
    ?assertEqual(
        {ok, {[], '|-', <<"q">>}},
        parse:sequent(<<"|- q">>)
    ).


sequent_missing_premises(_Config) ->
    ?assertEqual(
        {error, <<",p|-q">>},
        parse:sequent(<<", p |- q">>)
    ),
    ?assertEqual(
        {error, <<",|-q">>},
        parse:sequent(<<"p, |- q">>)
    ),
    ?assertEqual(
        {error, <<",q|-q">>},
        parse:sequent(<<"p,, q |- q">>)
    ).


sequent_missing_conclusion(_Config) ->
    ?assertEqual(
        {error, <<"|-">>},
        parse:sequent(<<"p, q |-">>)
    ),
    ?assertEqual(
        {error, <<"q">>},
        parse:sequent(<<"p, q">>)
    ),
    ?assertEqual(
        {error, <<"p">>},
        parse:sequent(<<"p">>)
    ).


implication_with_parenthesis(_Config) ->
    ?assertEqual(
        {ok, {{<<"p">>, '->', <<"q">>}, '->', <<"r">>}},
        parse:expr(<<"(p -> q) -> r">>)
    ).


disjunction_with_parenthesis(_Config) ->
    ?assertEqual(
        {ok, {<<"p">>, '|', {<<"q">>, '|', <<"r">>}}},
        parse:expr(<<"p | (q | r)">>)
    ).


conjunction_with_parenthesis(_Config) ->
    ?assertEqual(
        {ok, {<<"p">>, '&', {<<"q">>, '&', <<"r">>}}},
        parse:expr(<<"p & (q & r)">>)
    ).


