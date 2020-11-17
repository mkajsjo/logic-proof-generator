-module(main).

-export(
    [
        eval/2,
        propositions/1,
        combinations/1,
        truth_table/1,
        to_string/1,
        header/1,
        print_truth_table/1,
        foo/2,
        prove/1,
        construct/2
    ]
).


-record(
   proof_struct,
   {
        given,
        assumption,
        sought,
        dependency_graph,
        conclusion,
        queue
   }
).


eval({A, '|', B}, Ps) ->
    eval(A, Ps) orelse eval(B, Ps);
eval({A, '&', B}, Ps) ->
    eval(A, Ps) andalso eval(B, Ps);
eval({'!', A}, Ps) ->
    not eval(A, Ps);
eval({A, '->', B}, Ps) ->
    not eval(A, Ps) orelse eval(B, Ps);
eval(P, Ps) ->
    maps:get(P, Ps).


propositions(Expr) ->
    maps:keys(propositions(Expr, #{})).

propositions({A, _, B}, Ps) ->
    propositions(B, propositions(A, Ps));
propositions({_, A}, Ps) ->
    propositions(A, Ps);
propositions(P, Ps) ->
    maps:put(P, false, Ps).


combinations(Ps) ->
    lists:foldl(
        fun (P, Acc) ->
            [
                [N | A]
            ||
                N <- [{P, false}, {P, true}],
                A <- Acc
            ]
        end,
        [[]],
        lists:reverse(Ps)
    ).


truth_table(Expr) ->
    lists:foldl(
        fun (N, Acc) ->
            Ps = maps:from_list(N),
            T = [B || {_, B} <- N],
            [T ++ [eval(Expr, Ps)] | Acc]
        end,
        [],
        combinations(propositions(Expr))
    ).


to_string({'!', Expr}) when is_tuple(Expr) ->
    <<
        "!(",
        (to_string(Expr))/binary,
        ")"
    >>;
to_string({'!', Expr}) ->
    <<
        "!",
        (to_string(Expr))/binary
    >>;
to_string({A0, Op, B0}) ->
    <<
        (fix_precedence(A0, lower_precedence_ops(Op, left)))/binary,
        " ",
        (atom_to_binary(Op, utf8))/binary,
        " ",
        (fix_precedence(B0, lower_precedence_ops(Op, right)))/binary
    >>;
to_string(P) ->
    atom_to_binary(P, utf8).


fix_precedence({_, Op, _} = Expr, Ops) ->
    S = to_string(Expr),
    case lists:member(Op, Ops) of
        true ->
            <<"(", S/binary, ")">>;
        false ->
            S
    end;
fix_precedence(Expr, _) ->
    to_string(Expr).


lower_precedence_ops('&', _) ->
    ['|', '->'];
lower_precedence_ops('|', _) ->
    ['->'];
lower_precedence_ops('->', left) ->
    ['->'];
lower_precedence_ops(_, _) ->
    [].


header(Expr) ->
    [
        to_string(N)
    ||
        N <- propositions(Expr) ++ [Expr]
    ].


column_widths(List) ->
    [
        string:length(N)
    ||
        N <- List
    ].


print_truth_table(Expr) ->
    Header = header(Expr),
    ColumnWidths = column_widths(Header),
    Table = truth_table(Expr),
    io:fwrite([row_to_string(Header, ColumnWidths), "\n"]),
    Spacer = lists:duplicate(lists:sum(ColumnWidths) + 3 * length(ColumnWidths) + 1, "-"),
    io:fwrite([Spacer, "\n"]),
    lists:foreach(
        fun (Row0) ->
            Row =
                [
                    case V of
                        true ->
                            <<"T">>;
                        false ->
                            <<"F">>
                    end
                ||
                    V <- Row0
                ],
            io:fwrite([row_to_string(Row, ColumnWidths), "\n"])
        end,
        Table
    ).


row_to_string(Row, ColumnWidths) ->
    [
        <<"| ">>,
        [
            [string:pad(S, W), <<" | ">>]
        ||
            {S, W} <- lists:zip(Row, ColumnWidths)
        ]
    ].


foo({A, _, B} = Expr, {Map, Exprs}) ->
    AExprs = maps:get(A, Map, []),
    BExprs = maps:get(B, Map, []),
    Map2 = maps:put(A, [Expr | AExprs], Map),
    Map3 = maps:put(B, [Expr | BExprs], Map2),
    Exprs2 = maps:put(Expr, true, Exprs),
    {MapA, ExprsA} = foo(A, {Map3, Exprs2}),
    foo(B, {MapA, ExprsA});
foo({_, A} = Expr, {Map, Exprs}) ->
    AExprs = maps:get(A, Map, []),
    Map2 = maps:put(A, [Expr | AExprs], Map),
    Exprs2 = maps:put(Expr, true, Exprs),
    foo(A, {Map2, Exprs2});
foo(P, {Map, Exprs}) ->
    Exprs2 = maps:put(P, true, Exprs),
    {Map, Exprs2}.


prove({Premises, '|-', Conclusion}) ->
    {DependencyGraph, Sought} =
        lists:foldl(
            fun foo/2,
            {#{}, #{}},
            [Conclusion | Premises]
        ),
    f(
        #proof_struct{
            given = maps:from_list([{P, true} || P <- Premises]),
            sought = Sought,
            dependency_graph = DependencyGraph,
            conclusion = Conclusion,
            queue = maps:keys(Sought)
        }
    ).


f(#proof_struct{queue = []}) ->
    no_proof_found;
f(#proof_struct{conclusion = Conclusion} = PS) ->
    [Expr | Queue] = PS#proof_struct.queue,
    case construct(Expr, PS#proof_struct.given) of
        hehe ->
            f(PS#proof_struct{queue = Queue});
        Conclusion ->
            proof_found;
        Expr ->
            Queue2 =
                Queue ++ maps:get(Expr, PS#proof_struct.dependency_graph, []),
            Given =
                deconstruct(Expr, maps:put(Expr, true, PS#proof_struct.given)),
            f(PS#proof_struct{queue = Queue2, given = Given})
    end.


construct({A, '&', B} = Expr, Given) ->
    case Given of
        #{A := _, B := _} ->
            Expr;
        _ ->
            deconstruct(Expr, Given, maps:keys(Given))
    end;
construct({A, '|', B} = Expr, Given) ->
    case Given of
        #{A := _} ->
            Expr;
        #{B := _} ->
            Expr;
        _ ->
            deconstruct(Expr, Given, maps:keys(Given))
    end;
construct({'!', {'!', A}} = Expr, Given) ->
    case Given of
        #{A := _} ->
            Expr;
        _ ->
            deconstruct(Expr, Given, maps:keys(Given))
    end;
construct(Expr, Given) ->
    case Given of
        #{false := _} ->
            Expr;
        #{Expr := _} ->
            Expr;
        _ ->
            deconstruct(Expr, Given, maps:keys(Given))
    end.


deconstruct(_, _, []) ->
    hehe;
deconstruct(Expr, Given, [G | Gs]) ->
    case G of
        {Expr, '&', _} ->
            Expr;
        {_, '&', Expr} ->
            Expr;
        {Key, '->', Expr} ->
            case Given of
                #{Key := _} ->
                    Expr;
                _ ->
                    hehe
            end;
        {'!', {'!', Expr}} ->
            Expr;
        _ ->
            deconstruct(Expr, Given, Gs)
    end.


deconstruct({A, '&', B}, Given) ->
    Given2 = Given#{A => true, B => true},
    Given3 = deconstruct(A, Given2),
    deconstruct(B, Given3);
deconstruct({A, '->', B}, Given) ->
    NotB = {'!', B},
    case Given of
        #{A := _} ->
            Given2 = Given#{B => true},
            deconstruct(B, Given2);
        #{NotB := _} ->
            Given2 = Given#{{'!', A} => true},
            deconstruct({'!', A}, Given2)
    end;
deconstruct({'!', {'!', Expr}}, Given) ->
    Given2 = Given#{Expr => true},
    deconstruct(Expr, Given2);
deconstruct({'!', Expr}, Given) ->
    case Given of
        #{Expr := _} ->
            false;
        _ ->
            Given
    end;
deconstruct(_, Given) ->
    Given.
