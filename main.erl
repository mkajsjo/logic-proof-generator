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


%prove({Premises, '|-', Conclusion}) ->
%    {DependencyGraph, Sought} =
%        lists:foldl(
%            fun foo/2,
%            {#{}, #{}},
%            [Conclusion | Premises]
%        ),
%    Given =
%        lists:foldl(
%            fun deconstruct/2,
%            maps:from_list([{P, true} || P <- Premises]),
%            Premises
%        ),
%    f(
%        #proof_struct{
%            given = Given,
%            sought = Sought,
%            dependency_graph = DependencyGraph,
%            conclusion = Conclusion,
%            queue = maps:keys(Sought)
%        }
%    ).


%f(#proof_struct{queue = []}) ->
%    no_proof_found;
%f(#proof_struct{conclusion = Conclusion} = PS) ->
%    [Expr | Queue] = PS#proof_struct.queue,
%    case construct(Expr, PS#proof_struct.given) of
%        hehe ->
%            f(PS#proof_struct{queue = Queue});
%        Conclusion ->
%            proof_found;
%        Expr ->
%            Queue2 =
%                Queue ++ maps:get(Expr, PS#proof_struct.dependency_graph, []),
%            Given =
%                deconstruct(Expr, maps:put(Expr, true, PS#proof_struct.given)),
%            f(PS#proof_struct{queue = Queue2, given = Given})
%    end.


construct({A, '&', B} = Expr, Given) ->
    case Given of
        #{A := _, B := _} ->
            Expr;
        _ ->
            hehe
    end;
construct({A, '|', B} = Expr, Given) ->
    case Given of
        #{A := _} ->
            Expr;
        #{B := _} ->
            Expr;
        _ ->
            hehe
    end;
construct({'!', {'!', A}} = Expr, Given) ->
    case Given of
        #{A := _} ->
            Expr;
        _ ->
            hehe
    end;
construct(Expr, Given) ->
    case Given of
        #{false := _} ->
            Expr;
        #{Expr := _} ->
            Expr;
        _ ->
            hehe
    end.


deconstruct(false, Given) ->
    Given#{false => true};
deconstruct({A, '&', B}, Given) ->
    Given2 = Given#{A => true, B => true},
    Given3 = deconstruct(A, Given2),
    deconstruct(B, Given3);
deconstruct({A, '->', B}, Given) ->
    Given2 = deconstruct_helper(A, B, Given),
    deconstruct_helper({'!', B}, {'!', A}, Given2);
deconstruct({'!', {'!', Expr}}, Given) ->
    Given2 = Given#{Expr => true},
    deconstruct(Expr, Given2);
deconstruct({'!', Expr}, Given) ->
    deconstruct_helper(Expr, false, Given);
deconstruct(_, Given) ->
    Given.


deconstruct_helper(Key, Value, Given) ->
    case Given of
        #{Key := _} ->
            deconstruct(Value, Given#{Value => true});
        _ ->
            Given
    end.


%---


-record(
   ps,
   {
        proved = #{},
        assumption,
        proved_in_assumption = #{},
        elim_blocked = #{},
        intro_blocked = #{},
        conclusion,
        queue
   }
).


prove({Premises, '|-', Conclusion}) ->
    {_DependencyGraph, Sought} =
        lists:foldl(
            fun foo/2,
            {#{}, #{}},
            [Conclusion | Premises]
        ),
    Given =
        lists:foldl(
            fun deconstruct/2,
            maps:from_list([{P, true} || P <- Premises]),
            Premises
        ),
    prove_(
        #ps{
            proved = Given,
            conclusion = Conclusion,
            queue = maps:keys(Sought)
        }
    ).


prove_(PS) ->
    NrProvedBefore = maps:size(PS#ps.proved),
    PS2 =
        lists:foldl(
            fun intro/2,
            PS,
            PS#ps.queue
        ),
    PS3 =
        lists:foldl(
            fun intro/2,
            PS2,
            maps:keys(PS2#ps.elim_blocked)
        ),
    ProofFound = maps:is_key(PS3#ps.conclusion, PS3#ps.proved),
    BottomFound = maps:is_key(false, PS3#ps.proved),
    NrProvedAfter = maps:size(PS3#ps.proved),
    if
        ProofFound ->
            proof_found;
        BottomFound ->
            proof_found_by_bottom; %TODO just proof_found
        NrProvedAfter =:= NrProvedBefore ->
            PS4 =
                lists:foldl(
                    fun start_assumption/2,
                    PS3,
                    assumable(PS3)
                ),
            NrProvedAfter2 = maps:size(PS4#ps.proved),
            case NrProvedAfter2 =:= NrProvedBefore of
                true ->
                    no_proof_found;
                false ->
                    prove_(PS4#ps{queue = maps:keys(PS3#ps.intro_blocked)})
            end;
        true ->
            prove_(PS3#ps{queue = maps:keys(PS3#ps.intro_blocked)})
    end.


intro({A, '&', B} = Expr, PS) ->
    case {is_proved(A, PS), is_proved(B, PS), is_proved(Expr, PS)} of
        {_, _, true} ->
            PS;
        {true, true, _} ->
            add_intro_proof(skip, Expr, PS);
        {false, true, _} ->
            add_intro_blocked(A, Expr, PS);
        {true, false, _} ->
            add_intro_blocked(B, Expr, PS);
        _ ->
            add_intro_blocked(
                B,
                Expr,
                add_intro_blocked(A, Expr, PS)
            )
    end;
intro({A, '|', B} = Expr, PS) ->
    PS2 = add_intro_proof(A, Expr, PS),
    add_intro_proof(
        B,
        Expr,
        PS2
    );
intro({'!', {'!', A}} = Expr, PS) ->
    add_intro_proof(A, Expr, PS);
intro(_, PS) ->
    PS.


add_intro_proof(Key, Expr, PS) ->
    case {Key =:= skip orelse is_proved(Key, PS), is_proved(Expr, PS)} of
        {_, true} ->
            PS;
        {true, false} ->
            add_proof(Expr, PS);
        {false, false} ->
            add_intro_blocked(Key, Expr, PS)
    end.


elim(Expr, PS0) ->
    PS = elim_(Expr, PS0),
    add_elim_proof({'!', Expr}, false, PS).


elim_({A, '&', B}, PS) ->
    add_elim_proof(
        skip,
        B,
        add_elim_proof(skip, A, PS)
    );
elim_({A, '->', B}, PS) ->
    PS2 = add_elim_proof(A, B, PS),
    add_elim_proof(
        {'!', B},
        {'!', A},
        PS2
    );
elim_({'!', {'!', A}}, PS) ->
    add_elim_proof(skip, A, PS);
elim_({'!', A}, PS) ->
    add_elim_proof(A, false, PS);
elim_(_, PS) ->
    PS.


add_elim_proof(Key, Expr, PS) ->
    case {Key =:= skip orelse is_proved(Key, PS), is_proved(Expr, PS)} of
        {_, true} ->
            PS;
        {true, false} ->
            add_proof(Expr, PS);
        {false, false} ->
            add_elim_blocked(Key, Expr, PS)
    end.


add_proof(Expr, PS) ->
    PS2 = add_proof_(Expr, PS),
    IntroBlocked = maps:get(Expr, PS2#ps.intro_blocked, []),
    PS3 =
        lists:foldl(
            fun intro/2,
            PS2#ps{intro_blocked = maps:remove(Expr, PS2#ps.intro_blocked)},
            IntroBlocked
        ),
    ElimBlocked = maps:get(Expr, PS3#ps.elim_blocked, []),
    PS4 =
        lists:foldl(
            fun elim/2,
            PS3#ps{elim_blocked = maps:remove(Expr, PS3#ps.elim_blocked)},
            ElimBlocked
        ),
    elim(Expr, PS4).


add_proof_(Expr, #ps{assumption = undefined} = PS) ->
    PS#ps{proved = (PS#ps.proved)#{Expr => true}};
add_proof_(Expr, PS) ->
    PS#ps{proved_in_assumption = (PS#ps.proved_in_assumption)#{Expr => true}}.


is_proved(Expr, PS) ->
    maps:is_key(Expr, PS#ps.proved) orelse
    maps:is_key(Expr, PS#ps.proved_in_assumption).


add_intro_blocked(Key, Expr, PS) ->
    BlockedByKey = maps:get(Key, PS#ps.intro_blocked, []),
    PS#ps{intro_blocked = (PS#ps.intro_blocked)#{Key => [Expr | BlockedByKey]}}.


add_elim_blocked(Key, Expr, PS) ->
    BlockedByKey = maps:get(Key, PS#ps.elim_blocked, []),
    PS#ps{elim_blocked = (PS#ps.elim_blocked)#{Key => [Expr | BlockedByKey]}}.


assumable(#ps{intro_blocked = IB, elim_blocked = EB, assumption = Ass} = PS) ->
    [
        A
    ||
        A <- maps:keys(maps:merge(IB, EB)),
        not is_proved(A, PS),
        not is_proved({'!', A}, PS),
        A =/= Ass
    ].


start_assumption(Assumption, #ps{assumption = OldAssumption} = PS) ->
    Proved = maps:merge(PS#ps.proved, PS#ps.proved_in_assumption),
    Proved2 =
        case OldAssumption of
            undefined ->
                Proved;
            _ ->
                maps:put(OldAssumption, true, Proved)
        end,
    assumption(
        PS#ps{
            assumption = Assumption,
            proved = Proved2,
            proved_in_assumption = #{}
        }
    ).


assumption(PS) ->
    NrProvedBefore = maps:size(PS#ps.proved),
    PS2 =
        lists:foldl(
            fun intro/2,
            PS,
            PS#ps.queue
        ),
    PS3 =
        lists:foldl(
            fun intro/2,
            PS2,
            maps:keys(PS2#ps.elim_blocked)
        ),
    BottomFound = maps:is_key(false, PS3#ps.proved),
    NrProvedAfter = maps:size(PS3#ps.proved),
    if
        BottomFound ->
            end_assumption(PS3);
        NrProvedAfter =:= NrProvedBefore ->
            PS4 =
                lists:foldl(
                    fun start_assumption/2,
                    PS3,
                    assumable(PS3)
                ),
            NrProvedAfter2 = maps:size(PS4#ps.proved),
            case NrProvedAfter2 =:= NrProvedBefore of
                true ->
                    end_assumption(PS4);
                false ->
                    assumption(PS4#ps{queue = maps:keys(PS3#ps.intro_blocked)})
            end;
        true ->
            assumption(PS3#ps{queue = maps:keys(PS3#ps.intro_blocked)})
    end.


end_assumption(#ps{proved_in_assumption = Proved, assumption = Assumption} = PS0) ->
    PS = PS0#ps{proved_in_assumption = #{}, assumption = undefined},
    PS2 =
        case is_proved(false, PS) of
            true ->
                add_proof({'!', Assumption}, PS);
            false ->
                PS
        end,
    lists:foldl(
        fun (N, Acc) ->
                add_proof({Assumption, '->', N}, Acc)
        end,
        PS2,
        maps:keys(Proved)
    ).
