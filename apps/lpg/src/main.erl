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
        prove_dm/0
    ]
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
        queue,
        rules = #{},
        parent
   }
).


prove_dm() ->
    prove({[{'!', {p, '&', q}}], '|-', {{'!', p}, '|', {'!', q}}}).


prove({Premises, '|-', Conclusion}) ->
    {_DependencyGraph, Sought} =
        lists:foldl(
            fun foo/2,
            {#{}, #{}},
            [Conclusion | Premises]
        ),
    %Given = TODO remove
    %    lists:foldl(
    %        fun deconstruct/2,
    %        maps:from_list([{P, true} || P <- Premises]),
    %        Premises
    %    ),
    PS =
        lists:foldl(
            fun (Premise, Acc) ->
                    add_proof(Premise, {premise, []}, Acc)
            end,
            #ps{
                proved = #{},
                conclusion = Conclusion,
                queue = maps:keys(Sought)
            },
            Premises
        ),
    prove_(PS).


prove_(PS) ->
    NrProvedBefore = maps:size(PS#ps.proved),
    PS2 =
        lists:foldl(
            fun intro/2,
            PS,
            PS#ps.queue
        ),
    PS3 = PS2,
        %lists:foldl(
        %    fun elim/2,
        %    PS2,
        %    maps:keys(PS2#ps.elim_blocked)
        %),
    ProofFound = is_proved(PS3#ps.conclusion, PS3),
    CounterProofFound = is_proved(negate(PS3#ps.conclusion), PS3),
    BottomFound = is_proved(false, PS3),
    NrProvedAfter = maps:size(PS3#ps.proved),
    if
        BottomFound ->
            proof_found_by_bottom; %TODO just proof_found
        ProofFound ->
            {proof_found, reduce_proof_tree(PS3#ps.conclusion, PS3#ps.rules)};
        CounterProofFound ->
            counter_proof_found;
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
                    {no_proof_found, PS4#ps.proved};
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
            add_intro_proof(skip, Expr, {'&i', [A, B]}, PS);
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
    PS2 = add_intro_proof(A, Expr, {'|i1', [A]}, PS),
    add_intro_proof(
        B,
        Expr,
        {'|i2', [B]},
        PS2
    );
intro({'!', {'!', A}} = Expr, PS) ->
    add_intro_proof(A, Expr, {'!!i', [Expr]}, PS);
intro(_, PS) ->
    PS.


add_intro_proof(Key, Expr, Rule, PS) ->
    case {Key =:= skip orelse is_proved(Key, PS), is_proved(Expr, PS)} of
        {_, true} ->
            PS;
        {true, false} ->
            add_proof(Expr, Rule, PS);
        {false, false} ->
            add_intro_blocked(Key, Expr, PS)
    end.


elim(Expr, PS) ->
    %io:fwrite("ELIM: ~p~n", [Expr]), TODO remove elim_ function
    elim_(Expr, PS).


elim_({A, '&', B} = Expr, PS) ->
    add_elim_proof(
        skip,
        B,
        {'&e2', [Expr]},
        add_elim_proof(skip, A, {'&e1', [Expr]}, PS)
    );
elim_({A, '->', B} = Expr, PS) ->
    PS2 = add_elim_proof(A, B, {'->e', [A, Expr]}, PS),
    add_elim_proof(
        {'!', B},
        {'!', A},
        {'MT', [{'!', B}, Expr]},
        PS2
    );
elim_({'!', {'!', A}} = Expr, PS) ->
    add_elim_proof(skip, A, {'!!e', [Expr]}, PS);
elim_({'!', A} = Expr, PS) ->
    case is_proved(A, PS) of
        true ->
            add_proof(false, {'!e', [A, Expr]}, PS);
        false ->
            add_elim_blocked(A, Expr, PS)
    end;
elim_(Expr, PS) ->
    case is_proved({'!', Expr}, PS) of
        true ->
            add_proof(false, {'!e', [{'!', Expr}, Expr]}, PS);
        false ->
            PS
    end.


add_elim_proof(Key, Expr, Rule, PS) ->
    case {Key =:= skip orelse is_proved(Key, PS), is_proved(Expr, PS)} of
        {_, true} ->
            PS;
        {true, false} ->
            add_proof(Expr, Rule, PS);
        {false, false} ->
            add_elim_blocked(Key, Expr, PS)
    end.


add_proof(false, Rule, PS0) ->
    add_proof_rule(false, Rule, add_proof_(false, PS0));
add_proof(Expr, Rule, PS0) ->
    io:fwrite(lists:duplicate(2 * length(previous_assumptions(PS0)), " ") ++ "Expr ~p~n", [Expr]),
    PS =
        case Expr of
            {A, '->', B} ->
                case is_proved({negate(A), '->', B}, PS0) of
                    true ->
                        add_proof({A, '|', negate(A)}, {lem, []}, PS0);
                    false ->
                        PS0
                end;
            _ ->
                PS0
        end,
    PS2 = add_proof_rule(Expr, Rule, add_proof_(Expr, PS)),
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


add_proof_rule(Expr, {Rule, [Assumption, Expr2]}, #ps{assumption = A, rules = Rules} = PS) when Rule =:= '!i'; Rule =:= '->i' ->
    PS#ps{rules = Rules#{{A, Expr} => {Rule, [{Assumption, Assumption}, {Assumption, Expr2}]}}};
add_proof_rule(Expr, {Rule, Exprs}, #ps{assumption = A, rules = Rules} = PS) ->
    PS#ps{rules = Rules#{{A, Expr} => {Rule, [resolve_pointer(E, PS) || E <- Exprs]}}}.


resolve_pointer(_, undefined) ->
    {foo, loose_pointer}; %TODO remove
resolve_pointer(Expr, #ps{assumption = A, parent = P, rules = Rules}) ->
    case maps:is_key({A, Expr}, Rules) of
        true ->
            {A, Expr};
        false ->
            resolve_pointer(Expr, P)
    end.


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
    PreviousAssumptions = previous_assumptions(PS),
    [
        A
    ||
        A <- maps:keys(maps:merge(IB, EB)),
        not is_proved(A, PS),
        not is_proved({'!', A}, PS),
        not is_double_negated(A),
        not lists:member(A, PreviousAssumptions),
        not lists:member(negate(A), PreviousAssumptions),
        A =/= Ass
    ].


previous_assumptions(#ps{parent = undefined}) ->
    [];
previous_assumptions(#ps{assumption = Assumption, parent = Parent}) ->
    [Assumption | previous_assumptions(Parent)].


negate({'!', Expr}) ->
    Expr;
negate(Expr) ->
    {'!', Expr}.


is_double_negated({'!', {'!', _}}) ->
    true;
is_double_negated(_) ->
    false.


start_assumption(Assumption, PS) ->
    % Assumption could have been proved from previous assumption.
    case is_proved(Assumption, PS) of
        true ->
            PS;
        false ->
            io:fwrite(lists:duplicate(2 * length(previous_assumptions(PS)), " ") ++ "START ASSUMPTION: ~p~n", [Assumption]),
            Proved = maps:merge(PS#ps.proved, PS#ps.proved_in_assumption),
            PS2 =
                PS#ps{
                    assumption = Assumption,
                    proved = Proved,
                    proved_in_assumption = #{},
                    parent = PS,
                    rules = PS#ps.rules
                },
            assumption(
                add_proof(Assumption, {assumption, []}, PS2)
            )
    end.


assumption(PS) ->
    NrProvedBefore = maps:size(PS#ps.proved),
    PS2 =
        lists:foldl(
            fun intro/2,
            PS,
            PS#ps.queue
        ),
    PS3 = PS2,
        %lists:foldl(
        %    fun elim/2,
        %    PS2,
        %    maps:keys(PS2#ps.elim_blocked)
        %),
    BottomFound = is_proved(false, PS3),
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


useful_to_prove(PS) ->
    A = maps:keys(PS#ps.intro_blocked),
    B = maps:keys(PS#ps.elim_blocked),
    C = lists:merge(maps:values(PS#ps.intro_blocked)),
    D = lists:merge(maps:values(PS#ps.elim_blocked)),
    lists:usort(A ++ B ++ C ++ D).


end_assumption(#ps{proved_in_assumption = Proved, assumption = Assumption, parent = Parent, rules = Rules} = PS0) ->
    io:fwrite(lists:duplicate(2 * length(previous_assumptions(PS0)) - 2, " ") ++ "END ASSUMPTION: ~p~n~n", [Assumption]),
    case is_proved(false, PS0) of
        true ->
            lists:foldl(
                fun (N, Acc) ->
                        add_proof({Assumption, '->', N}, {'->i', [Assumption, false]}, Acc)
                end,
                add_proof({'!', Assumption}, {'!i', [Assumption, false]}, Parent#ps{rules = Rules}),
                [
                    P
                ||
                    P <- useful_to_prove(PS0),
                    not is_double_negated(P)
                ]
            );
        false ->
            lists:foldl(
                fun (N, Acc) ->
                        add_proof({Assumption, '->', N}, {'->i', [Assumption, N]}, Acc)
                end,
                Parent#ps{rules = Rules},
                [
                    P
                ||
                    P <- maps:keys(maps:with(useful_to_prove(PS0), Proved)),
                    not is_double_negated(P)
                ]
            )
    end.


reduce_proof_tree(Conclusion, ProofTree) ->
    reduce_proof_tree({undefined, Conclusion}, 0, ProofTree, []).


reduce_proof_tree({A, Expr}, Counter, ProofTree, Rules) ->
    {Rule, Exprs} = maps:get({A, Expr}, ProofTree, {bad_key, []}),
    [{Expr, Rule} | lists:concat([reduce_proof_tree(E, Counter, ProofTree, Rules) || E <- Exprs])].
