-module(proof).


-export(
    [
        solve/1,
        find_dm/0,
        find_dm2/0,
        find_q1/0,
        find/1
    ]
).


-record(
    ps,
    {
        proved = #{},
        proved_in_assumption = #{},
        assumption,
        next_proof_ref = 0,
        blocked = #{},
        conclusion,
        parent,
        rules = #{},
        proof_refs = #{},
        implications = #{},
        disjunctions = #{}
    }
).


solve(BinarySequent) ->
    case parse:sequent(BinarySequent) of
        {ok, Sequent} ->
            case find(Sequent) of
                no_proof_found ->
                    io:fwrite("No proof found~n");
                Proof ->
                    print:print_proof(Proof)
            end;
        {error, Error} ->
            io:fwrite("Error: ~p~n", [Error])
    end.


find_dm() ->
    find({[{'!', {p, '&', q}}], '|-', {{'!', p}, '|', {'!', q}}}).


find_dm2() ->
    find({[{{'!', p}, '|', {'!', q}}], '|-', {'!', {p, '&', q}}}).


find_q1() ->
    find({[{r, '->', {p, '|', q}}, {'!', {r, '&', q}}], '|-', {r, '->', p}}).


find({Premises, '|-', Conclusion}) ->
    SubExprs = sub_exprs([Conclusion | Premises]),
    PS = #ps{conclusion = Conclusion},
    PS2 =
        lists:foldl(
            fun (P, Acc) ->
                    add_proof({premise, []}, P, Acc)
            end,
            PS,
            Premises
        ),
    PS3 =
        lists:foldl(
            fun intro/2,
            PS2,
            SubExprs
        ),
    prove(PS3).


sub_exprs(Exprs) ->
    maps:keys(
        lists:foldl(
            fun sub_exprs/2,
            #{},
            Exprs
        )
    ).


sub_exprs({A, _, B} = Expr, Exprs) ->
    sub_exprs(B, sub_exprs(A, maps:put(Expr, true, Exprs)));
sub_exprs({_, A} = Expr, Exprs) ->
    sub_exprs(A, maps:put(Expr, true, Exprs));
sub_exprs(P, Exprs) ->
    maps:put(P, true, Exprs).


prove(PS) ->
    %TODO counter proof check?
    case is_proved(PS#ps.conclusion, PS) of
        true ->
            build_proof(PS);
        false ->
            PS2 = start_assumptions(PS),
            case nr_proved(PS2) =:= nr_proved(PS) of
                true ->
                    no_proof_found;
                false ->
                    prove(PS2)
            end
    end.


nr_proved(PS) ->
    maps:size(PS#ps.proved).


intro({A, '&', B} = Expr, PS) ->
    add_intro_if_proved({'&i', [A, B]}, Expr, PS);
intro({A, '|', B} = Expr, PS) ->
    PS2 = add_intro_if_proved({'|i1', [A]}, Expr, PS),
    add_intro_if_proved({'|i2', [B]}, Expr, PS2);
intro({'!', {'!', A}} = Expr, PS) ->
    add_intro_if_proved({'!!i', [A]}, Expr, PS);
intro(_, PS) ->
    PS.


elim(false, PS) ->
    lists:foldl(
        fun (Expr, Acc) ->
                add_proof({'Fe', [false]}, Expr, Acc)
        end,
        PS,
        useful_to_prove(PS)
    );
elim(Expr, PS) ->
    PS2 = elim_(Expr, PS),
    Rule = {'!e', [Expr, {'!', Expr}]},
    case is_proved({'!', Expr}, PS2) of
        true ->
            add_proof(Rule, false, PS2);
        false ->
            block({'!', Expr}, Rule, false, PS2)
    end.


elim_({A, '&', B} = Expr, PS) ->
    PS2 = add_proof({'&e1', [Expr]}, A, PS),
    add_proof({'&e2', [Expr]}, B, PS2);
elim_({A, '|', B} = Expr, PS) ->
    DisjunctionsWithB = maps:get(A, PS#ps.disjunctions, ordsets:new()),
    DisjunctionsWithA = maps:get(B, PS#ps.disjunctions, ordsets:new()),
    PS2 =
        PS#ps{
            disjunctions = (PS#ps.disjunctions)#{
                A => ordsets:add_element(Expr, DisjunctionsWithB),
                B => ordsets:add_element(Expr, DisjunctionsWithA)
            }
        },
    lists:foldl(
        fun (N, Acc) ->
                add_proof({'|e', [Expr, {A, '->', N}, {B, '->', N}]}, N, Acc)
        end,
        PS2,
        ordsets:to_list(
            ordsets:intersection(
                maps:get(A, PS2#ps.implications, ordsets:new()),
                maps:get(B, PS2#ps.implications, ordsets:new())
            )
        )
    );
elim_({A, '->', B} = Expr, PS) ->
    ImplElim = {'->e', [A, Expr]},
    MT = {'MT', [{'!', B}, Expr]},
    PS2 =
        case is_proved(A, PS) of
            true ->
                add_proof(ImplElim, B, PS);
            false ->
                block(A, ImplElim, B, PS)
        end,
    case is_proved({'!', B}, PS2) of
        true ->
            add_proof(MT, {'!', A}, PS2);
        false ->
            block({'!', B}, MT, {'!', A}, PS2)
    end;
elim_({'!', {'!', A}} = Expr, PS) ->
    add_proof({'!!e', [Expr]}, A, PS);
elim_({'!', A} = Expr, PS) ->
    Rule = {'!e', [A, Expr]},
    case is_proved(A, PS) of
        true ->
            add_proof(Rule, false, PS);
        false ->
            block(A, Rule, false, PS)
    end;
elim_(_, PS) ->
    PS.


add_intro_if_proved({_, Exprs} = Rule, Expr, PS) ->
    Unproved =
        [
            E
        ||
            E <- Exprs,
            not is_proved(E, PS)
        ],
    case Unproved of
        [] ->
            add_proof(Rule, Expr, PS);
        _ ->
            lists:foldl(
                fun(U, Acc) ->
                        block(U, Rule, Expr, [B || B <- Unproved, B =/= U], Acc)
                end,
                PS,
                Unproved
            )
    end.


block(Blocker, Rule, Expr, PS) ->
    block(Blocker, Rule, Expr, [], PS).


block(Blocker, Rule, Expr, ExtraBlockers, PS) ->
    Blocked = maps:get(Blocker, PS#ps.blocked, []),
    Entry = {Rule, Expr, ExtraBlockers},
    PS#ps{blocked = (PS#ps.blocked)#{Blocker => [Entry | Blocked]}}.


is_proved(Expr, PS) ->
    maps:is_key(Expr, PS#ps.proved) orelse
    maps:is_key(Expr, PS#ps.proved_in_assumption).


add_proof(Rule, Expr, PS) ->
    case is_proved(Expr, PS) of
        true ->
            PS;
        false ->
            %io:fwrite("Proof: ~p~n", [Expr]), %TODO remove
            PS2 =
                case Expr of
                    {A, '->', _} ->
                        add_proof({'LEM', []}, {A, '|', negate(A)}, PS);
                    _ ->
                        PS
                end,
            PS3 = add_proof_(Expr, PS2),
            PS4 = add_proof_rule(Rule, Expr, PS3),
            PS5 = unblock(Expr, PS4),
            elim(Expr, PS5)
    end.


unblock(Key, #ps{blocked = Blocked} = PS) ->
    PS2 = PS#ps{blocked = maps:remove(Key, Blocked)},
    PS3 =
        case Key of
            {A, '->', _} ->
                lists:foldl(
                    fun elim/2,
                    PS2,
                    ordsets:to_list(maps:get(A, PS#ps.disjunctions, ordsets:new()))
                );
            _ ->
                PS2
        end,
    lists:foldl(
        fun ({Rule, Expr, Blockers}, Acc) ->
            case lists:all(fun(B) -> is_proved(B, Acc) end, Blockers) of
                true ->
                    add_proof(Rule, Expr, Acc);
                false ->
                    Acc
            end
        end,
        PS3,
        maps:get(Key, Blocked, [])
    ).


add_proof_(
    Expr,
    #ps{
        assumption = A,
        proved = Proved,
        proved_in_assumption = Proved2,
        implications = Impl0
    } = PS
) ->
    Impl =
        case Expr of
            {P, '->', Q} ->
                Implied = maps:get(P, Impl0, ordsets:new()),
                Impl0#{P => ordsets:add_element(Q, Implied)};
            _ ->
                Impl0
        end,
    case A of
        undefined ->
            PS#ps{
                proved = Proved#{Expr => true},
                implications = Impl
            };
        _ ->
            PS#ps{
                proved_in_assumption = Proved2#{Expr => true},
                implications = Impl
            }
    end.


start_assumptions(#ps{blocked = B, conclusion = C} = PS) ->
    NewAssumptions =
        [
            A
        ||
            A <- maps:keys(B) ++ [negate(C)],
            allowed_assumption(A, PS)
        ],
    lists:foldl(
        fun start_assumption/2,
        PS,
        NewAssumptions
    ).


allowed_assumption(Expr, PS) ->
    PreviousAssumptions = previous_assumptions(PS),
    Banned =
        case Expr of
            {A, '&', B} ->
                is_proved(A, PS) orelse is_proved(B, PS);
            _ ->
                false
        end,
    not Banned
    andalso not is_proved(negate(Expr), PS)
    andalso not is_double_negated(Expr)
    andalso not lists:member(Expr, PreviousAssumptions)
    andalso not lists:member(negate(Expr), PreviousAssumptions).


previous_assumptions(#ps{parent = undefined}) ->
    [];
previous_assumptions(#ps{assumption = A, parent = P}) ->
    [A | previous_assumptions(P)].


negate({'!', Expr}) ->
    Expr;
negate(Expr) ->
    {'!', Expr}.


is_double_negated({'!', {'!', _}}) ->
    true;
is_double_negated(_) ->
    false.


is_implication({_, '->', _}) ->
    true;
is_implication(_) ->
    false.


start_assumption(Assumption, PS) ->
    % Assumption could have been proved from previous assumption.
    case is_proved(Assumption, PS) orelse is_proved(false, PS) of
        true ->
            PS;
        false ->
            %io:fwrite("Assumption: ~p~n", [Assumption]), %TODO remove
            Proved = maps:merge(PS#ps.proved, PS#ps.proved_in_assumption),
            PS2 =
                PS#ps{
                    assumption = Assumption,
                    proved = Proved,
                    proved_in_assumption = #{},
                    parent = PS
                },
            PS3 = add_proof({assumption, []}, Assumption, PS2),
            assumption(PS3)
    end.


assumption(PS) ->
    case is_proved(false, PS) of
        true ->
            end_assumption(PS);
        false ->
            PS2 = start_assumptions(PS),
            case nr_proved(PS2) =:= nr_proved(PS) of
                true ->
                    end_assumption(PS2);
                false ->
                    assumption(PS2)
            end
    end.


end_assumption(#ps{assumption = A, parent = P, proved_in_assumption = Proved, next_proof_ref = Ref,
                  rules = Rules, proof_refs = Refs} = PS0) ->
    %io:fwrite("End assumption: ~p~n~n", [A]), %TODO remove
    PS =
        P#ps{
            next_proof_ref = Ref,
            proof_refs = Refs,
            rules = Rules
        },
    PS2 =
        case {A, is_proved(false, PS0)} of
            {{'!', NotA}, true} ->
                add_proof({'PBC', [A, false]}, NotA, PS);
            {_, true} ->
                add_proof({'!i', [A, false]}, {'!', A}, PS);
            _ ->
                PS
        end,
    NewProofs =
        [
            N
        ||
            N <- maps:keys(maps:with(useful_to_prove(P), Proved))
        ],
    lists:foldl(
        fun (N, Acc) ->
            case allowed_implication({A, '->', N}) of
                true ->
                    add_proof({'->i', [A, N]}, {A, '->', N}, Acc);
                false ->
                    Acc
            end
        end,
        PS2,
        NewProofs
    ).


allowed_implication({{A, '&', _}, '->', A}) ->
    false;
allowed_implication({{_, '&', A}, '->', A}) ->
    false;
allowed_implication(_) ->
    true.


useful_to_prove(#ps{blocked = Blocked, disjunctions = DJ}) ->
    A = maps:keys(Blocked),
    B = [element(2, N) || N <- lists:merge(maps:values(Blocked))],
    C = maps:keys(DJ),
    [
        N
    ||
        N <- lists:usort(A ++ B ++ C),
        not is_double_negated(N),
        not is_implication(N),
        N =/= false
    ].


add_proof_rule({'|e', [Dj, ImplA, ImplB]}, Expr, PS) ->
    %^^^ Hack to move implications from assumptions to the correct place.
    DjRef = get_ref(Dj, PS),
    PS2 =
        case get_rule(ImplA, PS) of
            {_, '->i', [A, _]} when A < DjRef ->
                move_assumption(A, get_ref(ImplA, PS), PS);
            _ ->
                PS
        end,
    PS3 =
        case get_rule(ImplB, PS) of
            {_, '->i', [B, _]} when B < DjRef ->
                move_assumption(B, get_ref(ImplB, PS2), PS2);
            _ ->
                PS2
        end,
    add_rule(
        PS3#ps.next_proof_ref,
        {Expr, '|e', [DjRef, get_ref(ImplA, PS3), get_ref(ImplB, PS3)]},
        PS3#ps{proof_refs = PS#ps.proof_refs}
    );
add_proof_rule({Rule, Exprs}, Expr, PS) ->
    Ref =
        case {Rule, Expr} of % Hack to insert LEM before all implications.
            {'LEM', {A, '|', _}} ->
                get_ref(A, PS, PS#ps.next_proof_ref) - 1;
            _ ->
                PS#ps.next_proof_ref
        end,
    add_rule(
        Ref,
        {
            Expr,
            Rule,
            [get_ref(E, PS) || E <- Exprs]
        },
        PS
    ).


move_assumption(A, B, PS) when A > B ->
    PS;
move_assumption(A, B, PS) ->
    {Expr, Rule, Refs} = get_rule(B, PS),
    PS2 =
        lists:foldl(
            fun (R, Acc) ->
                    move_assumption(A, R, Acc)
            end,
            PS,
            Refs
        ),
    Exprs =
        [
            element(1, get_rule(R, PS))
        ||
            R <- Refs
        ],
    add_proof_rule({Rule, Exprs}, Expr, PS2).


add_rule(
    Ref,
    {Expr, _, _} = Rule,
    #ps{next_proof_ref = NextRef, rules = Rules, proof_refs = Refs} = PS
) ->
    PS#ps{
        next_proof_ref = NextRef + 2,
        rules = Rules#{Ref => Rule},
        proof_refs = Refs#{Expr => Ref}
    }.


get_ref(Expr, #ps{proof_refs = Refs}) ->
    maps:get(Expr, Refs).


get_ref(Expr, #ps{proof_refs = Refs}, Default) ->
    maps:get(Expr, Refs, Default).


get_rule(Ref, #ps{rules = Rules}) when is_integer(Ref) ->
    maps:get(Ref, Rules);
get_rule(Expr, #ps{rules = Rules, proof_refs = Refs}) ->
    Ref = maps:get(Expr, Refs),
    maps:get(Ref, Rules).


build_proof(#ps{conclusion = C, rules = Rules, proof_refs = Refs}) ->
    Ref = maps:get(C, Refs),
    ProofList = lists:keysort(1, lists:usort(build_proof(Ref, Rules))),
    fix_proof_references(ProofList).


build_proof(Ref, Rules) ->
    {Expr, Rule, Refs} = maps:get(Ref, Rules),
    [
        {Ref, Expr, Rule, Refs}
    |
        lists:merge([build_proof(R, Rules) || R <- Refs])
    ].


fix_proof_references(ProofList) ->
    fix_proof_references(ProofList, 1, #{}).


fix_proof_references([], _, _) ->
    [];
fix_proof_references([{Ref, Expr, Rule, Refs} | Ps], Counter, Map0) ->
    Map = Map0#{Ref => Counter},
    [
        {Counter, Expr, Rule, [maps:get(R, Map) || R <- Refs]}
    |
        fix_proof_references(Ps, Counter + 1, Map)
    ].


