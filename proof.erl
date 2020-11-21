-module(proof).


-export(
    [
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
        elim_blocked = #{}, %TODO ordsets
        intro_blocked = #{}, %TODO ordsets
        conclusion,
        queue,
        parent,
        rules = #{},
        proof_refs = #{},
        implications = #{},
        disjunctions = #{}
    }
).


find_dm() ->
    find({[{'!', {p, '&', q}}], '|-', {{'!', p}, '|', {'!', q}}}).


find_dm2() ->
    find({[{{'!', p}, '|', {'!', q}}], '|-', {'!', {p, '&', q}}}).


find_q1() ->
    find({[{r, '->', {p, '|', q}}, {'!', {r, '&', q}}], '|-', {r, '->', p}}).


find({Premises, '|-', Conclusion}) ->
    Queue = sub_exprs([Conclusion | Premises]),
    PS =
        #ps{
            conclusion = Conclusion,
            queue = Queue
        },
    PS2 =
        lists:foldl(
            fun (P, Acc) ->
                    add_proof({premise, []}, P, Acc)
            end,
            PS,
            Premises
        ),
    prove(PS2).


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
    NrProvedBefore = nr_proved(PS),
    PS2 = process_queue(PS),
    NrProvedAfter = nr_proved(PS2),
    ProofFound = is_proved(PS2#ps.conclusion, PS2),
    %TODO counter proof check?
    if
        ProofFound ->
            build_proof(PS2);
        NrProvedAfter =:= NrProvedBefore ->
            PS3 = start_assumptions(PS2),
            case nr_proved(PS3) =:= NrProvedBefore of
                true ->
                    no_proof_found;
                false ->
                    prove(requeue(PS3))
            end;
        true ->
            prove(requeue(PS2))
    end.


nr_proved(PS) ->
    maps:size(PS#ps.proved).


requeue(PS) ->
    PS#ps{queue = maps:keys(PS#ps.intro_blocked)}.


process_queue(PS) ->
    lists:foldl(
        fun intro/2,
        PS,
        PS#ps.queue
    ).


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
    case is_proved({'!', Expr}, PS2) of
        true ->
            add_proof({'!e', [Expr, {'!', Expr}]}, false, PS2);
        false ->
            add_elim_blocked({'!', Expr}, Expr, PS2)
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
    PS2 =
        case is_proved(A, PS) of
            true ->
                add_proof({'->e', [A, Expr]}, B, PS);
            false ->
                add_elim_blocked(A, Expr, PS)
        end,
    case is_proved({'!', B}, PS2) of
        true ->
            add_proof({'MT', [{'!', B}, Expr]}, {'!', A}, PS2);
        false ->
            add_elim_blocked({'!', B}, Expr, PS2)
    end;
elim_({'!', {'!', A}} = Expr, PS) ->
    add_proof({'!!e', [Expr]}, A, PS);
elim_({'!', A} = Expr, PS) ->
    case is_proved(A, PS) of
        true ->
            add_proof({'!e', [A, Expr]}, false, PS);
        false ->
            add_elim_blocked(A, Expr, PS)
    end;
elim_(_, PS) ->
    PS.


add_intro_if_proved({_, Exprs} = Rule, Expr, PS) ->
    Unproved =
        [
            {E, Expr}
        ||
            E <- Exprs,
            not is_proved(E, PS)
        ],
    case Unproved of
        [] ->
            add_proof(Rule, Expr, PS);
        _ ->
            lists:foldl(
                fun add_intro_blocked/2,
                PS,
                Unproved
            )
    end.


add_intro_blocked({Key, Expr}, PS) ->
    BlockedByKey = maps:get(Key, PS#ps.intro_blocked, []),
    PS#ps{intro_blocked = (PS#ps.intro_blocked)#{Key => [Expr | BlockedByKey]}}.


add_elim_blocked(Key, Expr, PS) ->
    BlockedByKey = maps:get(Key, PS#ps.elim_blocked, []),
    PS#ps{elim_blocked = (PS#ps.elim_blocked)#{Key => [Expr | BlockedByKey]}}.


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
            PS5 = unblock_intro(Expr, PS4),
            PS6 = unblock_elim(Expr, PS5),
            elim(Expr, PS6)
    end.


unblock_intro(Expr, PS) ->
    lists:foldl(
        fun intro/2,
        PS#ps{intro_blocked = maps:remove(Expr, PS#ps.intro_blocked)},
        maps:get(Expr, PS#ps.intro_blocked, [])
    ).


unblock_elim(Expr, PS) ->
    PS2 =
        case Expr of
            {A, '->', _} ->
                lists:foldl(
                    fun elim/2,
                    PS#ps{elim_blocked = maps:remove(Expr, PS#ps.elim_blocked)},
                    ordsets:to_list(maps:get(A, PS#ps.disjunctions, ordsets:new()))
                );
            _ ->
                PS
        end,
    lists:foldl(
        fun elim/2,
        PS2#ps{elim_blocked = maps:remove(Expr, PS2#ps.elim_blocked)},
        maps:get(Expr, PS2#ps.elim_blocked, [])
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


start_assumptions(#ps{intro_blocked = IB, elim_blocked = EB, conclusion = C} = PS) ->
    NewAssumptions =
        [
            A
        ||
            A <- maps:keys(maps:merge(IB, EB)) ++ [negate(C)],
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
    NrProvedBefore = nr_proved(PS),
    PS2 = process_queue(PS),
    NrProvedAfter = nr_proved(PS2),
    BottomFound = is_proved(false, PS2),
    if
        BottomFound ->
            end_assumption(PS2);
        NrProvedAfter =:= NrProvedBefore ->
            PS3 = start_assumptions(PS2),
            case nr_proved(PS3) =:= NrProvedBefore of
                true ->
                    end_assumption(PS3);
                false ->
                    assumption(requeue(PS3))
            end;
        true ->
            assumption(requeue(PS2))
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


useful_to_prove(#ps{intro_blocked = IB, elim_blocked = EB, disjunctions = DJ}) ->
    A = maps:keys(IB),
    B = maps:keys(EB),
    C = lists:merge(maps:values(IB)),
    D = lists:merge(maps:values(EB)),
    E = maps:keys(DJ),
    [
        N
    ||
        N <- lists:usort(A ++ B ++ C ++ D ++ E),
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


