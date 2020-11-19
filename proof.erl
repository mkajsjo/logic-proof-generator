-module(proof).


-export(
    [
        find_dm/0,
        find/1,
        prove/1 %TODO remove
    ]
).


-record(
    ps,
    {
        proved = #{},
        proved_in_assumption = #{},
        assumption,
        elim_blocked = #{},
        intro_blocked = #{},
        conclusion,
        queue,
        parent
    }
).


find_dm() ->
    find({[{'!', {p, '&', q}}], '|-', {{'!', p}, '|', {'!', q}}}).


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
    BottomFound = is_proved(false, PS2),
    ProofFound = is_proved(PS2#ps.conclusion, PS2),
    %TODO counter proof check?
    if
        BottomFound ->
            proof_found_by_bottom; %TODO just proof_found
        ProofFound ->
            proof_found;
        NrProvedAfter =:= NrProvedBefore ->
            start_assumptions(PS2);
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


elim({A, '&', B} = Expr, PS) ->
    PS2 = add_elim_if_proved({'&e1', [Expr]}, A, PS),
    add_elim_if_proved({'&e2', [Expr]}, B, PS2);
elim({A, '->', B} = Expr, PS) ->
    PS2 = add_elim_if_proved({'->e', [A, Expr]}, B, PS),
    add_elim_if_proved({'MT', [{'!', B}, Expr]}, A, PS2);
elim({'!', {'!', A}} = Expr, PS) ->
    add_elim_if_proved({'!!e', [Expr]}, A, PS);
elim({'!', A} = Expr, PS) ->
    add_elim_if_proved({'!e', [A, Expr]}, false, PS);
elim(false, PS) ->
    lists:foldl(
        fun (Expr, Acc) ->
                add_elim_if_proved({'Fe', [false]}, Expr, Acc)
        end,
        PS,
        useful_to_prove(PS)
    );
elim(Expr, PS) ->
    add_elim_if_proved({'!e', [{'!', Expr}, Expr]}, false, PS).


add_intro_if_proved({Rule, Exprs}, Expr, PS) ->
    Unproved =
        [
            {E, Expr}
        ||
            E <- Exprs,
            not is_proved(E, PS)
        ],
    case Unproved of
        [] ->
            add_proof(Expr, {Rule, Exprs}, PS);
        _ ->
            lists:foldl(
                fun add_intro_blocked/2,
                PS,
                Unproved
            )
    end.


add_elim_if_proved({Rule, Exprs}, Expr, PS) ->
    Unproved =
        [
            {E, Expr}
        ||
            E <- Exprs,
            not is_proved(E, PS)
        ],
    case Unproved of
        [] ->
            add_proof(Expr, {Rule, Exprs}, PS);
        _ ->
            lists:foldl(
                fun add_elim_blocked/2,
                PS,
                Unproved
            )
    end.


add_intro_blocked({Key, Expr}, PS) ->
    BlockedByKey = maps:get(Key, PS#ps.intro_blocked, []),
    PS#ps{intro_blocked = (PS#ps.intro_blocked)#{Key => [Expr | BlockedByKey]}}.


add_elim_blocked({Key, Expr}, PS) ->
    BlockedByKey = maps:get(Key, PS#ps.elim_blocked, []),
    PS#ps{elim_blocked = (PS#ps.elim_blocked)#{Key => [Expr | BlockedByKey]}}.


is_proved(Expr, PS) ->
    maps:is_key(Expr, PS#ps.proved) orelse
    maps:is_key(Expr, PS#ps.proved_in_assumption).


add_proof(Expr, {_Rule, _Exprs}, PS) ->
    case is_proved(Expr, PS) of
        true ->
            PS;
        false ->
            PS2 = add_proof_(Expr, PS),
            PS3 = unblock_intro(Expr, PS2),
            PS4 = unblock_elim(Expr, PS3),
            elim(Expr, PS4)
    end.


unblock_intro(Expr, PS) ->
    lists:foldl(
        fun intro/2,
        PS#ps{intro_blocked = maps:remove(Expr, PS#ps.intro_blocked)},
        maps:get(Expr, PS#ps.intro_blocked, [])
    ).


unblock_elim(Expr, PS) ->
    lists:foldl(
        fun elim/2,
        PS#ps{elim_blocked = maps:remove(Expr, PS#ps.elim_blocked)},
        maps:get(Expr, PS#ps.elim_blocked, [])
    ).


add_proof_(Expr, #ps{assumption = undefined} = PS) ->
    PS#ps{proved = (PS#ps.proved)#{Expr => true}};
add_proof_(Expr, PS) ->
    PS#ps{proved_in_assumption = (PS#ps.proved_in_assumption)#{Expr => true}}.


start_assumptions(#ps{intro_blocked = IB, elim_blocked = EB} = PS) ->
    PreviousAssumptions = previous_assumptions(PS),
    NewAssumptions =
        [
            A
        ||
            A <- maps:keys(maps:merge(IB, EB)),
            not is_proved(negate(A), PS),
            not is_double_negated(A),
            not lists:member(A, PreviousAssumptions),
            not lists:member(negate(A), PreviousAssumptions)
        ],
    lists:foldl(
        fun start_assumption/2,
        PS,
        NewAssumptions
    ).


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


start_assumption(Assumption, PS) ->
    % Assumption could have been proved from previous assumption.
    case is_proved(Assumption, PS) of
        true ->
            PS;
        false ->
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


end_assumption(#ps{assumption = A, parent = P, proved = Proved} = PS0) ->
    PS =
        case is_proved(false, PS0) of
            true ->
                add_proof({'!i', [A, false]}, {'!', A}, P);
            false ->
                P
        end,
    NewProofs =
        [
            N
        ||
            N <- maps:keys(maps:with(useful_to_prove(P), Proved)),
            not is_double_negated(N)
        ],
    lists:foldl(
        fun (N, Acc) ->
                add_proof({'->i', [A, N]}, {A, '->', N}, Acc)
        end,
        PS,
        NewProofs
    ).


useful_to_prove(#ps{intro_blocked = IB, elim_blocked = EB}) ->
    A = maps:keys(IB),
    B = maps:keys(EB),
    C = lists:merge(maps:values(IB)),
    D = lists:merge(maps:values(EB)),
    lists:usort(A ++ B ++ C ++ D).
