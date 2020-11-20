-module(lpg_print).

-export(
    [
        print_proof/1,
        expr_to_string/1,
        proof_to_iolist/1
    ]
).

-define(REFS_LENGTH, 12).
-define(SPACER_LENGTH, 3).


print_proof(Proof) ->
    io:fwrite(proof_to_iolist(Proof)).


proof_to_iolist(Proof) ->
    proof_to_iolist(Proof, calc_proof_paddings(Proof)).


proof_to_iolist([], _) ->
    [];
proof_to_iolist(
    [{Ref, Expr, Rule, Refs} | Ps],
    #{row_nr_size := RS, exprs_size := ES, open_boxes := OB, inner_boxes := IB} = Map0
) ->
    OpenBoxes = open_or_close_box(Rule, OB),
    InnerBoxes =
        case Rule of
            assumption ->
                [find_nr_inner_boxes(Ps) | IB];
            R when R =:= '->i'; R =:= '!i'; R =:= 'PBC' ->
                tl(IB);
            _ ->
                IB
        end,
    Map =
        Map0#{
            open_boxes => OpenBoxes,
            inner_boxes => InnerBoxes
        },
    [
        close_assumption_box(Rule, Map0),
        open_assumption_box(Rule, Map),
        string:pad(integer_to_binary(Ref), RS, trailing),
        <<"   ">>, %TODO other spacer?
        assumption_boxes_vertical(Map, leading),
        string:pad(expr_to_string(Expr), ES, trailing),
        <<"   ">>, %TODO other spacer?
        string:pad(
            unicode:characters_to_binary(
                [
                    string:pad(atom_to_binary(Rule, utf8), 3, trailing),
                    <<" ">>,
                    format_references(Rule, Refs)
                ]
            ),
            ?REFS_LENGTH,
            trailing
        ),
        assumption_boxes_vertical(Map, trailing),
        <<"\n">>
    |
        proof_to_iolist(Ps, Map)
    ].


calc_proof_paddings(Proof) ->
    calc_proof_paddings(
        Proof,
        #{
            row_nr_size => 0,
            open_boxes => 0,
            max_boxes => 0,
            exprs_size => 0
        }
    ).


calc_proof_paddings([], Acc) ->
    Acc#{inner_boxes => [0]};
calc_proof_paddings([{Ref, Expr, Rule, _} | Ps], Map) ->
    #{
        open_boxes := OpenBoxes0,
        max_boxes := MaxBoxes,
        exprs_size := ExprsSize
    }
        = Map,
    OpenBoxes = open_or_close_box(Rule, OpenBoxes0),
    calc_proof_paddings(
        Ps,
        #{
            row_nr_size => string:length(integer_to_binary(Ref)),
            open_boxes => OpenBoxes,
            max_boxes => max(OpenBoxes, MaxBoxes),
            exprs_size => max(string:length(expr_to_string(Expr)), ExprsSize)
        }
    ).


open_or_close_box(assumption, OpenBoxes) ->
    OpenBoxes + 1;
open_or_close_box(Rule, OpenBoxes) when Rule =:= '->i'; Rule =:= '!i'; Rule =:= 'PBC' ->
    OpenBoxes - 1;
open_or_close_box(_, OpenBoxes) ->
    OpenBoxes.


find_nr_inner_boxes(Proofs) ->
    find_nr_inner_boxes(Proofs, 0, 0).


find_nr_inner_boxes([], _, NrInnerBoxes) ->
    NrInnerBoxes;
find_nr_inner_boxes(_, -1, NrInnerBoxes) ->
    io:fwrite("NrInnerBoxes: ~p~n", [NrInnerBoxes]),
    NrInnerBoxes;
find_nr_inner_boxes([{_, _, assumption, _} | Ps], Counter, NrInnerBoxes) ->
    find_nr_inner_boxes(
        Ps,
        Counter + 1,
        max(NrInnerBoxes, Counter + 1)
    );
find_nr_inner_boxes([{_, _, Rule, _} | Ps], Counter, NrInnerBoxes) when Rule =:= '->i'; Rule =:= '!i'; Rule =:= 'PBC' ->
    find_nr_inner_boxes(
        Ps,
        Counter - 1,
        NrInnerBoxes
    );
find_nr_inner_boxes([_ | Ps], Counter, NrInnerBoxes) ->
    find_nr_inner_boxes(Ps, Counter, NrInnerBoxes).


open_assumption_box(assumption, Map) ->
    assumption_box_horizontal(Map);
open_assumption_box(_, _) ->
    <<>>.


close_assumption_box(Rule, Map) when Rule =:= '->i'; Rule =:= '!i'; Rule =:= 'PBC' ->
    assumption_box_horizontal(Map);
close_assumption_box(_, _) ->
    <<>>.


assumption_box_horizontal(
    #{
        row_nr_size := RowNrSize,
        exprs_size := ExprsSize,
        inner_boxes := [InnerBoxes | _],
        open_boxes := OpenBoxes,
        max_boxes := MaxBoxes
    }
) ->
    [
        lists:duplicate(RowNrSize + 3, <<" ">>), %TODO magic number
        string:pad(
            unicode:characters_to_binary(
                lists:duplicate(OpenBoxes - 1, <<"|">>)
                ++ [<<"┼"/utf8>> | lists:duplicate(InnerBoxes, <<"-">>)]
            ),
            MaxBoxes,
            leading
        ),
        lists:duplicate(ExprsSize + InnerBoxes + ?SPACER_LENGTH + ?REFS_LENGTH, <<"-">>),
        <<"┼"/utf8>>,
        lists:duplicate(OpenBoxes - 1, <<"|">>),
        <<"\n">>
    ].


assumption_boxes_vertical(#{open_boxes := O, max_boxes := M, inner_boxes := [I|_]}, PadDirection) ->
    Foo =
        case PadDirection of
            leading ->
                lists:duplicate(O, <<"|">>) ++ lists:duplicate(I, <<" ">>);
            trailing ->
                lists:duplicate(I, <<" ">>) ++ lists:duplicate(O, <<"|">>)
        end,
    string:pad(
        unicode:characters_to_binary(Foo),
        M,
        PadDirection
    ).


format_references(Rule, [A, B]) when Rule =:= '->i'; Rule =:= '!i'; Rule =:= 'PBC' ->
    [
        integer_to_binary(A),
        <<"-">>,
        integer_to_binary(B)
    ];
format_references(_, Refs) ->
    lists:join(
        <<",">>,
        [integer_to_binary(R) || R <- Refs]
    ).


expr_to_string({'!', {_, _, _} = Expr}) ->
    <<
        "!(",
        (expr_to_string(Expr))/binary,
        ")"
    >>;
expr_to_string({'!', Expr}) ->
    <<
        "!",
        (expr_to_string(Expr))/binary
    >>;
expr_to_string({A0, Op, B0}) ->
    <<
        (fix_precedence(A0, lower_precedence_ops(Op, left)))/binary,
        " ",
        (atom_to_binary(Op, utf8))/binary,
        " ",
        (fix_precedence(B0, lower_precedence_ops(Op, right)))/binary
    >>;
expr_to_string(P) ->
    atom_to_binary(P, utf8).


fix_precedence({_, Op, _} = Expr, Ops) ->
    S = expr_to_string(Expr),
    case lists:member(Op, Ops) of
        true ->
            <<"(", S/binary, ")">>;
        false ->
            S
    end;
fix_precedence(Expr, _) ->
    expr_to_string(Expr).


lower_precedence_ops('&', _) ->
    ['|', '->'];
lower_precedence_ops('|', _) ->
    ['->'];
lower_precedence_ops('->', left) ->
    ['->'];
lower_precedence_ops(_, _) ->
    [].
