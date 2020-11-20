-module(lpg_print).

-export(
    [
        print_proof/1,
        expr_to_string/1,
        proof_to_iolist/1
    ]
).


print_proof(Proof) ->
    io:fwrite(proof_to_iolist(Proof)).


proof_to_iolist([]) ->
    [];
proof_to_iolist([{Ref, Expr, Rule, Refs} | Ps]) ->
    [
        string:pad(integer_to_binary(Ref), 2, trailing), %TODO don't pad fixed length
        <<"   ">>, %TODO other spacer?
        string:pad(expr_to_string(Expr), 16, trailing), %TODO don't pad fixed length
        <<"   ">>, %TODO other spacer?
        atom_to_binary(Rule, utf8), %TODO pad, custom?
        <<" ">>,
        lists:join(<<",">>, [integer_to_binary(R) || R <- Refs]), %TODO range when closing assumption
        <<"\n">>
    |
        proof_to_iolist(Ps)
    ].


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
