-module(parse).

-export(
    [
        sequent/1,
        expr/1
    ]
).


sequent(String) ->
    case parse_sequent({[], []}, tokenize(String)) of
        {ok, Expr} ->
            {ok, Expr};
        {error, Tokens} ->
            {error, detokenize(Tokens)}
    end.


expr(String) ->
    case parse_expr(tokenize(String)) of
        {ok, Expr} ->
            {ok, Expr};
        {error, Tokens} ->
            {error, detokenize(Tokens)}
    end.


tokenize(<<>>) ->
    [];
tokenize(<<"|-", Rest/binary>>) ->
    ['|-' | tokenize(Rest)];
tokenize(<<" ", Rest/binary>>) ->
    tokenize(Rest);
tokenize(<<"&", Rest/binary>>) ->
    ['&' | tokenize(Rest)];
tokenize(<<"|", Rest/binary>>) ->
    ['|' | tokenize(Rest)];
tokenize(<<"->", Rest/binary>>) ->
    ['->' | tokenize(Rest)];
tokenize(<<"!", Rest/binary>>) ->
    ['!' | tokenize(Rest)];
tokenize(<<"(", Rest/binary>>) ->
    ['(' | tokenize(Rest)];
tokenize(<<")", Rest/binary>>) ->
    [')' | tokenize(Rest)];
tokenize(<<"false", Rest/binary>>) ->
    [false | tokenize(Rest)];
tokenize(<<",", Rest/binary>>) ->
    [',' | tokenize(Rest)];
tokenize(<<P:8, Rest/binary>>) when P >= $a, P =< $z; P >= $A, P =< $Z ->
    [<<P>> | tokenize(Rest)].


detokenize([]) ->
    <<>>;
detokenize([Token | Tokens]) when is_atom(Token) ->
    <<(atom_to_binary(Token, utf8))/binary, (detokenize(Tokens))/binary>>;
detokenize([Token | Tokens]) ->
    <<Token/binary, (detokenize(Tokens))/binary>>.


parse_sequent(_, ['|-']) ->
    {error, ['|-']};
parse_sequent(_, [',', '|-' | _] = Tokens) ->
    {error, Tokens};
parse_sequent({[], []}, [',' | Tokens]) ->
    {error, [',' | Tokens]};
parse_sequent({Exprs, Unparsed}, [',' | Tokens]) ->
    case parse_expr(lists:reverse(Unparsed)) of
        {ok, Expr} ->
            parse_sequent({[Expr | Exprs], []}, Tokens);
        {error, Rest} ->
            {error, Rest ++ [',' | Tokens]}
    end;
parse_sequent({Exprs, []}, ['|-' | Tokens]) ->
    case parse_expr(Tokens) of
        {ok, Conclusion} ->
            {ok, {lists:reverse(Exprs), '|-', Conclusion}};
        {error, Rest} ->
            {error, Rest}
    end;
parse_sequent({Exprs, Unparsed}, ['|-' | Tokens]) ->
    case parse_expr(lists:reverse(Unparsed)) of
        {ok, Expr} ->
            case parse_expr(Tokens) of
                {ok, Conclusion} ->
                    {ok, {lists:reverse([Expr | Exprs]), '|-', Conclusion}};
                {error, Rest} ->
                    {error, Rest}
            end;
        {error, Rest} ->
            {error, Rest ++ ['|-' | Tokens]}
    end;
parse_sequent({Exprs, Unparsed}, [T | Tokens]) ->
    parse_sequent({Exprs, [T | Unparsed]}, Tokens);
parse_sequent({_, Unparsed}, []) ->
    {error, lists:reverse(Unparsed)}.


parse_expr(Expr) ->
    case parse_paranthesis(Expr) of
        {ok, Result} ->
            {ok, Result};
        {error, _} ->
            case parse_implication([], Expr) of
                {ok, Result} ->
                    {ok, Result};
                {error, _} ->
                    case parse_disjunction([], lists:reverse(Expr)) of
                        {ok, Result} ->
                            {ok, Result};
                        {error, _} ->
                            case parse_conjunction([], lists:reverse(Expr)) of
                                {ok, Result} ->
                                    {ok, Result};
                                {error, _} ->
                                    case parse_negation(Expr) of
                                        {ok, Result} ->
                                            {ok, Result};
                                        {error, _} ->
                                            case parse_proposition(Expr) of
                                                {ok, Result} ->
                                                    {ok, Result};
                                                {error, Rest} ->
                                                    {error, Rest}
                                            end
                                    end
                            end
                    end
            end
    end.


parse_negation(['!' | Unparsed]) ->
    case parse_expr(Unparsed) of
        {ok, Expr} ->
            {ok, {'!', Expr}};
        {error, Rest} ->
            {error, Rest}
    end;
parse_negation(Rest) ->
    {error, Rest}.


parse_paranthesis(['(' | Unparsed]) ->
    case lists:last(Unparsed) of
        ')' ->
            case parse_expr(lists:droplast(Unparsed)) of
                {ok, Expr} ->
                    {ok, Expr};
                {error, Rest} ->
                    {error, Rest}
            end;
        _ ->
            {error, ['(' | Unparsed]}
    end;
parse_paranthesis(Rest) ->
    {error, Rest}.


parse_implication(Acc, ['->' | Tokens]) ->
    case parse_expr(lists:reverse(Acc)) of
        {ok, A} ->
            case parse_expr(Tokens) of
                {ok, B} ->
                    {ok, {A, '->', B}};
                {error, _} ->
                    parse_implication(['->' | Acc], Tokens)
            end;
        {error, _} ->
            parse_implication(['->' | Acc], Tokens)
    end;
parse_implication(Acc, [T | Tokens]) ->
    parse_implication([T | Acc], Tokens);
parse_implication(Acc, []) ->
    {error, lists:reverse(Acc)}.


parse_conjunction(Acc, ['&' | Tokens]) ->
    case parse_expr(Acc) of
        {ok, B} ->
            case parse_expr(lists:reverse(Tokens)) of
                {ok, A} ->
                    {ok, {A, '&', B}};
                {error, _} ->
                    parse_conjunction(['&' | Acc], Tokens)
            end;
        {error, _} ->
            parse_conjunction(['&' | Acc], Tokens)
    end;
parse_conjunction(Acc, [T | Tokens]) ->
    parse_conjunction([T | Acc], Tokens);
parse_conjunction(Acc, []) ->
    {error, Acc}.


parse_disjunction(Acc, ['|' | Tokens]) ->
    case parse_expr(Acc) of
        {ok, B} ->
            case parse_expr(lists:reverse(Tokens)) of
                {ok, A} ->
                    {ok, {A, '|', B}};
                {error, _} ->
                    parse_disjunction(['|' | Acc], Tokens)
            end;
        {error, _} ->
            parse_disjunction(['|' | Acc], Tokens)
    end;
parse_disjunction(Acc, [T | Tokens]) ->
    parse_disjunction([T | Acc], Tokens);
parse_disjunction(Acc, []) ->
    {error, Acc}.


parse_proposition([false]) ->
    {ok, false};
parse_proposition([<<P>>]) ->
    {ok, <<P>>};
parse_proposition(Rest) ->
    {error, Rest}.



