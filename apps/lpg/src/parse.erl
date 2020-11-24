-module(parse).

-export(
    [
        sequent/1
    ]
).


sequent(String) ->
    parse_sequent({[], []}, tokenize(String)).


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


parse_sequent({Exprs, Unparsed}, [',' | Tokens]) ->
    case parse_expr(lists:reverse(Unparsed)) of
        {ok, Expr} ->
            parse_sequent({[Expr | Exprs], []}, Tokens);
        {error, Rest} ->
            {error, Rest ++ [',' | Tokens]}
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
            {error, Rest ++ [',' | Tokens]}
    end;
parse_sequent({Exprs, Unparsed}, [T | Tokens]) ->
    parse_sequent({Exprs, [T | Unparsed]}, Tokens);
parse_sequent(Acc, []) ->
    {error, lists:reverse(Acc)}.


parse_expr(Expr) ->
    case parse_paranthesis(Expr) of
        {ok, Result} ->
            {ok, Result};
        {error, _} ->
            case parse_implication([], lists:reverse(Expr)) of
                {ok, Result} ->
                    {ok, Result};
                {error, _} ->
                    case parse_conjunction([], Expr) of
                        {ok, Result} ->
                            {ok, Result};
                        {error, Rest} ->
                            case parse_disjunction([], Expr) of
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
    case parse_expr(Acc) of
        {ok, B} ->
            case parse_expr(lists:reverse(Tokens)) of
                {ok, A} ->
                    {ok, {A, '->', B}};
                {error, Rest} ->
                    {error, Rest}
            end;
        {error, Rest} ->
            {error, Rest ++ lists:reverse(Tokens)}
    end;
parse_implication(Acc, [T | Tokens]) ->
    parse_implication([T | Acc], Tokens);
parse_implication(Acc, []) ->
    {error, Acc}.


parse_conjunction(Acc, ['&' | Tokens]) ->
    case parse_expr(lists:reverse(Acc)) of
        {ok, A} ->
            case parse_expr(Tokens) of
                {ok, B} ->
                    {ok, {A, '&', B}};
                {error, Rest} ->
                    {error, Rest}
            end;
        {error, Rest} ->
            {error, Rest ++ Tokens}
    end;
parse_conjunction(Acc, [T | Tokens]) ->
    parse_conjunction([T | Acc], Tokens);
parse_conjunction(Acc, []) ->
    {error, lists:reverse(Acc)}.


parse_disjunction(Acc, ['|' | Tokens]) ->
    case parse_expr(lists:reverse(Acc)) of
        {ok, A} ->
            case parse_expr(Tokens) of
                {ok, B} ->
                    {ok, {A, '|', B}};
                {error, Rest} ->
                    {error, Rest}
            end;
        {error, Rest} ->
            {error, Rest ++ Tokens}
    end;
parse_disjunction(Acc, [T | Tokens]) ->
    parse_disjunction([T | Acc], Tokens);
parse_disjunction(Acc, []) ->
    {error, lists:reverse(Acc)}.


parse_proposition([false]) ->
    {ok, false};
parse_proposition([<<P>>]) ->
    {ok, <<P>>};
parse_proposition(Rest) ->
    {error, Rest}.



