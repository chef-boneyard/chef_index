-module(chef_lucene).
-export([parse/1,file/1]).
-define(p_charclass,true).
-define(p_choose,true).
-define(p_label,true).
-define(p_not,true).
-define(p_one_or_more,true).
-define(p_optional,true).
-define(p_scan,true).
-define(p_seq,true).
-define(p_string,true).
-define(p_zero_or_more,true).



%% @author Seth Falcon <seth@opscode.com>
%% Copyright 2011-2012 Opscode, Inc. All Rights Reserved.
%%
%% This file is provided to you under the Apache License,
%% Version 2.0 (the "License"); you may not use this file
%% except in compliance with the License.  You may obtain
%% a copy of the License at
%%
%%   http://www.apache.org/licenses/LICENSE-2.0
%%
%% Unless required by applicable law or agreed to in writing,
%% software distributed under the License is distributed on an
%% "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
%% KIND, either express or implied.  See the License for the
%% specific language governing permissions and limitations
%% under the License.
%%

-define(i2b(X), iolist_to_binary(X)).
-define(gv(X, L), proplists:get_value(X, L)).

% make sure these atoms are available.
-define(or_op1, 'OR').
-define(or_op2, '||').
-define(and_op1, 'AND').
-define(and_op2, '&&').
-define(not_op, 'NOT').
-define(not_bang_op, '!').

-spec file(file:name()) -> any().
file(Filename) -> case file:read_file(Filename) of {ok,Bin} -> parse(Bin); Err -> Err end.

-spec parse(binary() | list()) -> any().
parse(List) when is_list(List) -> parse(list_to_binary(List));
parse(Input) when is_binary(Input) ->
  setup_memo(),
  Result = case 'query'(Input,{{line,1},{column,1}}) of
             {AST, <<>>, _Index} -> AST;
             Any -> Any
           end,
  release_memo(), Result.

-spec 'query'(input(), index()) -> parse_result().
'query'(Input, Index) ->
  p(Input, Index, 'query', fun(I,D) -> (p_choose([fun 'star_star'/2, p_zero_or_more(p_choose([fun 'expression'/2, fun 'space'/2]))]))(I,D) end, fun(Node, _Idx) ->
    ?i2b(Node)
 end).

-spec 'star_star'(input(), index()) -> parse_result().
'star_star'(Input, Index) ->
  p(Input, Index, 'star_star', fun(I,D) -> (p_string(<<"*:*">>))(I,D) end, fun(Node, _Idx) ->Node end).

-spec 'expression'(input(), index()) -> parse_result().
'expression'(Input, Index) ->
  p(Input, Index, 'expression', fun(I,D) -> (p_choose([fun 'operation'/2, fun 'group'/2, fun 'field_phrase'/2, fun 'field'/2, fun 'field_range'/2, fun 'term'/2, fun 'string'/2]))(I,D) end, fun(Node, _Idx) ->Node end).

-spec 'term'(input(), index()) -> parse_result().
'term'(Input, Index) ->
  p(Input, Index, 'term', fun(I,D) -> (p_choose([p_seq([fun 'keyword'/2, p_one_or_more(fun 'valid_letter'/2)]), p_seq([p_not(fun 'keyword'/2), p_one_or_more(fun 'valid_letter'/2)])]))(I,D) end, fun(Node, _Idx) ->Node end).

-spec 'field'(input(), index()) -> parse_result().
'field'(Input, Index) ->
  p(Input, Index, 'field', fun(I,D) -> (p_seq([p_label('name', fun 'field_name'/2), p_string(<<":">>), p_label('arg', p_choose([fun 'fuzzy_op'/2, fun 'term'/2, fun 'group'/2, fun 'string'/2]))]))(I,D) end, fun(Node, _Idx) ->
    [<<"content:">>, ?gv(name, Node), <<"__=__">>, ?gv(arg, Node)]
 end).

-spec 'field_phrase'(input(), index()) -> parse_result().
'field_phrase'(Input, Index) ->
  p(Input, Index, 'field_phrase', fun(I,D) -> (p_seq([p_label('name', fun 'field_name'/2), p_string(<<":">>), p_string(<<"\"">>), p_label('str', p_seq([fun 'term'/2, p_zero_or_more(p_seq([fun 'space'/2, fun 'term'/2]))])), p_string(<<"\"">>)]))(I,D) end, fun(Node, _Idx) ->
    P = ?gv(str, Node),
    [<<"content:\"">>, ?gv(name, Node), <<"__=__">>, P, <<"\"">>]
 end).

-spec 'field_range'(input(), index()) -> parse_result().
'field_range'(Input, Index) ->
  p(Input, Index, 'field_range', fun(I,D) -> (p_seq([fun 'field_name'/2, p_string(<<":">>), p_choose([p_seq([p_string(<<"[">>), fun 'range_entry'/2, p_string(<<"\sTO\s">>), fun 'range_entry'/2, p_string(<<"]">>)]), p_seq([p_string(<<"{">>), fun 'range_entry'/2, p_string(<<"\sTO\s">>), fun 'range_entry'/2, p_string(<<"}">>)])])]))(I,D) end, fun(Node, _Idx) ->
    % FIXME: this needs a cleanup
    case Node of
        [FieldName, <<":">>, [<<"[">>, <<"*">>, <<" TO ">>, <<"*">>, <<"]">>]] ->
            [<<"content:">>, FieldName, <<"__=__*">>];
        [FieldName, <<":">>, [<<"{">>, <<"*">>, <<" TO ">>, <<"*">>, <<"}">>]] ->
            [<<"content:">>, FieldName, <<"__=__*">>];

        [FieldName, <<":">>, [<<"[">>, S, <<" TO ">>, <<"*">>, <<"]">>]] ->
            [<<"content:[">>, FieldName, <<"__=__">>, S, <<" TO ">>,
                  FieldName, <<"__=__\\ufff0]">>];
        [FieldName, <<":">>, [<<"{">>, S, <<" TO ">>, <<"*">>, <<"}">>]] ->
            [<<"content:{">>, FieldName, <<"__=__">>, S, <<" TO ">>,
                  FieldName, <<"__=__\\ufff0}">>];

        [FieldName, <<":">>, [<<"[">>, <<"*">>, <<" TO ">>, E, <<"]">>]] ->
            [<<"content:[">>, FieldName, <<"__=__">>, <<" TO ">>,
                  FieldName, <<"__=__">>, E, <<"]">>];
        [FieldName, <<":">>, [<<"{">>, <<"*">>, <<" TO ">>, E, <<"}">>]] ->
            [<<"content:{">>, FieldName, <<"__=__">>, <<" TO ">>,
                  FieldName, <<"__=__">>, E, <<"}">>];
        
        [FieldName, <<":">>, [<<"[">>, S, <<" TO ">>, E, <<"]">>]] ->
            [<<"content:[">>, FieldName, <<"__=__">>, S, <<" TO ">>,
                  FieldName, <<"__=__">>, E, <<"]">>];
        [FieldName, <<":">>, [<<"{">>, S, <<" TO ">>, E, <<"}">>]] ->
            [<<"content:{">>, FieldName, <<"__=__">>, S, <<" TO ">>,
                  FieldName, <<"__=__">>, E, <<"}">>]
    end
 end).

-spec 'field_name'(input(), index()) -> parse_result().
'field_name'(Input, Index) ->
  p(Input, Index, 'field_name', fun(I,D) -> (p_seq([p_not(fun 'keyword'/2), p_one_or_more(fun 'valid_letter'/2)]))(I,D) end, fun(Node, _Idx) ->Node end).

-spec 'range_entry'(input(), index()) -> parse_result().
'range_entry'(Input, Index) ->
  p(Input, Index, 'range_entry', fun(I,D) -> (p_choose([p_string(<<"*">>), p_one_or_more(fun 'valid_letter'/2)]))(I,D) end, fun(Node, _Idx) ->Node end).

-spec 'group'(input(), index()) -> parse_result().
'group'(Input, Index) ->
  p(Input, Index, 'group', fun(I,D) -> (p_seq([p_string(<<"(">>), fun 'query'/2, p_string(<<")">>)]))(I,D) end, fun(Node, _Idx) ->Node end).

-spec 'operation'(input(), index()) -> parse_result().
'operation'(Input, Index) ->
  p(Input, Index, 'operation', fun(I,D) -> (p_choose([fun 'binary_op'/2, fun 'unary_op'/2, fun 'fuzzy_op'/2, fun 'boost_op'/2]))(I,D) end, fun(Node, _Idx) ->Node end).

-spec 'binary_op'(input(), index()) -> parse_result().
'binary_op'(Input, Index) ->
  p(Input, Index, 'binary_op', fun(I,D) -> (p_seq([p_label('lhs', p_choose([fun 'group'/2, fun 'field_phrase'/2, fun 'field'/2, fun 'field_range'/2, fun 'term'/2])), p_optional(fun 'space'/2), p_label('op', fun 'bool_op'/2), p_optional(fun 'space'/2), p_label('rhs', fun 'query'/2)]))(I,D) end, fun(Node, _Idx) ->
    [?gv(lhs, Node), <<" ">>, ?gv(op, Node), <<" ">>, ?gv(rhs, Node)]
 end).

-spec 'bool_op'(input(), index()) -> parse_result().
'bool_op'(Input, Index) ->
  p(Input, Index, 'bool_op', fun(I,D) -> (p_choose([p_string(<<"AND">>), p_string(<<"&&">>), p_string(<<"OR">>), p_string(<<"||">>)]))(I,D) end, fun(Node, _Idx) ->Node end).

-spec 'unary_op'(input(), index()) -> parse_result().
'unary_op'(Input, Index) ->
  p(Input, Index, 'unary_op', fun(I,D) -> (p_choose([fun 'not_op'/2, fun 'required_op'/2, fun 'prohibited_op'/2]))(I,D) end, fun(Node, _Idx) ->Node end).

-spec 'not_op'(input(), index()) -> parse_result().
'not_op'(Input, Index) ->
  p(Input, Index, 'not_op', fun(I,D) -> (p_seq([p_choose([p_seq([p_label('op', p_string(<<"NOT">>)), fun 'space'/2]), p_seq([p_label('op', p_string(<<"!">>)), p_optional(fun 'space'/2)])]), p_label('arg', p_choose([fun 'group'/2, fun 'field'/2, fun 'field_range'/2, fun 'term'/2, fun 'string'/2]))]))(I,D) end, fun(Node, _Idx) ->
    Op = ?gv(op, hd(Node)),
    Spc = case tl(hd(Node)) of
              [] -> <<"">>;
              [S] -> S
          end,
    [Op, Spc, ?gv(arg, tl(Node))]
 end).

-spec 'required_op'(input(), index()) -> parse_result().
'required_op'(Input, Index) ->
  p(Input, Index, 'required_op', fun(I,D) -> (p_seq([p_not(fun 'valid_letter'/2), p_label('op', p_string(<<"+">>)), p_label('arg', p_choose([fun 'term'/2, fun 'string'/2]))]))(I,D) end, fun(Node, _Idx) ->
    [?gv(op, Node), ?gv(arg, Node)]
 end).

-spec 'prohibited_op'(input(), index()) -> parse_result().
'prohibited_op'(Input, Index) ->
  p(Input, Index, 'prohibited_op', fun(I,D) -> (p_seq([p_not(fun 'valid_letter'/2), p_label('op', p_string(<<"-">>)), p_label('arg', p_choose([fun 'field'/2, fun 'field_range'/2, fun 'term'/2, fun 'string'/2]))]))(I,D) end, fun(Node, _Idx) ->
    [?gv(op, Node), ?gv(arg, Node)]
 end).

-spec 'boost_op'(input(), index()) -> parse_result().
'boost_op'(Input, Index) ->
  p(Input, Index, 'boost_op', fun(I,D) -> (p_seq([p_label('arg', p_choose([fun 'term'/2, fun 'string'/2])), p_string(<<"^">>), p_label('param', fun 'fuzzy_param'/2)]))(I,D) end, fun(Node, _Idx) ->
    [?gv(arg, Node), <<"^">>, ?gv(param, Node)]
 end).

-spec 'fuzzy_op'(input(), index()) -> parse_result().
'fuzzy_op'(Input, Index) ->
  p(Input, Index, 'fuzzy_op', fun(I,D) -> (p_seq([p_label('arg', p_choose([fun 'term'/2, fun 'string'/2])), p_string(<<"~">>), p_label('param', p_optional(fun 'fuzzy_param'/2))]))(I,D) end, fun(Node, _Idx) ->
    case ?gv(param, Node) of
        [] -> [?gv(arg, Node), <<"~">>];
        Param -> [?gv(arg, Node), <<"~">>, Param]
    end
 end).

-spec 'fuzzy_param'(input(), index()) -> parse_result().
'fuzzy_param'(Input, Index) ->
  p(Input, Index, 'fuzzy_param', fun(I,D) -> (p_seq([p_one_or_more(p_charclass(<<"[0-9]">>)), p_optional(p_seq([p_string(<<".">>), p_charclass(<<"[0-9]">>)]))]))(I,D) end, fun(Node, _Idx) ->Node end).

-spec 'string'(input(), index()) -> parse_result().
'string'(Input, Index) ->
  p(Input, Index, 'string', fun(I,D) -> (p_seq([p_string(<<"\"">>), p_label('str', p_seq([fun 'term'/2, p_zero_or_more(p_seq([fun 'space'/2, fun 'term'/2]))])), p_string(<<"\"">>)]))(I,D) end, fun(Node, _Idx) ->
    [<<"\"">>, ?gv(str, Node), <<"\"">>]
 end).

-spec 'keyword'(input(), index()) -> parse_result().
'keyword'(Input, Index) ->
  p(Input, Index, 'keyword', fun(I,D) -> (p_choose([p_string(<<"AND">>), p_string(<<"OR">>), p_string(<<"NOT">>)]))(I,D) end, fun(Node, _Idx) ->Node end).

-spec 'valid_letter'(input(), index()) -> parse_result().
'valid_letter'(Input, Index) ->
  p(Input, Index, 'valid_letter', fun(I,D) -> (p_seq([p_one_or_more(fun 'start_letter'/2), p_zero_or_more(p_choose([p_charclass(<<"[a-zA-Z0-9*?@_+.\/-]">>), p_seq([p_string(<<"\\">>), fun 'special_char'/2])]))]))(I,D) end, fun(Node, _Idx) ->Node end).

-spec 'start_letter'(input(), index()) -> parse_result().
'start_letter'(Input, Index) ->
  p(Input, Index, 'start_letter', fun(I,D) -> (p_choose([p_charclass(<<"[a-zA-Z0-9_.*\/]">>), p_seq([p_string(<<"\\">>), fun 'special_char'/2])]))(I,D) end, fun(Node, _Idx) ->Node end).

-spec 'space'(input(), index()) -> parse_result().
'space'(Input, Index) ->
  p(Input, Index, 'space', fun(I,D) -> (p_one_or_more(p_charclass(<<"[\s\t]">>)))(I,D) end, fun(Node, _Idx) ->Node end).

-spec 'special_char'(input(), index()) -> parse_result().
'special_char'(Input, Index) ->
  p(Input, Index, 'special_char', fun(I,D) -> (p_choose([p_string(<<"[">>), p_string(<<"]">>), p_string(<<"\\">>), p_charclass(<<"[!(){}^\"~*?:]">>)]))(I,D) end, fun(Node, _Idx) ->Node end).



-file("peg_includes.hrl", 1).
-type index() :: {{line, pos_integer()}, {column, pos_integer()}}.
-type input() :: binary().
-type parse_failure() :: {fail, term()}.
-type parse_success() :: {term(), input(), index()}.
-type parse_result() :: parse_failure() | parse_success().
-type parse_fun() :: fun((input(), index()) -> parse_result()).
-type xform_fun() :: fun((input(), index()) -> term()).

-spec p(input(), index(), atom(), parse_fun(), xform_fun()) -> parse_result().
p(Inp, StartIndex, Name, ParseFun, TransformFun) ->
  case get_memo(StartIndex, Name) of      % See if the current reduction is memoized
    {ok, Memo} -> %Memo;                     % If it is, return the stored result
      Memo;
    _ ->                                        % If not, attempt to parse
      Result = case ParseFun(Inp, StartIndex) of
        {fail,_} = Failure ->                       % If it fails, memoize the failure
          Failure;
        {Match, InpRem, NewIndex} ->               % If it passes, transform and memoize the result.
          Transformed = TransformFun(Match, StartIndex),
          {Transformed, InpRem, NewIndex}
      end,
      memoize(StartIndex, Name, Result),
      Result
  end.

-spec setup_memo() -> ets:tid().
setup_memo() ->
  put({parse_memo_table, ?MODULE}, ets:new(?MODULE, [set])).

-spec release_memo() -> true.
release_memo() ->
  ets:delete(memo_table_name()).

-spec memoize(index(), atom(), term()) -> true.
memoize(Index, Name, Result) ->
  Memo = case ets:lookup(memo_table_name(), Index) of
              [] -> [];
              [{Index, Plist}] -> Plist
         end,
  ets:insert(memo_table_name(), {Index, [{Name, Result}|Memo]}).

-spec get_memo(index(), atom()) -> {ok, term()} | {error, not_found}.
get_memo(Index, Name) ->
  case ets:lookup(memo_table_name(), Index) of
    [] -> {error, not_found};
    [{Index, Plist}] ->
      case proplists:lookup(Name, Plist) of
        {Name, Result}  -> {ok, Result};
        _  -> {error, not_found}
      end
    end.

-spec memo_table_name() -> ets:tid().
memo_table_name() ->
    get({parse_memo_table, ?MODULE}).

-ifdef(p_eof).
-spec p_eof() -> parse_fun().
p_eof() ->
  fun(<<>>, Index) -> {eof, [], Index};
     (_, Index) -> {fail, {expected, eof, Index}} end.
-endif.

-ifdef(p_optional).
-spec p_optional(parse_fun()) -> parse_fun().
p_optional(P) ->
  fun(Input, Index) ->
      case P(Input, Index) of
        {fail,_} -> {[], Input, Index};
        {_, _, _} = Success -> Success
      end
  end.
-endif.

-ifdef(p_not).
-spec p_not(parse_fun()) -> parse_fun().
p_not(P) ->
  fun(Input, Index)->
      case P(Input,Index) of
        {fail,_} ->
          {[], Input, Index};
        {Result, _, _} -> {fail, {expected, {no_match, Result},Index}}
      end
  end.
-endif.

-ifdef(p_assert).
-spec p_assert(parse_fun()) -> parse_fun().
p_assert(P) ->
  fun(Input,Index) ->
      case P(Input,Index) of
        {fail,_} = Failure-> Failure;
        _ -> {[], Input, Index}
      end
  end.
-endif.

-ifdef(p_seq).
-spec p_seq([parse_fun()]) -> parse_fun().
p_seq(P) ->
  fun(Input, Index) ->
      p_all(P, Input, Index, [])
  end.

-spec p_all([parse_fun()], input(), index(), [term()]) -> parse_result().
p_all([], Inp, Index, Accum ) -> {lists:reverse( Accum ), Inp, Index};
p_all([P|Parsers], Inp, Index, Accum) ->
  case P(Inp, Index) of
    {fail, _} = Failure -> Failure;
    {Result, InpRem, NewIndex} -> p_all(Parsers, InpRem, NewIndex, [Result|Accum])
  end.
-endif.

-ifdef(p_choose).
-spec p_choose([parse_fun()]) -> parse_fun().
p_choose(Parsers) ->
  fun(Input, Index) ->
      p_attempt(Parsers, Input, Index, none)
  end.

-spec p_attempt([parse_fun()], input(), index(), none | parse_failure()) -> parse_result().
p_attempt([], _Input, _Index, Failure) -> Failure;
p_attempt([P|Parsers], Input, Index, FirstFailure)->
  case P(Input, Index) of
    {fail, _} = Failure ->
      case FirstFailure of
        none -> p_attempt(Parsers, Input, Index, Failure);
        _ -> p_attempt(Parsers, Input, Index, FirstFailure)
      end;
    Result -> Result
  end.
-endif.

-ifdef(p_zero_or_more).
-spec p_zero_or_more(parse_fun()) -> parse_fun().
p_zero_or_more(P) ->
  fun(Input, Index) ->
      p_scan(P, Input, Index, [])
  end.
-endif.

-ifdef(p_one_or_more).
-spec p_one_or_more(parse_fun()) -> parse_fun().
p_one_or_more(P) ->
  fun(Input, Index)->
      Result = p_scan(P, Input, Index, []),
      case Result of
        {[_|_], _, _} ->
          Result;
        _ ->
          {fail, {expected, Failure, _}} = P(Input,Index),
          {fail, {expected, {at_least_one, Failure}, Index}}
      end
  end.
-endif.

-ifdef(p_label).
-spec p_label(atom(), parse_fun()) -> parse_fun().
p_label(Tag, P) ->
  fun(Input, Index) ->
      case P(Input, Index) of
        {fail,_} = Failure ->
           Failure;
        {Result, InpRem, NewIndex} ->
          {{Tag, Result}, InpRem, NewIndex}
      end
  end.
-endif.

-ifdef(p_scan).
-spec p_scan(parse_fun(), input(), index(), [term()]) -> parse_result().
p_scan(_, [], Index, Accum) -> {lists:reverse( Accum ), [], Index};
p_scan(P, Inp, Index, Accum) ->
  case P(Inp, Index) of
    {fail,_} -> {lists:reverse(Accum), Inp, Index};
    {Result, InpRem, NewIndex} -> p_scan(P, InpRem, NewIndex, [Result | Accum])
  end.
-endif.

-ifdef(p_string).
-spec p_string(binary()) -> parse_fun().
p_string(S) ->
    Length = erlang:byte_size(S),
    fun(Input, Index) ->
      try
          <<S:Length/binary, Rest/binary>> = Input,
          {S, Rest, p_advance_index(S, Index)}
      catch
          error:{badmatch,_} -> {fail, {expected, {string, S}, Index}}
      end
    end.
-endif.

-ifdef(p_anything).
-spec p_anything() -> parse_fun().
p_anything() ->
  fun(<<>>, Index) -> {fail, {expected, any_character, Index}};
     (Input, Index) when is_binary(Input) ->
          <<C/utf8, Rest/binary>> = Input,
          {<<C/utf8>>, Rest, p_advance_index(<<C/utf8>>, Index)}
  end.
-endif.

-ifdef(p_charclass).
-spec p_charclass(string() | binary()) -> parse_fun().
p_charclass(Class) ->
    {ok, RE} = re:compile(Class, [unicode, dotall]),
    fun(Inp, Index) ->
            case re:run(Inp, RE, [anchored]) of
                {match, [{0, Length}|_]} ->
                    {Head, Tail} = erlang:split_binary(Inp, Length),
                    {Head, Tail, p_advance_index(Head, Index)};
                _ -> {fail, {expected, {character_class, binary_to_list(Class)}, Index}}
            end
    end.
-endif.

-ifdef(p_regexp).
-spec p_regexp(binary()) -> parse_fun().
p_regexp(Regexp) ->
    {ok, RE} = re:compile(Regexp, [unicode, dotall, anchored]),
    fun(Inp, Index) ->
        case re:run(Inp, RE) of
            {match, [{0, Length}|_]} ->
                {Head, Tail} = erlang:split_binary(Inp, Length),
                {Head, Tail, p_advance_index(Head, Index)};
            _ -> {fail, {expected, {regexp, binary_to_list(Regexp)}, Index}}
        end
    end.
-endif.

-ifdef(line).
-spec line(index() | term()) -> pos_integer() | undefined.
line({{line,L},_}) -> L;
line(_) -> undefined.
-endif.

-ifdef(column).
-spec column(index() | term()) -> pos_integer() | undefined.
column({_,{column,C}}) -> C;
column(_) -> undefined.
-endif.

-spec p_advance_index(input() | unicode:charlist() | pos_integer(), index()) -> index().
p_advance_index(MatchedInput, Index) when is_list(MatchedInput) orelse is_binary(MatchedInput)-> % strings
  lists:foldl(fun p_advance_index/2, Index, unicode:characters_to_list(MatchedInput));
p_advance_index(MatchedInput, Index) when is_integer(MatchedInput) -> % single characters
  {{line, Line}, {column, Col}} = Index,
  case MatchedInput of
    $\n -> {{line, Line+1}, {column, 1}};
    _ -> {{line, Line}, {column, Col+1}}
  end.
