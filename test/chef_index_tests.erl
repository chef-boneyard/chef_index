%% Copyright 2015 Chef Server, Inc. All Rights Reserved.
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

-module(chef_index_tests).
-include_lib("eunit/include/eunit.hrl").
-define(EXPECTED_DOC, [<<"<doc>">>,
                       [[<<"<field name=\"">>,<<"X_CHEF_id_CHEF_X">>,<<"\">">>,<<"a1">>,
                         <<"</field>">>],
                        [<<"<field name=\"">>,<<"X_CHEF_database_CHEF_X">>,<<"\">">>,<<"chef_db1">>,
                         <<"</field>">>],
                        [<<"<field name=\"">>,<<"X_CHEF_type_CHEF_X">>,<<"\">">>,<<"role">>,
                         <<"</field>">>]],
                       [],
                       [<<"<field name=\"">>,<<"content">>,<<"\">">>,
                        [[<<"X_CHEF_database_CHEF_X">>,<<"__=__">>,<<"chef_db1">>,<<" ">>],
                         [<<"X_CHEF_id_CHEF_X">>,<<"__=__">>,<<"a1">>,<<" ">>],
                         [<<"X_CHEF_type_CHEF_X">>,<<"__=__">>,<<"role">>,<<" ">>],
                         [<<"key1">>,<<"__=__">>,<<"value1">>,<<" ">>],
                         [<<"key2">>,<<"__=__">>,<<"value2">>,<<" ">>]],
                        <<"</field>">>],
                       <<"</doc>">>]).

-define(EXPECTED_DELETE_DOC, [<<"<delete><id>">>,<<"a1">>,<<"</id></delete>">>]).

chef_index_test_() ->
    {foreach,
     fun() ->
             chef_index_test_utils:start_stats_hero(),
             application:set_env(chef_index, rabbitmq_vhost, <<"testvhost">>),
             meck:new([chef_index_queue, chef_index_expand], [passthrough])
     end,
     fun(_) ->
             meck:unload([chef_index_queue, chef_index_expand])
     end,
     [{"add calls chef_index_queue:set when search_queue_mode is rabbitmq",
       fun() ->
               application:set_env(chef_index, search_queue_mode, rabbitmq),
               meck:expect(chef_index_queue, set, fun(<<"testvhost">>, role, <<"a1">>, <<"db1">>, [{}]) -> ok end),
               chef_index:add(role, <<"a1">>, <<"db1">>, [{}], <<"abcde">>),
               ?assert(meck:validate(chef_index_queue))
       end
      },
      {"delete calls chef_index_queue:delete when search_queue_mode is rabbitmq",
       fun() ->
               application:set_env(chef_index, search_queue_mode, rabbitmq),
               meck:expect(chef_index_queue, delete, fun(<<"testvhost">>, role, <<"a1">>, <<"db1">>) -> ok end),
               chef_index:delete(role, <<"a1">>, <<"db1">>, none),
               ?assert(meck:validate(chef_index_queue))
       end
      }
     ]
    }.
