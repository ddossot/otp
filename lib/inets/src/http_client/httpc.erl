%%
%% %CopyrightBegin%
%%
%% Copyright Ericsson AB 2009-2010. All Rights Reserved.
%%
%% The contents of this file are subject to the Erlang Public License,
%% Version 1.1, (the "License"); you may not use this file except in
%% compliance with the License. You should have received a copy of the
%% Erlang Public License along with this software. If not, it can be
%% retrieved online at http://www.erlang.org/.
%%
%% Software distributed under the License is distributed on an "AS IS"
%% basis, WITHOUT WARRANTY OF ANY KIND, either express or implied. See
%% the License for the specific language governing rights and limitations
%% under the License.
%%
%% %CopyrightEnd%
%%
%%

%% Description:
%%% This version of the HTTP/1.1 client supports:
%%%      - RFC 2616 HTTP 1.1 client part
%%%      - RFC 2818 HTTP Over TLS

-module(httpc).

-behaviour(inets_service).

%% API
-export([
	 request/1, request/2, request/4, request/5,
	 cancel_request/1, cancel_request/2,
	 set_option/2, set_option/3,
	 set_options/1, set_options/2,
	 store_cookies/2, store_cookies/3, 
	 cookie_header/1, cookie_header/2, 
	 which_cookies/0, which_cookies/1, 
	 reset_cookies/0, reset_cookies/1, 
	 stream_next/1,
	 default_profile/0, 
	 profile_name/1, profile_name/2,
	 info/0, info/1
	]).

%% Behavior callbacks
-export([start_standalone/1, start_service/1, 
	 stop_service/1, 
	 services/0, service_info/1]).

-include("http_internal.hrl").
-include("httpc_internal.hrl").

-define(DEFAULT_PROFILE, default).


%%%=========================================================================
%%%  API
%%%=========================================================================

default_profile() ->
    ?DEFAULT_PROFILE.


profile_name(?DEFAULT_PROFILE) ->
    httpc_manager;
profile_name(Profile) -> 
    profile_name("httpc_manager_", Profile).

profile_name(Prefix, Profile) when is_atom(Profile) ->
    list_to_atom(Prefix ++ atom_to_list(Profile));
profile_name(Prefix, Profile) when is_pid(Profile) ->
    ProfileStr0 = 
	string:strip(string:strip(erlang:pid_to_list(Profile), left, $<), right, $>),
    F = fun($.) -> $_; (X) -> X end, 
    ProfileStr = [F(C) || C <- ProfileStr0], 
    list_to_atom(Prefix ++ "pid_" ++ ProfileStr).


%%--------------------------------------------------------------------------
%% request(Url) -> {ok, {StatusLine, Headers, Body}} | {error,Reason} 
%% request(Url Profile) ->
%%           {ok, {StatusLine, Headers, Body}} | {error,Reason} 
%%
%%	Url - string() 
%% Description: Calls request/4 with default values.
%%--------------------------------------------------------------------------

request(Url) ->
    request(Url, default_profile()).

request(Url, Profile) ->
    request(get, {Url, []}, [], [], Profile).


%%--------------------------------------------------------------------------
%% request(Method, Request, HTTPOptions, Options [, Profile]) ->
%%           {ok, {StatusLine, Headers, Body}} | {ok, {Status, Body}} |
%%           {ok, RequestId} | {error,Reason} | {ok, {saved_as, FilePath}
%%
%%	Method - atom() = head | get | put | post | trace | options| delete 
%%	Request - {Url, Headers} | {Url, Headers, ContentType, Body} 
%%	Url - string() 
%%	HTTPOptions - [HttpOption]
%%	HTTPOption - {timeout, Time} | {connect_timeout, Time} | 
%%                   {ssl, SSLOptions} | {proxy_auth, {User, Password}}
%%	Ssloptions = [SSLOption]
%%	SSLOption =  {verify, code()} | {depth, depth()} | {certfile, path()} |
%%	{keyfile, path()} | {password, string()} | {cacertfile, path()} |
%%	{ciphers, string()} 
%%	Options - [Option]
%%	Option - {sync, Boolean} | {body_format, BodyFormat} | 
%%	{full_result, Boolean} | {stream, To} |
%%      {headers_as_is, Boolean}  
%%	StatusLine = {HTTPVersion, StatusCode, ReasonPhrase}</v>
%%	HTTPVersion = string()
%%	StatusCode = integer()
%%	ReasonPhrase = string()
%%	Headers = [Header]
%%      Header = {Field, Value}
%%	Field = string()
%%	Value = string()
%%	Body = string() | binary() - HTLM-code
%%
%% Description: Sends a HTTP-request. The function can be both
%% syncronus and asynchronous in the later case the function will
%% return {ok, RequestId} and later on a message will be sent to the
%% calling process on the format {http, {RequestId, {StatusLine,
%% Headers, Body}}} or {http, {RequestId, {error, Reason}}}
%%--------------------------------------------------------------------------

request(Method, Request, HttpOptions, Options) ->
    request(Method, Request, HttpOptions, Options, default_profile()). 

request(Method, {Url, Headers}, HTTPOptions, Options, Profile) 
  when (Method =:= options) orelse 
       (Method =:= get) orelse 
       (Method =:= head) orelse 
       (Method =:= delete) orelse 
       (Method =:= trace) andalso 
       (is_atom(Profile) orelse is_pid(Profile)) ->
    ?hcrt("request", [{method,       Method}, 
		      {url,          Url},
		      {headers,      Headers}, 
		      {http_options, HTTPOptions}, 
		      {options,      Options}, 
		      {profile,      Profile}]),
    case http_uri:parse(Url) of
	{error, Reason} ->
	    {error, Reason};
	ParsedUrl ->
	    handle_request(Method, Url, ParsedUrl, Headers, [], [], 
			   HTTPOptions, Options, Profile)
    end;
     
request(Method, {Url,Headers,ContentType,Body}, HTTPOptions, Options, Profile) 
  when ((Method =:= post) orelse (Method =:= put)) andalso 
       (is_atom(Profile) orelse is_pid(Profile)) ->
    ?hcrt("request", [{method,       Method}, 
		      {url,          Url},
		      {headers,      Headers}, 
		      {content_type, ContentType}, 
		      {body,         Body}, 
		      {http_options, HTTPOptions}, 
		      {options,      Options}, 
		      {profile,      Profile}]),
    case http_uri:parse(Url) of
	{error, Reason} ->
	    {error, Reason};
	ParsedUrl ->
	    handle_request(Method, Url, 
			   ParsedUrl, Headers, ContentType, Body, 
			   HTTPOptions, Options, Profile)
    end.


%%--------------------------------------------------------------------------
%% cancel_request(RequestId) -> ok
%% cancel_request(RequestId, Profile) -> ok
%%   RequestId - As returned by request/4  
%%                                 
%% Description: Cancels a HTTP-request.
%%-------------------------------------------------------------------------
cancel_request(RequestId) ->
    cancel_request(RequestId, default_profile()).

cancel_request(RequestId, Profile) 
  when is_atom(Profile) orelse is_pid(Profile) ->
    ?hcrt("cancel request", [{request_id, RequestId}, {profile, Profile}]),
    ok = httpc_manager:cancel_request(RequestId, profile_name(Profile)), 
    receive  
	%% If the request was already fulfilled throw away the 
	%% answer as the request has been canceled.
	{http, {RequestId, _}} ->
	    ok 
    after 0 ->
	    ok
    end.


%%--------------------------------------------------------------------------
%% set_options(Options) -> ok | {error, Reason}
%% set_options(Options, Profile) -> ok | {error, Reason}
%%   Options - [Option]
%%   Profile - atom()
%%   Option - {proxy, {Proxy, NoProxy}} | {max_sessions, MaxSessions} | 
%%            {max_pipeline_length, MaxPipeline} | 
%%            {pipeline_timeout, PipelineTimeout} | {cookies, CookieMode} | 
%%            {ipfamily, IpFamily}
%%   Proxy - {Host, Port}
%%   NoProxy - [Domain | HostName | IPAddress]   
%%   MaxSessions, MaxPipeline, PipelineTimeout = integer()   
%%   CookieMode - enabled | disabled | verify
%%   IpFamily - inet | inet6 | inet6fb4
%% Description: Informs the httpc_manager of the new settings. 
%%-------------------------------------------------------------------------
set_options(Options) ->
    set_options(Options, default_profile()).
set_options(Options, Profile) when is_atom(Profile) orelse is_pid(Profile) ->
    ?hcrt("set cookies", [{options, Options}, {profile, Profile}]),
    case validate_options(Options) of
	{ok, Opts} ->
	    try 
		begin
		    httpc_manager:set_options(Opts, profile_name(Profile))
		end
	    catch
		exit:{noproc, _} ->
		    {error, inets_not_started}
	    end;
	{error, Reason} ->
	    {error, Reason}
    end.

set_option(Key, Value) ->
    set_option(Key, Value, default_profile()).

set_option(Key, Value, Profile) ->
    set_options([{Key, Value}], Profile).


%%--------------------------------------------------------------------------
%% store_cookies(SetCookieHeaders, Url [, Profile]) -> ok | {error, reason} 
%%   
%%                                 
%% Description: Store the cookies from <SetCookieHeaders> 
%%              in the cookie database
%% for the profile <Profile>. This function shall be used when the option
%% cookie is set to verify. 
%%-------------------------------------------------------------------------
store_cookies(SetCookieHeaders, Url) ->
    store_cookies(SetCookieHeaders, Url, default_profile()).

store_cookies(SetCookieHeaders, Url, Profile) 
  when is_atom(Profile) orelse is_pid(Profile) ->
    ?hcrt("store cookies", [{set_cookie_headers, SetCookieHeaders}, 
			    {url,                Url},
			    {profile,            Profile}]),
    try 
	begin
	    {_, _, Host, Port, Path, _} = http_uri:parse(Url),
	    Address     = {Host, Port}, 
	    ProfileName = profile_name(Profile),
	    Cookies     = httpc_cookie:cookies(SetCookieHeaders, Path, Host),
	    httpc_manager:store_cookies(Cookies, Address, ProfileName), 
	    ok
	end
    catch 
	exit:{noproc, _} ->
	    {error, {not_started, Profile}};
	error:{badmatch, Bad} ->
	    {error, {parse_failed, Bad}}
    end.


%%--------------------------------------------------------------------------
%% cookie_header(Url [, Profile]) -> Header | {error, Reason}
%%               
%% Description: Returns the cookie header that would be sent when making
%% a request to <Url>.
%%-------------------------------------------------------------------------
cookie_header(Url) ->
    cookie_header(Url, default_profile()).

cookie_header(Url, Profile) ->
    ?hcrt("cookie header", [{url,     Url},
			    {profile, Profile}]),
    try 
	begin
	    httpc_manager:which_cookies(Url, profile_name(Profile))
	end
    catch 
	exit:{noproc, _} ->
	    {error, {not_started, Profile}}
    end.


%%--------------------------------------------------------------------------
%% which_cookies() -> [cookie()]
%% which_cookies(Profile) -> [cookie()]
%%               
%% Description: Debug function, dumping the cookie database
%%-------------------------------------------------------------------------
which_cookies() ->
    which_cookies(default_profile()).

which_cookies(Profile) ->
    ?hcrt("which cookies", [{profile, Profile}]),
    try 
	begin
	    httpc_manager:which_cookies(profile_name(Profile))
	end
    catch 
	exit:{noproc, _} ->
	    {error, {not_started, Profile}}
    end.


%%--------------------------------------------------------------------------
%% info() -> list()
%% info(Profile) -> list()
%%               
%% Description: Debug function, retreive info about the profile
%%-------------------------------------------------------------------------
info() ->
    info(default_profile()).

info(Profile) ->
    ?hcrt("info", [{profile, Profile}]),
    try 
	begin
	    httpc_manager:info(profile_name(Profile))
	end
    catch 
	exit:{noproc, _} ->
	    {error, {not_started, Profile}}
    end.


%%--------------------------------------------------------------------------
%% reset_cookies() -> void()
%% reset_cookies(Profile) -> void()
%%               
%% Description: Debug function, reset the cookie database
%%-------------------------------------------------------------------------
reset_cookies() ->
    reset_cookies(default_profile()).

reset_cookies(Profile) ->
    ?hcrt("reset cookies", [{profile, Profile}]),
    try 
	begin
	    httpc_manager:reset_cookies(profile_name(Profile))
	end
    catch 
	exit:{noproc, _} ->
	    {error, {not_started, Profile}}
    end.


%%--------------------------------------------------------------------------
%% stream_next(Pid) -> Header | {error, Reason}
%%               
%% Description: Triggers the next message to be streamed, e.i. 
%%              same behavior as active once for sockets.
%%-------------------------------------------------------------------------
stream_next(Pid) ->
    ?hcrt("stream next", [{handler, Pid}]),
    httpc_handler:stream_next(Pid).


%%%========================================================================
%%% Behaviour callbacks
%%%========================================================================
start_standalone(PropList) ->
    ?hcrt("start standalone", [{proplist, PropList}]),
    case proplists:get_value(profile, PropList) of
	undefined ->
	    {error, no_profile};
	Profile ->
	    Dir = 
		proplists:get_value(data_dir, PropList, only_session_cookies),
	    httpc_manager:start_link(Profile, Dir, stand_alone)
    end.

start_service(Config) ->
    ?hcrt("start service", [{config, Config}]),
    httpc_profile_sup:start_child(Config).

stop_service(Profile) when is_atom(Profile) ->
    ?hcrt("stop service", [{profile, Profile}]),
    httpc_profile_sup:stop_child(Profile);
stop_service(Pid) when is_pid(Pid) ->
    ?hcrt("stop service", [{pid, Pid}]),
    case service_info(Pid) of
	{ok, [{profile, Profile}]} ->
	    stop_service(Profile);
	Error ->
	    Error
    end.

services() ->
    [{httpc, Pid} || {_, Pid, _, _} <- 
			 supervisor:which_children(httpc_profile_sup)].
service_info(Pid) ->
    try [{ChildName, ChildPid} || 
	    {ChildName, ChildPid, _, _} <- 
		supervisor:which_children(httpc_profile_sup)] of
	Children ->
	    child_name2info(child_name(Pid, Children))
    catch
	exit:{noproc, _} ->
	    {error, service_not_available} 
    end.


%%%========================================================================
%%% Internal functions
%%%========================================================================

handle_request(Method, Url, 
	       {Scheme, UserInfo, Host, Port, Path, Query}, 
	       Headers, ContentType, Body, 
	       HTTPOptions0, Options0, Profile) ->

    Started    = http_util:timestamp(), 
    NewHeaders = [{http_util:to_lower(Key), Val} || {Key, Val} <- Headers],

    try
	begin
	    HTTPOptions   = http_options(HTTPOptions0),
	    Options       = request_options(Options0), 
	    Sync          = proplists:get_value(sync,   Options),
	    Stream        = proplists:get_value(stream, Options),
	    Host2         = header_host(Scheme, Host, Port), 
	    HeadersRecord = header_record(NewHeaders, Host2, HTTPOptions),
	    Receiver   = proplists:get_value(receiver, Options),
	    SocketOpts = proplists:get_value(socket_opts, Options),
	    Request = #request{from          = Receiver,
			       scheme        = Scheme, 
			       address       = {Host, Port},
			       path          = Path, 
			       pquery        = Query, 
			       method        = Method,
			       headers       = HeadersRecord, 
			       content       = {ContentType, Body},
			       settings      = HTTPOptions, 
			       abs_uri       = Url, 
			       userinfo      = UserInfo, 
			       stream        = Stream, 
			       headers_as_is = headers_as_is(Headers, Options),
			       socket_opts   = SocketOpts, 
			       started       = Started},
	    case httpc_manager:request(Request, profile_name(Profile)) of
		{ok, RequestId} ->
		    handle_answer(RequestId, Sync, Options);
		{error, Reason} ->
		    {error, Reason}
	    end
	end
    catch
	error:{noproc, _} ->
	    {error, {not_started, Profile}};
	throw:Error ->
	    Error
    end.


handle_answer(RequestId, false, _) ->
    {ok, RequestId};
handle_answer(RequestId, true, Options) ->
    receive
	{http, {RequestId, saved_to_file}} ->
	    {ok, saved_to_file};
	{http, {RequestId, {_,_,_} = Result}} ->
	    return_answer(Options, Result);
	{http, {RequestId, {error, Reason}}} ->
	    {error, Reason}
    end.

return_answer(Options, {{"HTTP/0.9",_,_}, _, BinBody}) ->
    Body = maybe_format_body(BinBody, Options),
    {ok, Body};
   
return_answer(Options, {StatusLine, Headers, BinBody}) ->

    Body = maybe_format_body(BinBody, Options),
    
    case proplists:get_value(full_result, Options, true) of
	true ->
	    {ok, {StatusLine, Headers, Body}};
	false ->
	    {_, Status, _} = StatusLine,
	    {ok, {Status, Body}}
    end.

maybe_format_body(BinBody, Options) ->
    case proplists:get_value(body_format, Options, string) of
	string ->
	    binary_to_list(BinBody);
	_ ->
	    BinBody
    end.

%% This options is a workaround for http servers that do not follow the 
%% http standard and have case sensative header parsing. Should only be
%% used if there is no other way to communicate with the server or for
%% testing purpose.
headers_as_is(Headers, Options) ->
     case proplists:get_value(headers_as_is, Options, false) of
	 false ->
	     [];
	 true  ->
	     Headers
     end.


http_options(HttpOptions) ->
    HttpOptionsDefault = http_options_default(),
    http_options(HttpOptionsDefault, HttpOptions, #http_options{}).

http_options([], [], Acc) ->
    Acc;
http_options([], HttpOptions, Acc) ->
    Fun = fun(BadOption) ->
		    Report = io_lib:format("Invalid option ~p ignored ~n", 
					   [BadOption]),
		    error_logger:info_report(Report)
	  end,
    lists:foreach(Fun, HttpOptions),
    Acc;
http_options([{Tag, Default, Idx, Post} | Defaults], HttpOptions, Acc) ->
    case lists:keysearch(Tag, 1, HttpOptions) of
	{value, {Tag, Val0}} ->
	    case Post(Val0) of
		{ok, Val} ->
		    Acc2 = setelement(Idx, Acc, Val),
		    HttpOptions2 = lists:keydelete(Tag, 1, HttpOptions),
		    http_options(Defaults, HttpOptions2, Acc2);
		error ->
		    Report = io_lib:format("Invalid option ~p:~p ignored ~n", 
					   [Tag, Val0]),
		    error_logger:info_report(Report),
		    HttpOptions2 = lists:keydelete(Tag, 1, HttpOptions),
		    http_options(Defaults, HttpOptions2, Acc)
	    end;
	false ->
	    DefaultVal = 
		case Default of
		    {value, Val} ->
			Val;
		    {field, DefaultIdx} ->
			element(DefaultIdx, Acc)
		end,
	    Acc2 = setelement(Idx, Acc, DefaultVal),
	    http_options(Defaults, HttpOptions, Acc2)
    end.
		    
http_options_default() ->
    VersionPost = 
	fun(Value) when is_atom(Value) ->
		{ok, http_util:to_upper(atom_to_list(Value))};
	   (Value) when is_list(Value) ->
		{ok, http_util:to_upper(Value)};
	   (_) ->
		error
	end,
    TimeoutPost = fun(Value) when is_integer(Value) andalso (Value >= 0) ->
			  {ok, Value};
		     (infinity = Value) ->
			  {ok, Value};
		     (_) ->
			  error
		  end,
    AutoRedirectPost = fun(Value) when (Value =:= true) orelse 
				       (Value =:= false) ->
			       {ok, Value};
			  (_) ->
			       error
		       end,
    SslPost = fun(Value) when is_list(Value) ->
		      {ok, Value};
		 (_) ->
		      error
	      end,
    ProxyAuthPost = fun({User, Passwd} = Value) when is_list(User) andalso 
						     is_list(Passwd) ->
			    {ok, Value};
		       (_) ->
			    error
		    end,
    RelaxedPost = fun(Value) when (Value =:= true) orelse 
				  (Value =:= false) ->
			  {ok, Value};
		     (_) ->
			  error
		  end,
    ConnTimeoutPost = 
	fun(Value) when is_integer(Value) andalso (Value >= 0) ->
		{ok, Value};
	   (infinity = Value) ->
		{ok, Value};
	   (_) ->
		error
	end,
    [
     {version,         {value, "HTTP/1.1"},              #http_options.version,         VersionPost}, 
     {timeout,         {value, ?HTTP_REQUEST_TIMEOUT},   #http_options.timeout,         TimeoutPost},
     {autoredirect,    {value, true},                    #http_options.autoredirect,    AutoRedirectPost},
     {ssl,             {value, []},                      #http_options.ssl,             SslPost},
     {proxy_auth,      {value, undefined},               #http_options.proxy_auth,      ProxyAuthPost},
     {relaxed,         {value, false},                   #http_options.relaxed,         RelaxedPost},
     %% this field has to be *after* the timeout field (as that field is used for the default value)
     {connect_timeout, {field,   #http_options.timeout}, #http_options.connect_timeout, ConnTimeoutPost}
    ].


request_options_defaults() ->
    VerifyBoolean = 
	fun(Value) when ((Value =:= true) orelse (Value =:= false)) ->
		ok;
	   (_) ->
		error
	end,

    VerifySync = VerifyBoolean,

    VerifyStream = 
	fun(none = _Value) -> 
		ok;
	   (self = _Value) -> 
		ok;
	   ({self, once} = _Value) -> 
		ok;
	   (Value) when is_list(Value) -> 
		ok;
	   (_) -> 
		error
	end,

    VerifyBodyFormat = 
	fun(string = _Value) ->
		ok;
	   (binary = _Value) ->
		ok;
	   (_) ->
		error
	end,
    
    VerifyFullResult = VerifyBoolean,

    VerifyHeaderAsIs = VerifyBoolean,

    VerifyReceiver = 
	fun(Value) when is_pid(Value) ->
		ok;
	   ({M, F, A}) when (is_atom(M) andalso 
			     is_atom(F) andalso 
			     is_list(A)) ->
		ok;
	   (Value) when is_function(Value, 1) ->
		ok;
	   (_) ->
		error
	end,

    VerifySocketOpts = 
	fun([]) ->
		{ok, undefined};
	   (Value) when is_list(Value) ->
		ok;
	   (_) ->
		error
	end,

    [
     {sync,          true,      VerifySync}, 
     {stream,        none,      VerifyStream},
     {body_format,   string,    VerifyBodyFormat},
     {full_result,   true,      VerifyFullResult},
     {headers_as_is, false,     VerifyHeaderAsIs},
     {receiver,      self(),    VerifyReceiver},
     {socket_opts,   undefined, VerifySocketOpts}
    ]. 

request_options(Options) ->
    Defaults = request_options_defaults(), 
    request_options(Defaults, Options, []).

request_options([], [], Acc) ->
    request_options_sanity_check(Acc),
    lists:reverse(Acc);
request_options([], Options, Acc) ->
    Fun = fun(BadOption) ->
		    Report = io_lib:format("Invalid option ~p ignored ~n", 
					   [BadOption]),
		    error_logger:info_report(Report)
	  end,
    lists:foreach(Fun, Options),
    Acc;
request_options([{Key, DefaultVal, Verify} | Defaults], Options, Acc) ->
    case lists:keysearch(Key, 1, Options) of
	{value, {Key, Value}} ->
	    case Verify(Value) of
		ok ->
		    Options2 = lists:keydelete(Key, 1, Options),
		    request_options(Defaults, Options2, [{Key, Value} | Acc]);
		{ok, Value2} ->
		    Options2 = lists:keydelete(Key, 1, Options),
		    request_options(Defaults, Options2, [{Key, Value2} | Acc]);
		error ->
		    Report = io_lib:format("Invalid option ~p:~p ignored ~n", 
					   [Key, Value]),
		    error_logger:info_report(Report),
		    Options2 = lists:keydelete(Key, 1, Options),
		    request_options(Defaults, Options2, Acc)
	    end;
	false ->
	    request_options(Defaults, Options, [{Key, DefaultVal} | Acc])
    end.

request_options_sanity_check(Opts) ->
    case proplists:get_value(sync, Opts) of
	Sync when (Sync =:= true) ->
	    case proplists:get_value(receiver, Opts) of
		Pid when is_pid(Pid) andalso (Pid =:= self()) ->
		    ok;
		BadReceiver ->
		    throw({error, {bad_options_combo, 
				   [{sync, true}, {receiver, BadReceiver}]}})
	    end,
	    case proplists:get_value(stream, Opts) of
		Stream when (Stream =:= self) orelse 
			    (Stream =:= {self, once}) ->
		    throw({error, streaming_error});
		_ ->
		    ok
	    end;
	_ ->
	    ok
    end,
    ok.

validate_options(Options) ->
    (catch validate_options(Options, [])).

validate_options([], ValidateOptions) ->
    {ok, lists:reverse(ValidateOptions)};

validate_options([{proxy, Proxy} = Opt| Tail], Acc) ->
    validate_proxy(Proxy),
    validate_options(Tail, [Opt | Acc]);

validate_options([{max_sessions, Value} = Opt| Tail], Acc) ->
    validate_max_sessions(Value),
    validate_options(Tail, [Opt | Acc]);

validate_options([{keep_alive_timeout, Value} = Opt| Tail], Acc) ->
    validate_keep_alive_timeout(Value),
    validate_options(Tail, [Opt | Acc]);

validate_options([{max_keep_alive_length, Value} = Opt| Tail], Acc) ->
    validate_max_keep_alive_length(Value),
    validate_options(Tail, [Opt | Acc]);

validate_options([{pipeline_timeout, Value} = Opt| Tail], Acc) ->
    validate_pipeline_timeout(Value),
    validate_options(Tail, [Opt | Acc]);

validate_options([{max_pipeline_length, Value} = Opt| Tail], Acc) ->
    validate_max_pipeline_length(Value), 
    validate_options(Tail, [Opt | Acc]);

validate_options([{cookies, Value} = Opt| Tail], Acc) ->
    validate_cookies(Value),
    validate_options(Tail, [Opt | Acc]);

validate_options([{ipfamily, Value} = Opt| Tail], Acc) ->
    validate_ipfamily(Value), 
    validate_options(Tail, [Opt | Acc]);

%% For backward compatibillity
validate_options([{ipv6, Value}| Tail], Acc) ->
    NewValue = validate_ipv6(Value), 
    Opt = {ipfamily, NewValue},
    validate_options(Tail, [Opt | Acc]);

validate_options([{ip, Value} = Opt| Tail], Acc) ->
    validate_ip(Value),
    validate_options(Tail, [Opt | Acc]);

validate_options([{port, Value} = Opt| Tail], Acc) ->
    validate_port(Value), 
    validate_options(Tail, [Opt | Acc]);

validate_options([{socket_opts, Value} = Opt| Tail], Acc) ->
    validate_socket_opts(Value), 
    validate_options(Tail, [Opt | Acc]);

validate_options([{verbose, Value} = Opt| Tail], Acc) ->
    validate_verbose(Value), 
    validate_options(Tail, [Opt | Acc]);

validate_options([{_, _} = Opt| _], _Acc) ->
    {error, {not_an_option, Opt}}.


validate_proxy({{ProxyHost, ProxyPort}, NoProxy} = Proxy) 
  when is_list(ProxyHost) andalso 
       is_integer(ProxyPort) andalso 
       is_list(NoProxy) ->
    Proxy;
validate_proxy(BadProxy) ->
    bad_option(proxy, BadProxy).

validate_max_sessions(Value) when is_integer(Value) andalso (Value >= 0) ->
    Value;
validate_max_sessions(BadValue) ->
    bad_option(max_sessions, BadValue).

validate_keep_alive_timeout(Value) when is_integer(Value) andalso (Value >= 0) ->
    Value;
validate_keep_alive_timeout(infinity = Value) ->
    Value;
validate_keep_alive_timeout(BadValue) ->
    bad_option(keep_alive_timeout, BadValue).

validate_max_keep_alive_length(Value) when is_integer(Value) andalso (Value >= 0) ->
    Value;
validate_max_keep_alive_length(BadValue) ->
    bad_option(max_keep_alive_length, BadValue).

validate_pipeline_timeout(Value) when is_integer(Value) ->
    Value;
validate_pipeline_timeout(infinity = Value) ->
    Value;
validate_pipeline_timeout(BadValue) ->
    bad_option(pipeline_timeout, BadValue).

validate_max_pipeline_length(Value) when is_integer(Value) ->
    Value;
validate_max_pipeline_length(BadValue) ->
    bad_option(max_pipeline_length, BadValue).

validate_cookies(Value) 
  when ((Value =:= enabled)  orelse 
	(Value =:= disabled) orelse 
	(Value =:= verify)) ->
    Value;
validate_cookies(BadValue) ->
    bad_option(cookies, BadValue).

validate_ipv6(Value) when (Value =:= enabled) orelse (Value =:= disabled) ->
    case Value of
	enabled ->
	    inet6fb4;
	disabled ->
	    inet
    end;  
validate_ipv6(BadValue) ->
    bad_option(ipv6, BadValue).

validate_ipfamily(Value) 
  when (Value =:= inet) orelse (Value =:= inet6) orelse (Value =:= inet6fb4) ->
    Value;
validate_ipfamily(BadValue) ->
    bad_option(ipfamily, BadValue).

validate_ip(Value) 
  when is_tuple(Value) andalso ((size(Value) =:= 4) orelse (size(Value) =:= 8)) ->
    Value;
validate_ip(BadValue) ->
    bad_option(ip, BadValue).
    
validate_port(Value) when is_integer(Value) ->
    Value;
validate_port(BadValue) ->
    bad_option(port, BadValue).

validate_socket_opts(Value) when is_list(Value) ->
    Value;
validate_socket_opts(BadValue) ->
    bad_option(socket_opts, BadValue).

validate_verbose(Value) 
  when ((Value =:= false) orelse 
	(Value =:= verbose) orelse 
	(Value =:= debug) orelse 
	(Value =:= trace)) ->
    ok;
validate_verbose(BadValue) ->
    bad_option(verbose, BadValue).

bad_option(Option, BadValue) ->
    throw({error, {bad_option, Option, BadValue}}).


header_host(https, Host, 443 = _Port) ->
    Host;
header_host(http, Host, 80 = _Port) ->
    Host;
header_host(_Scheme, Host, Port) ->
    Host ++ ":" ++ integer_to_list(Port).


header_record(NewHeaders, Host, #http_options{version = Version}) ->
    header_record(NewHeaders, #http_request_h{}, Host, Version).

header_record([], RequestHeaders, Host, Version) ->
    validate_headers(RequestHeaders, Host, Version);
header_record([{"cache-control", Val} | Rest], RequestHeaders, Host, Version) ->
    header_record(Rest, RequestHeaders#http_request_h{'cache-control' = Val},
		  Host, Version);  
header_record([{"connection", Val} | Rest], RequestHeaders, Host, Version) ->
    header_record(Rest, RequestHeaders#http_request_h{connection = Val}, Host,
		 Version);
header_record([{"date", Val} | Rest], RequestHeaders, Host, Version) ->
    header_record(Rest, RequestHeaders#http_request_h{date = Val}, Host, 
		  Version);  
header_record([{"pragma", Val} | Rest], RequestHeaders, Host, Version) ->
    header_record(Rest, RequestHeaders#http_request_h{pragma = Val}, Host,
		  Version);  
header_record([{"trailer", Val} | Rest], RequestHeaders, Host, Version) ->
    header_record(Rest, RequestHeaders#http_request_h{trailer = Val}, Host,
		  Version);  
header_record([{"transfer-encoding", Val} | Rest], RequestHeaders, Host, 
	      Version) ->
    header_record(Rest, 
		  RequestHeaders#http_request_h{'transfer-encoding' = Val},
		  Host, Version);  
header_record([{"upgrade", Val} | Rest], RequestHeaders, Host, Version) ->
    header_record(Rest, RequestHeaders#http_request_h{upgrade = Val}, Host,
		  Version);  
header_record([{"via", Val} | Rest], RequestHeaders, Host, Version) ->
    header_record(Rest, RequestHeaders#http_request_h{via = Val}, Host, 
		  Version);  
header_record([{"warning", Val} | Rest], RequestHeaders, Host, Version) ->
    header_record(Rest, RequestHeaders#http_request_h{warning = Val}, Host,
		  Version);  
header_record([{"accept", Val} | Rest], RequestHeaders, Host, Version) ->
    header_record(Rest, RequestHeaders#http_request_h{accept = Val}, Host,
		  Version);  
header_record([{"accept-charset", Val} | Rest], RequestHeaders, Host, Version) ->
    header_record(Rest, RequestHeaders#http_request_h{'accept-charset' = Val}, 
		  Host, Version);  
header_record([{"accept-encoding", Val} | Rest], RequestHeaders, Host, 
	      Version) ->
    header_record(Rest, RequestHeaders#http_request_h{'accept-encoding' = Val},
		  Host, Version);  
header_record([{"accept-language", Val} | Rest], RequestHeaders, Host, 
	      Version) ->
    header_record(Rest, RequestHeaders#http_request_h{'accept-language' = Val},
		  Host, Version);  
header_record([{"authorization", Val} | Rest], RequestHeaders, Host, Version) ->
    header_record(Rest, RequestHeaders#http_request_h{authorization = Val}, 
		  Host, Version);  
header_record([{"expect", Val} | Rest], RequestHeaders, Host, Version) ->
    header_record(Rest, RequestHeaders#http_request_h{expect = Val}, Host,
		  Version);
header_record([{"from", Val} | Rest], RequestHeaders, Host, Version) ->
    header_record(Rest, RequestHeaders#http_request_h{from = Val}, Host, 
		  Version);  
header_record([{"host", Val} | Rest], RequestHeaders, Host, Version) ->
    header_record(Rest, RequestHeaders#http_request_h{host = Val}, Host, 
		  Version);
header_record([{"if-match", Val} | Rest], RequestHeaders, Host, Version) ->
    header_record(Rest, RequestHeaders#http_request_h{'if-match' = Val},
		  Host, Version);  
header_record([{"if-modified-since", Val} | Rest], RequestHeaders, Host, 
	      Version) ->
    header_record(Rest, 
		  RequestHeaders#http_request_h{'if-modified-since' = Val},
		  Host, Version);  
header_record([{"if-none-match", Val} | Rest], RequestHeaders, Host, Version) ->
    header_record(Rest, RequestHeaders#http_request_h{'if-none-match' = Val}, 
		  Host, Version);  
header_record([{"if-range", Val} | Rest], RequestHeaders, Host, Version) ->
    header_record(Rest, RequestHeaders#http_request_h{'if-range' = Val}, 
		  Host, Version);  

header_record([{"if-unmodified-since", Val} | Rest], RequestHeaders, Host, 
	      Version) ->
    header_record(Rest, RequestHeaders#http_request_h{'if-unmodified-since' 
						      = Val}, Host, Version);  
header_record([{"max-forwards", Val} | Rest], RequestHeaders, Host, Version) ->
    header_record(Rest, RequestHeaders#http_request_h{'max-forwards' = Val}, 
		  Host, Version);  
header_record([{"proxy-authorization", Val} | Rest], RequestHeaders, Host, 
	      Version) ->
    header_record(Rest, RequestHeaders#http_request_h{'proxy-authorization' 
						      = Val}, Host, Version);  
header_record([{"range", Val} | Rest], RequestHeaders, Host, Version) ->
    header_record(Rest, RequestHeaders#http_request_h{range = Val}, Host, 
		  Version);  
header_record([{"referer", Val} | Rest], RequestHeaders, Host, Version) ->
    header_record(Rest, RequestHeaders#http_request_h{referer = Val}, Host, 
		  Version);  
header_record([{"te", Val} | Rest], RequestHeaders, Host, Version) ->
    header_record(Rest, RequestHeaders#http_request_h{te = Val}, Host, 
		  Version);  
header_record([{"user-agent", Val} | Rest], RequestHeaders, Host, Version) ->
    header_record(Rest, RequestHeaders#http_request_h{'user-agent' = Val}, 
		  Host, Version);  
header_record([{"allow", Val} | Rest], RequestHeaders, Host, Version) ->
    header_record(Rest, RequestHeaders#http_request_h{allow = Val}, Host, 
		  Version);  
header_record([{"content-encoding", Val} | Rest], RequestHeaders, Host, 
	      Version) ->
    header_record(Rest, 
		  RequestHeaders#http_request_h{'content-encoding' = Val},
		  Host, Version);  
header_record([{"content-language", Val} | Rest], RequestHeaders, 
	      Host, Version) ->
    header_record(Rest, 
		  RequestHeaders#http_request_h{'content-language' = Val}, 
		  Host, Version);  
header_record([{"content-length", Val} | Rest], RequestHeaders, Host, Version) ->
    header_record(Rest, RequestHeaders#http_request_h{'content-length' = Val},
		  Host, Version);  
header_record([{"content-location", Val} | Rest], RequestHeaders, 
	      Host, Version) ->
    header_record(Rest, 
		  RequestHeaders#http_request_h{'content-location' = Val},
		  Host, Version);  
header_record([{"content-md5", Val} | Rest], RequestHeaders, Host, Version) ->
    header_record(Rest, RequestHeaders#http_request_h{'content-md5' = Val}, 
		  Host, Version);  
header_record([{"content-range", Val} | Rest], RequestHeaders, Host, Version) ->
    header_record(Rest, RequestHeaders#http_request_h{'content-range' = Val},
		  Host, Version);  
header_record([{"content-type", Val} | Rest], RequestHeaders, Host, Version) ->
    header_record(Rest, RequestHeaders#http_request_h{'content-type' = Val}, 
		  Host, Version);  
header_record([{"expires", Val} | Rest], RequestHeaders, Host, Version) ->
    header_record(Rest, RequestHeaders#http_request_h{expires = Val}, Host, 
		  Version);  
header_record([{"last-modified", Val} | Rest], RequestHeaders, Host, Version) ->
    header_record(Rest, RequestHeaders#http_request_h{'last-modified' = Val},
		  Host, Version);  
header_record([{Key, Val} | Rest], RequestHeaders, Host, Version) ->
    header_record(Rest, RequestHeaders#http_request_h{
			  other = [{Key, Val} |
				   RequestHeaders#http_request_h.other]}, 
		  Host, Version).

validate_headers(RequestHeaders = #http_request_h{te = undefined}, Host, 
		 "HTTP/1.1" = Version) ->
    validate_headers(RequestHeaders#http_request_h{te = ""}, Host, 
		     "HTTP/1.1" = Version);
validate_headers(RequestHeaders = #http_request_h{host = undefined}, 
		 Host, "HTTP/1.1" = Version) ->
    validate_headers(RequestHeaders#http_request_h{host = Host}, Host, Version);
validate_headers(RequestHeaders, _, _) ->
    RequestHeaders.


child_name2info(undefined) ->
    {error, no_such_service};
child_name2info(httpc_manager) ->
    {ok, [{profile, default}]};
child_name2info({httpc, Profile}) ->
    {ok, [{profile, Profile}]}.

child_name(_, []) ->
    undefined;
child_name(Pid, [{Name, Pid} | _]) ->
    Name;
child_name(Pid, [_ | Children]) ->
    child_name(Pid, Children).

%% d(F) ->
%%    d(F, []).

%% d(F, A) -> 
%%     d(get(dbg), F, A).

%% d(true, F, A) ->
%%     io:format(user, "~w:~w:" ++ F ++ "~n", [self(), ?MODULE | A]);
%% d(_, _, _) ->
%%     ok.

