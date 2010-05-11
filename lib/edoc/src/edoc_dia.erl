%%
%% %CopyrightBegin%
%% 
%% Copyright Ericsson AB 1996-2009. All Rights Reserved.
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

%% @doc EDoc interface to Dialyzer specifications and types.

-module(edoc_dia).

-export([add_data/5, edoc_dialyzer_tag/1, is_dialyzer_tag/1, 
         dialyzer_data/1, tags/3]).

-include("edoc.hrl").
-include("edoc_types.hrl").

-record(dia_data, {line = 0, name = '', data}).

-type edoc_env() :: edoc_lib:edoc_env().
-type proplist() :: [proplists:property()].
-type syntaxTree() :: syntax_tools:syntaxTree().

-define(DIALYZER_SPECS, none).
-define(REPORT_MISSING_TYPE, true).
-define(REPORT_TYPE_MISMATCH, true).

-define(TOP_TYPE, term).

%% @doc Adds Dialyzer data to the environment.
-type entry() :: #entry{}.
-type entries() :: [entry()].
-spec add_data(syntaxTree(), entries(), Options::proplist(), module(),
               edoc_env()) -> edoc_env().

%% The argument Module is not used.
add_data(Forms, Entries, Opts, _Module, Env) ->
    case dialyzer_specs_usage(Opts) of
        none ->
            Env;
        Usage ->
            DiaData = collect(Forms),
            add_data1(DiaData, Entries, Usage, Opts, Env)
    end.

collect(Forms) ->
    [dia_data(F) ||
        F <- Forms,
        {attribute, {T, _}} <- [erl_syntax_lib:analyze_form(F)],
        is_dialyzer_tag(T)].

dia_data(F) ->
    L = erl_syntax:get_pos(F),
    {Name, Data0} = erl_syntax_lib:analyze_wild_attribute(F),
    Data = case {Name, Data0} of
               {type, {{record, R}, Fs, []}} ->
                   {{record, R}, {type, 0, record, [{atom,0,R} | Fs]}, []};
               _ ->
                   Data0
           end,
    #dia_data{line = L, name = Name, data = Data}.

add_data1(DiaData, Entries, Usage, Opts, Env) ->
    Specs0 = dia_specs(DiaData, Entries, Usage, Opts),
    TypeDefs0 = dia_types(DiaData),
    {TypeDefs, Specs, Missing} = types_and_specs(Specs0, TypeDefs0),
    Env#env{dialyzer_data = {TypeDefs, Specs, Missing}}.
    
%% Converts from Dialyzer representation to EDoc representation.
dia_types(DiaData) ->
    [#tag{name = type, line = L,
          data = {#t_typedef{name = type_name(TypeNameRepr),
                             args = d2e(Args),
                             type = d2e(opaque2abstr(Name, Type))},
                  _Doc=""}} ||
        #dia_data{line = L, name = Name, 
                  data = {TypeNameRepr, Type, Args}} <- DiaData,
        edoc_dialyzer_tag(Name) =:= type].

%% Turns an opaque type into an abstract datatype.
%% Note: top level annotation is ignored.
opaque2abstr(opaque, _T) -> undefined;
opaque2abstr(type, T) -> T.

dia_specs(DiaData, Entries, Usage, Opts) ->
    SpecEntries = if 
                      Usage =:= all -> % EDoc
                          edoc_data:function_filter(Entries, Opts);
                      is_list(Usage) -> % Ignore @hidden and @private.
                          select_entries(Usage, Entries)
                  end,
    Specs = sets:from_list([Name || #entry{name=Name} <- SpecEntries]),
    [#tag{name = spec, line = L,
          data = #t_spec{name = #t_name{name = element(1, FunName)},
                         clauses = d2e_clauses(TypeSpecs)}} ||
        #dia_data{line = L, name = spec,
                  data = {SpecFun, TypeSpecs}} <- DiaData,
        sets:is_element(FunName = fun_name(SpecFun), Specs)].

%% Restrict the set of specifications. Exactly those types used
%% (indirectly) by some chosen spec are "tagged".
%%
%% Note: for now it is assumed that when Dialyzer specifications
%% and types are used for documentation outside EDoc, it is OK
%% to return data for specifications and types that are not used
%% (such as callback functions in behavior modules).
select_entries(MFAs, Entries) ->
    T = sets:from_list(MFAs),
    [E || #entry{name = N}=E <- Entries, sets:is_element(N, T)].

fun_name({F,A}) when is_atom(F), is_integer(A), A >= 0 ->
    {F,A};
fun_name({M,F,A}) when is_atom(F), is_atom(M), is_integer(A), A >= 0 ->
    %% Note: the module M is ignored!
    {F,A}.

d2e_clauses(TypeSpecs) ->
    [#t_clause{type = TFun} || TFun <- d2e(TypeSpecs)].

d2e({ann_type,_,[V, T0]}) ->
    %% Note: the -spec/-type syntax allows annotations everywhere, but
    %% EDoc does not. The fact that the annotation is added to the
    %% type here does not necessarily mean that it will be used by the
    %% layout module.
    T = d2e(T0),
    ?add_t_ann(T, element(3, V));
d2e({paren_type,_,[T]}) ->
    d2e(T); % Is this OK?
d2e({type,_,no_return,[]}) ->
    #t_type{name = #t_name{name = none}};
d2e({remote_type,_,[{atom,_,M},{atom,_,F},Ts0]}) ->
    Ts = d2e(Ts0),
    typevar_anno(#t_type{name = #t_name{module = M, name = F}, args = Ts}, Ts);
d2e({type,_,'fun',[{type,_,product,As0},Ran0]}) ->
    Ts = [Ran|As] = d2e([Ran0|As0]),
    %% Assume that the linter has checked type variables.
    typevar_anno(#t_fun{args = As, range = Ran}, Ts);
d2e({type,_,'fun',[A0={type,_,any},Ran0]}) ->
    Ts = [A, Ran] = d2e([A0, Ran0]),
    typevar_anno(#t_fun{args = [A], range = Ran}, Ts);
d2e({type,_,'fun',[]}) ->
    #t_type{name = #t_name{name = function}, args = []};    
d2e({type,_,any}) ->
    #t_var{name = '...'}; % Kludge... not a type variable!
d2e({type,_,nil,[]}) ->
    #t_nil{};
d2e({type,_,list,[T0]}) ->
    T = d2e(T0),
    typevar_anno(#t_list{type = T}, [T]);
d2e({type,_,nonempty_list,[T0]}) ->
    T = d2e(T0),
    typevar_anno(#t_nonempty_list{type = T}, [T]);
d2e({type,_,bounded_fun,[T,Gs0]}) ->
    [F0|Gs] = Ts = d2e([T|Gs0]),
    F = ?set_t_ann(F0, lists:keydelete(type_variables, 1, ?t_ann(F0))),
    %% Assume that the linter has checked type variables.
    typevar_anno(F#t_fun{guards = Gs}, Ts);
d2e({type,_,range,[I1,I2]}) ->
    #t_integer_range{from = element(3, I1), to = element(3, I2)};
d2e({type,_,constraint,[N,Ts0]}) ->
    Ts = d2e(Ts0),
    typevar_anno(#t_guard{name = #t_name{name = element(3, N)}, args = Ts},
                 Ts);
d2e({type,_,union,Ts0}) ->
    Ts = d2e(Ts0),
    typevar_anno(#t_union{types = Ts}, Ts);
d2e({type,_,tuple,any}) ->
    #t_type{name = #t_name{name = tuple}, args = []};
d2e({type,_,binary,[Base,Unit]}) ->
    #t_binary{base_size = element(3, Base),
              unit_size = element(3, Unit)};
d2e({type,_,tuple,Ts0}) ->
    Ts = d2e(Ts0),
    typevar_anno(#t_tuple{types = Ts}, Ts);
d2e({type,_,record,[Name|Fs0]}) ->
    Atom = #t_atom{val = element(3, Name)},
    Fs = d2e(Fs0),
    typevar_anno(#t_record{name = Atom, fields = Fs}, Fs);
d2e({type,_,field_type,[Name,Type0]}) ->
    Type = d2e(Type0),
    typevar_anno(#t_field{name = #t_atom{val = element(3, Name)}, type = Type},
                 [Type]);
d2e({typed_record_field,{record_field,L,Name},Type}) ->
    d2e({type,L,field_type,[Name,Type]});
d2e({typed_record_field,{record_field,L,Name,_E},Type}) ->
    d2e({type,L,field_type,[Name,Type]});
d2e({record_field,L,_Name,_E}=F) ->
    d2e({typed_record_field,F,{type,L,any,[]}}); % Maybe skip...
d2e({record_field,L,_Name}=F) ->
    d2e({typed_record_field,F,{type,L,any,[]}}); % Maybe skip...
d2e({type,_,Name,Types0}) ->
    Types = d2e(Types0),
    typevar_anno(#t_type{name = #t_name{name = Name}, args = Types}, Types);
d2e({var,_,'_'}) ->
    #t_type{name = #t_name{name = ?TOP_TYPE}};
d2e({var,_,TypeName}) ->
    TypeVar = ordsets:from_list([TypeName]),
    T = #t_var{name = TypeName},
    %% Annotate type variables with the name of the variable.
    %% Doing so will stop edoc_layout (and possibly other layout modules)
    %% from using the argument name from the source or to invent a new name.
    T1 = ?add_t_ann(T, {type_variables, TypeVar}),
    ?add_t_ann(T1, TypeName);
d2e(L) when is_list(L) ->
    [d2e(T) || T <- L];
d2e({atom,_,A}) ->
    #t_atom{val = A};
d2e({integer,_,I}) ->
    #t_integer{val = I};
d2e(undefined = U) -> % opaque
    U.

%% A type annotation (a tuple; neither an atom nor a list).
typevar_anno(Type, Ts) ->
    Vs = typevars(Ts),
    case ordsets:to_list(Vs) of
        [] -> Type;
        _ -> ?add_t_ann(Type, {type_variables, Vs})
    end.

-record(xs, {all_typedefs,
             used_typedefs = dict:new(),
             missing = []}).

%% Exactly those types used (indirectly) by some chosen spec are "tagged".
types_and_specs(Specs0, TypeDefs0) ->
    DT0 = dict:from_list([{decl_name(T), T} || T <- TypeDefs0]),
    XS0 = #xs{all_typedefs = DT0},
    {Specs, XS} = specs(Specs0, XS0, []),
    #xs{used_typedefs = UDT, missing = Missing} = XS,
    TypeL = [Tag || {_,Tag}<- dict:to_list(UDT)],
    {TypeL, Specs, Missing}.

specs([], XS, Ss) ->
    {Ss, XS};
specs([Tag0 | L], XS0, Ss) ->
    #tag{line = Line, data = #t_spec{clauses = Clauses0}=Spec0} = Tag0,
    {Clauses, XS} = clauses(Clauses0, XS0, Line, []),
    Tag = Tag0#tag{data = Spec0#t_spec{clauses = Clauses}},
    specs(L, XS, [Tag | Ss]).

clauses([], XS, _Line, Clauses) ->
    {lists:reverse(Clauses), XS};
clauses([Cl | Cls], XS0, Line, Clauses) ->
    #t_clause{type = TFun0, defs = []} = Cl,
    XS = used_types(TFun0, XS0),
    {Guards, Defs0} = guard_defs(TFun0#t_fun.guards),
    TFun = TFun0#t_fun{guards = Guards},
    VDefs = typevar_defs([TFun], Defs0),
    Defs = Defs0 ++ defs(VDefs),
    Clause = Cl#t_clause{type = TFun, defs = Defs},
    clauses(Cls, XS, Line, [Clause | Clauses]).

defs(Defs) ->
    lists:usort(Defs).

%% Add V = term() for type variables (unless bounded by is_subtype/2).
typevar_defs(_Types, _SubTypeVars) ->
    [].
%% typevar_defs(Types, SubTypeVars) ->
%%     [#t_def{name = #t_var{name = N},
%%             type = #t_type{name = #t_name{name = ?TOP_TYPE}}} ||
%%         N <- ordsets:to_list(typevars(Types)),
%%         [] =:= [N1 || #t_def{name = #t_var{name = N1}} <- SubTypeVars,
%%                       N =:= N1]].

%% Some guards are turned into definitions. Example:
%%   when is_subtype(X, tuple())
%% yields
%%   X = tuple()
%% Some caution is necessary since a subset relation is turned into a
%% definition. The variable (X) must not be a subset of more than one
%% type. But it is allowed to have variables that depend upon themselves
%% since Dialyzer allows recursive types.
guard_defs(Guards) ->
    AllVG = [{V, G} || #t_guard{args = [A | _]}=G <- Guards,
                       V <- typevars([A])],
    VGs = [{G, T} || {V, [G]} <- sofs:to_external(family(AllVG)),
                     is_tuple(T = simple_guard(G, V))],
    guard_defs(Guards, VGs, [], []).

family(L) ->
    sofs:relation_to_family(sofs:relation(L)).

simple_guard(#t_guard{name = #t_name{name = is_subtype},
                         args = [#t_var{name = N}=V, T]}, Var) ->
    true = N =:= Var,
    {V, T};
simple_guard(_, _V) ->
    no.

guard_defs([], _VGs, Guards, Defs) ->
    {lists:reverse(Guards), lists:reverse(Defs)};
guard_defs([G | Gs], VGs, Guards, Defs) ->
    case lists:keyfind(G, 1, VGs) of
        {G, {N, T}} ->
            Def = #t_def{name = N, type = T},
            guard_defs(Gs, VGs, Guards, [Def | Defs]);
        false ->
            guard_defs(Gs, VGs, [G | Guards], Defs)
    end.

used_types(#t_type{name = Name, args = Args}, XS0) ->
    XS = used_types(Args, XS0),
    #t_name{module = Mod, name = N} = Name,
    NArgs = length(Args),
    used_type(N, NArgs, Mod, XS);
used_types(#t_var{}, XS) ->
    XS;
used_types(#t_fun{args = Args0, range = Range0, guards = Guards0}, XS0) ->
    XS1 = used_types(Args0, XS0),
    XS2 = used_types(Range0, XS1),
    used_types(Guards0, XS2);
used_types(#t_tuple{types = Types0}, XS) ->
    used_types(Types0, XS);
used_types(#t_list{type = Type0}, XS) ->
    used_types(Type0, XS);
used_types(#t_nil{}, XS) ->
    XS;
used_types(#t_nonempty_list{type = Type0}, XS) ->
    used_types(Type0, XS);
used_types(#t_atom{}, XS) ->
    XS;
used_types(#t_integer{}, XS) ->
    XS;
used_types(#t_integer_range{}, XS) ->
    XS;
used_types(#t_binary{}, XS) ->
    XS;
used_types(#t_float{}, XS) ->
    XS;
used_types(#t_union{types = Types0}, XS) ->
    used_types(Types0, XS);
used_types(#t_record{fields = Fields0}=T, XS0) ->
    XS = used_types(Fields0, XS0),
    #t_record{name = #t_atom{val = Name}} = T,
    used_type({record, Name}, 0, _Mod = [], XS);
used_types(#t_record_name{}, XS) ->
    XS;
used_types(#t_field{type = Type0}, XS0) ->
    used_types(Type0, XS0);
used_types(#t_guard{args = Args0}, XS0) ->
    used_types(Args0, XS0);
used_types(undefined, XS) -> % opaque
    XS;
used_types([], XS) ->
    XS;
used_types([E0 | Es0], XS0) ->
    used_types(Es0, used_types(E0, XS0)).

used_type(N, NArgs, Mod, XS0) ->
    TypeName = {N, NArgs},
    case dict:find(TypeName, XS0#xs.all_typedefs) of
        {ok, TagType} when Mod =:= [] ->
            used_datatype(TagType, XS0);
        {ok, _TagType} when Mod =/= [] ->
             % Ignore external types.
            XS0;
        error ->
            case 
                Mod =/= [] 
                orelse edoc_types:is_predefined(N, NArgs) 
                orelse is_predefined_otp_type(N, NArgs)
            of
                true ->
                    XS0;
                false ->
                    XS0#xs{missing = [TypeName | XS0#xs.missing]}
            end
    end.

used_datatype(#tag{data = {#t_typedef{}=T, _Doc}}=Tag, XS0) ->
    #t_typedef{name = N, args = As, type = Type0, defs = []}=T,
    TypeNameRepr = type_name_repr(N),
    TypeName = {TypeNameRepr, length(As)},
    case dict:find(TypeName, XS0#xs.used_typedefs) of
        error ->
            XS = XS0#xs{used_typedefs = 
                            dict:store(TypeName, Tag, XS0#xs.used_typedefs)},
            case TypeNameRepr of
                {record, _} ->
                    #t_record{fields = Fields0} = Type0,
                    used_types(Fields0, XS);
                _ -> 
                    used_types(Type0, XS)
            end;
        {ok, _Tag1} ->
            XS0
    end.

%% @doc Creates tags a la EDoc for Dialyzer specifications and types.
-spec tags(entries(), edoc_env(), Options::proplist()) -> entries().

tags([], _Env, _Opts) ->
    [];
tags([E0 | Es], Env, Opts) ->
    case dialyzer_specs_usage(Opts) of
        none ->
            [E0 | Es];
        Usage ->
            {DiaTs, DiaSs, Missing} = Env#env.dialyzer_data,
            ST = dict:from_list([{decl_name(S), S} || S <- DiaSs]),
            DT0 = dict:from_list([{decl_name(T), T} || T <- DiaTs]),
            report_missing_types(Missing, Opts),
            DT = keep_typedef_text([E0 | Es], DT0),
            Globals = [T || {_Name, T} <- dict:to_list(DT)],
            E = E0#entry{data = Globals ++ E0#entry.data},
            [Entry || E1 <- [E | Es],
                      Entry <- use_dialyzer_spec(E1, Opts, ST, DT, Usage)]
    end.
            
dialyzer_specs_usage(Opts) ->
    proplists:get_value(dialyzer_specs, Opts, ?DIALYZER_SPECS).

use_dialyzer_spec(#entry{name = Name, data = Ts0}=E, Opts, ST, DT, Usage) ->
    case dict:find(Name, ST) of
        error when tuple_size(Name) =:= 2, is_list(Usage) ->
            %% Note that only entries whose names have the form {_,_}
            %% are functions.
            [];
        error ->
            [E];
        {ok, SpecTag} ->
            %% Note: it is possible to have one EDoc and one Dialyzer type
            %% with the same name. (This should be corrected in File.)
            %% Here we just check if there is possibly a type mismatch:
            report_type_mismatch(Ts0, DT, SpecTag, Name, Opts),
            %% Discard @type and @spec:
            %% (In particular: the annotations that are used when there
            %%  is no @returns are thrown away.)
            Ts = [SpecTag] ++ 
                  [T || #tag{name = N}=T <- Ts0, not is_dialyzer_tag(N)],
            [E#entry{data = Ts}]
    end.

%% Note: the annotations ('string' in edoc_parser.yrl) that can be
%% assigned to types are not retained. Not yet, anyway.
keep_typedef_text(Entries, DT0) ->
    DocL = [{decl_name(T), Doc} ||
               #entry{data = Tags} <- Entries,
               #tag{name = type, data = {_TypeDef, Doc}}=T <- Tags,
               Doc =/= ""],
    Fun = fun({Name, Doc}, DT) ->
                  case dict:find(Name, DT) of
                      {ok, #tag{data = {TypeDef, ""}}=Tag} ->
                          dict:store(Name, Tag#tag{data = {TypeDef, Doc}}, DT);
                      error ->
                          DT
                  end
          end,
    lists:foldl(Fun, DT0, DocL).

typevars(Ts) ->
    ordsets:union(get_typevars(Ts)).

get_typevars(Ts) ->
    [Vs || T <- Ts, T =/= undefined, {type_variables, Vs} <- ?t_ann(T)].

report_missing_types(Missing, Opts) ->
    %% Unless {preprocess, true} is given, types may be missing:
    DoCheck = proplists:get_value(report_missing_type, Opts,
                                  ?REPORT_MISSING_TYPE) =:= true,
    _ = [edoc_report:warning(missing(N)) || DoCheck, N <- Missing],
    ok.

missing({N, A}) when is_atom(N), is_integer(A) ->
    io_lib:format("missing type ~w/~w", [N, A]);
missing({{record,R}, 0}) ->
    io_lib:format("untyped record ~w", [R]).

report_type_mismatch(Tags, DT, DSpec, Name, Opts) ->
    DoCheck = proplists:get_value(report_type_mismatch, Opts,
                                  ?REPORT_TYPE_MISMATCH) =:= true,
    case {DSpec, [T || DoCheck, #tag{name = spec}=T <- Tags]} of
        {#tag{name = spec,
              line = DLine,
              data = #t_spec{clauses = DCs}},
         [#tag{name = spec,
               line = ELine,
               data = #t_spec{clauses = ECs}}]} ->
            tmis(DCs, ECs, DLine, ELine, Name);
        _ ->
            ok
    end,
    [case dict:find(TName = decl_name(T), DT) of
         {ok, #tag{line = DL, 
                   data = {#t_typedef{args = DArgs,
                                      type = DRange,
                                      defs = DTDefs}, _}}} ->
             tmis(return_type(DRange), return_type(ERange), DL, EL, TName)
             andalso tmis(DTDefs, ETDefs, DL, EL, TName)
             andalso tmis(DArgs, EArgs, DL, EL, TName);
         error ->
             ok
     end
     || DoCheck,
        #tag{name = type,
             line = EL,
             data = {#t_typedef{args = EArgs, 
                                type = ERange,
                                defs = ETDefs}, _}}=T <- Tags],
    ok.

return_type(undefined) -> [];
return_type(Type) -> [Type].

tmis(DT, ET, DL, EL, {N, A}) ->
    try true = teq(DT, ET)
    catch _:_ ->
            edoc_report:warning(io_lib:fwrite("~w: possible type mismatch"
                                              " ~w/~w (~w)",
                                              [DL, N, A, EL])),
            false
    end.

teq([], []) ->
    true;
teq([DT | DTs], [ET | ETs]) ->
    teq(DT, ET) andalso teq(DTs, ETs);
teq(#t_clause{type = DT, defs = DDefs}, #t_clause{type = ET, defs = EDefs}) ->
    teq(DT, ET) andalso teq(DDefs, EDefs);
teq(#t_var{name = N}, #t_var{name = N}) ->
    true;
teq(#t_type{name = Name, args = DAs}, #t_type{name = Name, args = EAs}) ->
    teq(DAs, EAs);
teq(#t_fun{args = DAs, range = DRan}, #t_fun{args = EAs, range = ERan}) ->
    teq(DAs, EAs) andalso teq(DRan, ERan);
teq(#t_tuple{types = DTs}, #t_tuple{types = ETs}) ->
    teq(DTs, ETs);
teq(#t_list{type = DT}, #t_list{type = ET}) ->
    teq(DT, ET);
teq(#t_nil{}, #t_nil{}) ->
    true;
teq(#t_nonempty_list{type = DT}, #t_nonempty_list{type = ET}) ->
    teq(DT, ET);
teq(#t_atom{val = Atom}, #t_atom{val = Atom}) ->
    true;
teq(#t_integer{val = Integer}, #t_integer{val = Integer}) ->
    true;
teq(#t_integer_range{from = F, to = T}, #t_integer_range{from = F, to = T}) ->
    true;
teq(#t_binary{base_size = BSz, unit_size = USz}, 
    #t_binary{base_size = BSz, unit_size = USz}) ->
    true;
teq(#t_float{val = Float}, #t_float{val = Float}) ->
    true;
teq(#t_union{types = DTs}, #t_union{types = ETs}) ->
    teq(DTs, ETs); % Don't bother to sort atoms...
teq(#t_record{name = Name, fields = DFs}, 
    #t_record{name = Name, fields = EFs}) ->
    teq(DFs, EFs);
teq(#t_record_name{name = Name}, #t_record_name{name = Name}) ->
    true;
teq(#t_field{type = DT}, #t_field{type = ET}) ->
    teq(DT, ET);
teq(#t_guard{args = DAs}, #t_guard{args = EAs}) ->
    teq(DAs, EAs);
teq(_, _) ->
    false.

%% @doc Returns `none' if the option `dialyzer_specs' is equal to `none',
%% otherwise typedefs, specs, and missing types.

dialyzer_data(#env{dialyzer_data = DialyzerData}) ->
    DialyzerData.

%% @doc Returns `true' if `Tag' is one of the attribute tags
%% recognized by Dialyzer.

-spec is_dialyzer_tag(Tag::atom()) -> boolean().

is_dialyzer_tag(opaque) -> true;
is_dialyzer_tag(spec) -> true;
is_dialyzer_tag(type) -> true;
is_dialyzer_tag(_) -> false.

%% @doc Returns the kind of the attribute tag.

-type tag_kind() :: 'type' | 'spec' | 'unknown'.
-spec edoc_dialyzer_tag(Tag::atom()) -> tag_kind().

edoc_dialyzer_tag(opaque) -> type;
edoc_dialyzer_tag(spec) -> spec;
edoc_dialyzer_tag(type) -> type;
edoc_dialyzer_tag(_) -> unknown.

decl_name(#tag{name = spec, 
               data = #t_spec{name = #t_name{name = N}, clauses = [C|_]}}) ->
    {N, length((C#t_clause.type)#t_fun.args)};
decl_name(#tag{name = type, 
               data = {#t_typedef{name = Name, args = As},_}}) ->
    {type_name_repr(Name), length(As)}.

type_name({record, R}) ->
    #t_record_name{name = R};
type_name(N) ->
    #t_name{name = N}.

type_name_repr(#t_name{name = N}) ->
    N;
type_name_repr(#t_record_name{name = N}) ->
    {record, N}.

%% (Haven't enumerated iolist() and iodata() here.)
is_predefined_otp_type(array, 0) -> true;
is_predefined_otp_type(dict, 0) -> true;
is_predefined_otp_type(digraph, 0) -> true;
is_predefined_otp_type(gb_set, 0) -> true;
is_predefined_otp_type(gb_tree, 0) -> true;
is_predefined_otp_type(queue, 0) -> true;
is_predefined_otp_type(set, 0) -> true;
is_predefined_otp_type(tid, 0) -> true;
is_predefined_otp_type(_, _) -> false.
