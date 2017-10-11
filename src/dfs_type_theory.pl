%%
% Copyright 2017 Harm Brouwer <me@hbrouwer.eu>
%                Noortje Venhuizen <njvenhuizen@gmail.com>
%
% Licensed under the Apache License, Version 2.0 (the "License");
% you may not use this file except in compliance with the License.
% You may obtain a copy of the License at
%
%     http://www.apache.org/licenses/LICENSE-2.0
%
% Unless required by applicable law or agreed to in writing, software
% distributed under the License is distributed on an "AS IS" BASIS,
% WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
% See the License for the specific language governing permissions and
% limitations under the License.
%%

:- module(dfs_type_theory,
        [
                op(900,xfx,::),

                dfs_fapply/3,
                dfs_fapply_deriv/3,
                dfs_function_vector/3
        ]).

% dfs_fapply(+Function,+Argument,-Function)

dfs_fapply(F0::(T1,T2),F1::T1,F2::T2) :-
        F0 =.. [P|As],
        F2 =.. [P|[F1|As]].

% dfs_fapply_deriv(+FunctionList,+ModelMatrix,-Derivation)

dfs_fapply_deriv([F|Fs],MM,[(F,V)|Ts]) :-
        dfs_function_vector(F,MM,V),
        dfs_fapply_deriv_(F,Fs,MM,Ts).

dfs_fapply_deriv_(_,[],_,[]) :- !.
dfs_fapply_deriv_(F0,[F1|Fs],MM,[(F2,V)|Ts]) :-
        dfs_fapply(F0,F1,F2),
        dfs_function_vector(F2,MM,V),
        dfs_fapply_deriv_(F2,Fs,MM,Ts).

% dfs_function_vector(+Function,+ModelMatrix,-FunctionVector)

dfs_function_vector(F,MM,V) :-
        subset_model_matrix(MM,F,SMM),
        dfs_function_vector_(SMM,V).

dfs_function_vector_([],[]).
dfs_function_vector_([MV|MVs],[U|Us]) :-
        sum_model_vector(MV,S),
        length(MV,L),
        U is S / L,
        dfs_function_vector_(MVs,Us).

% subset_model_matrix(+ModelMatrix,+Function,-SubsetMatrix)

subset_model_matrix([],_,[]).
subset_model_matrix([MV|MVs],F,[SV|SVs]) :-
        subset_model_vector(MV,F,SV),
        subset_model_matrix(MVs,F,SVs).

% subset_model_vector(+ModelVector,+Function,-SubsetMatrix)

subset_model_vector([],_,[]).
subset_model_vector([(AP,S)|Ts],F::e,[(AP,S)|STs]) :-   % <-- entities
        AP =.. [_|As],
        memberchk(F,As),
        !, subset_model_vector(Ts,F::e,STs).
subset_model_vector([(F,S)|Ts],F::t,[(F,S)|STs]) :-     % <-- truth values
        !, subset_model_vector(Ts,F::t,STs).
subset_model_vector([(AP,S)|Ts],F::_,[(AP,S)|STs]) :-   % <-- functions
        F =.. [P|As0], 
        AP =.. [P|As1],
        append(_,As0,As1),
        !, subset_model_vector(Ts,F::_,STs).
subset_model_vector([_|Ts],F,STs) :-
        subset_model_vector(Ts,F,STs).

% sum_model_vector(+ModelVector,-Sum)

sum_model_vector(MV,Sum) :-
        sum_model_vector_(MV,0,Sum).

sum_model_vector_([],Sum,Sum).
sum_model_vector_([(_,S)|Ts],SumAcc,Sum) :-
        SumAcc0 is SumAcc + S,
        sum_model_vector_(Ts,SumAcc0,Sum).
