/*
 * Copyright 2017-2022 Harm Brouwer <me@hbrouwer.eu>
 *     and Noortje Venhuizen <njvenhuizen@gmail.com>
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

:- module(yap_random,
        [
                maybe/1,
                set_random/1
        ]).

%!      maybe(+P) is semidet.
%
%       As in SWI-prolog: Succeed with probability P, fail with probability 
%       1-P.

maybe(P) :-
        R is random,
        R < P.

%!      set_random(seed(+Seed)) is det.
%
%       As in SWI-prolog: Set the seed of the random generator for this
%       thread.

set_random(seed(Seed)) :-
        srandom(Seed).
