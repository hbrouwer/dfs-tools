#!/usr/bin/env python
# -*- coding: utf-8 -*-

# Copyright 2022 Harm Brouwer <me@hbrouwer.eu>
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

import pandas as pd
import numpy as np
import random as rnd
import scipy.stats as sps

def dfs_msubset(fn_models, num_models, num_iterations, fn_subset,
        enforce_pos_inf=True, enforce_neg_inf=True):
    """Reduce model set using subset sampling.

    Reduce the dimensionality of an m x n model matrix X using subset
    sampling. The following procedure is repeated for "num_iterations" to
    arrive at an k x n matrix X' (where k < m) that maximally reflects the
    knowledge encoded in the original matrix X:

    (1) Take a subset of k rows of matrix X, and call it X';

    (2) Check if all columns of matrix X' are informative, and if the
    reduced matrix encodes the same positive and/or negative constraints (if
    enforced) as the unreduced matrix, otherwise skip to the next iteration;

    (3) Compute the similarity between X and X' on the basis of the
    proposition-by-proposition inference scores in X and X';

    (4) If X' is the best approximation of X so far, store it;

    (5) Run next iteration, and rerun from step (1);

    (6) If we have reached "num_iterations", return the best X' found.
    
    Args:
        fn_models (:obj:`str`):
            filename of the input model matrix.
        num_models (:obj:`int`):
            number of subsetted models.
        num_iterations (:obj:`int`):
            number of sample iterations.
        fn_selected (:obj:`str`):
            filename of the output model matrix.
        enforce_pos_inf (:obj:`bool`):
            flags whether positive inferences should be enforced.
        enforce_neg_inf (:obj:`bool`):
            flags whether negative inferences should be enforeced.
    
    """
    ms = pd.read_csv(fn_models, header=None, sep=" ")
    ms = ms.to_numpy()

    ps = ms[0,:]
    ms = ms[1:,:].astype(int)

    ms_iv = inference_vector(ms)

    sms = np.zeros((num_models, len(ps)))
    sms_r = 0
    itr = 0
    while itr < num_iterations:
        nsms = ms[rnd.sample(range(1,len(ms)), num_models),:]
        if not(all(np.sum(nsms, axis=0) > 1)):
            # print("Bad sample: Zero vectors ... redo iteration")
            continue
        nsms_iv = inference_vector(nsms)
        if (enforce_pos_inf and not(equal_pos_inf(ms_iv, nsms_iv))):
            # print("Bad sample: Missing positive inferences ... redo iteration") 
            continue
        if (enforce_neg_inf and not(equal_neg_inf(ms_iv, nsms_iv))):
            # print("Bad sample: Missing negative inferences ... redo iteration") 
            continue
        nsms_r, _ = sps.pearsonr(ms_iv, nsms_iv)
        print("Iteration: ", itr + 1, ", r=", nsms_r, sep="")
        if (nsms_r > sms_r):
            sms   = nsms
            sms_r = nsms_r
        itr = itr + 1
    print("\nBest r =", sms_r)
    
    df = pd.DataFrame(sms, columns=ps)
    df.to_csv(fn_subset, index=False, sep=" ")
    print("\nWrote [", fn_subset,"]")

def equal_pos_inf(ms_iv, sms_iv):
    """True iff inference vectors enforce the same positive inferences.

    Args:
        ms_iv (:obj:`ndarray`):
            inference vector of the original model matrix
        sms_iv (:obj:`ndarray`):
            inference vector of the subsetted model matrix

    Returns:
        (:obj:`bool`): True if inference vectors enforce the same positive
            inferences.

    """
    return all((ms_iv < 1) == (sms_iv < 1))

def equal_neg_inf(ms_iv, sms_iv):
    """True iff inference vectors enforce the same negative inferences.

    Args:
        ms_iv (:obj:`ndarray`):
            inference vector of the original model matrix
        sms_iv (:obj:`ndarray`):
            inference vector of the subsetted model matrix

    Returns:
        (:obj:`bool`): True if inference vectors enforce the same negative
            inferences.

    """
    return all((ms_iv > -1) == (sms_iv > -1))

def inference_vector(ms):
    """Compute inference vector for a given model set.

    Computes a vector containing the inference score of each proposition,
    given each other proposition.

    Args:
        ms (:obj:`ndarray`): matrix of models

    Returns:
        (:obj:`ndarray`): vector of inference scores

    """
    _, nps = ms.shape
    mx = np.zeros((nps, nps))
    for i1 in range(nps):
        for i2 in range(nps):
            mx[i1, i2] = inference(ms[:,i1], ms[:,i2])
    return mx.reshape(nps ** 2)

def inference(v1, v2):
    """Compute inference score of v1 from v2.

    Args:
        v1 (:obj:`ndarray`): vector a
        v2 (:obj:`ndarray`): vector b
    
    Returns
        (:obj:`float`): inference score of a from b
    
    """
    pr_ab = cond_pr(v1, v2)
    pr_a  = prior_pr(v1)
    if (pr_ab > pr_a):
        return (pr_ab - pr_a) / (1.0 - pr_a)
    else:
        return (pr_ab - pr_a) / pr_a

def prior_pr(v):
    """Compute prior probability of a vector.

    Args:
        v (:obj:`ndarray`): vector a

    Returns
        (:obj:`float`): prior probability of a

    """
    return np.sum(v) / len(v)

def conj_pr(v1, v2):
    """Compute prior conjunction probability of two vectors.

    Args:
        v1 (:obj:`ndarray`): vector a
        v2 (:obj:`ndarray`): vector b
    
    Returns
        (:obj:`float`): conjunction probability of a and b
    
    """
    if all(v1 == v2):
        return prior_pr(v1)
    else:
        return prior_pr(v1 * v2)

def cond_pr(v1, v2):
    """Compute conditional probaility of v1 given v2.

    Args:
        v1 (:obj:`ndarray`): vector a
        v2 (:obj:`ndarray`): vector b
    
    Returns
        (:obj:`float`): conditional probability of a given b
    
    """
    return conj_pr(v1, v2) / prior_pr(v2)
