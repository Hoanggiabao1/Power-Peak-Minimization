from pysat.formula import *
from pysat.pb import *
from pysat.solvers import *
from pysat.examples.rc2 import RC2
from math import log2, ceil
import time
import sys
import os
import re
import pysat.card as card
from math import ceil,floor
import argparse


neg_X = {}
neg_XS_pair = {}
pos_A = {}

def input_files(file_name):
    W = [0]
    precedence_relations = set()
    Ex_Time = [0]

    # Đọc file task_power
    with open(f"task_power/{file_name}.txt") as f:
        for line in f:
            W.append(int(line.strip()))

    # Đọc file data
    with open(f"data/{file_name}.IN2") as f:
        lines = f.readlines()

    n = int(lines[0])
    for idx, line in enumerate(lines[1:], start=1):
        line = line.strip()
        if idx > n:
            pair = tuple(map(int, line.split(',')))
            if pair == (-1, -1):
                break
            precedence_relations.add(pair)
        else:
            Ex_Time.append(int(line))

    return n, W, precedence_relations, Ex_Time

def parse_3pm_file(input_file):
    with open(input_file, 'r') as file:
        lines = file.readlines()

    # Skip comments and parse the first meaningful line
    line_index = 0
    while lines[line_index].startswith('c'):
        line_index += 1

    n, m, c = map(int, lines[line_index].strip().split())
    T, W = [0], [0]
    precedence_relations = []

    # Parse task information
    for i in range(1, n + 1):
        t, w = map(int, lines[line_index + i].strip().split())
        T.append(t)
        W.append(w)

    # Parse precedence relations
    for line in lines[line_index + n + 1:]:
        i, j = map(int, line.strip().split(','))
        if i == -1 and j == -1:
            break
        precedence_relations.append((i, j))

    return n, m, c, T, W, precedence_relations


vpool = IDPool(start_from=1)
X = lambda j, k: vpool.id('X{0}@{1}'.format(j, k))
S = lambda j, t: vpool.id('S{0}@{1}'.format(j, t))
A = lambda j, t: vpool.id('A{0}@{1}'.format(j, t))
E = lambda j: vpool.id('E{0}'.format(j))

def get_single_machine_time(ealiest_st_time, T):
    C_max = 0
    st_T_pair = sorted(list(zip(ealiest_st_time, T)))
    for r, t in st_T_pair:
        C_max = max(C_max, r) + t
    return C_max


def get_precedence_constraints(n, m, c, T, W, precedence_relations):
    pre_list = [[] for _ in range(n + 1)]
    pre_task_list = [{i} for i in range(n + 1)]
    pre_time_list = [0] * (n + 1)
    suc_list = [[] for _ in range(n + 1)]
    suc_task_list = [{i} for i in range(n + 1)]
    suc_time_list = [0] * (n + 1)
    in_degree = [0] * (n + 1)
    que = [0] * (n + 1)
    ql = 0
    qr = 0
    topo_list = []
    tau_list = [0]*(n+1)
    tau_r_list = [0]*(n+1)

    for i, j in precedence_relations:
        pre_list[j].append(i)
        suc_list[i].append(j)
        in_degree[j] += 1
    for i in range(1, n + 1):
        if in_degree[i] == 0:
            que[qr] = i
            qr += 1
    while ql != qr:
        me = que[ql]
        ql += 1
        topo_list.append(me)
        for tt in suc_list[me]:
            in_degree[tt] -= 1
            if in_degree[tt] == 0:
                que[qr] = tt
                qr += 1


    for me in topo_list:
        for suc in suc_list[me]:
            pre_task_list[suc] = pre_task_list[suc].union(pre_task_list[me])
        pre_time_list[me] = sum([T[pre] for pre in pre_task_list[me]])
        tau_i = (ceil(pre_time_list[me]/c)-1) * c
        single_machine_value = get_single_machine_time([tau_list[j] for j in pre_task_list[me] if j!=me],
                                                       [T[j] for j in pre_task_list[me] if j!=me])
        tau_i = max(tau_i, single_machine_value)
        if tau_i > floor(tau_i/c)*c and len(pre_list[me])!=0:
            tau_i = max(tau_i, floor(tau_i/c)*c + min([T[j] for j in pre_list[me]]))
        if ceil((tau_i + T[me])/c) > floor(tau_i/c) + 1:
            tau_i = (floor(tau_i/c) + 1) * c
        tau_list[me] = tau_i


    for me in topo_list[::-1]:
        for pre in pre_list[me]:
            suc_task_list[pre] = suc_task_list[pre].union(suc_task_list[me])
        suc_time_list[me] = sum([T[suc] for suc in suc_task_list[me]])
        tau_i_r = (ceil(suc_time_list[me]/c)-1) * c
        single_machine_value = get_single_machine_time([tau_r_list[j] for j in suc_task_list[me]  if j!=me],
                                                       [T[j] for j in suc_task_list[me] if j!=me])
        tau_i_r = max(tau_i_r, single_machine_value)
        if tau_i_r > floor(tau_i_r/c)*c and len(suc_list[me])!=0:
            tau_i_r = max(tau_i_r, floor(tau_i_r/c)*c + min([T[j] for j in suc_list[me]]))
        if ceil((tau_i_r + T[me])/c) > floor(tau_i_r/c) + 1:
            tau_i_r = (floor(tau_i_r/c) + 1) * c
        tau_r_list[me] = tau_i_r




    cnf_precedence = CNF()
    for i in range(1, n + 1):
        impossible_station_l = tau_list[i] // c
        for j in range(1, impossible_station_l + 1):
            cnf_precedence.append([-X(i, j)])
            neg_X[X(i, j)] = 1
        assert impossible_station_l < m
        l_slot = tau_list[i] - c * (impossible_station_l)
        for t in range(l_slot):
            cnf_precedence.append([-X(i, impossible_station_l + 1), -S(i, t)])
            neg_XS_pair[(X(i, impossible_station_l + 1), S(i, t))] = 1

        tau_r_list[i] += T[i]-1
        impossible_station_r = tau_r_list[i] // c
        for j in range(1, impossible_station_r + 1):
            cnf_precedence.append([-X(i, m - j + 1)])
            neg_X[X(i, m-j+1)] = 1
        assert impossible_station_r < m
        r_slot = tau_r_list[i] - c * (impossible_station_r)
        for t in range(1, r_slot + 1):
            cnf_precedence.append([-X(i, m - impossible_station_r), -S(i, c - t)])
            neg_XS_pair[(X(i, m - impossible_station_r), S(i, c - t))]=1

    return cnf_precedence


def get_longTask_constraints(n, m, c, T, W, precedence_relations):
    LongTask_cnf = CNF()
    for i in range(1, n + 1):
        # print(i, "---------------------------------")
        l = c - T[i]
        r = T[i] - 1
        if l > r:
            continue

        for t in range(l, r + 1):
            # print(f"A({i},{t})")
            pos_A[A(i, t)] = 1
            LongTask_cnf.append([A(i, t)])

    return LongTask_cnf

def get_wcnf_insatance(n, m, c, T, W, precedence_relations, vpool, ub, lb):
    wcnf = WCNF()

    nb_E = ceil(log2(ub + 1))

    for i in range(0, nb_E + 1):
        wcnf.append([-E(i)], weight=2 ** i)

    '''Tasks assigned to the same workstation have the sum of their processing times bounded by c'''
    for k in range(1, m + 1):
        lits = []
        weight = []
        for j in range(1, n + 1):
            if X(j, k) in neg_X:
                continue
            lits.append(X(j, k))
            weight.append(T[j])
        wcnf.extend(
            PBEnc.leq(
                lits=lits,
                weights=weight, bound=c, vpool=vpool, encoding=EncType.binmerge
            )
        )
    '''Tasks assigned  to the same workstation have the sum of their processing times bounded by c'''

    for j in range(1, n + 1):
        # wcnf.append([X(j, k) for k in range(1, m + 1)])  # (1)
        wcnf.extend(
            card.CardEnc.equals(lits=[X(j, k) 
                                for k in range(1, m + 1) 
                                if X(j, k) not in neg_X], bound=1, encoding=card.EncType.cardnetwrk,
                                vpool=vpool))  # (1)(2)
        wcnf.extend(
            card.CardEnc.equals(lits=[S(j, t) for t in range(0, c - T[j] + 1)], bound=1,
                                        encoding=card.EncType.cardnetwrk, vpool=vpool))  # (4)(5)
        for k in range(1, m + 1):
            # wcnf.extend([[-X(j, kk), -X(j, k)] for kk in range(1, k)])  # (2)
            for i in range(1, j):
                wcnf.extend([[-X(i, k), -X(j, k), -A(i, t), -A(j, t)] 
                                for t in range(0, c) 
                                if X(i, k) not in neg_X 
                                if X(j, k) not in neg_X])  # (7)

        # wcnf.append([S(j, t) for t in range(0, c - T[j] + 1)])  # (4)
        for t in range(0, c - T[j] + 1):
            # wcnf.extend([[-S(j, t), -S(j, t1)] for t1 in range(0, t)])  # (5)
            wcnf.extend([[-S(j, t), A(j, t + eps)] 
                            for eps in range(0, T[j]) 
                            if A(j, t+eps) not in pos_A])  # (8)

        wcnf.extend([[-S(j, t)] for t in range(c - T[j] + 1, c)])  # (6)

    """ new precedence relations """
    # for i, j in precedence_relations:
    #     for h in range(1, m + 1):
    #         # wcnf.extend([[-X(j, k), -X(i, h)] for k in range(1, h)])  # (3)
    #         wcnf.extend([[-X(i, h), -X(j, h), -S(i, t1), -S(j, t2)] for t2 in range(0, c - T[j] + 1) for t1 in
    #                      range(t2 + 1, c - T[i] + 1)])  # (9)

    for i, j in precedence_relations:
        for k in range(1, m + 1):
            bound = k
            lits = [X(j, k)] if X(j, k) not in neg_X else []
            for h in range(1, k + 1):
                if X(i, h) in neg_X:
                    bound -= 1
                    continue
                lits.append(-X(i, h))
            wcnf.extend(
                card.CardEnc.atmost(
                    lits=lits,
                    bound=bound,
                    encoding=card.EncType.cardnetwrk, vpool=vpool
                )
            )
            for t in range(0, c - T[j] + 1):
                    S_lits = [-S(i, tau) for tau in range(0, t-T[i]+1)]
                    wcnf.extend(
                        card.CardEnc.atmost(
                            lits = [S(j,t), X(i, k), X(j,k)] + S_lits,
                            bound = 2 + len(S_lits),
                            encoding=card.EncType.cardnetwrk, vpool=vpool
                        )
                    )


    """ new precedence relations """

    lits = [E(x) for x in range(nb_E + 1)]
    weights = [2 ** x for x in range(nb_E + 1)]
    wcnf.extend(PBEnc.geq(lits=lits, weights=weights, bound=lb, vpool=vpool, encoding=EncType.binmerge))

    l_ub = sum([2 ** i for i in range(nb_E + 1)])
    for t in range(c):
        lits = [A(j, t) for j in range(1, 1 + n)] + [-E(x) for x in range(nb_E + 1)]
        weights = [W[j] for j in range(1, 1 + n)] + [2 ** x for x in range(nb_E + 1)]
        wcnf.extend(PBEnc.leq(lits=lits, weights=weights, bound=l_ub, vpool=vpool, encoding=EncType.binmerge))

    return wcnf


def merge_wcnf(wcnf1, wcnf2):
    for clause in wcnf2.hard:
        wcnf1.append(clause)

    for clause, weight in zip(wcnf2.soft, wcnf2.wght):
        wcnf1.append(clause, weight=weight)

    wcnf1.topw = max(wcnf1.topw, wcnf2.topw)
    return wcnf1


if __name__ == '__main__':


    parser = argparse.ArgumentParser(description="python3 this.py <path/to/3pm> <path/to/wcnf_old> <m> <c>")
    parser.add_argument("input_path", help="path/to/3pm")
    parser.add_argument("output_path", help="path/to/wcnf_old")
    parser.add_argument("m", type=int, help="number of machines")
    parser.add_argument("c", type=int, help="number of cycles")
    args = parser.parse_args()
    input_file = args.input_path
    output_path = args.output_path
    m = int(args.m)
    c = int(args.c)

    start_time = time.time()
    n, W, precedence_relations, T = input_files(input_file)
    for j in range(1, n + 1):
        for k in range(1, m + 1):
            var_id = X(j, k)
    
    for j in range(1, n + 1):
        for t in range(0, c):
            var_id = S(j, t)

    for j in range(1, n + 1):
        for t in range(0, c):
            var_id = A(j, t)

    lb = min(W[1:])
    ub = sum(sorted(W[1:], reverse=True)[:min(m, len(W) - 1)])
    print("lb:{0} ub:{1}".format(lb, ub))
    wcnf = WCNF()
    wcnf.extend(get_precedence_constraints(n, m, c, T, W, precedence_relations))
    wcnf.extend(get_longTask_constraints(n, m, c, T, W, precedence_relations))
    wcnf = merge_wcnf(wcnf,get_wcnf_insatance(n, m, c, T, W, precedence_relations, vpool, ub, lb))
    solve_start_time = time.time()
    print(f"$$$ TimeEncoding: {solve_start_time - start_time}")
    print(f"RESULT_VAR_HARD_SOFT {wcnf.nv} {len(wcnf.hard)} {len(wcnf.soft)}")
    wcnf.to_file(output_path)
