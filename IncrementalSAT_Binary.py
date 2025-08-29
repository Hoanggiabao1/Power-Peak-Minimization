from math import inf
import re
import time
import threading
import signal
from tracemalloc import start
from turtle import st
from numpy import var
from pysat.solvers import Glucose3
import fileinput
from tabulate import tabulate
import webbrowser
import sys
from pysat.pb import PBEnc
import math
import time
import fileinput
import csv
import sys
import subprocess

def generate_variables(n, m, c):
    # X[i][s]: task i for station s
    X = [[i*m + s + 1 for s in range(m)] for i in range(n)]
    
    # B[i][t]: task i start at time unit t
    B = [[i*c + t + 1 + X[-1][-1] for t in range(c)] for i in range(n)]
    
    # A[i][t]: task i being executed at time unit t
    A = [[i*c + t + 1 + B[-1][-1] for t in range(c)] for i in range(n)]

    return X, B, A

def input_file(file_name):
    W = []
    precedence_relations = set()
    Ex_Time = []

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

def generate_clauses(n, m, c, W, Ex_Time, precedence_relations, UB, LB):
    X, B, A = generate_variables(n, m, c)
    n_bits = int(math.log2(UB)) + 1
    binU = [A[-1][-1] + 1 + i for i in range(n_bits)]

    clauses = []
    # Each task is assigned to exactly one station
    for i in range(n):
        clause = [X[i][s] for s in range(m)]
        clauses.append(clause)
        for s1 in range(m):
            for s2 in range(s1 + 1, m):
                clauses.append([-X[i][s1], -X[i][s2]])
    
    # Precedence relations between stations
    for (i,j) in precedence_relations:
        for s1 in range(m):
            for s2 in range(s1):  # s2 < s1
                clauses.append([-X[i - 1][s1], -X[j - 1][s2]])

    # Precedence relations within same station
    for (i, j) in precedence_relations:
        for s in range(m):
            for t1 in range(c):
                for t2 in range(t1): # t2 < t1   
                    clauses.append([-X[i - 1][s], -X[j - 1][s], -B[i - 1][t1], -B[j - 1][t2]])
    
    # Each task starts exactly once
    for i in range(n):
        clause = [B[i][t] for t in range(c)]
        clauses.append(clause)
        for t1 in range(c):
            for t2 in range(t1 + 1, c):
                clauses.append([-B[i][t1], -B[i][t2]])

    # Tasks must start within feasible time windows
    feasible_start_times = []
    for i in range(n):
        feasible_start_times.append(list(range(c - Ex_Time[i] + 1)))
    for i in range(n):
        for t in range(c):
            if t not in feasible_start_times[i]:
                clauses.append([-B[i][t]])
    
    # Task activation (B_{i,t} -> A_{i,t+ε} for ε ∈ {0, ..., t_i-1})
    for i in range(n):
        for t in feasible_start_times[i]:
            for epsilon in range(Ex_Time[i]):
                clauses.append([-B[i][t], A[i][t + epsilon]])
           
    # Task execution (A_{i,t} -> X_{i,s} for s ∈ {1, ..., m})
    # Prevent simultaneous execution on same station
    for i in range(n):
        for j in range(i + 1, n):
            for s in range(m):
                for t in range(c):
                    clauses.append([-X[i][s], -X[j][s], -A[i][t], -A[j][t]])

    start = binU[-1] + 1
   
    lists = []
    weights = []
    for i in range(len(binU)):
        lists.append(binU[i])
        weights.append(2**i)
    
    pb_clauses_lb = PBEnc.geq(lits=lists, weights=weights,
                              bound=LB,
                              top_id=start)
    
    for clause in pb_clauses_lb:
        clauses.append(clause)

    if pb_clauses_lb.nv > start:
        start = pb_clauses_lb.nv + 1

    upper_bound = 2**n_bits - 1
    for t in range(c):
        lists = []
        weights =[]
        
        for i in range(n):
            lists.append(A[i][t])
            weights.append(W[i])
        
        for j in range(len(binU)):
            lists.append(-binU[j])
            weights.append(2**j)
        
        # Create PB constraint: sum(coeffs[i] * lits[i]) <= UB
        pb_clauses = PBEnc.leq( lits=lists, weights=weights, 
                                bound=upper_bound, 
                                top_id=start)
        # Update variable counter for any new variables created by PBEnc
        if pb_clauses.nv > start:
            start = pb_clauses.nv + 1
        
        for clause in pb_clauses:
            clauses.append(clause)

    return clauses, binU, start-1

def get_value(n, m, c, model, W, UB = 0):
    ans_map = [[0 for _ in range(c)] for _ in range(m + 1)]
    start_B = n*m
    start_A = start_B + n*c
    start_U = start_A + n*c
    for i in range(m):
        for j in range(c):
            for k in range(n):
                if ((model[k*m  + i] > 0) and model[start_A + k*c + j] > 0):
                    ans_map[i][j] = W[k]

    for i in range(c):
        ans_map[m][i] = sum(ans_map[j][i] for j in range(m))
    peak = max(ans_map[m][i] for i in range(c))
    return ans_map, peak

def caculate_UB_and_LB(n, m, c, W):
    W_sorted = sorted(W)
    W_sorted.reverse()
    LB = max(W)
    UB = sum(W_sorted[i] for i in range(m))
    print("UB:", UB, "LB:", LB)
    return UB, LB

def optimal(filename):
    n, W, precedence_relations, Ex_Time = input_file(filename[0])
    m = filename[1]
    c = filename[2]
    UB, LB = caculate_UB_and_LB(n, m, c, W)
    clauses, binU, var = generate_clauses(n, m, c, W, Ex_Time, precedence_relations, UB, LB)
    upper_bound = 2**len(binU) - 1
    solver = Glucose3()
    for clause in clauses:
        solver.add_clause(clause)

    start_time = time.time()
    best_ansmap = None
    best_peak = None
    sol = 0
    num_var = var
    num_clauses = len(clauses)
   
    while True:
        sol+=1
        if time.time() - start_time >= 3600:
            return None
        if solver.solve():
            model = solver.get_model()
            ansmap, peak = get_value(n, m, c, model, W)
            print("Current peak: ", peak, end="\r")
            best_ansmap = ansmap
            best_peak = peak
            solver = Glucose3()
            
            lists = []
            weights = []
            for i in range(len(binU)):
                lists.append(-binU[i])
                weights.append(2**i)
            
            pb_clauses_lb = PBEnc.geq(lits=lists, weights=weights,
                                        bound=upper_bound - peak + 1,
                                        top_id=num_var + 1)

            num_clauses = len(clauses)
            for clause in pb_clauses_lb:
                solver.add_clause(clause)
                num_clauses += 1
            
            for clause in clauses:
                solver.add_clause(clause)
            
        else:
            break

    if best_ansmap is not None:
        return best_ansmap, best_peak, sol, n, num_var, num_clauses
    else:
        return None

file_name = [
    ["MERTENS", 6, 6],      #0
    ["MERTENS", 2, 18],     #1
    ["BOWMAN", 5, 20],      #2
    ["JAESCHKE", 8, 6],     #3
    ["JAESCHKE", 3, 18],    #4
    ["JACKSON", 8, 7],      #5
    ["JACKSON", 3, 21],     #6
    ["MANSOOR", 4, 48],     #7
    ["MANSOOR", 2, 94],     #8
    ["MITCHELL", 8, 14],    #9
    ["MITCHELL", 3, 39],    #10
    ["ROSZIEG", 10, 14],    #11
    ["ROSZIEG", 4, 32],     #12
    ["BUXEY", 14, 25],      #13
    ["BUXEY", 7, 47],       #14
    ["SAWYER", 14, 25],     #15
    ["SAWYER", 7, 47],      #16
    ["GUNTHER", 14, 40],    #17
    ["GUNTHER", 9, 54],     #18
    ["BUXEY", 8, 41],       #19
    ["ROSZIEG", 6, 25],     #20
    ["BUXEY", 11, 33],      #21
    ["SAWYER", 12, 30],     #22
    ["SAWYER", 8, 41],      #23
    ["GUNTHER", 9, 61],     #24
    ["HESKIA", 8, 138],     #25
    ["HESKIA", 3, 342],     #26
    ["HESKIA", 5, 205],      #27
    ["WARNECKER", 25, 65]   #28
    ]

for i in file_name:
    start_time = time.time()
    res = optimal(i)
    end_time = time.time() - start_time
    peak = "-"
    ansmap = []
    sol = n = num_var = num_clauses = "-"
    if res != None:
        best_ansmap, peak, sol, n, num_var, num_clauses = res
        print("Best peak =", peak)
    
    inresult = [i[0], n, i[1], i[2], num_var, num_clauses, peak, sol, end_time, "Optimal"]
    with open("Output/Binary.csv", "a", newline='') as f:
            writer = csv.writer(f)
            writer.writerow(inresult)