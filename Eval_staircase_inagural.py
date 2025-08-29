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

# input variables in database ?? mertens 1
n = 7 #58
m = 6 #25
c = 6 #65
val = 0
cons = 0    
sol = 0
solbb = 0
type = 1
#           0              1                2           3           4           5           6           7               8                   9
file = ["MITCHELL.IN2","MERTENS.IN2","BOWMAN.IN2","ROSZIEG.IN2","BUXEY.IN2","HESKIA.IN2","SAWYER.IN2","JAESCHKE.IN2","MANSOOR.IN2",
        "JACKSON.IN2","GUNTHER.IN2", "WARNECKE.IN2"]
#            9          10              11          12          13          14          15          16          17   
filename = file[1]

fileName = filename.split(".")

with open('task_power/'+fileName[0]+'.txt', 'r') as file:
    W = [int(line.strip()) for line in file]

neighbors = [[ 0 for i in range(n)] for j in range(n)]

visited = [False for i in range(n)]
toposort = []
clauses = []
time_list = []
adj = []
forward = [0 for i in range(n)]
# W = [41, 13, 21, 24, 11, 11, 41, 32, 31, 25, 29, 25, 31, 3, 14, 37, 34, 6, 18, 35, 18, 19, 25, 40, 20, 20, 36, 23, 29, 48, 41, 20, 31, 25, 1]


def input_file(filename):
    cnt = 0
    for line in fileinput.input('data/'+filename +'.IN2'):
        line = line.strip()
        if line:
            if cnt == 0:
                n = int(line)
                neighbors = [[ 0 for i in range(n)] for j in range(n)]
                visited = [False for i in range(n)]
            elif cnt <= n: # type: ignore
                time_list.append(int(line))
            else:
                line = line.split(",")
                if(line[0] != "-1" and line[1] != "-1"):
                    adj.append([int(line[0])-1, int(line[1])-1])
                    neighbors[int(line[0])-1][int(line[1])-1] = 1
                else:
                    break
            cnt = cnt + 1
    fileinput.close()
    return n, neighbors, visited


def generate_variables(n,m,c):
    x = [[j*m+i+1 for i in range (m)] for j in range(n)]
    
    a = [[m*n + j*c + i + 1 for i in range (c)] for j in range(n)]
    
    s = []
    cnt = m*n + c*n + 1
    for j in range(n):
        tmp = []
        for i in range(c - time_list[j] + 1):
            tmp.append(cnt)
            cnt = cnt + 1
        s.append(tmp)
    return x, a, s

def dfs(v):
    visited[v] = True
    for i in range(n):
        if(neighbors[v][i] == 1 and visited[i] == False):
            dfs(i)
    toposort.append(v)

def preprocess(n,m,c,time_list,adj):
    earliest_start = [[-9999999 for _ in range(m)] for _ in range(n)]
    latest_start = [[99999999 for _ in range(m)] for _ in range(n)]
    ip1 = [[0 for _ in range(m)] for _ in range(n)]
    test_ip1 = [[0 for _ in range(m)] for _ in range(n)]
    ip2 = [[[0 for _ in range(c)] for _ in range(m)] for _ in range(n)]
    # Compute earliest possible starting date and assigned workstation
    for i in range(n):
        if not visited[i]:
            dfs(i)
    toposort.reverse()
    # print(toposort)
    for j in toposort:
        k = 0
        earliest_start[j][k] = 0
        for i in range(n):
            if neighbors[i][j] == 1:

                earliest_start[j][k] = max(earliest_start[j][k], earliest_start[i][k] + time_list[i])

                while(earliest_start[j][k] > c - time_list[j]):
                    ip1[j][k] = 1
                    # print('X '+str(j+1)+' '+str(k+1))
                    k = k + 1
                    earliest_start[j][k] = max(0, earliest_start[i][k] + time_list[i])

                if earliest_start[j][k] <= c - time_list[j] :
                    for t in range(earliest_start[j][k]):
                        
                        if(ip2[j][k][t] == 0):
                            # with open("output.txt", "a") as output_file: 
                            #     sys.stdout = output_file  
                            #     print(j+1, k+1, t, file=output_file) 
                            ip2[j][k][t] = 1
    toposort.reverse()
    for j in toposort:
        k = m-1
        latest_start[j][k] = c - time_list[j]
        for i in range(n):
            if(neighbors[j][i] == 1): 
                latest_start[j][k] = min(latest_start[j][k], latest_start[i][k] - time_list[j])
                while(latest_start[j][k] < 0):
                    ip1[j][k] = 1
                    # print('X '+str(j+1)+' '+str(k+1))
                    k = k - 1
                    latest_start[j][k] = min(c - time_list[j], latest_start[i][k] - time_list[j])
                
                if(latest_start[j][k] >= 0):
                        for t in range(latest_start[j][k] + 1, c):
                            
                            if(ip2[j][k][t] == 0):
                                # with open("output.txt", "a") as output_file: 
                                #     sys.stdout = output_file
                                #     print(j+1, k+1, t, file=output_file) 
                                ip2[j][k][t] = 1
    
    # print(ip2)
    return ip1,ip2

def get_key(value):
    for key, value in var_map.items():
        if val == value:
            return key
    return None
def get_var(name, *args):
    global var_counter
    key = (name,) + args

    if key not in var_map:
        var_counter += 1
        var_map[key] = var_counter
    return var_map[key]

def set_var(var, name, *args):
    key = (name,) + args
    if key not in var_map:
        var_map[key] = var
    return var_map[key]

def generate_clauses(n,m,c,time_list,adj,ip1,ip2):
    clauses = []

    #staircase constraints
    for j in range(n):
        
        set_var(X[j][0], "R", j, 0)
        for k in range(1,m-1):
            if ip1[j][k] == 1:
                set_var(get_var("R", j, k-1), "R", j, k)
            else:
                clauses.append([-get_var("R", j, k-1), get_var("R", j, k)])
                clauses.append([-X[j][k], get_var("R", j, k)])
                clauses.append([-X[j][k], -get_var("R", j, k-1)])
                clauses.append([X[j][k], get_var("R", j, k-1), -get_var("R", j, k)])
        # last machine
        if ip1[j][m-1] == 1:
            clauses.append([get_var("R", j, m-2)])
        else:
            clauses.append([get_var("R", j, m-2), X[j][m-1]])
            clauses.append([-get_var("R", j, m-2), -X[j][m-1]])
        

    for (i,j) in adj:
        for k in range(m-1):
            if ip1[i][k+1] == 1:
                continue
            clauses.append([-get_var("R", j, k), -X[i][k+1]])

    print("first 3 constraints (staircase):", len(clauses))

    # T[j][t] represents "task j starts at time t or earlier"
    for j in range(n):
        last_t = c-time_list[j]
        
        # Special case: Full cycle tasks (only one feasible start time: t=0)
        if last_t == 0:
            # Force the task to start at t=0 (equivalent to original constraint #4)
            clauses.append([S[j][0]])
        else:
            # First time slot
            set_var(S[j][0], "T", j, 0)
            
            # Intermediate time slots
            for t in range(1, last_t):
                clauses.append([-get_var("T", j, t-1), get_var("T", j, t)]) # T[j][t-1] -> T[j][t]
                clauses.append([-S[j][t], get_var("T", j, t)]) # S[j][t] -> T[j][t]
                clauses.append([-S[j][t], -get_var("T", j, t-1)]) # S[j][t] -> ¬T[j][t-1]
                clauses.append([S[j][t], get_var("T", j, t-1), -get_var("T", j, t)]) # T[j][t] -> (T[j][t-1] ∨ S[j][t])
            
            # Last time slot (ensures at least one start time)
            clauses.append([get_var("T", j, last_t-1), S[j][last_t]])
            clauses.append([-get_var("T", j, last_t-1), -S[j][last_t]])
    
    print("4 5 6 constraints (staircase):", len(clauses))

    #7
    for i in range(n-1):
        for j in range(i+1,n):
            for k in range (m):
                if ip1[i][k] == 1 or ip1[j][k] == 1 :
                    continue
                for t in range(c):
                    # if ip2[i][k][t] == 1 or ip2[j][k][t] == 1:
                    #     continue
                    clauses.append([-X[i][k], -X[j][k], -A[i][t], -A[j][t]])
    print("7 constraints:", len(clauses))
    #8
    for j in range(n):
        for t in range (c-time_list[j]+1):
            for l in range (time_list[j]):
                if(time_list[j] >= c/2 and t+l >= c-time_list[j] and t+l < time_list[j]):
                    continue
                clauses.append([-S[j][t],A[j][t+l]])
    
    print("8 constraints:", len(clauses))

    for i,j in adj:
        for k in range(m):
            if ip1[i][k] == 1 or ip1[j][k] == 1:
                continue
            left_bound = time_list[i] - 1
            right_bound = c - time_list[j]
            clauses.append([-X[i][k], -X[j][k], -get_var("T", j, left_bound)])
            for t in range (left_bound + 1, right_bound):
                t_i = t - time_list[i]+1
                clauses.append([-X[i][k], -X[j][k], -get_var("T", j, t), -S[i][t_i]])
            for t in range (max(0,right_bound - time_list[i] + 1), c - time_list[i] + 1):
                clauses.append([-X[i][k], -X[j][k], -S[i][t], -get_var("T",j,c-time_list[j]-1)])

    cons = len(clauses)
    print("Constraints:",cons)

    #10
    for j in range(n):
        for k in range(m):
            if ip1[j][k] == 1:
                clauses.append([-X[j][k]])
                continue
                # print("constraint ", j+1, k+1)
            #11
            for t in range(c - time_list[j] +1):
                if ip2[j][k][t] == 1:
                    clauses.append([-X[j][k], -S[j][t]])
                    # print("constraint ", j+1, k+1, t)
    
    #12 
    for j in range(n):
        if(time_list[j] >= c/2):
            for t in range(c-time_list[j],time_list[j]):
                clauses.append([A[j][t]])
    print("12 constraints:", len(clauses))
    return clauses

def solve(solver, start_time, timeout=3600):
    current_time = time.time()
    remaining_time = timeout - (current_time - start_time)
    
    if remaining_time <= 0:
        print("Timeout reached before calling solver")
        return None
    
    # Use threading to implement timeout for solver.solve()
    result = [None]  # Use list to allow modification in nested function
    exception = [None]
    
    def solve_worker():
        try:
            if solver.solve():
                result[0] = solver.get_model()
            else:
                result[0] = False  # No solution found
        except Exception as e:
            exception[0] = e
    
    # Start solver in separate thread
    solver_thread = threading.Thread(target=solve_worker)
    solver_thread.daemon = True
    solver_thread.start()
    
    # Wait for thread to complete or timeout
    solver_thread.join(timeout=remaining_time)
    
    if solver_thread.is_alive():
        print(f"Solver timeout reached after {remaining_time:.2f} seconds")
        # Note: We can't actually kill the solver thread, but we return None
        # The thread will continue running in background until solver completes
        return None
    
    if exception[0]:
        raise exception[0]
    
    if result[0] is False:
        # print("no solution")
        return None
    
    return result[0]

def get_value(solution,best_value):
    if solution is None:
        return 100, []
    else:
        x = [[  solution[j*m+i] for i in range (m)] for j in range(n)]
        a = [[  solution[m*n + j*c + i ] for i in range (c)] for j in range(n)]
        s = []
        cnt = m*n + c*n
        for j in range(n):
            tmp = []
            for i in range(c - time_list[j] + 1):
                tmp.append(solution[cnt])
                cnt += 1
            s.append(tmp)
        t = 0
        value = 0

        for t in range(c):
            tmp = 0
            for j in range(n):
                if a[j][t] > 0 :
                    # tmp = tmp + W[j]
                    for l in range(max(0,t-time_list[j]),t+1):
                        if l < len(s[j]) and s[j][l] > 0 :
                            tmp = tmp + W[j]
                            # print(tmp)
                            break
                
            if tmp > value:
                value = tmp
                # print(value)

        constraints = []
        for t in range(c):
            tmp = 0
            station = []
            for j in range(n):
                if a[j][t] > 0:
                    # tmp = tmp + W[j]
                    # station.append(j+1)
                    for l in range(max(0,t-time_list[j]),t+1):
                        if l < len(s[j]) and s[j][l] > 0:
                            tmp = tmp + W[j]
                            station.append(j+1)
                            break
            if tmp >= min(best_value, value):
                constraints.append(station)
                # print("value:",value)
        unique_constraints = list(map(list, set(map(tuple, constraints))))

        return value, unique_constraints

def generate_binary(n,m,c, X, S, A, W, UB, LB, clauses, var_counter):
    soft_clauses = []
    n_bit = int(math.log2(UB)) + 1
    binU =[]
    
    for i in range(n_bit):
        binU.append(var_counter + 1)
        var_counter+=1
        soft_clauses.append([[-var_counter], 2**i])
    var = var_counter + 1
    variables = []
    weight = []
    for i in range(n_bit):
        variables.append(binU[i])
        weight.append(2**i)
    
    pb_clauses_lb = PBEnc.geq(lits=variables, weights=weight, bound=LB, top_id=var)

    if pb_clauses_lb.nv > var:
            var = pb_clauses_lb.nv + 1
    
    for clause in pb_clauses_lb.clauses:
        clauses.append(clause)

    for t in range(c):
        variables = []
        weight = []
        for i in range(n):
            variables.append(A[i][t])
            weight.append(W[i])
        
        for i in range(n_bit):
            variables.append(-binU[i])
            weight.append(2**i)

        upper_bound = sum(2**j for j in range(n_bit))
        # Create PB constraint: sum(power_terms) - sum(binary_terms) <= 0
        # This is equivalent to: sum(power_terms) <= sum(binary_terms)
        pb_clauses = PBEnc.leq(lits=variables, weights=weight, bound=upper_bound,
                                 top_id=var)
            
        # Update variable counter
        if pb_clauses.nv > var:
            var = pb_clauses.nv + 1
            
        # Add the encoded clauses to WCNF
        for clause in pb_clauses.clauses:
            clauses.append(clause)

    return clauses, soft_clauses, var

def generate_inagural(n,m,c, X, S, A, W, UB, LB, clauses, var_counter):
    soft_clauses = []
    U = []
    for i in range(LB + 1, UB):
        U.append(var_counter + 1)
        var_counter += 1
        soft_clauses.append([[-var_counter], 1])
    
    for i in range(1, len(U)):
        clauses.append([-U[i], U[i-1]])
    
    var = var_counter + 1
    for t in range(c):
        variables = []
        weight = []
        for i in range(len(U)):
            variables.append(-U[i])
            weight.append(1)
        for i in range(n):
            variables.append(A[i][t])
            weight.append(W[i])
        pb_clauses = PBEnc.leq( lits=variables, weights=weight, 
                                bound=UB, 
                                top_id=var)
        # Update variable counter for any new variables created by PBEnc
        if pb_clauses.nv > var:
            var = pb_clauses.nv + 1
            
        # Add the encoded clauses to WCNF
        for clause in pb_clauses.clauses:
            clauses.append(clause)

    return clauses, soft_clauses, var

def write_wcnf_with_h_prefix(clauses, soft_clauses, var, filename = "problem.wcnf"):
    with open(filename, 'w') as f:
        # Calculate statistics
        total_clauses = len(clauses) + len(soft_clauses)
        top_weight = max(soft_clauses[i][1] for i in range(len(soft_clauses))) + 1
            
        f.write(f"p wcnf {var} {total_clauses} {top_weight}\n")    
        # Write hard constraints with 'h' prefix
        for clause in clauses:
            f.write(str(top_weight) + " ")
            f.write(" ".join(map(str, clause)))
            f.write(" 0\n")
            
        # Write soft constraints with their weights
        for item in soft_clauses:
            clause = item[0][0]
            weight = item[1]        
            f.write(f"{weight} ")
            f.write(" " + str(clause))
            f.write(" 0\n")
def solve_maxsat():
    try:
        result = subprocess.run(["wsl","./EvalMaxSAT_bin", "problem.wcnf"],
                                stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE,
                                text=True, timeout=3600)

        # print(f"Solver output:\n{result.stdout}")
        # Parse solver output
        lines = result.stdout.strip().split('\n')
        for line in lines:
            if line.startswith('v '):
                # Extract variable assignments - could be binary string or space-separated
                var_string = line[2:].strip()
                    
                # Check if it's a binary string (all 0s and 1s)
                if var_string and all(c in '01' for c in var_string):
                    # Convert binary string to variable assignments
                    assignment = []
                    for i, bit in enumerate(var_string):
                        if bit == '1':
                            assignment.append(i + 1)  # Variables are 1-indexed, true
                        else:
                            assignment.append(-(i + 1))
                    return assignment
                else:
                    # Handle space-separated format
                    try:
                        assignment = [int(x) for x in var_string.split() if x != '0']
                        return assignment
                    except ValueError:
                        # Fallback: treat as binary string anyway
                        assignment = []
                        for i, bit in enumerate(var_string):
                            if bit == '1':
                                assignment.append(i + 1)
                        return assignment
        return None
    except subprocess.TimeoutExpired: 
        return None

def get_value2(n, m, c, model, W, UB = 0):
    ans_map = [[0 for _ in range(c)] for _ in range(m + 1)]
    start_B = n*m
    start_A = start_B + n*c
    start_U = start_A + n*c
    
    for i in range(m):
        for j in range(c):
            for k in range(n):
                if ((model[k*m  + i] > 0) and model[start_B + k*c + j] > 0):
                    ans_map[i][j] = W[k]
    
    for i in range(c):
        ans_map[m][i] = sum(ans_map[j][i] for j in range(m))
    peak = max(ans_map[m][i] for i in range(c))
    return ans_map, peak

def optimal(X,S,A,n,m,c,start_time):
    global var_counter, var_map
    ip1,ip2 = preprocess(n,m,c,time_list,adj)
    
    clauses = generate_clauses(n,m,c,time_list,adj,ip1,ip2)
    solver = Glucose3()
    for clause in clauses:
        solver.add_clause(clause)

    model = solve(solver,start_time = start_time)
    if model is None:
        print("No solution found.")
        return 0, var_counter, clauses, [], "UNSAT" 
    infinity = 1000000
    result = get_value(model, infinity)
    start = var_counter
    bestValue, station = result
    print("initial value:",bestValue)
    print("initial station:",station)
    clauses, soft_clauses, var = generate_inagural(n,m,c, X, S, A, W, bestValue, max(W), clauses, start)
    write_wcnf_with_h_prefix(clauses, soft_clauses, var, filename = "problem.wcnf")
    model = solve_maxsat()
    if model is None:
        print("Time out")
        return 0, var, clauses, soft_clauses, "Time out"
    
    ansmap, bestValue = get_value2(n, m, c, model, W)
    print("Best value =", bestValue)
    return bestValue, var, clauses, soft_clauses, "Optimal"

def write_fancy_table_to_csv(ins, n, m, c, val, s_cons, h_cons, peak, status, time, filename="Output.csv"):
    with open("Output/" + filename, "a", newline='') as f:
        writer = csv.writer(f)
        row = []
        row.append(ins)
        row.append(str(n))
        row.append(str(m))
        row.append(str(c))
        row.append(str(val))
        row.append(str(s_cons))
        row.append(str(h_cons))
        row.append(str(peak))
        row.append(status)
        row.append(str(time))
        writer.writerow(row)

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
    with open('task_power/'+i[0]+'.txt', 'r') as file:
        W = [int(line.strip()) for line in file]
    toposort = []
    clauses = []
    time_list = []
    adj = []
    n, neighbors, visited = input_file(i[0])
    m = i[1]
    c = i[2]
    var_counter = 0
    print("n = ",n)
    X, A, S = generate_variables(n,m,c)
    val = max(S)

    # print(val)
    var_counter = max(val)
    var_map = {}

    start_time = time.time()
    solval, vari, clauses, soft_clauses, status = optimal(X,S,A,n,m,c,start_time) #type: ignore
    end_time = time.time()
    write_fancy_table_to_csv(i[0], n, m, c, vari, len(soft_clauses), len(clauses), solval, status, end_time - start_time)
    

