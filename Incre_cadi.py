from math import inf
import math
import re
import time
import signal

from numpy import var
from pysat.solvers import Cadical195 
import fileinput
from tabulate import tabulate
import webbrowser
import sys
from pysat.pb import PBEnc
import csv
import subprocess
# input variables in database ?? mertens 1
n = 25
m = 6
c = 25
val = 0
cons = 0
sol = 0
solbb = 0
type = 1
#           0              1                2           3           4           5           6           7               8                   9
file = ["MITCHELL.IN2","MERTENS.IN2","BOWMAN.IN2","ROSZIEG.IN2","BUXEY.IN2","HESKIA.IN2","SAWYER.IN2","JAESCHKE.IN2","MANSOOR.IN2",
        "JACKSON.IN2","GUNTHER.IN2", "WARNECKE.IN2"]
#            9          10              11          12          13          14          15          16          17   
filename = file[3]

fileName = filename.split(".")

with open('task_power/'+fileName[0]+'.txt', 'r') as file:
    W = [int(line.strip()) for line in file]

neighbors = [[ 0 for i in range(n)] for j in range(n)]
reversed_neighbors = [[ 0 for i in range(n)] for j in range(n)]

visited = [False for i in range(n)]
toposort = []
clauses = []
time_list = []
adj = []
forward = [0 for i in range(n)]
var_map = {}
var_counter = 0
# W = [41, 13, 21, 24, 11, 11, 41, 32, 31, 25, 29, 25, 31, 3, 14, 37, 34, 6, 18, 35, 18, 19, 25, 40, 20, 20, 36, 23, 29, 48, 41, 20, 31, 25, 1]

def read_input():
    cnt = 0
    global n, adj, neighbors, reversed_neighbors, filename, time_list, forward
    with open('data/' + filename, 'r') as f:
        for line in f:
            line = line.strip()
            if line:
                if cnt == 0:
                    n = int(line)
                elif cnt <= n: # type: ignore
                    time_list.append(int(line))
                else:
                    line = line.split(",")
                    if(line[0] != "-1" and line[1] != "-1"):
                        adj.append([int(line[0])-1, int(line[1])-1])
                        neighbors[int(line[0])-1][int(line[1])-1] = 1
                        reversed_neighbors[int(line[1])-1][int(line[0])-1] = 1
                    else:
                        break
                cnt = cnt + 1


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
    
    # sys.stdout = sys.__stdout__


    # for j in range(n):
    #     for k in range(m):
    #         for t in range(c):
                # if(ip1[j][k] == 1):
                #     continue
                # if(j == 11 or j == 14):
                #     print(f"task {j+1} in machine {k+1} time {t+1}: {ip2[j][k][t]}")
                # if(j == 0 and k == 2):
                #     print(f"task {j+1} in machine {k+1} time {t+1}: {ip2[j][k][t]}")
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

def generate_clauses(n,m,c,time_list,adj,ip1,ip2,X,S,A):
    # #test
    # clauses.append([X[11 - 1][2 - 1]])
    global clauses
    global var_map
    global var_counter
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
    # # 1
    # for j in range (0, n):
    #     # if(forward[j] == 1):
    #     #     continue
    #     constraint = []
    #     for k in range (0, m):
    #         if ip1[j][k] == 1:
    #             continue
    #         constraint.append(X[j][k])
    #     clauses.append(constraint)
    # # 2 
    # for j in range(0,n):
    #     # if(forward[j] == 1):
    #     #     continue
    #     for k1 in range (0,m-1):
    #         for k2 in range(k1+1,m):
    #             if ip1[j][k1] == 1 or ip1[j][k2] == 1:
    #                 continue
    #             clauses.append([-X[j][k1], -X[j][k2]])

    # #3
    # for a,b in adj:
    #     for k in range (0, m-1):
    #         for h in range(k+1, m):
    #             if ip1[b][k] == 1 or ip1[a][h] == 1:
    #                 continue
    #             clauses.append([-X[b][k], -X[a][h]])


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
    
    # Original constraints #4 and #5 
    # #4
    # for j in range(n):
    #     clauses.append([S[j][t] for t in range (c-time_list[j]+1)])

    # #5
    # for j in range(n):
    #     for k in range(c-time_list[j]):
    #         for h in range(k+1, c-time_list[j]+1):
    #             clauses.append([-S[j][k], -S[j][h]])

    # #6
    # for j in range(n):
    #     for t in range(c-time_list[j]+1,c):
    #         if t > c- time_list[j]:
    #             clauses.append([-S[j][t]])
    
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

    # addtional constraints
    # a task cant run before its active time

    # for j in range(n):
    #     for t in range (c-time_list[j]+1):
    #         for l in range (t):
    #             if(time_list[j] >= c/2 and l >= c-time_list[j] and l < time_list[j]):
    #                 continue
    #             clauses.append([-S[j][t],-A[j][l]])


    # addtional constraints option 2


    # for j in range(n):
    #     for t in range (c-1): 
    #         if(time_list[j] >= c/2 and t+1 >= c-time_list[j] and t+1 < time_list[j]):
    #             continue
    #         clauses.append([ -A[j][t], A[j][t+1] , S[j][max(0,t-time_list[j]+1)]])
    
    # #9

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
    # for i, j in adj:
    #     for k in range(m):
    #         if ip1[i][k] == 1 or ip1[j][k] == 1:
    #             continue
    #         for t1 in range(c - time_list[i] +1):
    #             #t1>t2
    #             for t2 in range(c-time_list[j]+1):
    #                 if ip2[i][k][t1] == 1 or ip2[j][k][t2] == 1:
    #                     continue
    #                 if t1 > t2:
    #                     clauses.append([-X[i][k], -X[j][k], -S[i][t1], -S[j][t2]])
    cons = len(clauses)
    print("Constraints:",cons)

    # #10
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

def solve(solver):
    if solver.solve():
        model = solver.get_model()
        return model
    else:
        # print("no solution")
        return None

def print_solution(solution):
    if solution is None:
        # print("No solution found.")
        return None
    else:
        x = [[solution[j*m+i] for i in range(m)] for j in range(n)]
        a = [[solution[m*n + j*c + i] for i in range(c)] for j in range(n)]
        # s = [[solution[m*n + c*n + j*c + i] for i in range(c)] for j in range(n)]
        cnt = m*n + c*n 
        s = []
        for j in range(n):
            tmp = []
            for i in range(c - time_list[j] + 1):
                tmp.append(solution[cnt])
                cnt += 1
            s.append(tmp)
        table = [[0 for t in range(c)] for k in range(m)]
        for k in range(m):
            for t in range(c):
                for j in range(n):
                    if x[j][k] > 0 and a[j][t] > 0 and table[k][t] == 0:
                        for l in range(max(0,t-time_list[j]),t+1):
                            if l < len(s[j]) and s[j][l] > 0:
                                table[k][t] = j+1

        # Generate HTML content
        html_content = """
        <!DOCTYPE html>
        <html>
        <head>
            <title>Task Assignment to Machines</title>
            <style>
                table {
                    width: 100%;
                    border-collapse: collapse;
                }
                table, th, td {
                    border: 1px solid black;
                }
                th, td {
                    padding: 8px;
                    text-align: center;
                }
                th {
                    background-color: #f2f2f2;
                }
            </style>
        </head>
        <body>
            <h2>Task Assignment to Machines</h2>
            <table>
                <tr>
                    <th>Machine</th>
                    """ + "".join([f"<th>Time {t+1}</th>" for t in range(c)]) + """
                </tr>
        """

        for k in range(m):
            row = f"<tr><td>Machine {k+1}</td>" + "".join([f"<td>{table[k][t]}</td>" if table[k][t] > 0 else "<td></td>" for t in range(c)]) + "</tr>"
            html_content += row

        html_content += """
            </table>
        </body>
        </html>
        """

        # Write HTML content to a file
        file_path = "task_assignment.html"
        with open(file_path, "w") as file:
            file.write(html_content)

        # Open the HTML file in the default web browser
        # webbrowser.open(file_path)

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
        lowval = 0
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
            if tmp < lowval or lowval == 0:
                lowval = tmp
                # print("lowval:",lowval)
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

        return value, lowval, unique_constraints

def optimal(X,S,A,n,m,c,sol,solbb,start_time):
    ip1,ip2 = preprocess(n,m,c,time_list,adj)

    # print(ip2[])
    clauses = generate_clauses(n,m,c,time_list,adj,ip1,ip2,X,S,A)

    solver = Cadical195()
    for clause in clauses:
        solver.add_clause(clause)

    # Check timeout before initial solve
    current_time = time.time()
    remaining_time = 3600 - (current_time - start_time)
    if remaining_time <= 0:
        print("Instance timeout before initial solve")
        return 0, var_counter, clauses, [], "TIMEOUT"

    # Use timeout for initial solve
    # model = solve_with_timeout(solver, min(int(remaining_time), 3600))
    model = solve(solver)
    if model is None:
        print("Initial solve timed out or no solution")
        return 0, var_counter, clauses, [], "TIMEOUT"
        
    bestSolution = model 
    infinity = 1000000
    result = get_value(model, infinity)

    bestValue, lowval, station = result
    lowval = max(W)
    print("initial value:",bestValue)
    print("initial station:",station)
    start_var = var_counter
    clauses , soft_clauses, var, U, solver1 = generate_inagural(n,m,c, X, S, A, W, bestValue, lowval, clauses, start_var, solver)
    # Using incremental SAT solving
    pre_idx = bestValue-lowval-1
    while (True):
        # Check timeout
        current_time = time.time()
        if current_time - start_time >= 3600:
            print("Time limit exceeded.")
            return bestValue, var, clauses, soft_clauses, "Time Limit Exceeded"
            
        remaining_time = 3600 - (current_time - start_time)
        if remaining_time <= 1:  # Need at least 1 second
            print("Time limit exceeded - insufficient time remaining")
            return bestValue, var, clauses, soft_clauses, "Time Limit Exceeded"
            
        # Use timeout for each iterative solve
        # model = solve_with_timeout(solver1, min(int(remaining_time), 3600))  # Max 3600s per iteration
        model = solve(solver1)
        if model is None:
            print("No solution found maxsat or timeout.")
            return bestValue, var, clauses, soft_clauses, "Optimal"
            
        ansmap, bestValue = get_value2(n, m, c, model, W)
        print("best value:", bestValue, end="\r")
        idx = bestValue - lowval - 1
        solver1.add_clause([-U[idx-1]])
        for i in range (idx, pre_idx):
            if pre_idx > 0:
                solver1.add_clause([-U[i]])
        pre_idx = idx
        

    
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
def solve_maxsat():
    try:
        result = subprocess.run([
                                'wsl', '../MaxSat/Es_lab_trainning/PowerPeak/MaxHS/MaxHS/build/release/bin/maxhs',
                                '-printSoln',
                                'problem.wcnf'
                                ], capture_output=True, text=True, timeout=3600)

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

def generate_inagural(n,m,c, X, S, A, W, UB, LB, clauses, var_counter, solver):
    soft_clauses = []
    U = []
    for i in range(LB + 1, UB):
        U.append(var_counter + 1)
        var_counter += 1
        soft_clauses.append([[-var_counter], 1])
    
    for i in range(1, len(U)):
        clauses.append([-U[i], U[i-1]])
        solver.add_clause([-U[i], U[i-1]])
    
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
            solver.add_clause(clause)

    return clauses, soft_clauses, var, U, solver
def write_fancy_table_to_csv(ins, n, m, c, val, s_cons, h_cons, peak, status, time, filename="Incremental_cadical.csv"):
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
    ["ROSZIEG", 6, 25],     #13
    ["HESKIA", 8, 138],     #14
    ["HESKIA", 3, 342],     #15
    ["HESKIA", 5, 205],     #16
    ["BUXEY", 14, 25],      #17
    ["BUXEY", 7, 47],       #18
    ["BUXEY", 8, 41],       #19
    ["BUXEY", 11, 33],      #20
    ["SAWYER", 14, 25],     #21
    ["SAWYER", 7, 47],      #22
    ["SAWYER", 8, 41],      #23
    ["SAWYER", 12, 30],     #24
    ["GUNTHER", 14, 40],    #25
    ["GUNTHER", 9, 54],     #26
    ["GUNTHER", 9, 61],     #27
    ["WARNECKE",25, 65]     #28
    ]

def reset(idx):
    global n, m, c, val, cons, sol, solbb, type, filename, W, neighbors, reversed_neighbors, visited, toposort, clauses, time_list, adj, forward, var_map, var_counter
    m = file_name[idx][1]
    c = file_name[idx][2]
    val = 0
    cons = 0
    sol = 0
    solbb = 0
    type = 1
    var_counter = 0
    var_map = {}
    filename = file_name[idx][0] + ".IN2"
    W = [int(line.strip()) for line in open('task_power/'+file_name[idx][0]+'.txt')]
    neighbors = [[ 0 for i in range(100)] for j in range(100)]
    reversed_neighbors = [[ 0 for i in range(100)] for j in range(100)]
    visited = [False for i in range(100)]
    toposort = []
    clauses = []
    time_list = []
    adj = []
    forward = [0 for i in range(100)]


def main():
    global n, m, c, val, cons, sol, solbb, type, filename, W, neighbors, reversed_neighbors, visited, toposort, clauses, time_list, adj, forward, var_map, var_counter
    for idx in range(11,17):
        reset(idx)
        read_input()
        X, A, S = generate_variables(n,m,c)
        val = max(S)

        # print(val)
        var_counter = max(val)
        var_map = {}

        sol = 0
        solbb = 0
        start_time = time.time()
        solval, vari, clauses, soft_clauses, status = optimal(X,S,A,n,m,c,sol,solbb,start_time)
        end_time = time.time()
        write_fancy_table_to_csv(filename.split(".")[0], n, m, c, vari, len(soft_clauses), len(clauses), solval, status, end_time - start_time)
    


main()

