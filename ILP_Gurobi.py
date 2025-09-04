import gurobipy
import time
import csv
from gurobipy import GRB

env = gurobipy.Env(empty=True)
env.setParam('WLSACCESSID', '33d03b04-b102-4c1e-ac3a-28c7c2521a55')
env.setParam('WLSSECRET', '818ea3b4-b954-4e96-bb07-2de85bbeb7c8')
env.setParam('LICENSEID', 2663665)
env.start()

def create_assignment_model(n, m, c, model, Ex_times):
    X = [[model.addVar(vtype=gurobipy.GRB.BINARY, name=f'X_{i}_{j}') for j in range(m)] for i in range(n)]
    S = [[model.addVar(vtype=gurobipy.GRB.BINARY, name=f'S_{i}_{t}') for t in range(c)] for i in range(n)]
    Wmax = model.addVar(vtype=gurobipy.GRB.INTEGER, name="Wmax")
    model.update()
    return model, X, S, Wmax

def add_assignment_constraints(n, m, c, model, X, S, Wmax, W, Ex_times, precedence_relations):
    cons = 0
    # (1) Objective
    model.setObjective(Wmax, gurobipy.GRB.MINIMIZE)
    cons += 1

    # (2) Each task assigned to exactly one station
    for j in range(n):
        model.addConstr(gurobipy.quicksum(X[j][k] for k in range(m)) == 1)
        cons += 1

    # (3) Processing times at each station ≤ c
    for k in range(m):
        model.addConstr(gurobipy.quicksum(Ex_times[j] * X[j][k] for j in range(n)) <= c)
        cons += 1
        # print(" + ".join([f"{Ex_times[j]}*X[{j},{k}]" for j in range(n)]) + f" <= {c}")
    
    # (4) Precedence: X[j,k] ≤ sum_{h<k} X[i,h] for i ≺ j
    for (i, j) in precedence_relations:
        for k in range(m):
            model.addConstr(X[j-1][k] <= gurobipy.quicksum(X[i-1][h] for h in range(k + 1)))
            cons += 1
    # (5) Each task assigned to exactly one start time
    for j in range(n):
        model.addConstr(gurobipy.quicksum(S[j][t] for t in range(c - Ex_times[j] + 1)) == 1)
        cons += 1
        # print(" + ".join([f"S[{j},{t}]" for t in range(c - Ex_times[j] + 1)]) + " = 1")

    # (6) S[j,t] ≤ sum_{τ=t-ti}^{t} S[i,τ] + 2 - X[i,k] - X[j,k]
    for (i, j) in precedence_relations:
        if i > 0 and j > 0:
            for k in range(m):
                for t in range(c - Ex_times[j-1] + 1):
                    tau_range = range(t - Ex_times[i-1] + 1)
                    model.addConstr(
                        S[j-1][t] <= gurobipy.quicksum(S[i-1][tau] for tau in tau_range) + 2 - X[i-1][k] - X[j-1][k]
                    )
                    cons += 1
                    # In ràng buộc nếu cần
                    # print(
                    #     f"S[{j-1},{t}] <= "
                    #     + " + ".join([f"S[{i-1},{tau}]" for tau in tau_range])
                    #     + f" + 2 - X[{i-1},{k}] - X[{j-1},{k}]"
                    # )

    # (7) X[i,k] + X[j,k] + sum_{τ=t-ti+1}^{t} S[i,τ] + sum_{τ=t-tj+1}^{t} S[j,τ] ≤ 3
    for i in range(n - 1):
        for j in range(i + 1, n):
            for k in range(m):
                for t in range(c):
                    model.addConstr(
                        X[i][k] + X[j][k] +
                        gurobipy.quicksum(S[i][tau] for tau in range(t - Ex_times[i] + 1, t + 1)) +
                        gurobipy.quicksum(S[j][tau] for tau in range(t - Ex_times[j] + 1, t + 1))
                        <= 3
                    )
                    cons += 1

    # (8) Power peak constraint
    for t in range(c):
        model.addConstr(
            gurobipy.quicksum([
                W[j] * gurobipy.quicksum([S[j][s] for s in range(t - Ex_times[j] + 1, t + 1)])
                for j in range(n)
            ]) <= Wmax
        )
        cons += 1
        # print(" + ".join([f"{W[j]}*(" + " + ".join([f"S[{j},{s}]" for s in range(max(0, t - Ex_times[j]), t + 1)]) + ")" for j in range(n)]) + f" <= Wmax")


    # (9) Variable domains (already set by binary_var/integer_var)
    return model, cons

def solve_assignment_problem(n, m, c, Ex_times, precedence_relations, W):
    model, X, S, Wmax = create_assignment_model(n, m, c, gurobipy.Model(env=env), Ex_times)
    model, cons = add_assignment_constraints(n, m, c, model, X, S, Wmax, W, Ex_times, precedence_relations)
    model.Params.TimeLimit = 3600
    model.Params.LogToConsole = 0  # Nếu muốn tắt log
    model.optimize()
    return model, len(X) + len(S), cons

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

def get_value(solution, n, m, c, W, Ex_times):
    X_values = [[0 for _ in range(m)] for _ in range(n)]
    S_values = [[0 for _ in range(c)] for _ in range(n)]

    for i in range(n):
        for k in range(m):
            var_name = f"X_{i}_{k}"
            X_values[i][k] = solution.getVarByName(var_name).X

    for i in range(n):
        for t in range(c):
            var_name = f"S_{i}_{t}"
            S_values[i][t] = solution.getVarByName(var_name).X

    schedule = [[0 for _ in range(c)] for _ in range(m + 1)]

    for k in range(m):
        for j in range(n):
            for t in range(c):
                for t0 in range(Ex_times[j]):
                    if X_values[j][k] == 1 and t - t0 >= 0 and S_values[j][t - t0] == 1:
                        schedule[k][t] = W[j]

    schedule[m] = [sum(schedule[j][t] for j in range(m)) for t in range(c)]
    peak = max(schedule[m])
    Wmax = solution.getVarByName("Wmax").X
    return schedule, Wmax, peak

def write_to_csv(result):
    with open("Output/result_gurobi.csv", "a") as f:
        writer = csv.writer(f)
        writer.writerow(result)

def optimal(filename):
    n, W, precedence_relations, Ex_times = input_file(filename[0])
    m = filename[1]  # Number of stations
    c = filename[2]  # Increased capacity to avoid infeasibility
    print(f"n={n}, m={m}, c={c}")
    start_time = time.time()
    solution, var, cons = solve_assignment_problem(n, m, c, Ex_times, precedence_relations, W)
    end_time = time.time()
    print("Time taken:", end_time - start_time)
    if solution:
        print(f"Solution for {filename[0]} with n={n}, m={m}, c={c}:")
        schedule, Wmax, peak = get_value(solution, n, m, c, W, Ex_times)
        print("Peak =", peak)
        write_to_csv([filename[0], n, m, c, peak, var, cons, end_time - start_time])
    else:
        print("No solution found.")
        write_to_csv([filename[0], n, m, c, "Timeout", var, cons, end_time - start_time])

file_name = [
    # Easy families 
    # MERTENS 
    ["MERTENS", 6, 6],      # 0
    ["MERTENS", 2, 18],     # 1
    ["MERTENS", 5, 7],      # 2
    ["MERTENS", 5, 8],      # 3
    ["MERTENS", 3, 10],     # 4
    ["MERTENS", 2, 15],     # 5
    # Easy/MERTENS count: 6

    # BOWMAN
    ["BOWMAN", 5, 20],      # 6
    # Easy/BOWMAN count: 1

    # JAESCHKE
    ["JAESCHKE", 8, 6],     # 7
    ["JAESCHKE", 3, 18],    # 8
    ["JAESCHKE", 6, 8],     # 9
    ["JAESCHKE", 4, 10],    # 10
    ["JAESCHKE", 3, 18],    # 11
    # Easy/JAESCHKE count: 5

    # JACKSON
    ["JACKSON", 8, 7],      # 12
    ["JACKSON", 3, 21],     # 13
    ["JACKSON", 6, 9],      # 14
    ["JACKSON", 5, 10],     # 15
    ["JACKSON", 4, 13],     # 16
    ["JACKSON", 4, 14],     # 17
    # Easy/JACKSON count: 6

    # MANSOOR
    ["MANSOOR", 4, 48],     # 18
    ["MANSOOR", 2, 94],     # 19
    ["MANSOOR", 3, 62],     # 20
    # Easy/MANSOOR count: 3

    # MITCHELL
    ["MITCHELL", 8, 14],    # 21
    ["MITCHELL", 3, 39],    # 22
    ["MITCHELL", 8, 15],    # 23
    ["MITCHELL", 5, 21],    # 24
    ["MITCHELL", 5, 26],    # 25
    ["MITCHELL", 3, 35],    # 26
    # Easy/MITCHELL count: 6

    # ROSZIEG
    ["ROSZIEG", 10, 14],    # 27
    ["ROSZIEG", 4, 32],     # 28
    ["ROSZIEG", 6, 25],     # 29
    ["ROSZIEG", 8, 16],     # 30
    ["ROSZIEG", 8, 18],     # 31
    ["ROSZIEG", 6, 21],     # 32
    # Easy/ROSZIEG count: 6

    # HESKIA
    ["HESKIA", 8, 138],     # 33
    ["HESKIA", 3, 342],     # 34
    ["HESKIA", 5, 205],     # 35
    ["HESKIA", 5, 216],     # 36
    ["HESKIA", 4, 256],     # 37
    ["HESKIA", 4, 324],     # 38
    # Easy/HESKIA count: 6

    # Easy families total count: 39

    # Hard families
    # BUXEY
    ["BUXEY", 7, 47],       # 39
    ["BUXEY", 8, 41],       # 40
    ["BUXEY", 11, 33],      # 41
    ["BUXEY", 13, 27],      # 42
    ["BUXEY", 12, 30],      # 43
    ["BUXEY", 7, 54],       # 44
    ["BUXEY", 10, 36],      # 45
    # Hard/BUXEY count: 7

    # SAWYER
    ["SAWYER", 14, 25],     # 46
    ["SAWYER", 7, 47],      # 47
    ["SAWYER", 8, 41],      # 48
    ["SAWYER", 12, 30],     # 49
    ["SAWYER", 13, 27],     # 50
    ["SAWYER", 11, 33],     # 51
    ["SAWYER", 10, 36],     # 52
    ["SAWYER", 7, 54],      # 53
    ["SAWYER", 5, 75],      # 54
    # Hard/SAWYER count: 9

    # GUNTHER
    ["GUNTHER", 9, 54],     # 55
    ["GUNTHER", 9, 61],     # 56
    ["GUNTHER", 14, 41],    # 57
    ["GUNTHER", 12, 44],    # 58
    ["GUNTHER", 11, 49],    # 59
    ["GUNTHER", 8, 69],     # 60
    ["GUNTHER", 7, 81],     # 61
    # Hard/GUNTHER count: 7

    # WARNECKE
    ["WARNECKE", 25, 65],   # 62
    ["WARNECKE", 31, 54],   # 63
    ["WARNECKE", 29, 56],   # 64
    ["WARNECKE", 29, 58],   # 65
    ["WARNECKE", 27, 60],   # 66
    ["WARNECKE", 27, 62],   # 67
    ["WARNECKE", 24, 68],   # 68
    ["WARNECKE", 23, 71],   # 69
    ["WARNECKE", 22, 74],   # 70
    ["WARNECKE", 21, 78],   # 71
    ["WARNECKE", 20, 82],   # 72
    ["WARNECKE", 19, 86],   # 73
    ["WARNECKE", 17, 92],   # 74
    ["WARNECKE", 17, 97],   # 75
    ["WARNECKE", 15, 104],  # 76
    ["WARNECKE", 14, 111],  # 77
    # Hard/WARNECKE count: 16

    # LUTZ2
    ["LUTZ2", 49, 11],      # 78
    ["LUTZ2", 44, 12],      # 79
    ["LUTZ2", 40, 13],      # 80
    ["LUTZ2", 37, 14],      # 81
    ["LUTZ2", 34, 15],      # 82
    ["LUTZ2", 31, 16],      # 83
    ["LUTZ2", 29, 17],      # 84
    ["LUTZ2", 28, 18],      # 85
    ["LUTZ2", 26, 19],      # 86
    ["LUTZ2", 25, 20],      # 87
    ["LUTZ2", 24, 21],      # 88
    # Hard/LUTZ2 count: 11

    # Hard families total count: 50

    # Total: 89
    ]

for i in range(10):
    optimal(file_name[i])