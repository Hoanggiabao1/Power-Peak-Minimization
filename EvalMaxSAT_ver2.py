from pysat.formula import CNF, WCNF
from pysat.solvers import Solver
from pysat.pb import PBEnc
from pysat.pb import EncType
import math
import time
import fileinput
import csv
import sys
import subprocess

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

def write_fancy_table_to_csv(result, filename="Eval_newencoding.csv"):
    with open("Output/" + filename, "a", newline='') as f:
        writer = csv.writer(f)
        writer.writerow(result)

def write_wcnf_with_h_prefix(filename, wcnf_filename):
    res = subprocess.run(
        ["python3", "3pm.py", filename[0], wcnf_filename, str(filename[1]), str(filename[2])],
        text=True,
        check=True,
        capture_output=True  # <- thêm dòng này
    )
    output = res.stdout
    
    for line in output.splitlines():
        print(line)
        if line.startswith("RESULT_VAR_HARD_SOFT"):
            _, nv, num_hard, num_soft = line.split()
            nv = int(nv)
            num_hard = int(num_hard)
            num_soft = int(num_soft)

    return nv, num_hard, num_soft
                    
def solve_new(filename):
    wcnf_filename = "problem_eval.wcnf"
    nv, num_hard, num_soft = write_wcnf_with_h_prefix(filename, wcnf_filename)
    # Use external MaxSAT solver (tt-open-wbo-inc)
    try:
        result = subprocess.run(
                                ['./EvalMaxSAT_bin', wcnf_filename],
                                stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE,
                                text=True, timeout=3600
                                )

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
                    return assignment, nv, num_hard, num_soft
                else:
                    # Handle space-separated format
                    try:
                        assignment = [int(x) for x in var_string.split() if x != '0']
                        return assignment, nv, num_hard, num_soft
                    except ValueError:
                        # Fallback: treat as binary string anyway
                        assignment = []
                        for i, bit in enumerate(var_string):
                            if bit == '1':
                                assignment.append(i + 1)
                        return assignment, nv, num_hard, num_soft
        return None, nv, num_hard, num_soft
    except subprocess.TimeoutExpired: 
        return None, nv, num_hard, num_soft

def write_fancy_table_to_html(matrix, filename="Output.html", input_file_name="", peak=None):
    with open("Output/" + filename, "w", encoding="utf-8") as f:
        # Viết header HTML
        f.write("<!DOCTYPE html>\n<html>\n<head>\n")
        f.write("<meta charset='utf-8'>\n")
        f.write("<title>Power Table</title>\n")
        f.write("<style>\n")
        f.write("table {border-collapse: collapse;}\n")
        f.write("td, th {border: 1px solid #333; padding: 5px; text-align: right; font-size: 12px;}\n")
        f.write("th {background-color: #f2f2f2;}\n")
        f.write("h2 {text-align: left;}\n")
        f.write("h3 {color: red; text-align: left;}\n")
        f.write("</style>\n")
        f.write("</head>\n<body>\n")

        f.write(f"<h2>{input_file_name}</h2>\n")

        # Bọc div cho cuộn ngang
        f.write("<div style='overflow-x: auto;'>\n")
        f.write("<table>\n")
        
        # Ghi từng dòng dữ liệu
        for i, row in enumerate(matrix):
            if i == len(matrix) - 1:
                prefix = "Power peak"
            else:
                prefix = "Station " + str(i + 1)

            f.write("<tr>\n")
            f.write(f"<td>{prefix}</td>\n")
            for val in row:
                f.write(f"<td>{val}</td>\n")
            f.write("</tr>\n")

        f.write("</table>\n")
        f.write("</div>\n")
        
        # Thêm dòng cuối ghi Power peak nếu có
        f.write(f"<h3>Power peak = {peak}</h3>\n")

        f.write("</body>\n</html>")

def solve_MaxSat_SAML3P(file_name):
    n, W, precedence_relations, Ex_Time = input_file(file_name[0])
    m = file_name[1]
    c = file_name[2]
    print("-"*100)
    print(f"Input file: {file_name[0]}, n={n}, m={m}, c={c}")
    start_time = time.time()
    result, nv, num_hard, num_soft = solve_new(file_name)
    end_time = time.time()
    total_time = end_time - start_time
    if result is None:
        write_fancy_table_to_csv([file_name[0], n, m, c, nv, num_hard, num_soft, "UNSAT", total_time])
        return
    ans_map, peak = get_value(n, m, c, result, W)
    print(f"File: {file_name[0]}, n={n}, m={m}, c={c} => Peak: {peak}, Time: {total_time:.2f}s")
    write_fancy_table_to_csv([file_name[0], n, m, c, nv, num_hard, num_soft, peak, total_time])
    write_fancy_table_to_html(ans_map, filename="Output.html", input_file_name=f"{file_name[0]}_{m}_{c}", peak=peak)

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
    ["HESKIA", 8, 138],     #19
    ["BUXEY", 8, 41],       #20
    ["ROSZIEG", 6, 25],     #21
    ["SAWYER", 8, 41],      #22
    ["HESKIA", 3, 342],     #23
    ["HESKIA", 5, 205],     #24
    ["BUXEY", 11, 33],      #25
    ["SAWYER", 12, 30],     #26
    ["GUNTHER", 9, 61],     #27
    ["WARNECKER", 25, 65],   #28
    ["SAWYER2", 12, 30],     #29
    ["GUNTHER2", 9, 61],     #30
    ["WARNECKER2", 25, 65]   #31
    ]

file_name1 = [
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

for input_in in file_name1:
    solve_MaxSat_SAML3P(input_in)

