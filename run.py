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

if __name__ == "__main__":
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

    for i in file_name[:1]:
        start_time = time.time()
        # Gọi IncrementalSAT_Normal.py qua subprocess và truyền input
        try:
            res = subprocess.run(
                ["python", ".\IncrementalSAT_Normal.py", i[0], i[1], i[2]],
                capture_output=True,
                text=True,
                timeout=3600
            )
        except Exception:
            res = None
        print(res)
        end_time = time.time() - start_time
        peak = "-"
        ansmap = []
        sol = n = num_var = num_clauses = "-"
        if res is not None and res.stdout:
            lines = res.stdout.splitlines()
            for line in lines:
                if line.startswith("Peak:"):
                    peak = line.split(":", 1)[1].strip()
                elif line.startswith("Mapping:"):
                    try:
                        ansmap = ast.literal_eval(line.split(":", 1)[1].strip())
                    except Exception:
                        ansmap = []
                elif line.startswith("Iterations:"):
                    sol = line.split(":", 1)[1].strip()
                elif line.startswith("Num tasks:"):
                    n = line.split(":", 1)[1].strip()
                elif line.startswith("Num variables:"):
                    num_var = line.split(":", 1)[1].strip()
                elif line.startswith("Num clauses:"):
                    num_clauses = line.split(":", 1)[1].strip()
            print("Final peak: ", peak)
            write_fancy_table_to_html(ansmap, input_file_name = i[0], peak=peak)
            inresult = [i[0], n, i[1], i[2], num_var, num_clauses, peak, sol, end_time, "Optimal"]
        else:
            print("Unsat hoặc Timeout")
            inresult = [i[0], "-", i[1], i[2], "-", "-", "-", "-", ">3600", "Timeout"]

        with open("Output/Normal.csv", "a", newline='') as f:
            writer = csv.writer(f)
            writer.writerow(inresult)