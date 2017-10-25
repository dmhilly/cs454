import os
import re
import subprocess
from termcolor import colored

import time

def valid_benches():
    return [ "add.imp"
           , "arrayIterate.imp"
           , "arb1.imp"
           , "assign.imp"
           , "assignToArray.imp"
           , "countToN.imp"
           , "find.imp"
           , "mult.imp"
           , "nopost.imp"
           , "rev.imp"
           , "simplarr.imp"
           , "sort3.imp"
           , "v_order.imp" ]

def valid_benches_stress():
    return [ "binary_search.imp"
           , "bubble.imp"
           , "factorial.imp"
           #, "fiba.imp"
           , "findMax.imp"
           , "gcd.imp"
           , "lcm.imp"
           , "mod.imp"
           , "prime.imp"
           , "v_sync.imp"]

def invalid_benches(): 
    return [ "multFalse.imp"
           , "rev_bad.imp"
           , "wrong_add.imp" ]

def invalid_benches_stress(): 
    return [ "find.imp"
           , "prime_bad.imp" ]

def entries():
    return [ 
             ( "Ken Chen"
             , "../chenken/"
             , ["./check_valid.sh"]
             , "../competition_benchmarks"
             , lambda x : (matches("valid"))(x) and not (matches("invalid"))(x)
             , matches("invalid"))
             ,
             ( "Jayshree Sarathy and Valerie Chen"
             , "../chenvalerie/vcgen/"
             , ["scala", "-cp", "classes", "VCGen"]
             , "../../competition_benchmarks"
             , lambda x : (matches("\nsat\n"))(x) and not (matches("unsat"))(x)
             , matches("unsat"))
             ,
             ( "Max Del Giudice"
             , "../delgiudice/"
             , ["bash", "run.sh"]
             , "../competition_benchmarks"
             , lambda x : (matches("valid"))(x) and not (matches("invalid"))(x)
             , matches("invalid"))
             ,
             ( "Shuwen Deng and Zeyu Wang"
             , "../dengshuwen/"
             , ["./verify.sh"]
             , ""
             , lambda x : (matches("unsat"))(x)
             , lambda x : (matches("sat"))(x) and not (matches("unsat"))(x))
             ,
             ( "Christopher Fu"
             , "../fuchristopher/"
             , ["stack", "exec", "vcgen-exe"]
             , "../competition_benchmarks"
             , lambda x : (matches("sat"))(x) and not (matches("unsat"))(x)
             , matches("unsat"))
             ,
             ( "Yiding Hao"
             , "../haoyiding/vcgen/"
             , ["scala", "-cp", "classes", "VCGen"]
             , "../../competition_benchmarks"
             , lambda x : (matches("The program is correct."))(x) and not (matches("The program is not correct."))(x)
             , matches("The program is not correct."))
             ,
             ( "Lucas Paul"
             , "../paullucas/"
             , ["bash", "run.sh"]
             , "../competition_benchmarks"
             , lambda x : (matches("valid"))(x) and not (matches("invalid"))(x)
             , matches("invalid"))
             ,
             ( "Tyler Petrochko"
             , "../petrochkotyl/vcgen/"
             , ["scala", "-cp", "classes", "VCGen"]
             , "../../competition_benchmarks"
             , lambda x : (matches("Valid"))(x) and not (matches("Invalid"))(x)
             , matches("Invalid"))
             ,
          #    # poruthoornisha doesn't compile
             ( "Kate Rogers and Devin Hilly"
             , "../rogerskate/"
             , ["scala", "-cp", "classes", "VCGen"]
             , "../competition_benchmarks"
             , lambda x : (matches("unsat"))(x)
             , lambda x : (matches("sat"))(x) and not (matches("unsat"))(x))
             ,
             ( "Julian Rosenblum"
             , "../rosenblum/"
             , ["./verify"]
             , "../competition_benchmarks"
             , matches("Verification successful")
             , matches("Verification failed"))
             ,
             ( "Yuyang Sang and Jialu Zhang"
             , "../sangyuyang/vcgen/"
             , ["bash", "run.sh"]
             , "../../competition_benchmarks"
             , lambda x : (matches("valid"))(x) and not (matches("invalid"))(x)
             , matches("invalid"))
             ,
             ( "Anton Xue and Jake Albert"
             , "../xueanton/vcgen/"
             , ["scala", "-cp", "classes", "VCGen"]
             , "../../competition_benchmarks"
             , lambda x : (matches("verified"))(x) and not (matches("not verified"))(x)
             , matches("not verified"))
             ]

def add_prefix(pre, benches):
    return map(lambda b : pre + b, benches)

def run_benchmark(prog, bench, correct_out):
    try:
        p = subprocess.Popen(prog + [bench], stdout=subprocess.PIPE, stderr = subprocess.STDOUT)
        out, e = p.communicate(timeout=20)

    except subprocess.TimeoutExpired:
        return None
    except:
        return False

    if e is not None:
        return None
    elif correct_out(out):
        return True
    else:
        return False

def run_benchmarks(prog, benches, correct_out):
    correct = 0
    incorrect = 0
    timeout = 0

    for b in benches:
        res = run_benchmark(prog, b, correct_out)

        if res is None:
            print (colored("[" + b + "] - TIMEOUT", "grey"))
            timeout += 1
        elif res:
            print (colored("[" + b + "] - PASSED", "green"))
            correct += 1
        else:
            print (colored("[" + b + "] - FAILED", "red"))
            incorrect += 1

    return (correct, incorrect, timeout)

def run(prog, pre, valid_folder, invalid_folder, valid_message, invalid_message, valid_bench, invalid_bench):
    pre_valid = pre + "/" + valid_folder + "/"
    pre_invalid = pre + "/" + invalid_folder + "/"

    val = add_prefix(pre_valid, valid_bench)
    inval = add_prefix(pre_invalid, invalid_bench)

    (vc, vi, vt) = run_benchmarks(prog, val, valid_message)

    (invc, invi, it) = run_benchmarks(prog, inval, invalid_message)

    correct = vc + invc
    incorrect = vi + invi
    timeouts = vt + it

    return (correct, incorrect, timeouts)

def matches(s):
    return (lambda x : re.search(s, x.decode('utf-8')))

def calc_score(c, i):
    return (5 * c) - (2 * i)

def print_scores(scores):
    names_scores = scores.items()
    names_scores = list(names_scores)
    names_scores.sort(key = lambda x: cmp_tuples(x), reverse = True)

    print ("Name - Score")

    for (n, (c, i, t)) in names_scores:
        print (n + "-" + str(calc_score(c, i)))

def cmp_tuples(t1,):
    (n1, (x1, y1, z1)) = t1
    return x1

def run_over_entries(scores, valid_folder, invalid_folder,valid_bench, invalid_bench):
    startDir = os.getcwd()
    total_score = 0.0

    for (name, d, prog, b, cor, inc) in entries():

        (ex_c, ex_i, ex_t) = scores.get(name, (0, 0, 0))

        input(name)

        os.chdir(d)

        starttime = time.time()

        (c, i, t) = run(prog, b, valid_folder, invalid_folder, cor, inc, valid_bench, invalid_bench)

        endtime = time.time()

        diff = endtime - starttime

        print (colored("Correct: " + str(c), "green"))
        print (colored("Incorrect: " + str(i), "red"))
        print (colored("Timeouts: " + str(t), "red"))

        score = (c * 5) - (i * 2)

        scores[name] = (ex_c + c, ex_i + i, ex_t + t)

        print ("\n")

        print (colored("Score: " + str(score), "yellow"))

        print (colored("Running time: " + str(diff), "yellow"))


        total_score += score

        os.chdir(startDir)

        input("")

    return (scores, total_score)

def main():
    scores = {}


    startDir = os.getcwd()

    total_submissions = len(entries())

    (scores, total_score) = run_over_entries(scores, "valid", "invalid", valid_benches(), invalid_benches())

    print_scores(scores)
    input()

    avg_score = total_score / total_submissions

    print ("\nAverage Score = " + str(avg_score))

    (scores, total_score) = run_over_entries(scores, "valid_stress", "invalid_stress", valid_benches_stress(), invalid_benches_stress())

    print_scores(scores)

    avg_score = total_score / total_submissions

    print ("\nAverage Score = " + str(avg_score))

if __name__ == "__main__":
    main()