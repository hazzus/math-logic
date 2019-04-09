import random
import string
import sys
import os

f_chars = list(string.ascii_uppercase)
start = 'E'
non_term = {'E', 'D', 'C', 'N', 'V'}
rules = {
    'E': ['D'] * 85 + ['D -> E'] * 15,
    'D': ['C'] * 85 + ['D | C'] * 15,
    'C': ['N'] * 85 + ['C & N'] * 15,
    'N': ['!N'] * 10 + ['V'] * 80 + ['(E)'] * 10,
    'V': f_chars
}


def generate_expr():
    result = start
    while True:
        cur = 0
        flag = False
        for sym in result:
            if sym in non_term:
                replacement = random.choice(rules[sym])
                result = result[:cur] + replacement + result[cur + 1:]
                flag = True
                cur += len(replacement) - 1
            cur += 1
        if not flag:
            break
    return result

if __name__ == '__main__':
    while True:
        expr = generate_expr()
        with open('test.txt', 'w') as test_file:
            test_file.write(expr)
        os.system('cat test.txt | stack run > result.txt')
        result_str = None
        with open('result.txt', 'r') as res_file:
            result_str = res_file.read().strip()
        if result_str == ':(':
            print(':( occured')
            continue
        with open('result.txt', 'w') as res_file:
            res_file.write(result_str)
        os.system('cat result.txt | 3stress/main > final.txt')
        with open('final.txt', 'r') as final_file:
            if final_file.read().strip() == 'Proof is incorrect':
                print('Fucked up')
                break
