from copy import copy
from enum import Enum
from multiprocessing.sharedctypes import Value
from queue import Empty
from numpy import var

from setuptools import find_packages
import pycosat


def read_cnf_file(fname):
    try:
        file = open(fname, 'r')
        lines = file.readlines()

        for c, line in enumerate(lines):
            if line[0] != 'c':
                break

        prob = lines[c].split()
        if len(prob) != 4 or prob[0] != 'p' or prob[1] != 'cnf':
            raise ValueError
        n = int(prob[2])
        m = int(prob[3])

        lits = [int(val) for val in (("".join(lines[(c+1):])).split())]

        clauses = []
        clause = []
        for lit in lits:
            if lit == 0:
                clauses.append(clause)
                clause = []
            elif lit < -n or lit > n:
                raise ValueError
            else:
                clause.append(lit)
        if len(clauses) != m:
            raise ValueError
        return clauses
    except ValueError:
        return 'INVALID'


def write_cnf_file(cnf, fname, comments=["no description"]):
    file = open(fname, 'w')
    for comment in comments:
        file.write('c '+comment+'\n')
    m = len(cnf)
    lits = []
    for c in cnf:
        lits += c
    n = max(max(lits), -min(lits))
    file.write('p cnf {} {}\n'.format(n, m))
    for c in cnf:
        file.writelines((' '.join(map(str, c)))+' 0\n')
    file.close()


gate_types = "01CANOEX"
nullary_gates = "01"
unary_gates = "CN"
binary_gates = "AOEX"


def valid_gate_type(g):
    return len(g) == 1 and gate_types.find(g) != -1


def is_nullary(g):
    return len(g) == 1 and nullary_gates.find(g) != -1


def is_unary(g):
    return len(g) == 1 and unary_gates.find(g) != -1


def is_binary(g):
    return len(g) == 1 and binary_gates.find(g) != -1


def is_gate_valid(h, g):
    return h < g and h > 0

class Circuit:
    def __init__(self, n, gates):
        self.n = n
        self.gates = gates

    def __str__(self):
        tmp = []
        for i, gate in enumerate(self.gates, self.n+1):
            tmp.append('{} : {}\n'.format(i, gate))
        return ''.join(tmp)


def read_circuit_file(fname, isVerbose):
    gates = []

    try:
        file = open(fname)
        lines = [line[:-1] for line in file.readlines()]

        if len(lines) < 2 or not lines:
            raise ValueError
        n = int(lines[0])
        g_number_so_far = n + 1

        for line in lines[1:]:
            line = line.split()
            line_length = len(line)
            g = line[0]

            if not(valid_gate_type(g)):
                if isVerbose:
                    print("Not a valid gate type!", g)
                raise ValueError

            if is_nullary(g) and line_length == 1:
                if line_length != 1:
                    raise ValueError
                gates += [[g]]
            elif is_unary(g) and line_length == 2:
                h1 = int(line[1])
                if not(is_gate_valid(h1, g_number_so_far)):
                    raise ValueError
                gates += [[g, h1]]
            elif is_binary(g) and line_length == 3:
                h1 = int(line[1])
                h2 = int(line[2])
                if not(is_gate_valid(h1, g_number_so_far)) or not(is_gate_valid(h2, g_number_so_far)):
                    raise ValueError
                gates += [[g, h1, h2]]
            else:
                raise ValueError

            g_number_so_far += 1

        return Circuit(n, gates)
    except ValueError:
        return "INVALID"


def CSAT_to_SAT(circuit):
    cnf = []

    for g, gate in enumerate(circuit.gates, start=circuit.n + 1):
        gate_type = gate[0]
        gate_length = len(gate)

        h1 = 0
        h2 = 0

        if gate_length == 2:
            h1 = gate[1]
        elif gate_length == 3:
            h1 = gate[1]
            h2 = gate[2]

        if gate_type == "0":
            cnf += [[-g]]
        elif gate_type == "1":
            cnf += [[g]]
        elif gate_type == "C":
            cnf += [[g, -h1], [-g, h1]]
        elif gate_type == "N":
            cnf += [[g, h1], [-g, -h1]]
        elif gate_type == "A":
            cnf += [[-g, h1], [-g, h2], [g, -h1, -h2]]
        elif gate_type == "O":
            cnf += [[g, -h1], [g, -h2], [-g, h1, h2]]
        elif gate_type == "E":
            cnf += [[g, -h1, -h2], [g, h1, h2], [-g, h1, -h2], [-g, -h1, h2]]
        else:
            cnf += [[-g, -h1, -h2], [-g, h1, h2], [g, h1, -h2], [g, -h1, h2]]

    cnf += [[circuit.n + len(circuit.gates)]]
    return cnf


def create_distinct_variables_cnf(n, g):
    cnf = []
    var_list = [e+1 for e in range(n)]
    original_vars = var_list[:int(len(var_list)/2)]
    copy_vars = var_list[int(len(var_list)/2):]
    tuple_list = list(zip(original_vars, copy_vars))
    t1, t2 = tuple_list[0]
    cnf += [[-g, -t1, -t2], [-g, t1, t2], [g, t1, -t2], [g, -t1, t2]]
    g += 1

    for ti, tj in tuple_list[1:]:
        cnf += [[-g, -ti, -tj], [-g, ti, tj], [g, ti, -tj], [g, -ti, tj]]
        g += 1
        cnf += [[g, -(g-2)], [g, -(g-1)], [-g, g-2, g-1]]
        g += 1
    return cnf


def find_correct_copy_g(gate, n, original_g, circuit_len):
    if gate <= n:
        return n + gate
    else:
        return original_g + circuit_len


def find_correct_original_g(gate, n):
    if gate > n:
        return gate + n
    return gate


def copy_circuit(circuit):
    n = circuit.n
    double_n = 2 * n
    original_gates = circuit.gates
    copy_gates = []

    for index, gate in enumerate(circuit.gates):
        gate_length = len(gate)

        if gate_length == 1:
            copy_gates += [[gate]]
        elif gate_length == 2:
            original_g = find_correct_original_g(gate[1], n)
            original_gates[index] = [
                gate[0], original_g]
            copy_gates += [[gate[0],
                            find_correct_copy_g(gate[1], n, original_g, len(original_gates))]]
        else:
            first_original_g = find_correct_original_g(gate[1], n)
            second_original_g = find_correct_original_g(gate[2], n)
            original_gates[index] = [
                gate[0], first_original_g, second_original_g]
            copy_gates += [[gate[0],
                            find_correct_copy_g(gate[1], n, first_original_g, len(original_gates)), find_correct_copy_g(gate[2], n, second_original_g, len(original_gates))]]

    last_gate = ["A", double_n + len(original_gates), double_n +
                 len(original_gates) + len(copy_gates)]
    return Circuit(double_n, original_gates + copy_gates + [last_gate])


def reduce_CSAT_to_SAT(infile, outfile, isVerbose=False):
    circuit = read_circuit_file(infile, True)
    if circuit == "INVALID":
        write_cnf_file([[-1], [1]], outfile)
        return
    cnf = CSAT_to_SAT(circuit)
    write_cnf_file(cnf, outfile)


def reduce_CSAT2_to_SAT(infile, outfile):
    circuit = read_circuit_file(infile, True)
    if circuit == "INVALID":
        write_cnf_file([[-1], [1]], outfile)
        return
    composite_circuit = copy_circuit(circuit)
    cnf = CSAT_to_SAT(composite_circuit)
    variables_cnf = create_distinct_variables_cnf(
        composite_circuit.n, composite_circuit.n + len(composite_circuit.gates) + 1)
    write_cnf_file(cnf + variables_cnf, outfile)


def run_examples():
    cnf = read_cnf_file('hole6.cnf')  # UNSAT
    res = pycosat.solve(cnf)
    print(res != 'UNSAT')  # False

    cnf = read_cnf_file('hanoi4.cnf')  # SAT
    res = pycosat.solve(cnf)
    print(res != 'UNSAT')  # True

    reduce_CSAT_to_SAT('test1.circuit', 'test1.cnf')
    cnf = read_cnf_file('test1.cnf')
    res = pycosat.solve(cnf)
    print(res != 'UNSAT') # False

    reduce_CSAT_to_SAT('test2.circuit', 'test2.cnf')
    cnf = read_cnf_file('test2.cnf')
    res = pycosat.solve(cnf)
    print(res != 'UNSAT') # True

    reduce_CSAT2_to_SAT('test2.circuit', 'test2_2.cnf')
    cnf = read_cnf_file('test2_2.cnf')
    res = pycosat.solve(cnf)
    print(res != 'UNSAT') # True

    reduce_CSAT_to_SAT('sub1.circuit', 'sub1.cnf')
    cnf = read_cnf_file('sub1.cnf')
    res = pycosat.solve(cnf)
    print(res != 'UNSAT') # True

    reduce_CSAT_to_SAT('sub2.circuit', 'sub2.cnf')
    cnf = read_cnf_file('sub2.cnf')
    res = pycosat.solve(cnf)
    print(res != 'UNSAT') # True

    reduce_CSAT_to_SAT('div1.circuit', 'div1.cnf')
    cnf = read_cnf_file('div1.cnf')
    res = pycosat.solve(cnf)
    print(res != 'UNSAT') # True

    reduce_CSAT_to_SAT('div2.circuit', 'div2.cnf')
    cnf = read_cnf_file('div2.cnf')
    res = pycosat.solve(cnf)
    print(res != 'UNSAT') # false

    reduce_CSAT_to_SAT("empty.circuit", "empty.cnf")
    cnf = read_cnf_file("empty.cnf")
    res = pycosat.solve(cnf)
    print(res!='UNSAT') # false

    reduce_CSAT_to_SAT("letter.circuit", "letter.cnf")
    cnf = read_cnf_file("letter.cnf")
    res = pycosat.solve(cnf)
    print(res!='UNSAT') # false

    reduce_CSAT_to_SAT("letters.circuit", "letters.cnf")
    cnf = read_cnf_file("letters.cnf")
    res = pycosat.solve(cnf)
    print(res!='UNSAT') # false

    reduce_CSAT_to_SAT("test3.circuit", "test3.cnf")
    cnf = read_cnf_file("test3.cnf")
    res = pycosat.solve(cnf)
    print(res!='UNSAT') # false
run_examples()
