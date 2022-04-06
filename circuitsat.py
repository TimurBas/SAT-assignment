from enum import Enum
import pycosat

def read_cnf_file(fname) :
    # Parse a file in DIMACS .cnf format as described in the file
    # http://archive.dimacs.rutgers.edu/pub/challenge/satisfiability/doc/satformat.dvi
    #
    # A successfully parsed cnf results in a list of clauses where each clause is a list of positive and negative literals
    # described by positive and negative integers as in the DIMACS format. This list may be input directly to pycosat
    try:
        file = open(fname,'r')
        lines = file.readlines()   
        
        for c, line in enumerate(lines):
            if line[0]!='c':
                break

        prob = lines[c].split()
        if len(prob)!=4 or prob[0]!='p' or prob[1]!='cnf':
            raise ValueError
        n = int(prob[2])
        m = int(prob[3]) 
        
        lits = [int(val) for val in (("".join(lines[(c+1):])).split())]

        clauses = []
        clause = []
        for lit in lits:
            if lit==0:
                clauses.append(clause)
                clause=[]
            elif lit<-n or lit>n:
                raise ValueError
            else:
                clause.append(lit)
        if len(clauses)!=m:
            raise ValueError
        return clauses
    except ValueError:
        return 'INVALID'

def write_cnf_file(cnf,fname,comments=["no description"]) :
    # Write a cnf to the DIMACS .cnf format
    file = open(fname,'w')
    for comment in comments:
        file.write('c '+comment+'\n')
    m = len(cnf)
    lits=[]
    for c in cnf:
        lits+=c
    n = max(max(lits),-min(lits))
    file.write('p cnf {} {}\n'.format(n,m))
    for c in cnf:
        file.writelines((' '.join(map(str,c)))+' 0\n')
    file.close()
    
gate_types = "01CANOEX"
nullary_gates = "01"
unary_gates = "CN"
binary_gates = "AOEX"

def valid_gate_type(g):
    return len(g)==1 and gate_types.find(g)!=-1

def is_nullary(g):
    return len(g)==1 and nullary_gates.find(g)!=-1

def is_unary(g):
    return len(g)==1 and unary_gates.find(g)!=-1

def is_binary(g):
    return len(g)==1 and binary_gates.find(g)!=-1

class Circuit:
    # A simple representatioin of a Boolean circuit

    # 'n' is an integer describing the number of inputs
    # 'gates' is a list of gates of the circuit. Each gate is a list of length 1, 2 or 3.
    # The i-th gate of the circuit is implicitly enumerated, starting from n+1.
    # The first element of each gate list is a character that specifies the type of gate
    # and the remaining elements are integers that specify the inputs to the gate
    # as described in the read_circuit_file function below.
    # The last gate of the circuit is the output of the circuit.

    def __init__(self,n,gates):
        self.n = n
        self.gates = gates

    def __str__(self):
        tmp=[]
        for i,gate in enumerate(self.gates,self.n+1):
            tmp.append('{} : {}\n'.format(i,gate))
        return ''.join(tmp)
        
def read_circuit_file(fname) :
    # Parse a file in the Optimization .circuit format we define as follows:
    # The first line of file consists of a single number describing the number n of inputs to the circuit
    # Each remaining line describes a single gate of the circuit.
    # There must be at least one such line, and the last line describes the output gate of the circuit.
    # Gates are implicitly enumerated, starting from n+1. The inputs are numbered 1 through n.
    # A description of a gate consists of its type specified as a single character describing the type of function
    # followed by zero, one, or two postive integers (for nullary (i.e. constants), unary or binary gates).
    # A nullary gate is either the Boolean constant TRUE (type '1') or the Boolean constant FALSE (type '0').
    # A unary gate is either a COPY gate (type 'C') or a NOT gate (type 'N').
    # A binary gate is either an AND gate (type 'A'), an OR gate (type 'O'), an XOR gate (type 'X'), or an EQUAL gate (type 'E').
    # The input(s) to the gate is described by positive integers that may refer to either an input or to an *already described* gate.
    #
    # A successfully parsed circuit is returned as a Circuit class.
    # Otherwise the string 'INVALID' is returned.
    
    #
    # TODO
    #
    pass

def CSAT_to_SAT(C):
    # reduction between valid internal representations
    # input is a Circuit object
    # output is list of clauses that each are a list of positive and negative literals
    cnf = []

    #
    # TODO
    # return cnf
    
def reduce_CSAT_to_SAT(infile,outfile):
    # performs reduction from CircuitSAT to SAT
    # the input is read from infile and the output written to outfile
    # valid encodings of CSAT instances are encoded in the Optimization .circuit format
    # valid encodings of SAT instances are encoded in the DIMACS .cnf format
    
    C = read_circuit_file(infile)
    #
    # TODO
    #
   
def reduce_CSAT2_to_SAT(infile,outfile):
    # performs reduction from CircuitSAT2 to SAT
    # the input is read from infile and the output written to outfile
    # valied encodings of CSAT instances are encoded in the Optimization .circuit format
    # valid encodings of SAT instances are encoded in the DIMACS .cnf format
    
    C = read_circuit_file(infile)  
    #
    # TODO
    #
   
def run_examples():
    cnf = read_cnf_file('hole6.cnf') # UNSAT
    res = pycosat.solve(cnf)
    print(res!='UNSAT') # False

    cnf = read_cnf_file('hanoi4.cnf') # SAT
    res= pycosat.solve(cnf)
    print(res!='UNSAT') # True

    reduce_CSAT_to_SAT('test1.circuit','test1.cnf')
    cnf = read_cnf_file('test1.cnf')
    res = pycosat.solve(cnf)
    print(res!='UNSAT') # ?

    reduce_CSAT_to_SAT('test2.circuit','test2.cnf')
    cnf = read_cnf_file('test2.cnf')
    res = pycosat.solve(cnf)
    print(res!='UNSAT') # ?

    reduce_CSAT2_to_SAT('test2.circuit','test2_2.cnf')
    cnf = read_cnf_file('test2_2.cnf')
    res = pycosat.solve(cnf)
    print(res!='UNSAT') # ?

    reduce_CSAT_to_SAT('sub1.circuit','sub1.cnf')
    cnf = read_cnf_file('sub1.cnf')
    res = pycosat.solve(cnf)
    print(res!='UNSAT') # ?

    reduce_CSAT_to_SAT('sub2.circuit','sub2.cnf')
    cnf = read_cnf_file('sub2.cnf')
    res = pycosat.solve(cnf)
    print(res!='UNSAT') # ?
    
    reduce_CSAT_to_SAT('div1.circuit','div1.cnf')
    cnf = read_cnf_file('div1.cnf')
    res = pycosat.solve(cnf)
    print(res!='UNSAT') # ?

    reduce_CSAT_to_SAT('div2.circuit','div2.cnf')
    cnf = read_cnf_file('div2.cnf')
    res = pycosat.solve(cnf)
    print(res!='UNSAT') # ?
    
