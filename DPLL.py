import random
import time
import copy

#####################################################
#####################################################
# Please enter the number of hours you spent on this
# assignment here
num_hours_i_spent_on_this_assignment = 12
#####################################################
#####################################################

#####################################################
#####################################################
# Give one short piece of feedback about the course so far. What
# have you found most interesting? Is there a topic that you had trouble
# understanding? Are there any changes that could improve the value of the
# course to you? (We will anonymize these before reading them.)
# The in course questions are interesting which give us the chance to
# work on the challenge together. It would be better if the sildes of the
# course can be put on the course website earlier.
#####################################################
#####################################################


# A clause consists of a set of symbols, each of which is negated
# or not. A clause where
# clause.symbols = {"a": 1, "b": -1, "c": 1}
# corresponds to the statement: a OR (NOT b) OR c .
class Clause:
    def __init__(self):
        #self.symbols = {}
        pass

    def from_str(self, s):
        s = s.split()
        self.symbols = {}
        for token in s:
            if token[0] == "-":
                sign = -1
                symbol = token[1:]
            else:
                sign = 1
                symbol = token
            self.symbols[symbol] = sign

    def __str__(self):
        tokens = []
        for symbol,sign in self.symbols.items():
            token = ""
            if sign == -1:
                token += "-"
            token += symbol
            tokens.append(token)
        return " ".join(tokens)

# A SAT instance consists of a set of CNF clauses. All clauses
# must be satisfied in order for the SAT instance to be satisfied.
class SatInstance:
    def __init__(self):
        #self.symbols = set()
        #self.clauses = []
        pass

    def from_str(self, s):
        self.symbols = set()
        self.clauses = []
        for line in s.splitlines():
            clause = Clause()
            clause.from_str(line)
            self.clauses.append(clause)
            for symbol in clause.symbols:
                self.symbols.add(symbol)
        self.symbols = sorted(self.symbols) # why sort the symbols ?

    def __str__(self):
        s = ""
        for clause in self.clauses:
            s += str(clause)
            s += "\n"
        return s

    # Takes as input an assignment to symbols and returns True or
    # False depending on whether the instance is satisfied.
    # Input:
    # - assignment: Dictionary of the format {symbol: sign}, where sign
    #       is either 1 or -1.
    # Output: True or False
    def is_satisfied(self, assignment):
        ###########################################
        # Start your code
        #print("My code here")
        for clause in self.clauses:
            flag = False
            for symbol in clause.symbols:
                if(symbol in assignment and clause.symbols[symbol] == assignment[symbol]):
                    flag = True
                    break
            if(flag != True):
                return False
        return True
        # End your code
        ###########################################


# Finds a satisfying assignment to a SAT instance,
# using the DPLL algorithm.
# Input: SAT instance
# Output: Dictionary of the format {symbol: sign}, where sign
#         is either 1 or -1.
def consistent(clauses):
    assignment = {}
    for clause in clauses:
        symbols = clause.symbols
        if(len(symbols) != 1):
            return False
        for symbol in symbols:
            if(symbol not in assignment):
                assignment[symbol] = symbols[symbol]
            else:
                if(assignment[symbol] != symbols[symbol]):
                    return False
    return True

def exist_empty(clauses):
    for clause in clauses:
        if(len(clause.symbols) == 0):
            return True
    return False

def pure_elimination(clauses, symbols, assign):
    # symbols is a set
    for symbol in symbols:
        if(symbol in assign): #already assigned, no need to check
            continue
        count = 0
        value = 1 # default value of flag
        pure = True
        for clause in clauses:
            sym = clause.symbols
            if(symbol in sym):
                if(count == 0):
                    value = sym[symbol]
                    count += 1
                else:
                    if(sym[symbol] != value):
                        pure = False
                        break
        if(count == 0):
            #sym in not in any clause
            continue
        if(pure):
            #assign the value
            assign[symbol] = value
            # do the elimination
            for clause in clauses:
                if(symbol in clause.symbols):
                    clause.symbols = {symbol:value}

def unit_propogation(clauses, symbols, assign):
    # symbols is a set
    for clause in clauses:
        sym = clause.symbols
        if(len(sym) == 1):
            # unit
            for symbol in sym:
                if(symbol in assign):
                    break
                value = sym[symbol]
                assign[symbol] = value # update assignment
                for clause in clauses:
                    if(symbol in clause.symbols and clause.symbols[symbol] != value):
                        del clause.symbols[symbol]
                    if(symbol in clause.symbols and clause.symbols[symbol] == value):
                        clause.symbols = {symbol:value}

def solve_dpll(instance):
    ###########################################
    # Start your code
    #initialize the assignment
    assignment = []
    #use backtraking dpll
    def dpll(clauses, symbols, assign):
        '''
        for clause in clauses:
            print(clause, end = " ")
        print()
        '''
        if(consistent(clauses)):
            unit_propogation(clauses, symbols, assign)
            assignment.append(copy.deepcopy(assign))
            return True
        if(exist_empty(clauses)):
            return False
        pure_elimination(clauses, symbols, assign)
        unit_propogation(clauses, symbols, assign)
        l = ""
        #select a symbol for next iteration
        for symbol in symbols:
            if symbol not in assign:
                l = symbol
                break
        pos = Clause()
        pos.from_str(l)
        clauses_pos = copy.deepcopy(clauses + [pos])
        assign_pos = copy.deepcopy(assign)
        neg = Clause()
        neg.from_str("-" + l)
        clauses_neg = copy.deepcopy(clauses + [neg])
        assign_neg = copy.deepcopy(assign)
        if(len(l) == 0):
            return dpll(clauses, symbols, assign_pos)
        else:
            return dpll(clauses_pos, symbols, assign_pos) or dpll(clauses_neg, symbols, assign_neg)
    find = dpll(instance.clauses, instance.symbols, {})
    for symbol in instance.symbols:
        if(symbol not in assignment[0]):
            assignment[0][symbol] = 1
    return assignment[0]
    # End your code
    ###########################################


with open("small_instances.txt", "r") as input_file:
    instance_strs = input_file.read()

instance_strs = instance_strs.split("\n\n")

with open("small_assignments_inferred.txt", "w") as output_file:
    for instance_str in instance_strs:
        if instance_str.strip() == "":
            continue
        instance = SatInstance()
        instance.from_str(instance_str)
        assignment = solve_dpll(instance)
        print(sorted(assignment, key = lambda x:int(x)))
        #print("DPLL done!")
        #print(assignment)
        print(instance.is_satisfied(assignment)) # to test whether it works
        for symbol_index, (symbol,sign) in enumerate(assignment.items()):
            if symbol_index != 0:
                output_file.write(" ")
            token = ""
            if sign == -1:
                token += "-"
            token += symbol
            output_file.write(token)
        output_file.write("\n")

















