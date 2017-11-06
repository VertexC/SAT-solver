import random
import time
import copy


# A clause consists of a set of symbols, each of which is negated
# or not. A clause where
# clause.symbols = {"a": 1, "b": -1, "c": 1}
# corresponds to the statement: a OR (NOT b) OR c .
class Clause:
    def __init__(self):
        self.symbols = {}
        pass

    def from_str(self, s):
        s = s.split()
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
                if(symbol in assignment and clause.symbols[symbol] == assignment[symbol][0]):
                    flag = True
                    break
            if(flag != True):
                return False
        return True
        # End your code
        ###########################################

# Perform Unit rule
# until no or conflict
def unitpropagation(assign_record,decision_level,clauses,implication_stack):
    last_signed_symbol = None
    last_signed_clause = Clause()
    while(True):
        unit_flag = False
        for clause in clauses:
            symbols = clause.symbols
            # to how many symbols left unsigned
            count = 0
            unsigned_symbol = 0
            value = 1
            satisfied_flag = False
            for symbol in symbols:
                if (assign_record[symbol][0] == symbols[symbol]):
                    satisfied_flag = True
                    break
                if (assign_record[symbol][0] == 0):
                    count += 1
                    unsigned_symbol = symbol
                    value = symbols[symbol]
            if (not satisfied_flag and count == 0):
                # conflict
                # learn a new clause
                '''
                print("=======")
                print(assign_record)
                print(clause.symbols)
                print(last_signed_clause.symbols)
                print(last_signed_symbol)
                print("=======")
                '''
                new_clause = Clause()
                for symbol in last_signed_clause.symbols:
                    if(symbol != last_signed_symbol):
                        if(symbol not in new_clause.symbols):
                            new_clause.symbols[symbol] = -last_signed_clause.symbols[symbol]
                for symbol in clause.symbols:# current conflict clause
                    if(symbol != last_signed_symbol):
                        if(symbol not in new_clause.symbols):
                            new_clause.symbols[symbol] = -clause.symbols[symbol]
                return new_clause,True
            if (satisfied_flag == True):
                continue
            if (count == 1):
                unit_flag = True
                # make implication
                if (decision_level not in implication_stack):
                    implication_stack[decision_level] = {unsigned_symbol: value}
                else:
                    implication_stack[decision_level][unsigned_symbol] = value
                # update record
                last_signed_clause = copy.deepcopy(clause)
                last_signed_symbol = unsigned_symbol
                '''
                print("======")
                print(last_signed_clause.symbols)
                print(last_signed_symbol)
                print("======")
                '''
                assign_record[unsigned_symbol][0] = value
                assign_record[unsigned_symbol][2] = decision_level
        if (not unit_flag):
            break
    return  None,False

# check the proper decision level to roll back
def conflict_analysis(decision_level, decision_stack, implication_stack, assign_record, new_clause):
    # get the back_level from the new_clause
    level = []
    for symbol in new_clause.symbols:
        if symbol not in new_clause.symbols:
            level.append(assign_record[symbol][2])
    level = sorted(level)
    if(len(level) >= 2):
        back_level = level[-2]
        # clean implication_stack and decision_stack of current level
        # reupdate the record in implication_stack
        while (decision_level > back_level):
            if (decision_level in implication_stack):
                for symbol in implication_stack[decision_level]:
                    assign_record[symbol] = (0, 1, 0)
                del implication_stack[decision_level]

            assign_record[decision_stack[decision_level][0]] = (0, 1, 0)
            del decision_stack[decision_level]
            decision_level -= 1
        return back_level
    else:
        # in the same level. there is conflict
        # use flip
        back_level = decision_level
        while (back_level >= 0):
            pass
            # clean implication_stack and decision_stack of current level
            # reupdate the record in implication_stack
            if (back_level in implication_stack):
                for symbol in implication_stack[back_level]:
                    assign_record[symbol][0] = 0
                del implication_stack[back_level]
            (symbol, value) = decision_stack[back_level]
            if (assign_record[symbol][1] != 1):
                # cannot be flipped, need to back upper level
                assign_record[symbol] = (0, 1, 0)
                del decision_stack[back_level]
                back_level -= 1
                continue
            else:
                # flip the value, and make flip invalid
                decision_stack[back_level] = (symbol, -value)
                assign_record[symbol][:-1] = (-value, 0)
                break
        return back_level

# check if all assigned
def all_assigned(assign_record):
    for symbol in assign_record:
        if(assign_record[symbol][0] == 0):
            return False # not assigned yet
    return True # all assigned

# Finds a satisfying assignment to a SAT instance,
# using the CDCL algorithm.
# Input: SAT instance
# Output: Dictionary of the format {symbol: sign}, where sign
#         is either 1 or -1.
def CDCL(symbols, clauses):
    # assign_record: record the symbol sate of assigned
    # {symbol:[0 not assigned|1|-1, 0 fisrtime, flip valid, level])
    assign_record = {}
    # literal_record: record the count of different literal
    # {symbol:(count of positive,count of negative)}
    literal_record = {}
    # initialize
    for symbol in symbols:
        assign_record[symbol] = [0,1,0]
    for clause in clauses:
        for symbol in clause.symbols:
            value = clause.symbols[symbol]
            if ((symbol, value) not in literal_record):
                literal_record[(symbol, value)] = 0
            literal_record[(symbol, value)] += 1
    # literal_mheap: record the count of different literal
    # [(symbol,sign,count)]
    literal_mheap = []
    for literal in literal_record:
        literal_mheap.append((literal[0], literal[1], literal_record[literal]))
    literal_mheap = sorted(literal_mheap, key=lambda x:x[-1], reverse = True)
    # decision_stack
    # {decision level: (symbolm,sign)}
    decision_stack = {}
    decision_level = 0
    # implication_stack
    # {decision_level: {symbol:sign}}
    implication_stack = {}
    while(not all_assigned(assign_record)):
        # make decision
        for item in literal_mheap:
            if(assign_record[item[0]][0] == 0):
                # take it as decision
                decision_stack[decision_level] = (item[0],item[1])
                assign_record[item[0]][0] = item[1]
                assign_record[item[0]][2] = decision_level
                break

        # perform unit propagation
        while(True):
            new_clause, conflict = unitpropagation(assign_record,decision_level,clauses,implication_stack)
            if(not conflict):
                break
            # print(new_clause)
            # conflict, learn the new_clause
            clauses.append(new_clause)
            beta = conflict_analysis(decision_level, decision_stack, implication_stack, assign_record, new_clause)
            if(beta < 0):
                print("Not SAT")
                return {}
                # not SAT
            decision_level = beta
        # update decision level
        decision_level += 1
    return assign_record



with open("bonus_instances.txt", "r") as input_file:
    instance_strs = input_file.read()

instance_strs = instance_strs.split("\n\n")

with open("bonus_assignments_inferred_by_CDCL_conflict_learning.txt", "w") as output_file:
    count = 0
    for instance_str in instance_strs:
        instance = SatInstance()
        instance.from_str(instance_str)
        if instance_str.strip() == "":
            continue
        instance = SatInstance()
        instance.from_str(instance_str)
        # use CDCL to give the assignment
        assignment = CDCL(instance.symbols, instance.clauses)
        #print(sorted(assignment, key = lambda x:int(x[0])))
        # check the assignment
        print(instance.is_satisfied(assignment)) # to test whether it works
        for symbol_index, (symbol,(sign,valid,level)) in enumerate(assignment.items()):
            if symbol_index != 0:
                output_file.write(" ")
            token = ""
            if sign == -1:
                token += "-"
            token += symbol
            output_file.write(token)
        output_file.write("\n")
        count += 1
        print(count)
        print(time.strftime("%Y-%m-%d %A %X", time.localtime()))


















