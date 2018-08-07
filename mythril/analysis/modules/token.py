from z3 import *
from mythril.analysis import solver
from mythril.analysis.ops import *
from mythril.analysis.report import Issue
from mythril.exceptions import UnsatError
import re
import logging

#reg = re.compile("calldata\[(?P<index>[1-9])\]")

INCLUDE_RESULTS_INUNSAT_PATHES = True

def detect_token_sstore(val, to):

    return "calldata" in str(val) and ("+" in str(val) or "-" in str(val))

def gen_description(item):
    return ""
    (instruction, to, val, input_dep_val_x, input_dep_to_x, model) = item

    description = "Value depends on calldata\n"
    # description += "\n TO:"
    # description += str(type(to))
    # #description += solver.pretty_print_model(to)
    # description += str(to) + "\n"
    # description += "\n VAL:"
    # description += str(type(val))
    # description += str(val) + "\n\n\n"
    return description


def gen_debug(item):
    return ""
    (instruction, to, val, input_dep_val_x, input_dep_to_x, model) = item
    if model == None:
        return ""
    else:
        debug = "SOLVER OUTPUT:\n" + solver.pretty_print_model(model) + "\n\n\n"
        return debug

def get_calldata_under_add_or_sub(ex, search_add_sub, parentop, res):
    if not isinstance(ex, ExprRef):
        return
    #print(ex.decl().name())

    if search_add_sub and (ex.decl().name() == "bvsub" or ex.decl().name() == "bvadd"):
        #print("found root add or sub")
        parentop = ex.decl().name()
        search_add_sub = False
    elif not search_add_sub and re.match("calldata_MAIN\[[0-9]+\]", ex.decl().name()):
        res.append((parentop, ex.decl().name()))

    for i in range(ex.num_args()):
        get_calldata_under_add_or_sub(ex.arg(i), search_add_sub, parentop, res)

    return res

def get_calldata(ex, res):
    if not isinstance(ex, ExprRef):
        return

    if re.match("calldata_MAIN\[[0-9]+\]", ex.decl().name()):
        res.append(ex.decl().name() + "\n")

    for i in range(ex.num_args()):
        get_calldata(ex.arg(i), res)

    return res

def check_if_proper_token_semantics(sstors):
    for x in sstors:
        for y in sstors:
            if x != y:
                (_, _, _, input_dep_val_x, input_dep_to_x, _) = x
                (_, _, _, input_dep_val_y, input_dep_to_y, _) = y

                r = set(map(lambda x: x[1], filter(lambda x: x[0] == "bvsub", input_dep_val_x)))
                l = set(map(lambda x: x[1], filter(lambda x: x[0] == "bvadd", input_dep_val_y)))

                inter_val = r.intersection(l)
                # print(r)
                # print(l)
                # print(inter_val)
                # print(input_dep_to_x)
                # print(input_dep_to_y)
                if len(inter_val) > 0: # and (len(input_dep_to_y) > 0 or len(input_dep_to_x) > 0):
                    return True

                r = set(map(lambda x: x[1], filter(lambda x: x[0] == "bvsub", input_dep_val_y)))
                l = set(map(lambda x: x[1], filter(lambda x: x[0] == "bvadd", input_dep_val_x)))

                inter_val = r.intersection(l)
                # print(r)
                # print(l)
                # print(inter_val)
                if len(inter_val) > 0: # and (len(input_dep_to_y) > 0 or len(input_dep_to_x) > 0):
                    return True
    return False


'''
MODULE DESCRIPTION:

find tokens 
'''
def execute(statespace):
    logging.debug("[TOKEN] Executing module: TOKEN?")
    #print("coverage:" + str(statespace.laser.coverage))
    # print("calls:" + str(statespace.calls))
    # print("SSTORE:" + str(statespace.sstors))

    issues = []
    temp = dict()

    def add_sstore(inst, to, val, model):
        key = node.contract_name + "." + node.function_name
        logging.debug(key)
        if(not key in temp):
            temp[key] = list()        

        #+x = re.search(reg, str(val))
        call_data_dep_values = get_calldata_under_add_or_sub(val, True, None, [])
        to_calldata_dep = get_calldata(to, [])

        temp[key].append((inst, to, val, set(call_data_dep_values), set(to_calldata_dep), model))

    for k in statespace.nodes:
        node = statespace.nodes[k]

        for state in node.states:

            instruction = state.get_current_instruction()

            if(instruction['opcode'] == "SSTORE"):
                stack = copy.deepcopy(state.mstate.stack)
                to = stack.pop()

                val = stack.pop()

                if detect_token_sstore(val, to):
                    #print()
                    #print(to)
                    #print()
                    try:
                        logging.debug("[TOKEN] found matching store")
                        model = solver.get_model(node.constraints, timeout = 600)

                        add_sstore(instruction, to, val, model)

                    except UnsatError:
                            logging.debug("[TOKEN] no model found")
                            if INCLUDE_RESULTS_INUNSAT_PATHES:
                                logging.debug("[TOKEN] no model, but still add")
                                add_sstore(instruction, to, val, None)

    #print(temp)


    for key, values in temp.items():
        keysplit = key.split(".",1)
        func = keysplit[1]
        cont = keysplit[0]
        # # has_add = any(filter(lambda x: x[3], values))
        # # has_sub = any(filter(lambda x: x[4], values))
        # to_dep_on_call = list(filter(lambda x: x[3], values))
        if check_if_proper_token_semantics(values):
            issues.append(Issue(cont, func, instruction['address'], "Token +/- SSTORE, Coverage: " + str(statespace.laser.coverage), "Warning", str("".join(list(map(gen_description, values)))), str("".join(list(map(gen_debug, values))))))

    return issues
