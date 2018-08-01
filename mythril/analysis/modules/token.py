from z3 import *
from mythril.analysis import solver
from mythril.analysis.ops import *
from mythril.analysis.report import Issue
from mythril.exceptions import UnsatError
import re
import logging

INCLUDE_RESULTS_INUNSAT_PATHES = True

def detect_token_sstore(val, to):
    return "calldata" in str(val) and ("+" in str(val) or "-" in str(val))

def gen_description(item):
    (instruction, to, val, has_add, has_sub, to_dep_onCalldata, model) = item

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
    (instruction, to, val, has_add, has_sub, to_dep_onCalldata, model) = item
    if model == None:
        return ""
    else:
        debug = "SOLVER OUTPUT:\n" + solver.pretty_print_model(model) + "\n\n\n"
        return debug


'''
MODULE DESCRIPTION:

find tokens 
'''
def execute(statespace):
    logging.debug("[TOKEN] Executing module: TOKEN?")

    issues = []
    temp = dict()

    def add_sstore(inst, to, val, model):
        key = node.contract_name + "." + node.function_name
        logging.debug(key)
        if(not key in temp):
            temp[key] = list()        
        temp[key].append((inst, to, val, "+" in str(val), "-" in str(val), "calldata" in str(to), model))

    for k in statespace.nodes:
        node = statespace.nodes[k]

        for state in node.states:

            instruction = state.get_current_instruction()

            if(instruction['opcode'] == "SSTORE"):
                stack = copy.deepcopy(state.mstate.stack)
                to = stack.pop()
                val = stack.pop()

                if detect_token_sstore(val, to):
                    try:
                        logging.debug("[TOKEN] found matching store")
                        model = solver.get_model(node.constraints)

                        add_sstore(instruction, to, val, model)

                    except UnsatError:
                            logging.debug("[TOKEN] no model found")
                            if INCLUDE_RESULTS_INUNSAT_PATHES:
                                logging.debug("[TOKEN] no model, but still add")
                                add_sstore(instruction, to, val, None)

    #print(temp)


    for key, values in temp.items():
        keysplit = key.split(".",1)
        func = keysplit[0]
        cont = keysplit[1]
        has_add = any(filter(lambda x: x[3], values))
        has_sub = any(filter(lambda x: x[4], values))
        to_dep_on_call = list(filter(lambda x: x[5], values))
        if has_add and has_sub and len(to_dep_on_call) >= 1:
            issues.append(Issue(cont, func, instruction['address'], "Token +/- SSTORE", "Warning", str("".join(list(map(gen_description, values)))), str("".join(list(map(gen_debug, values))))))

    return issues
