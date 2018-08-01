from z3 import *
from mythril.analysis import solver
from mythril.analysis.ops import *
from mythril.analysis.report import Issue
from mythril.exceptions import UnsatError
import re
import logging


'''
MODULE DESCRIPTION:

find tokens 
'''


def execute(statespace):

    logging.debug("Executing module: TOKEN?")

    issues = []

    for k in statespace.nodes:
        node = statespace.nodes[k]

        for state in node.states:

            instruction = state.get_current_instruction()

            if(instruction['opcode'] == "SSTORE"):

                logging.debug("[UNCHECKED_SUICIDE] found sstore " + node.function_name)

                description = "The function `" + node.function_name + "` executes the SSTORE instruction. "

                stack = copy.deepcopy(state.mstate.stack)
                to = stack.pop()
                val = stack.pop()

                logging.debug(to)
                logging.debug(val)

                is_store_calldata = False

                if ("calldata" in str(to) and "calldata" in str(val)):
                    description += "Location and value depends on calldata\n"
                    is_store_calldata = True
                

                # constrained = False
               

                # index = 0

                # while(can_solve and index < len(node.constraints)):

                #     constraint = node.constraints[index]
                #     index += 1

                #     m = re.search(r'storage_([a-z0-9_&^]+)', str(constraint))

                #     if (m):
                #         constrained = True
                #         idx = m.group(1)

                #         logging.debug("STORAGE CONSTRAINT FOUND: " + idx)

                #         func = statespace.find_storage_write(state.environment.active_account.address, idx)

                #         if func:
                #             description += "\nThere is a check on storage index " + str(idx) + ". This storage index can be written to by calling the function `" + func + "`."
                #             break
                #         else:
                #             logging.debug("[UNCHECKED_SUICIDE] No storage writes to index " + str(idx))
                #             can_solve = False
                #             break

                #     elif (re.search(r"caller", str(constraint)) and re.search(r'[0-9]{20}', str(constraint))):
                #         can_solve = False
                #         break

                # if not constrained:
                #     description += "\nIt seems that this function can be called without restrictions."

                if is_store_calldata:

                    try:

                        model = solver.get_model(node.constraints)

                        debug = "SOLVER OUTPUT:\n" + solver.pretty_print_model(model)

                        issue = Issue(node.contract_name, node.function_name, instruction['address'], "Unchecked SSTORE", "Warning", description, debug)
                        issues.append(issue)

                    except UnsatError:
                            logging.debug("[UNCHECKED_SUICIDE] no model found")

    return issues
