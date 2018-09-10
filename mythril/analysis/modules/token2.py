import logging
import re

from mythril.analysis import solver
from mythril.analysis.ops import *
from mythril.analysis.report import Issue
from mythril.exceptions import UnsatError
from mythril.laser.ethereum.taint_analysis import TaintRunner

'''
MODULE DESCRIPTION:
This module finds what could be a token system. 

Requirements, Sender balance check in contraints, 
'''


def execute(statespace):
    """ Executes the analysis module"""
    logging.debug("Executing module: TOKEN2")

    issues = []
    taints = []

    for state, node in _get_states_with_opcode(statespace, "CALLDATALOAD"):
        #state = node.states[index]
        taint_stack = [False for _ in state.mstate.stack]
        taint_stack[-1] = True
        taints.append(TaintRunner.execute(statespace, node, state, initial_stack=taint_stack))

    for state, node in _get_tainted_sstores(statespace, taints):
        funtcion_we_are_in = node.contract_name + "." + node.function_name
        following_sstores = _get_sstore_along_the_line(statespace, node)

        if len(following_sstores) > 0:
            # logging.info("Found SSTORE %s following an SSTORE in (%s)"%(len(following_sstores), funtcion_we_are_in))
            # logging.debug("%s: BEGIN Contraints of first SSTORE"%(funtcion_we_are_in))

            r_n_constraints = map(_normalize_constraint, filter(_relevant_constraint, node.constraints))

            # for c in r_n_constraints:
            #     logging.info(c)


            matches = check_for_token_pattern(state, following_sstores, r_n_constraints)

            if len(matches) > 0:
                issues.append(Issue(node.contract_name, node.function_name, None,
                           "Found a transfer like function",
                           "WUPI"))
            else:
                logging.info("Found no matching sstores")

            # logging.debug("%s: END Contraints, those where the relevant constraints"%(funtcion_we_are_in))

            # logging.debug("%s: Leading value =\n%s"%(funtcion_we_are_in, _get_value_sstore(state)))
            # logging.debug("%s: Following value =\n%s"%(funtcion_we_are_in, _get_value_sstore(following_sstores[0])))
        else: 
            logging.info("%s: FOUND SSTORE (%s), but nothing followed"%(funtcion_we_are_in, _get_value_sstore(state)))

    return issues

def check_for_token_pattern(sstore_start, following_sstores, relevant_n_constraints):
    matches = []
    op_set = set(["bvsub", "bvadd"])

    matching_constraints = check_sstore_value(sstore_start, op_set, relevant_n_constraints)

    for f_sstore in following_sstores:
        for c in matching_constraints:
            res = check_sstore_value(f_sstore, op_set - set([c["op"]]), [c["constraint"]])
            if len(res) > 0:
                matches.append({"store1": sstore_start, "store2": f_sstore, "constraint": c})

    return matches

    # must contain relevant constraint storagevalue as well as plus or minus


def check_sstore_value(sstore, s_ops, relevant_n_constraints):
    sstore_i, sstore_val = _get_value_sstore(sstore) 
    matches = []
    for constraint in relevant_n_constraints:

        # logging.debug("store")
        # logging.debug(sstore_val)
        # logging.debug("constraint")
        # logging.debug(constraint)


        # logging.debug("T"*70)
        # logging.debug(term_str(sstore_val))

        # logging.debug("\n=")
        # logging.debug(term_str(sstore_i))
        # logging.debug("T"*70)

        if sstore_i == None:
            raise Exception("AHHHLkjfklsajfdljaslfjl")

        #storage_in_term = in_term(sstore_val, lambda x: str(x) == str(constraint["gt"]))
        storage_in_term = in_term(sstore_val, lambda x: _contains_storage(x) != None) #already checked that for first store via taint analysis
        index_self_ref = in_term(sstore_val, lambda x: term_str(x) == "storage_" + term_str(sstore_i))  #check selfref, 
        calldata_in_term = in_term(sstore_val, lambda x: str(x) == str(constraint["lt"]))
        op_in_term = in_term(sstore_val, lambda x: x.decl().name() in s_ops )

        # logging.debug("storage_in_term")
        # logging.debug(storage_in_term)

        # logging.debug("calldata_in_term")
        # logging.debug(calldata_in_term)

        # logging.debug("index_self_ref")
        # logging.debug(index_self_ref)

        # logging.debug("op_in_term")
        # if op_in_term != None:
        #     logging.debug(op_in_term.decl().name())
       
        if storage_in_term != None and calldata_in_term != None  and op_in_term != None and index_self_ref != None:
            matches.append({"constraint": constraint, "op": op_in_term.decl().name()})
    
    return matches

def term_str(term):
    return str(term).replace('\n', ' ').replace('\r', '').strip()

def in_term(term, f):
    if not isinstance(term, ExprRef):
        return None
    
    if f(term):
        return term

    for i in range(term.num_args()):
        r = in_term(term.arg(i), f)
        if r != None:
            return r

    return None

def _relevant_constraint(constraint):
    # storage value must be greater or equal some other thing.
    if not isinstance(constraint, ExprRef):
        return False

    #logging.info(constraint.decl().name())
    rootOp = constraint.decl().name()

    if not(rootOp == "bvult" or \
       rootOp == "bvugt" or \
       rootOp == "bvuge" or \
       rootOp == "bvule"):
        return False

    lhs = constraint.arg(0)
    rhs = constraint.arg(1)

    # <
    if rootOp == 'bvult':
        return (_contains_calldata(lhs) and _contains_storage(rhs))
    # >
    elif rootOp == 'bvugt':
        return (_contains_calldata(rhs) and _contains_storage(lhs))
    # >=
    elif rootOp == 'bvuge':
        return (_contains_calldata(rhs) and _contains_storage(lhs))
    # <=
    elif rootOp == 'bvule':
        return (_contains_calldata(lhs) and _contains_storage(rhs))

    return True

def _normalize_constraint(constraint):
    if not isinstance(constraint, ExprRef):
        return False

    #logging.info(constraint.decl().name())
    rootOp = constraint.decl().name()

    if not(rootOp == "bvult" or \
       rootOp == "bvugt" or \
       rootOp == "bvuge" or \
       rootOp == "bvule"):
        return False

    lhs = constraint.arg(0)
    rhs = constraint.arg(1)

    # <
    if rootOp == 'bvult':
        return {"gt": rhs, "lt": lhs}
    # >
    elif rootOp == 'bvugt':
        return {"gt": lhs, "lt": rhs}
    # >=
    elif rootOp == 'bvuge':
        return {"gt": lhs, "lt": rhs}
    # <=
    elif rootOp == 'bvule':
        return {"gt": rhs, "lt": lhs}
    else:
        raise Exception("ahhhh you are soooo not normal")


def _contains_calldata(z3_term):
    #logging.debug("%s should contain calldata"%str(z3_term))
    m = re.search(r'calldata_MAIN\[([0-9]+)\]', str(z3_term))
    if(m):
        offset = m.group(1)
        ret = "calldata_MAIN[%s]"%(offset)
        #logging.debug("YES %s"%(ret))
        return ret
    else:
        #logging.debug("NO")
        return None

def _contains_storage(z3_term):
    #logging.debug("%s should contain storage"%str(z3_term))
    m = re.match(r'storage_([a-z0-9_&^]+)', str(z3_term))
    if(m):
        #logging.debug("YES")
        return True
    else:
        #logging.debug("NO")
        return None


def _get_sstore_along_the_line(statespace, node_to_start):
    return _search_children(statespace, node_to_start, None)

def _get_tainted_sstores(statespace, taints):
    for state, node in _get_states_with_opcode(statespace, "SSTORE"):
        for taint in taints:
            if _check_sstore(state, taint):
                yield state, node

def _get_states_with_opcode(statespace, opcode):
    """ Gets all (state, node) tuples in in with opcode"""
    for k in statespace.nodes:
        node = statespace.nodes[k]
        for state in node.states:
            if state.get_current_instruction()["opcode"] == opcode:
                yield state, node

def _check_usage(state, taint_result):
    """Delegates checks to _check_{instruction_name}()"""
    opcode = state.get_current_instruction()['opcode']

    if opcode == 'SSTORE':
        if _check_sstore(state, taint_result):
            return [state]
    return []


def _check_sstore(state, taint_result):
    """ Check if store operation is dependent on the result of expression"""
    assert state.get_current_instruction()['opcode'] == 'SSTORE'
    return taint_result.check(state, -2)

def _get_value_sstore(state_sstore):
    #logging.info(state_sstore.get_current_instruction()['opcode'])
    assert state_sstore.get_current_instruction()['opcode'] == 'SSTORE'

    stack = copy.deepcopy(state_sstore.mstate.stack)
    to = stack.pop()
    val = stack.pop()

    #index, value = state_sstore.mstate.stack[-1], state_sstore.mstate.stack[-2]
    return to, val

def _search_children(statespace, node, constraint=[], index=0, depth=0, max_depth=64):
    """
    Checks the statespace for children states, with JUMPI or SSTORE instuctions,
    for dependency on expression
    :param statespace: The statespace to explore
    :param node: Current node to explore from
    :param index: Current state index node.states[index] == current_state
    :param depth: Current depth level
    :param max_depth: Max depth to explore
    :return: List of states that match the opcodes and are dependent on expression
    """
    logging.debug("SEARCHING SSTORE used after %d", node.uid)

    results = []

    if depth >= max_depth:
        return []

    # Explore current node from index
    for j in range(index, len(node.states)):
        current_state = node.states[j]
        current_instruction = current_state.get_current_instruction()
        if current_instruction['opcode'] in ['SSTORE']:
            element = [current_state]
            if _check_requires(element[0], node, statespace, constraint):
                 continue
            results += element

    # Recursively search children
    children = \
        [
            statespace.nodes[edge.node_to]
            for edge in statespace.edges
            if edge.node_from == node.uid
            # and _try_constraints(statespace.nodes[edge.node_to].constraints, constraint) is not None
        ]

    for child in children:
        results += _search_children(statespace, child, depth=depth + 1, max_depth=max_depth)

    return results

def _check_requires(state, node, statespace, constraint):
    """Checks if usage of overflowed statement results in a revert statement"""
    instruction = state.get_current_instruction()
    if instruction['opcode'] is not "JUMPI":
        return False
    children = [
            statespace.nodes[edge.node_to]
            for edge in statespace.edges
            if edge.node_from == node.uid
        ]

    for child in children:
        opcodes = [s.get_current_instruction()['opcode'] for s in child.states]
        if "REVERT" in opcodes or "ASSERT_FAIL" in opcodes:
            return True
    # I added the following case, bc of false positives if the max depth is not high enough
    if len(children) == 0:
        return True
    return False

################# NOT USED

def _dependent_on_storage(expression):
    """ Checks if expression is dependent on a storage symbol and returns the influencing storages"""
    pattern = re.compile(r"storage_[a-z0-9_&^]*[0-9]+")
    return pattern.findall(str(simplify(expression)))


def _get_storage_variable(storage, state):
    """
    Get storage z3 object given storage name and the state
    :param storage: storage name example: storage_0
    :param state: state to retrieve the variable from
    :return: z3 object representing storage
    """
    index = int(re.search('[0-9]+', storage).group())
    try:
        return state.environment.active_account.storage[index]
    except KeyError:
        return None


def _can_change(constraints, variable):
    """ Checks if the variable can change given some constraints """
    _constraints = copy.deepcopy(constraints)
    try:
        model = solver.get_model(_constraints)
    except UnsatError:
        return False
    try:
        initial_value = int(str(model.eval(variable, model_completion=True)))
        return _try_constraints(constraints, [variable != initial_value]) is not None
    except AttributeError:
        return False

def _get_influencing_storages(call):
    """ Examines a Call object and returns an iterator of all storages that influence the call value or direction"""
    state = call.state
    node = call.node

    # Get relevant storages
    to, value = call.to, call.value
    storages = []
    if to.type == VarType.SYMBOLIC:
        storages += _dependent_on_storage(to.val)
    if value.type == VarType.SYMBOLIC:
        storages += _dependent_on_storage(value.val)

    # See if they can change within the constraints of the node
    for storage in storages:
        variable = _get_storage_variable(storage, state)
        can_change = _can_change(node.constraints, variable)
        if can_change:
            yield storage


def _get_influencing_sstores(statespace, interesting_storages):
    """ Gets sstore (state, node) tuples that write to interesting_storages"""
    for sstore_state, node in _get_states_with_opcode(statespace, 'SSTORE'):
        index, value = sstore_state.mstate.stack[-1], sstore_state.mstate.stack[-2]
        try:
            index = util.get_concrete_int(index)
        except AttributeError:
            index = str(index)
        if "storage_{}".format(index) not in interesting_storages:
            continue

        yield sstore_state, node


# TODO: remove
def _try_constraints(constraints, new_constraints):
    """
    Tries new constraints
    :return Model if satisfiable otherwise None
    """
    _constraints = copy.deepcopy(constraints)
    for constraint in new_constraints:
        _constraints.append(copy.deepcopy(constraint))
    try:
        model = solver.get_model(_constraints)
        return model
    except UnsatError:
        return None
