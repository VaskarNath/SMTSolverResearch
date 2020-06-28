
from six.moves import cStringIO
import pysmt.environment
import pysmt.smtlib.parser
import pysmt.smtlib.script
from pysmt.smtlib.parser import SmtLibParser
from pysmt.fnode import FNode
from pysmt.smtlib.script import SmtLibCommand
from pysmt.shortcuts import *
from pysmt.typing import *

import sys
sys.path.append(".")
from var import VariableInfusion


DEMO_SMTLIB=\
"""
(set-logic QF_LIA)
(declare-fun p () Int)
(declare-fun q () Int)
(declare-fun x () Bool)
(declare-fun z () Bool)
(define-fun .def_1 () Bool (! (and x z) :cost 1))
(assert (=> x (> p q)))
(check-sat)
(push)
(assert (=> z (> q p)))
(check-sat)
(assert .def_1)
(check-sat)
(pop)
(check-sat)
"""


def formula_to_change_two_args(formula, ops):
    lst = []
    for arg in formula.args():
        lst.append(arg)
    return ops(lst[0], lst[1])


def formula_to_change_symbol(formula, ops):
    lst = []
    for arg in formula.args():
        lst.append(arg)
    return ops(lst[0], lst[1])


def change_script(script, fn, ops):
    for cmd in script:
        for i in range(len(cmd.args)):
            to_search = [cmd.args[i]]
            if isinstance(cmd.args[i], pysmt.fnode.FNode):
                while len(to_search) != 0:
                    curr = to_search.pop(0)
                    if fn(curr):
                        new_function = formula_to_change_two_args(curr, ops)
                        cmd.args[i] = cmd.args[i].substitute({curr: new_function})
                    for arg in curr.args():
                        to_search.append(arg)


def add_var(script, a, type):
    var = Symbol(a, type)
    c = SmtLibCommand(name='declare-fun', args=(var,))
    script.commands.insert(1, c)


def variable_inversion(script, ops):
    add_var(script, 'y', INT)
    for cmd in script:
        if cmd.name == 'declare-fun':
            continue
        for i in range(len(cmd.args)):
            to_search = [cmd.args[i]]
            if isinstance(cmd.args[i], pysmt.fnode.FNode):
                while len(to_search) != 0:
                    curr = to_search.pop(0)
                    if FNode.is_symbol(curr):
                        if curr in ops:
                            cmd.args[i] = cmd.args[i].substitute(ops)
                            break
                    for arg in curr.args():
                        to_search.append(arg)


def get_all_symbols(script):
    result = []
    for cmd in script:
        if cmd.name == 'declare-fun':
            for symbol in cmd.args:
                result.append(symbol)
    return result


def sat(script):
    solver = Solver(name='z3')
    for cmd in script:
        if cmd.name == 'assert':
            solver.add_assertion(cmd.args[0])
        elif cmd.name == 'check-sat':
            pass
            print(solver.solve())
    return solver.solve()


def get_all_number_symbols(script):
    real = []
    int = []
    for cmd in script:
        if cmd.name == 'declare-fun':
            if FNode.get_type(cmd.args[0]) == INT:
                int.append(cmd.args[0])
            if FNode.get_type(cmd.args[0]) == REAL:
                real.append(cmd.args[0])
    return int, real


if __name__ == "__main__":
    f = VariableInfusion([])
    parser = SmtLibParser()
    script = parser.get_script(cStringIO(DEMO_SMTLIB))
    buf_out = cStringIO()
    script.serialize(buf_out, daggify=False)

    variable_inversion(script, {Symbol('p', INT) : Times(Symbol('y', INT), Symbol('q', INT)),
                                Symbol('q', INT) : Div(Symbol('p', INT), Symbol('y', INT))})

    # print(get_all_number_symbols(script, [REAL, INT]))
    # print(get_all_symbols(script))

    # print(get_all_symbols(script))
    script.serialize(buf_out, daggify=False)
    print(buf_out.getvalue())

