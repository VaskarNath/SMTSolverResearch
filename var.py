from six.moves import cStringIO
import pysmt.environment
import pysmt.smtlib.parser
import pysmt.smtlib.script
import pysmt.smtlib.printers


from pysmt.smtlib.parser import SmtLibParser
from pysmt.fnode import FNode
from pysmt.smtlib.script import SmtLibCommand
from pysmt.shortcuts import *
from pysmt.typing import *


class VariableInfusion():

    def __init__(self, string):
        self.script_string = string
        parser = SmtLibParser()
        self.script = parser.get_script(cStringIO(string))
        self.symbols = self.get_all_symbols()
        self.int, self.real = self.get_all_number_symbols()
        # self.is_sat = self.sat(self.script)


    def create_symbol(self, a, type):
        self.symbols.append(Symbol(a, type))
        return Symbol(a, type)

    def script_copy(self):
        parser = SmtLibParser()
        return parser.get_script(cStringIO(self.script_string))

    def get_all_symbols(self):
        result = []
        for cmd in self.script:
            if cmd.name == 'declare-fun' or cmd.name == 'declare-const':
                for symbol in cmd.args:
                    result.append(symbol)
        return result

    def get_all_number_symbols(self):
        real = []
        int = []
        for cmd in self.script:
            if cmd.name == 'declare-fun':
                if FNode.get_type(cmd.args[0]) == INT:
                    int.append(cmd.args[0])
                if FNode.get_type(cmd.args[0]) == REAL:
                    real.append(cmd.args[0])
        return int, real

    def get_valid_var(self):
        alphabets = "a b c d e f g h i j k l m n o p q r s t u v w x y z".split(" ")
        symbol_names = [symbol.symbol_name() for symbol in self.symbols]
        for i in alphabets:
            if i not in symbol_names:
                return i
        raise IndexError

    def times(self):
        result = []
        new_symbol = self.create_symbol(self.get_valid_var(), INT)
        for i in range(len(self.int)):
            for j in range(i + 1, len(self.int)):
                a = self.int[i]
                b = self.int[j]
                result.append({a: Div(new_symbol, b), b: Div(new_symbol, a)})
        return result, [new_symbol]

    def division(self):
        result = []
        new_symbol = self.create_symbol(self.get_valid_var(), INT)
        for i in range(len(self.int)):
            for j in range(i + 1, len(self.int)):
                a = self.int[i]
                b = self.int[j]
                result.append({a: Times(new_symbol, b), b: Div(a, new_symbol)})
                result.append({a: Div(b, new_symbol), b: Times(a, new_symbol)})
        return result, [new_symbol]

    def plus(self):
        result = []
        new_symbol = self.create_symbol(self.get_valid_var(), INT)
        for i in range(len(self.int)):
            for j in range(i + 1, len(self.int)):
                a = self.int[i]
                b = self.int[j]
                result.append({a: Minus(new_symbol, b), b: Minus(new_symbol, a)})
        return result, [new_symbol]

    def minus(self):
        result = []
        new_symbol = self.create_symbol(self.get_valid_var(), INT)
        for i in range(len(self.int)):
            for j in range(i + 1, len(self.int)):
                a = self.int[i]
                b = self.int[j]
                result.append({a: Plus(new_symbol, b), b: Minus(a, new_symbol)})
                result.append({a: Minus(b, new_symbol), b: Plus(a, new_symbol)})
                return result, [new_symbol]

    def add_constant(self):
        result = []
        z = self.create_symbol(self.get_valid_var(), INT)
        c = self.create_symbol('c', INT)
        for i in range(len(self.int)):
            for j in range(i + 1, len(self.int)):
                x = self.int[i]
                y = self.int[j]
                result.append({x: Minus(Minus(z, c), y), y: Minus(Minus(z, c), x)})
                return result, [z, c]

    def mult_constant(self):
        result = []
        z = self.create_symbol(self.get_valid_var(), INT)
        c1 = self.create_symbol('c1', INT)
        c2 = self.create_symbol('c2', INT)
        c3 = self.create_symbol('c3', INT)
        for i in range(len(self.int)):
            for j in range(i + 1, len(self.int)):
                x = self.int[i]
                y = self.int[j]
                result.append({x: Div(Minus(Minus(z, Times(c2, y)), c3), c1),
                               y: Div(Minus(Minus(z, Times(c1, x)), c3), c2)})
                return result, [z, c1, c2, c3]

    def add_var(self, script, s):
        c = SmtLibCommand(name='declare-fun', args=(s,))
        script.commands.insert(1, c)

    def variable_inversion(self, script, sub, s):
        for symbol in s:
            self.add_var(script, symbol)
        for cmd in script:
            if cmd.name == 'declare-fun':
                continue
            for i in range(len(cmd.args)):
                if isinstance(cmd.args[i], pysmt.fnode.FNode):
                    cmd.args[i] = cmd.args[i].substitute(sub)
        return script

    def get_instances(self, subs, new_symbol):
        result = []
        for sub in subs:
            script = self.script_copy()
            result.append(self.variable_inversion(script, sub, new_symbol))
        return result

    def print_instances(self, instances):
        i = 1
        for instance in instances:
            buf_out = cStringIO()
            instance.serialize(buf_out, daggify=False)
            print("Instance ", i, ": ")
            print(buf_out.getvalue())
            print("SAT: ", self.sat(instance))
            print("*" * 50, "\n")
            i += 1

    def sat(self, script):
        solver = Solver(name='z3')
        for cmd in script:
            if cmd.name == 'assert':
                solver.add_assertion(cmd.args[0])
        return solver.solve()


if __name__ == "__main__":
    DEMO_SMTLIB = \
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

    f = VariableInfusion(DEMO_SMTLIB)
    subs, s = f.mult_constant()
    instances = f.get_instances(subs, s)
    f.print_instances(instances)








