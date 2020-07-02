from six.moves import cStringIO
import pysmt.environment
import pysmt.smtlib.parser
import pysmt.smtlib.script
import pysmt.smtlib.printers
import copy


from pysmt.smtlib.parser import SmtLibParser
from pysmt.fnode import FNode, FNodeContent
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
        self.node_num = 0
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
        print(self.symbols)
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
        func = []
        z = self.create_symbol(self.get_valid_var(), INT)
        c = self.create_symbol('c', INT)
        for i in range(len(self.int)):
            for j in range(i + 1, len(self.int)):
                x = self.int[i]
                y = self.int[j]
                func.append(Equals(z, Plus(Plus(x, c), y)))
                result.append({x: Minus(Minus(z, c), y), y: Minus(Minus(z, c), x)})
                return result, [z, c], func

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

    def add_func(self, script, func):
        c = SmtLibCommand(name='assert', args=(func,))
        script.commands.insert(-2, c)

    def variable_inversion(self, script, sub, s):
        for symbol in s:
            self.add_var(script, symbol)
        for cmd in script:
            if cmd.name == 'declare-fun':
                continue
            for i in range(len(cmd.args)):
                if isinstance(cmd.args[i], pysmt.fnode.FNode):
                    print(cmd.args[i], ": ", self.to_sub(cmd.args[i], sub))
                    cmd.args[i] = cmd.args[i].substitute(sub)
        return script

    def cpy_tree(self, root, subs, to_sub):
        if root == None:
            return None, []
        elif root.is_symbol():
            to_sub = []
            res = FNode(FNodeContent(root._content.node_type, (), (root._content.payload[0], root._content.payload[1])), self.node_num)
            if root in subs:
                to_sub = [res]
            self.node_num += 1
            return res, to_sub
        else:
            childrens = []
            to_sub = []
            for node in root._content.args:
                cpy, sub = self.cpy_tree(node, subs, [])
                childrens.append(cpy)
                to_sub.extend(sub)
            node_id = self.node_num
            self.node_num += 1
            content = FNodeContent(root._content.node_type, tuple(childrens), [None])
            res = FNode(content, node_id)
            return res, to_sub
    
    def change_tree(self, root, sub, sub_dict):
        if root == None:
            return None
        elif root.is_symbol():
            if root._node_id in sub_dict:
                if sub_dict[root._node_id] == 1:
                    for key in sub:
                        if key.symbol_name() == root.symbol_name():
                            return sub[key]  
            return root   
        else:
            childrens = []
            for node in root._content.args:
                cpy = self.change_tree(node, sub, sub_dict)
                childrens.append(cpy)
            node_id = root._node_id
            content = FNodeContent(root._content.node_type, tuple(childrens), [None])
            res = FNode(content, node_id)
            return res
    

    def diff_combinations(self, length):
        if length == 0:
            return []
        if length == 1:
            return [[1], [0]]
        lst = self.diff_combinations(length - 1)
        res = []
        for comb in lst:
            lst1 = comb.copy()
            lst1.insert(0, 1)
            lst2 = comb.copy()
            lst2.insert(0, 0)
            res.append(lst1) 
            res.append(lst2) 
        return res


    def nodes_to_sub_variations(self, script, subs):
        res = []
        all_sub = []
        for cmd in script:
            if cmd.name == 'declare-fun' or cmd.name == 'declare-const':
                continue
            for i in range(len(cmd.args)):
                formula = cmd.args[i]
                if isinstance(formula, pysmt.formula.FNode):
                    cpy, to_sub = self.cpy_tree(formula, subs, [])
                    cmd.args[i] = cpy
                    all_sub.extend(to_sub)
        combinations = self.diff_combinations(len(all_sub))
        for comb in combinations:
            d = {}
            for i in range(len(all_sub)):
                d[all_sub[i]._node_id] = comb[i]
            res.append(d)
        return res

    def sub_nodes(self, script, sub, sub_dict, s):
        for symbol in s:
            self.add_var(script, symbol)
        for cmd in script:
            if cmd.name == 'declare-fun' or cmd.name == 'declare-const':
                continue
            for i in range(len(cmd.args)):
                formula = cmd.args[i]
                if isinstance(formula, pysmt.formula.FNode):
                    cmd.args[i] = self.change_tree(formula, sub, sub_dict)

    def get_instances(self, subs, new_symbol, func):
        result = []
        for i in range(len(subs)):
            sub = subs[i]
            script = self.script_copy()
            nodes_combination = self.nodes_to_sub_variations(script, sub)
            for sub_dict in nodes_combination:
                inner_script = copy.deepcopy(script)
                self.sub_nodes(inner_script, sub, sub_dict, new_symbol)
                result.append(inner_script)
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

    f = VariableInfusion(DEMO_SMTLIB)
    subs, s = f.plus()
    instances = f.get_instances(subs, s, None)
    f.print_instances(instances)








