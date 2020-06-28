from pysmt.walkers.tree import Walker
from pysmt.walkers import DagWalker
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






if __name__ == "__main__":
    DEMO_SMTLIB = \
        """
        (set-logic QF_LIA)
        (declare-const p Int)
        (declare-const q Int)
        (declare-const x Bool)
        (declare-const z Bool)
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
    parser = SmtLibParser()
    script = parser.get_script(cStringIO(DEMO_SMTLIB))
    buf_out = cStringIO()

    f = DagWalker()

    for cmd in script:
        if cmd.name != "define-fun":
            continue
        for args in cmd.args:
            if isinstance(args, pysmt.fnode.FNode):
                print(args)
                print(f.iter_walk(args))
