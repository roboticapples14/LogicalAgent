from .LogicInterface import Prop
from enum import Enum

class Operator(Enum):
    CONJUNCTION = "AND"
    DISJUNCTION = "OR"
    IMPLICATION = "->"
    BICONDITIONAL = "<->"


class Expression(Prop):
    def __init__(self, propLeft, operator, propRight):
        self.propRight = propRight
        self.operator = operator
        self.propLeft = propLeft

    def __str__(self):
        return f"{self.propLeft.__str__()} {self.operator.value} {self.propRight.__str__()}"

    def evaluate(self, current_permutation) -> bool:
        leftValue = self.propLeft.evaluate(current_permutation)
        rightValue = self.propRight.evaluate(current_permutation)

        match self.operator:
            case Operator.CONJUNCTION: return leftValue and rightValue
            case Operator.DISJUNCTION: return leftValue or rightValue
            #according to CNF
            case Operator.IMPLICATION: return not leftValue or rightValue
            case Operator.BICONDITIONAL: return (not leftValue or rightValue) and (leftValue or not rightValue)

    def get_all_literals(self, alphabet):
        self.propLeft.get_all_literals(alphabet)
        self.propRight.get_all_literals(alphabet)




