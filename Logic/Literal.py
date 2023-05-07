from .LogicInterface import Prop

class Literal(Prop):
    def __init__(self, name, negFlag=False):
        self.name = name
        self.negated = negFlag

    def __str__(self):
        if self.negated is False:
            return f"{self.name}"
        else:
            return f"~{self.name}"

    def evaluate(self, current_permutation):
        return not current_permutation[self.name] if self.negated else current_permutation[self.name]

    def get_all_literals(self, alphabet):
        if isinstance(alphabet, dict):
            if alphabet[self.name] is not None:
                alphabet[self.name] = self
        else:
            raise ValueError("alphabet is not a dict")
