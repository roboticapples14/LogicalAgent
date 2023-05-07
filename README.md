This project contains a logical agent which maintains a belief base, and is capable of revising its beliefs when proposed new information

## Overview:
The Agent is instantiated with a set of sympy logical propositions, which informs the agent's initial beliefs.
Thereafter, any new information φ given to the agent will go through this pipeline:
    1. If the KB is empty, add φ
    2. Otherwise, perform resolution to evaluate if KB entails ~φ
    3. If KB does not entail ~φ, add φ
    4. Otherwise, use Levi identity to add φ by contracting contradicting beliefs and extending the belief base
        5. To find contradicting beliefs, use partial meet contraction with a heuristic which prioritizes beliefs with less entrenchment

## How to run
### Prerequisites:
* [Sympy](https://pypi.org/project/sympy/)

### Installation:
- Run main.py on Python Interpreter 3.9

### User interface
- Interact with the agent through a loop, choosing from 3 choices: 
    - 1 for revision (adding a new belief to the agent)
    - 2 for printing current belief base
    - 3 to exit

### Logic syntax
When adding a new belief for revision, please provide a string describing propositional logic in compliance with sympy string syntax (See https://docs.sympy.org/latest/modules/logic.html)
