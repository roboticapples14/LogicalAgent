from AI.Agent import Agent
from sympy import sympify

if __name__ == "__main__":
    run = True
    a = Agent(set())
    while(run):
        print("-----------Provide Input------------")
        print("1: for revision")
        print("2: for printing current belief base")
        print("3: Exit")
        inp = input("Action: \n")
        if inp == "1":
            print("provide string describing propositional logic")
            print("of which should be revised by the logical agent")
            print("in compliance with sympy string syntax")
            print(f"Current Belief Base: {a.belief_base}")
            try:
                logic_input = sympify(input("Logic: "))
            except:
                print("invalid input")
                continue

            a.add_predict(logic_input)
            print(f"Revised Belief Base: {a.belief_base}\n")
        elif inp == "2":
            print(f"Current Belief Base: {a.belief_base}\n")
        elif inp == "3":
            print("you have chosen to exit, bye")
            run = False
        else:
            print("invalid input")
            
