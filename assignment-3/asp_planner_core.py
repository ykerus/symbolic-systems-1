from planning import PlanningProblem, Action, Expr, expr
import planning

import clingo

def solve_planning_problem_using_ASP(planning_problem,t_max):
    """
    If there is a plan of length at most t_max that achieves the goals of a given planning problem,
    starting from the initial state in the planning problem, returns such a plan of minimal length.
    If no such plan exists of length at most t_max, returns None.

    Finding a shortest plan is done by encoding the problem into ASP, calling clingo to find an
    optimized answer set of the constructed logic program, and extracting a shortest plan from this
    optimized answer set.

    Parameters:
        planning_problem (PlanningProblem): Planning problem for which a shortest plan is to be found.
        t_max (int): The upper bound on the length of plans to consider.

    Returns:
        (list(Expr)): A list of expressions (each of which specifies a ground action) that composes
        a shortest plan for planning_problem (if some plan of length at most t_max exists),
        and None otherwise.
    """
    def convert(expression, neg=False):
        # converts expression of string format Expr to ASP
        # and converts it back if expression is already in ASP format
        string = str(expression)[1:] if neg else str(expression)
        converted, prev = "", ""
        for i, e in enumerate(string):
            if e.isupper() and prev != "_":
                converted += f"_{e.lower()}"
            elif (prev == " " or prev == "(") and e.islower():
                converted += f"_{e.upper()}"
            elif e == "_" and string[i+1].islower():
                converted += string[i+1].upper()
            elif e == "_":
                converted += string[i+1].lower()
            elif e == "~":
                converted += "-"
            elif e == "-":
                converted += "~"
            elif prev != "_":
                converted += e
            prev = e
        return converted

    def variables(args):
        # checks if any of the arguments is a (non-ground) variable
        for argtup in args:
            for arg in argtup:
                if (str(arg)[0].islower() and str(arg)[0] != "~") or \
                        (len(str(arg)) > 1 and str(arg)[1].islower() and str(arg)[0] == "~"):
                    return True
        return False

    actions = [[]]  # list within list to make it accessible for "on_model"
    def on_model(model):
        # for the optimal model: sort actions and build a list to return
        if model.optimality_proven:
            sorted_model = [str(atom) for atom in model.symbols(shown=True)]
            sorted_actions = ["" for i in range(len(sorted_model))]
            for i in range(len(sorted_model)):
                sorted_actions[int(sorted_model[i].split(",")[0].split("(")[-1])-1] = sorted_model[i]
            actions[0] += [convert(", ".join(atom[:-1].split(",")[1:])) for atom in sorted_actions]

    # definine initial state for our planning problem (i.e. the state at timestep 0)
    program = "".join([f"state(0,{convert(init)}).\n" for init in planning_problem.initial])

    for action in planning_problem.actions:
        # extract preconditions for actions from the problem
        preconds = [convert(precond) for precond in action.precond if str(precond)[0] != "~"]
        preneg = [convert(precond, neg=True) for precond in action.precond if str(precond)[0] == "~"]

        # define valid actions for each step, given the preconditions and the previous state
        program += f"action(T,{convert(action)}) :- step(T)"
        program += "," + ",".join([f"state(T-1,{precond})" for precond in preconds]) if len(preconds) > 0 else ""
        program += "," + ",".join([f"not state(T-1,{precond})" for precond in preneg]) if len(preneg) > 0 else ""
        program += f".\n"

        # define the effects of each action
        for effect in [convert(effect) for effect in action.effect if str(effect)[0] != "~"]:
            program += f"effect({convert(action)}, {effect}) :- action(T,{convert(action)}).\n"
        for undo in [convert(effect, neg=True) for effect in action.effect if str(effect)[0] == "~"]:
            program += f"undo({convert(action)}, {undo}) :- action(T,{convert(action)}).\n"

    # goals are positive goals: expressions without ~
    goals = [convert(goal) for goal in planning_problem.goals if str(goal)[0] != "~"]
    # goalsneg are negative goals: expressions with ~
    goalsneg = [convert(goal, neg=True) for goal in planning_problem.goals if str(goal)[0] == "~"]
    goal_args = [goal.args for goal in planning_problem.goals] # all args occuring in all goals
    if variables(goal_args):
        # if the goal contains (non-ground) variables, solve as follows
        # note: the following piece of code will work for any input, not only for goals with variables
        program += "goal :- not usedstep(T+1)," + ",".join([f"state(T,{goal})" for goal in goals])
        program += "," + ",".join([f"not state(T,{goal})" for goal in goalsneg]) if len(goalsneg) > 0 else ""
        program += ".\n"  # the goal is achieved if in the last step all conditions are met
        program += ":- not goal. \n"  # the goal must be achieved
    else:
        # if the goal only contains ground variables/atoms, solve as follows
        # note: this will not work if the goal contains variables, but it works much more efficient (therefore included)
        for goal in goals:
            program += f"goal({goal}).\n"
            program += ":- not usedstep(1), goal(G), not state(0, G).\n"  # if goal is not met at T=0, we must act
            program += ":- goal(G), usedstep(T), not usedstep(T+1), not state(T,G).\n"  # the goal must be achieved
        for goalneg in goalsneg:
            program += f"goalneg({goalneg}).\n"
            program += ":- not usedstep(1), goalneg(G), state(0, G).\n" # if goal is not met at T=0, we must act
            program += ":- goalneg(G), usedstep(T), not usedstep(T+1), state(T,G).\n"  # the goal must be achieved

    program += f"""
        step(1..{t_max}).  % define timesteps up to t_max """ + """
        {usedstep(T) : step(T)}.  % choose in which timesteps to act

        undo(A,E) :- undo(A,E).  % avoids warnings
        1{act(T,A) : action(T,A)}1 :- usedstep(T).  % at each timestep choose action
        state(T,E) :- act(T,A), state(T-1,E), not undo(A,E).  % copy prev state expression if not undone
        state(T,E) :- act(T,A), effect(A,E).  % update state with new effects

        :- usedstep(T), not usedstep(T-1), T>1.  % avoid "gaps" in steps

        #minimize {T : usedstep(T)}.  % we want to use the least possible number of actions
        #show act/2.  % we are only interested in the actions taken to reach the goal
    """

    control = clingo.Control()
    control.add("base", [], program)
    control.ground([("base", [])])
    control.configuration.solve.opt_mode = "optN"

    control.configuration.solve.models = 1
    answer = control.solve(on_model=on_model)

    if answer.satisfiable:
        # if a solution is found, return actions
        return actions[0]
    return None  # if no solution is found