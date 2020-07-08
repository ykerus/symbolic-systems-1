
from pysat.formula import CNF
from pysat.solvers import MinisatGH

from ortools.sat.python import cp_model

import gurobipy as gp
from gurobipy import GRB

import clingo



###
### Propagation function to be used in the recursive sudoku solver
###
def propagate(sudoku_possible_values,k):

    empty = True  # assume we are dealing with an empty suduko
    # try to disprove this is the case
    for i in range(k*k):
        for j in range(k*k):
            # if the number of possible values of cell (i,j) is less than the total number of possible values
            if len(sudoku_possible_values[i][j]) < k*k:
                empty = False  # then we have disproven that we are dealing with an empty sudoku
                break  # exit the for-loop
        if not empty:
            break
    if empty:
        # dealing with an empty sudoku: solve efficiently
        sudoku_possible_values = [[] for i in range(k*k)]
        values = list(range(1, k*k+1))
        for i1 in range(k):  # for each block along vertical axis
            for i2 in range(k):  # for each row within that block
                for v in values:  # we add values in each column that have no conflicts
                    sudoku_possible_values[i1*k + i2].append([v])
                values = values[-k:] + values[:-k]  # edit values to prevent conflicts
            values = values[-1:] + values[:-1]  # edit values to prevent conflicts
        return sudoku_possible_values

    # not dealing with empty sudoku: filter the possible values based on constraints
    checked = [] # keep track of which cells we used to remove conflicts
    change = True  # keep iteraterating as long as something changes in the sudoku
    # note: this can be done more efficiently if we keep track which cells become changed instead of which we used
    while change:
        change = False
        for i in range(k*k):
            for j in range(k*k):
                possibilities = sudoku_possible_values[i][j]  # possbile values for cell (i,j)
                if len(possibilities) == 1 and (i,j) not in checked:
                    checked.append((i,j))

                    value = possibilities[0]  # value we are certain of

                    # iterate over elements this value has influence on (in same row and column)
                    for idx in range(k*k):
                        # remove conflicting element in the same column
                        if idx != i and value in sudoku_possible_values[idx][j]:
                            sudoku_possible_values[idx][j].remove(value)
                            if len(sudoku_possible_values[idx][j]) == 1: # if number of possible values becomes 1
                                change = True # iterate again
                        # remove conflicting element in the same row
                        if idx != j and value in sudoku_possible_values[i][idx]:
                            sudoku_possible_values[i][idx].remove(value)
                            if len(sudoku_possible_values[i][idx]) == 1: # if number of possible values becomes 1
                                change = True # iterate again

                    # remove conflicting elements in the same block
                    for b1 in range(k * int(i / k), k + k * int(i / k)):  # row
                        for b2 in range(k * int(j / k), k + k * int(j / k)):  # column
                            if (b1, b2) != (i, j) and value in sudoku_possible_values[b1][b2]:
                                sudoku_possible_values[b1][b2].remove(value)

    return sudoku_possible_values

###
### Solver that uses SAT encoding
###
def solve_sudoku_SAT(sudoku,k):

    # give each possible value for cell (i, j) a (boolean) variable, resulting in in total k^6 variables
    variables = [[[v + k*k * (k*k * i + j) for v in range(1, k*k+1)] for j in range(k*k)] for i in range(k*k)]

    formula = CNF()

    # iterate over rows and columns
    for i in range(k*k):

        # keep track of which variables belong to the row and column and to which values v
        row_vars = [[] for v in range(k * k)]
        col_vars = [[] for v in range(k * k)]

        for j in range(k*k):
            if sudoku[i][j] > 0:
                # values we are certain of are added as unit clause
                formula.append([variables[i][j][sudoku[i][j]-1]])

            # each cell must contain a value
            formula.append(variables[i][j]) # this says: one of the variables belonging to (i,j) must be true
            for v1 in range(k*k):
                row_vars[v1].append(variables[i][j][v1])  # save the variable belonging to the row for each value
                col_vars[v1].append(variables[j][i][v1])  # same for the column: note the swapped i and j

                for v2 in range(v1+1, k*k):
                    # prevent cells from having multiple values
                    # in cell (i,j) any two variables v1, v2 (v1 != v2) cannot both be true
                    formula.append([-variables[i][j][v1], -variables[i][j][v2]])

        for v in range(k*k):
            # each row and column must contain each possible value
            formula.append(row_vars[v]) # for each possible value v, one corresponding variable must be true in row i
            formula.append(col_vars[v]) # same for the column

            for v1 in range(k*k):
                for v2 in range(v1+1, k*k):
                    # and values in rows and columns cannot appear more than once
                    # even though this is already implied, adding these lines speeds up the search process
                    formula.append([-row_vars[v][v1], -row_vars[v][v2]])
                    formula.append([-col_vars[v][v1], -col_vars[v][v2]])

    # iterate over blocks
    for b1 in range(k):  # block vertical index
        for b2 in range(k):  # block horizontal index
            # keep track of which variables belong to the block and to which values v
            block_vars = [[] for v in range(k * k)]
            for i in range(k * b1, k + k * b1):  # row
                for j in range(k * b2, k + k * b2):  # column
                    for v in range(k*k):  # value
                        block_vars[v].append(variables[i][j][v])
            for v in range(k*k):
                # the block must contain every possible value once
                formula.append(block_vars[v])
                for v1 in range(k*k):
                    for v2 in range(v1+1, k*k):
                        # and two values in the block cannot be the same
                        formula.append([-block_vars[v][v1], -block_vars[v][v2]])

    solver = MinisatGH()
    solver.append_formula(formula)

    answer = solver.solve()

    if answer:
        # if a solution is found
        # we convert the variables back to indices (i,j) and a value v
        solution = [[0 for j in range(k * k)] for i in range(k * k)]  # empty k*k x k*k solution grid
        for l in solver.get_model(): # for each variable l in the model
            if l > 0:  # variable l is true
                idx = l - 1  # this makes indexing easier
                i = int(idx / k**4)  # row index
                j = int(idx / (k*k) % (k*k))  # column index
                v = idx % (k*k) + 1  # value
                solution[i][j] = v
        return solution
    return None # if no solution is found

###
### Solver that uses CSP encoding
###
def solve_sudoku_CSP(sudoku,k):

    model = cp_model.CpModel()

    # using IntVars with a domain from 1 to and including 9 takes too much computation time
    # so define BoorVars for all possible values for each cell (i,j) (in total k^6 variables)
    variables = [[[model.NewBoolVar(f"x_{i}_{j}_{v}") for v in range(k*k)] for j in range(k*k)] for i in range(k*k)]

    # iterate over rows and columns
    for i in range(k*k):

        # keep track of which variables belong to the row and column and which values v
        row_vars = [[] for v in range(k * k)]
        col_vars = [[] for v in range(k * k)]

        for j in range(k*k):
            if sudoku[i][j] > 0:
                # constrain variable corresponding to given sudoku value to be true
                model.Add(variables[i][j][sudoku[i][j] - 1] == True)
                for v in [n for n in range(k*k) if n != sudoku[i][j] - 1]:
                    # and set each variable corresponding to other values for this cell to false
                    model.Add(variables[i][j][v] == False)

            # exacly one value must be chosen per cell
            model.Add(sum(variables[i][j]) == 1)

            for v in range(k*k):
                row_vars[v].append(variables[i][j][v])  # save the variable belonging to the row for each value
                col_vars[v].append(variables[j][i][v])  # same for column: note the swapped i and j
        for v in range(k*k):
            # each row and column must contain every possible value once
            model.Add(sum(row_vars[v]) == 1)
            model.Add(sum(col_vars[v]) == 1)

    # iterate over blocks
    for b1 in range(k):  # block vertical index
        for b2 in range(k):  # block horizontal index
            # keep track of which variables belong to the block and which value v
            block_vars = [[] for v in range(k * k)]
            for i in range(k * b1, k + k * b1):  # row
                for j in range(k * b2, k + k * b2):  # column
                    for v in range(k * k):  # value
                        block_vars[v].append(variables[i][j][v])
            for v in range(k * k):
                # the block must contain every possible value once
                model.Add(sum(block_vars[v]) == 1)

    solver = cp_model.CpSolver()
    answer = solver.Solve(model)

    if answer == cp_model.FEASIBLE:
        # if a solution is found
        solution = [[0 for j in range(k*k)] for i in range(k*k)]  # empty k*k x k*k solution grid
        for i in range(k*k):
            for j in range(k*k):
                for v in range(k*k):
                    # if a variable is true, we save its corresponding value for cell (i,j) in the solution
                    if solver.Value(variables[i][j][v]):
                        solution[i][j] = v + 1
        return solution
    return None # if no solution was found

###
### Solver that uses ASP encoding
###
def solve_sudoku_ASP(sudoku,k):
    def on_model(model):
        for atom in model.symbols(shown=True):
            # extract the solution from the model
            # convert clingo.Symbol to int via string (otherwise it doesn't work)
            i, j, v = [int(str(arg)) for arg in atom.arguments]
            solution[i][j] = v

    asp_program = f"""
        i(0..{k * k-1}).  % row indices
        j(0..{k * k-1}).  % column indices
        v(1..{k * k}).    % possible cell values

        % using section 3.1.11 from the guide https://github.com/potassco/guide/releases/tag/v2.2.0 about the use of colons
        x(I,J,V):v(V) :- i(I), j(J).  % if there is a row I and column J, cell (I, J) in the sudoku must get a value V
        :- x(I,J,V1), x(I,J,V2), V1!=V2.  % but cell (I, J) cannot have multiple values V
        :- x(I,J1,V), x(I,J2,V), J1!=J2.  % and the same value cannot appear in the same row
        :- x(I1,J,V), x(I2,J,V), I1!=I2.  % and the same value cannot appear in the same column

        % given two pairs of cell indices, we conclude if the cells are in the same block, or not
        same_block(I1,J1,I2,J2) :- I1/{k} == I2/{k}, J1/{k} == J2/{k}, i(I1), j(J1), i(I2), j(J2).

        % finally, the same value cannot appear in the same block
        :- same_block(I1,J1,I2,J2), x(I1,J1,V), x(I2,J2,V), I1!=I2, J1!=J2.

        #show x/3. % only show relevant values
    """

    if sum([sum(row) for row in sudoku]) == 0:
        # if we are dealing with an empty sudoku: solve efficiently
        values = list(range(1,k*k+1)) # 1..9
        for i1 in range(k):  # block vertical index
            for i2 in range(k):  # row within that block
                for j, v in enumerate(values):
                    # give every cell (i,j) a non-conflicting value v as facts in asp
                    asp_program += f"x({i1*k + i2},{j},{v})."
                values = values[-k:] + values[:-k]  # edit values to prevernt conflicts
            values = values[-1:] + values[:-1]  # edit values to prevernt conflicts
    else:
        # add values we're certain of as facts (these are given in the sudoku)
        for i in range(k*k):
            for j in range(k*k):
                if sudoku[i][j] > 0:
                    asp_program += f"x({i},{j},{sudoku[i][j]}).\n"

    control = clingo.Control()
    control.add("base", [], asp_program)
    control.ground([("base", [])])

    solution = [[0 for j in range(k*k)] for i in range(k*k)]  # empty k*k x k*k solution grid for "on_model"

    control.configuration.solve.models = 1  # we are only looking for 1 solution
    answer = control.solve(on_model=on_model)
    if answer.satisfiable:
        # if a solution is found
        return solution
    return None # if no solution is found

###
### Solver that uses ILP encoding
###
def solve_sudoku_ILP(sudoku,k):

    model = gp.Model()

    # add binary variables V[0], V[1], V[2], V[3], ..., V[k^6 - 1]
    V = model.addVars(k**6, vtype=GRB.BINARY, name="V")
    # store each variable corresponding to each possible value v for each cell (i,j)
    variables = [[[V[v + k*k*j + k**4*i] for v in range(k*k)] for j in range(k*k)] for i in range(k*k)]

    # iterate over rows and columns
    for i in range(k * k):

        # keep track of which variables belong to the row and column and to which values
        row_vars = [[] for v in range(k * k)]
        col_vars = [[] for v in range(k * k)]

        for j in range(k * k):
            if sudoku[i][j] > 0:
                # set variables corresponding to the given sudoku values to true
                model.addConstr(variables[i][j][sudoku[i][j] - 1] == True)
                for v in [n for n in range(k * k) if n != sudoku[i][j] - 1]:
                    # and set variables corresponding to other values for this cell to false
                    model.addConstr(variables[i][j][v] == False)

            # exacly one value must be chosen per cell
            model.addConstr(sum(variables[i][j]) == 1)

            for v in range(k * k):
                row_vars[v].append(variables[i][j][v])  # save the variable belonging to the row for each value
                col_vars[v].append(variables[j][i][v])  # same for column: note the swapped i and j
        for v in range(k * k):
            # each row and column must contain every possible value once
            model.addConstr(sum(row_vars[v]) == 1)
            model.addConstr(sum(col_vars[v]) == 1)

    # iterate over blocks
    for b1 in range(k):  # block vertical index
        for b2 in range(k):  # block horizontal index
            # keep track of which variables belong to the block and to which values
            block_vars = [[] for v in range(k * k)]
            for i in range(k * b1, k + k * b1):  # row
                for j in range(k * b2, k + k * b2):  # column
                    for v in range(k * k):  # value
                        block_vars[v].append(variables[i][j][v])
            for v in range(k * k):
                # the block must contain every possible value once
                model.addConstr(sum(block_vars[v]) == 1)

    # define some guess to work towards
    # that leads to a quick solution for an empty sudoku
    guess = []
    values = list(range(k*k))
    for i1 in range(k):  # block vertical index
        for i2 in range(k):  # row within that block
            for j, v in enumerate(values):
                # give every cell (i,j) a non-conflicting value v
                guess.append(V[int(values[j] + k*k * j + k**4 * (i1*k + i2))])
            values = values[-k:] + values[:-k]  # edit values to prevent conflicts
        values = values[-1:] + values[:-1]  # edit values to prevent conflicts

    # optimize for the empty sudoku, has no effect if the sudoku already has some values in it
    model.setObjective(gp.quicksum(guess), GRB.MAXIMIZE)

    model.optimize()

    if model.status == GRB.OPTIMAL:
        # if a solution is found
        solution = [[0 for j in range(k * k)] for i in range(k * k)]  # empty k*k x k*k solution grid
        for idx, var in enumerate(model.getVars()): # extract solution from the model
            if var.x:
                i = int(idx / k ** 4)  # row index
                j = int(idx / (k * k) % (k * k))  # column index
                v = idx % (k * k) + 1  # value
                solution[i][j] = v
        return solution
    return None # if no solution is found
