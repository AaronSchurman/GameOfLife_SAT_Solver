import z3
import os
import sys
from itertools import combinations, product


class SolverError(Exception):
    pass


def print_model(model, field):
    """This class will print the Model to the user

        This uses * to denote Alive Cells and . to denote Dead Cells
        @param z3 solver.model()
        @param 3D list field

        return none
    """
    for t in range(len(field)):
        print(f"State {t}:")
        for x in range(len(field[0])):
            row = []
            for y in range(len(field[0][0])):
                row.append('*' if model[field[t][x][y]] else '.')
            print(' '.join(row))
        if t != len(field)-1:
            print()


#             telling Z3 what frame is supposed
# constrainginng the frame size and #

def create_field(size_x, size_y, transitions):
    """This function creates a 3D feild of frames full of z3 Boolean variables
        
        field[0] is the start frame
        Each frame is a X by Y size grid
        Each cell is a z3 Boolean with the name Xpos.Ypos;t{frame_Num}
        @param int size_x
        @param int size_y
        @param int tranistions
        
        return 3D list field 
        
    """
    field = []
#     3D list of frames 0 being the first frame or inital condition
    for t in range(transitions):
        frame = [[z3.Bool(f"{x}.{y};t{t}") for y in range(size_y)] for x in range(size_x)]
        field.append(frame)
    return field


# one more variable that determins if inital or final board ??

def parse_final_input(filename):
    """This function will parse the input file
    
    @param string filename (Path to file)
    return int size_x, int size_y, int transitions, 2D boolean list state
    
    """
    #board size x and y, # of transitions to complete
    size_x, size_y, transitions = 0, 0, 0
    state = []
    with open(filename, 'r') as f:
        sizes = f.readline()
        size_x, size_y, transitions = sizes.split(' ')
        transitions = int(transitions)
        size_x = int(size_x)
        size_y = int(size_y)
        line = f.readline()
        while line:
            values = line.strip().split(' ')
#           values currently is list of * and .
            if len(values) != size_y:
                raise ValueError(f"Incorrect field size (y = {len(values)} expected = {size_y})")
            values = [v == '*' for v in values] # replaces charcters with true/false values
            state.append(values)
            line = f.readline()

    if len(state) != size_x:
        raise ValueError(f"Incorrect field size (x = {len(state)} expected = {size_x})")
    return size_x, size_y,transitions, state


# Here we must make it so that Z3 constraints the intial frame to at least x number of alive
# and y number of dead cells
def get_frame(frame):
    """returns a list of all of the cells in the given frame
        
        
        @param 2D list frame
        
        return 2D list (or single frame) from 3D list of frames
    
    """             
    result = []
    for x_ in range(0, len(frame)):    
        result.extend(frame[x_])
    return result                   

def get_state_constraints(frame, num_alive):
    """This function sets the intial state constraints on a single frame
    
    This function will set a constraint on z3 that a given frame can have only
    num_alive number of alive cells in the frame
    
    @param 2D list frame
    @param int num_alive
    
    return z3.AtMost( num_alive live cells in frame variables)
    
    
    """
    constraints = []
    frame_variables = get_frame(frame) # creates a 1D list of variables form a 2D frame
    return z3.AtMost(*frame_variables, int(num_alive))

def get_final_state_constraints(field, final_state, transitions):
    """This function will set the final frame constraints for z3
    
    This takes the input feild given in the input file and
    sets the constraints on z3
    
    @param 3D list field
    @param 2D list final_state
    @param int transitions
    
    return constraints
    
    """
    constraints = []
    for x in range(len(final_state)):
        for y in range(len(final_state[0])):
            constraints.append((field[transitions-1][x][y] == final_state[x][y]))
#             if intial state of x,y is dont care "-" then do nothing
#             this is constraining time 0 frame or the intial state
    return constraints



def get_neighbors(frame, x, y):
    """returns a list of a cells neighbors
        
        @param 2D list frame
        @param int x
        @param int y
        
        return result 
    """             
    result = []
    for x_, y_ in product(range(x-1, x+2), range(y-1, y+2)):
        # this will skip the cell itself           
        if x_ == x and y_ == y:
            continue
        # This line checks if the cell is in the frame ensuring that the neighbor exists       
        if x_ in range(0, len(frame)) and y_ in range(0, len(frame[0])):
            result.append(frame[x_][y_])
    return result


def get_gol_rules_constraints(field, transition_num):
    """This will give z3 constraints needed for every cell
    
    This is where all the magic happens for solving for the rules of Conways Game of Life
    The rules are as follows -
    - Any live cell with two or three live neighbours survives.
    - Any dead cell with three live neighbours becomes a live cell.
    - All other live cells die in the next generation. Similarly, all other dead cells stay dead.
    
    This is done with the z3 rules AtMost and AtLeast
    
    The program will start with the last frame in the feild and work backwards 
    Setting rules for the number of boolean alive and dead neighbors each cell is allowed to have
    The solver then takes these rules and works to come up with an intial frame 
    
    @param 3D list field
    @param int transition_num
    
    return constraints
    """
    assert(transition_num > 0)
    constraints = []
    t = transition_num
    for x in range(len(field[0])):
        for y in range(len(field[0][0])):
            cell = field[t][x][y]
            prev_cell = field[t-1][x][y]
            prev_neighbours = get_neighbors(field[t-1], x, y)
            
#           *prev == list of params 
#           AtLeast(bool variables, lower bound on true)                  
            constraints.append(
                    cell == z3.And( 
                        z3.AtLeast(prev_cell, *prev_neighbours, 3),
                        z3.AtMost(*prev_neighbours, 3)))
    return constraints


def solve_forward(field, final_state, transitions, num_alive):
    """This function builds a z3 SAT solver and inputs the constraints needed to solve for the initial frame
    
    @param 3D list field
    @param 2D list final_state
    @param int transitions
    @param int num_alive
    
    return field
    """
    solver = z3.Solver() # create solver
    solver.add(get_state_constraints(field[0], num_alive)) # add inital state constraits
    solver.add(z3.And(get_final_state_constraints(field, final_state, transitions))) # add final state constraints
    for t in range(1, len(field)):
        solver.add(get_gol_rules_constraints(field, t)) #add constraints based on Game of Life rules
    result = solver.check() # run solver
    if result == z3.sat:
        m = solver.model()
        print_model(m, field)
    else:
        print("Results not satisfactory")
        print("Perhaps try a differnt step #")
    return field

# support specification of target ?? 
# partial specification of target "At least 4 or at most 10 must be alive" ??

if __name__ == '__main__':
    fileIN_final = input("Input final states File:")
    if(fileIN_final[0] == '"'):
        fileIN_final = fileIN_final[1:-1]
    num_alive = input("Number of alive cells requested at start:")
    x, y, transitions, final_state = parse_final_input(fileIN_final) 
    field = create_field(x, y, transitions)
    solve_forward(field, final_state, transitions, num_alive)