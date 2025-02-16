import shutil
import cvc5
from cvc5 import Kind

def int_to_bits(x, n):
    """
    Converts an integer x to its n-bit binary representation as a list of booleans.
    The least significant bit (LSB) is stored at index 0.
    """
    bits = []
    for i in range(n):
        bits.append(((x >> i) & 1) == 1)
    return bits

def create_solver_and_logger(filename):
    """
    Creates a cvc5 solver, initializes its TermManager, and logs commands to an SMTLIB file.
    Returns a tuple containing the solver, term manager, and log file.
    """
    tm = cvc5.TermManager()
    solver = cvc5.Solver(tm)
    smt_file = open(filename, "w")
    
    smt_file.write("(set-logic ALL)\n")
    solver.setLogic("ALL")
    smt_file.write("(set-option :dag-thresh 0)\n")
    solver.setOption("dag-thresh", "0")
    smt_file.write("(set-option :produce-models true)\n")
    solver.setOption("produce-models", "true")
    
    return solver, tm, smt_file

def declareConst(tm, smt_file, sort, name):
    """
    Declares a constant of a given sort in the SMT solver and logs the declaration.
    Returns the term representing the declared constant.
    """
    smt_file.write(f"(declare-const {name} {sort})\n")
    return tm.mkConst(sort, name)

def assertFormula(solver, smt_file, formula):
    """
    Asserts a formula in the SMT solver and logs it in the SMTLIB file.
    """
    smt_file.write(f"(assert {formula})\n")
    solver.assertFormula(formula)

def checkSat(solver, smt_file):
    """
    Checks satisfiability of the asserted formulas and logs the commands.
    Returns the solver's satisfiability result.
    """
    smt_file.write("(check-sat)\n")
    result = solver.checkSat()
    if result.isSat():
        smt_file.write("(get-model)\n")
    return result

def ult_operation(X, Y, n):
    """
    Performs an unsigned less-than (ULT) operation on two n-bit integers X and Y using cvc5.
    It builds a logical formula that represents the condition: X < Y, 
    where the numbers are compared bit by bit from most significant to least significant.
    
    The idea is:
      - For each bit position k, ensure that all more-significant bits (positions k+1 to n-1) are equal.
      - Then check that at position k, X has a 0 (false) and Y has a 1 (true).
      - If any such condition is true, then X is less than Y.
    """
    # Create a unique SMT file name given X, Y, n
    filename = f"ult_{X}{Y}{n}.smt2"
    solver, tm, smt_file = create_solver_and_logger(filename)
    
    # Get Boolean sort and convert integers to bits.
    bool_sort = solver.getBooleanSort()
    x_bits = int_to_bits(X, n)
    y_bits = int_to_bits(Y, n)
    
    # Declare Boolean variables for each bit of X and Y.
    x_vars = []  # Variables representing bits of X (x0, x1, ..., x{n-1})
    y_vars = []  # Variables representing bits of Y (y0, y1, ..., y{n-1})
    for i in range(n):
        x_var = declareConst(tm, smt_file, bool_sort, f"x{i}")
        y_var = declareConst(tm, smt_file, bool_sort, f"y{i}")
        x_vars.append(x_var)
        y_vars.append(y_var)
    
    # Assert that each x_i and y_i match the actual bit values of X and Y.
    for i in range(n):
        x_val = solver.mkBoolean(x_bits[i])
        y_val = solver.mkBoolean(y_bits[i])
        assertFormula(solver, smt_file, tm.mkTerm(Kind.EQUAL, x_vars[i], x_val))
        assertFormula(solver, smt_file, tm.mkTerm(Kind.EQUAL, y_vars[i], y_val))
    
    # Build the conditions that represent the "X < Y" predicate.
    # For each bit position k:
    #   1. Ensure that for all bits more significant than k (positions k+1 to n-1),
    #      the bits in X and Y are equal.
    #   2. Check that at bit k, X's bit is 0 (false) and Y's bit is 1 (true).
    # If any such condition holds, then X is less than Y.
    conditions = []
    for k in range(n):
        equal_conditions = []
        for j in range(k+1, n):
            # Add condition: x_j equals y_j for every more significant bit j.
            equal_conditions.append(tm.mkTerm(Kind.EQUAL, x_vars[j], y_vars[j]))
        
        # Combine all equality conditions.
        if len(equal_conditions) > 1:
            prefix = tm.mkTerm(Kind.AND, *equal_conditions)
        elif equal_conditions:
            prefix = equal_conditions[0]
        else:
            # If there are no bits more significant than k, then the prefix is automatically true.
            prefix = tm.mkBoolean(True)
        
        # At bit k, X must be 0 and Y must be 1.
        bit_condition = tm.mkTerm(Kind.AND, tm.mkTerm(Kind.NOT, x_vars[k]), y_vars[k])
        
        # Combine the prefix (all higher bits equal) with the condition at bit k.
        cond_k = tm.mkTerm(Kind.AND, prefix, bit_condition)
        conditions.append(cond_k)
    
    # The overall formula is the OR of all conditions: if any condition is true, then X < Y.
    ult_formula = tm.mkTerm(Kind.OR, *conditions) if conditions else tm.mkBoolean(False)
    
    # Declare a Boolean variable 'r' to store the result of the comparison.
    r = declareConst(tm, smt_file, bool_sort, "r")
    # Assert that r is exactly equal to our computed unsigned less-than formula.
    assertFormula(solver, smt_file, tm.mkTerm(Kind.EQUAL, r, ult_formula))
    
    # Finalize the SMTLIB file by writing check commands.
    smt_file.write("(check-sat)\n")
    smt_file.write("(get-model)\n")
    
    # Check satisfiability of the formulas.
    result = checkSat(solver, smt_file)
    
    if result.isSat():
        # Retrieve the value of r (the result of the ULT operation) from the model.
        model_r = solver.getValue(r)
        result_str = str(model_r)
        print(f"Unsigned less-than Operation Result for X={X}, Y={Y}, n={n}: {result_str}")
    else:
        print("SMT constraints are unsatisfiable. Something went wrong.")
    
    # Close the SMTLIB log file and move it to the tests folder.
    smt_file.close()
    shutil.move(filename, f"tests/{filename}")

def run_tests():
    """
    Runs predefined test cases for the ult_operation function.
    """
    print("Test 1: ult_operation(2, 5, 4)")
    ult_operation(2, 5, 4)
    
    print("\nTest 2: ult_operation(7, 3, 4)")
    ult_operation(7, 3, 4)
    
    print("\nTest 3: ult_operation(1, 1, 4)")
    ult_operation(1, 1, 4)
    
    print("\nTest 4: ult_operation(3, 8, 4)")
    ult_operation(3, 8, 4)

if __name__ == "__main__":
    run_tests()