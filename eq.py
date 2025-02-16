
import cvc5
import shutil
from cvc5 import Kind

def int_to_bits(x, n):
    """Converts an integer to its n-bit binary representation as a list of booleans.
       The least significant bit is stored at index 0."""
    bits = []
    for i in range(n):
        bits.append(((x >> i) & 1) == 1)
    return bits

def create_solver_and_logger(filename):
    """Creates a new solver and opens an SMTLIB log file."""
    tm = cvc5.TermManager()
    solver = cvc5.Solver(tm)
    smt_file = open(filename, "w")
    
    # Set initial SMTLIB commands:
    smt_file.write("(set-logic ALL)\n")
    solver.setLogic("ALL")
    smt_file.write("(set-option :dag-thresh 0)\n")
    solver.setOption("dag-thresh", "0")
    smt_file.write("(set-option :produce-models true)\n")
    solver.setOption("produce-models", "true")
    return solver, tm, smt_file

def declareConst(tm, smt_file, sort, name):
    """Declares a constant of a given sort in the SMT solver and logs it."""
    smt_file.write("(declare-const {} {})\n".format(name, str(sort)))
    return tm.mkConst(sort, name)

def assertFormula(solver, smt_file, formula):
    """Asserts a formula in the SMT solver and records it in the SMT file."""
    smt_file.write("(assert {})\n".format(str(formula)))
    solver.assertFormula(formula)

def checkSat(solver, smt_file):
    """Checks the satisfiability of the asserted formulas and logs the query.
       If the result is SAT, it requests the solver to provide a model."""
    smt_file.write("(check-sat)\n")
    result = solver.checkSat()
    if result.isSat():
        smt_file.write("(get-model)\n")
    return result

def equality(X, Y, n):
    # Create a unique SMT file name given X, Y, n
    filename = f"eq_{X}_{Y}_{n}.smt2"
    solver, tm, smt_file = create_solver_and_logger(filename)
    
    # Get Boolean sort and convert integers to bits.
    bool_sort = solver.getBooleanSort()
    x_bits = int_to_bits(X, n)
    y_bits = int_to_bits(Y, n)
    
    # Create Boolean variables for x and y bits.
    x_vars = []
    y_vars = []
    for i in range(n):
        x_var = declareConst(tm, smt_file, bool_sort, f"x{i}")
        y_var = declareConst(tm, smt_file, bool_sort, f"y{i}")
        x_vars.append(x_var)
        y_vars.append(y_var)
    
    # Assert x and y bits based on their binary representation.
    for i in range(n):
        x_val = solver.mkBoolean(x_bits[i])
        y_val = solver.mkBoolean(y_bits[i])
        assertFormula(solver, smt_file, tm.mkTerm(Kind.EQUAL, x_vars[i], x_val))
        assertFormula(solver, smt_file, tm.mkTerm(Kind.EQUAL, y_vars[i], y_val))
    
    # Build equality, for each i, check x_i == y_i
    
    eq_terms = []
    for i in range(n):
        eq_terms.append(tm.mkTerm(Kind.EQUAL, x_vars[i], y_vars[i]))
        
    if len(eq_terms) > 1:
        equality_formula = tm.mkTerm(Kind.AND, *eq_terms)
    elif eq_terms:
        equality_formula = eq_terms[0]
    else:
        equality_formula = solver.mkBoolean(True)

    # Assert the overall equality condition.
    assertFormula(solver, smt_file, equality_formula)
    
    # Check satisfiability.
    result = checkSat(solver, smt_file)
    
   
    if result.isSat():
        print("Result = {}".format(result))
        print("Equality holds: X equals Y")
    else:
        print("Equality does not hold: X does not equal Y")
        print("Result = {}".format(result))
    
 
    smt_file.close()
    
    shutil.move(filename, f"tests/{filename}")

def run_tests():
    print("Test 1: equality(2, 2, 4) – Expected: Equality holds")
    equality(2, 2, 4)
    
    print("\nTest 2: equality(2, 3, 4) – Expected: Equality does not hold")
    equality(2, 3, 4)
    
    print("\nTest 3: equality(100, 100, 8) – Expected: Equality holds")
    equality(100, 100, 8)
    
    print("\nTest 4: equality(100, 101, 8) – Expected: Equality does not hold")
    equality(100, 101, 8)
    
    print("\nTest 5: equality(0, 0, 1) – Expected: Equality holds")
    equality(0, 0, 1)
    
    print("\nTest 6: equality(0, 1, 1) – Expected: Equality does not hold")
    equality(0, 1, 1)

if __name__ == "__main__":
    run_tests()
