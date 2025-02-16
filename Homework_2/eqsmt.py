import sys
import cvc5
import shutil
from cvc5 import Kind

def create_solver_and_logger(filename):
    """
    Creates a cvc5 solver, initializes its TermManager, and logs commands to an SMTLIB file.
    Returns a tuple (solver, term manager, smt_file).
    """
    tm = cvc5.TermManager()
    solver = cvc5.Solver(tm)
    smt_file = open(filename, "w")
    
    # Set the logic to quantifier-free bit-vectors.
    smt_file.write("(set-logic QF_BV)\n")
    solver.setLogic("QF_BV")
    smt_file.write("(set-option :produce-models true)\n")
    solver.setOption("produce-models", "true")
    
    return solver, tm, smt_file

def declareConst(tm, smt_file, sort, name):
    """
    Declares a constant of a given sort in the SMT solver and logs it.
    Returns the created constant term.
    """
    smt_file.write("(declare-const {} {})\n".format(name, str(sort)))
    return tm.mkConst(sort, name)

def assertFormula(solver, smt_file, formula):
    """
    Asserts a formula in the SMT solver and logs it in the SMTLIB file.
    """
    smt_file.write("(assert {})\n".format(str(formula)))
    solver.assertFormula(formula)

def checkSat(solver, smt_file):
    """
    Checks the satisfiability of the asserted formulas and logs the command.
    Returns the solver's result.
    """
    smt_file.write("(check-sat)\n")
    result = solver.checkSat()
    if result.isSat():
        smt_file.write("(get-model)\n")
    return result

def eqsmt_operation(X, Y, n):
    """
    Checks equality of two n-bit integers X and Y using the SMT bit-vector theory.
    
    Steps:
      1. Create a unique SMTLIB file and initialize the solver, term manager, and log file.
      2. Create a bit-vector sort for n-bit integers.
      3. Declare bit-vector variables for the inputs (x and y).
      4. Convert X and Y into bit-vector constants of width n.
      5. Assert that the declared variables x and y are equal to their corresponding constants.
      6. Assert the equality between x and y.
      7. Check the satisfiability of the SMT constraints and retrieve the model.
      8. Output the result: if the constraints are satisfiable, then X equals Y (true); otherwise, false.
      9. Close the SMTLIB file and move it to a designated folder.
    """
    filename = f"eqsmt_{X}_{Y}_{n}.smt2"
    solver, tm, smt_file = create_solver_and_logger(filename)
    
    # Create the bit-vector sort of width n.
    bv_sort = tm.mkBitVectorSort(n)
    
    # Use the helper function to declare bit-vector constants for x and y.
    x = declareConst(tm, smt_file, bv_sort, "x")
    y = declareConst(tm, smt_file, bv_sort, "y")
    
    # Create bit-vector constants for the given integers.
    x_val = tm.mkBitVector(n, X)
    y_val = tm.mkBitVector(n, Y)
    
    # Assert that x equals X and y equals Y.
    assertFormula(solver, smt_file, tm.mkTerm(Kind.EQUAL, x, x_val))
    assertFormula(solver, smt_file, tm.mkTerm(Kind.EQUAL, y, y_val))
    
    # Assert equality between x and y.
    eq_formula = tm.mkTerm(Kind.EQUAL, x, y)
    assertFormula(solver, smt_file, eq_formula)
    
    result = checkSat(solver, smt_file)
    
    if result.isSat():
        print("Result = {}".format(result))
        print("Equality holds: X equals Y")
    else:
        print("Result = {}".format(result))
        print("Equality does not hold: X does not equal Y")
    
    smt_file.close()
    shutil.move(filename, f"tests/{filename}")

def run_tests():
    """
    Runs a series of tests to validate the bit-vector equality operation.
    """
    print("Test 1: eqsmt_operation(5, 5, 8)  // 5 equals 5 should be true")
    eqsmt_operation(5, 5, 8)
    
    print("\nTest 2: eqsmt_operation(5, 6, 8)  // 5 equals 6 should be false")
    eqsmt_operation(5, 6, 8)
    
    print("\nTest 3: eqsmt_operation(-1, -1, 8)  // -1 equals -1 should be true")
    eqsmt_operation(-1, -1, 8)
    
    print("\nTest 4: eqsmt_operation(-1, 1, 8)  // -1 equals 1 should be false")
    eqsmt_operation(-1, 1, 8)
    
    print("\nTest 5: eqsmt_operation(123456, 123456, 32)  // 123456 equals 123456 should be true")
    eqsmt_operation(123456, 123456, 32)

if __name__ == "__main__":
    run_tests()
