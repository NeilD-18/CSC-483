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
    Declares a constant of a given sort in the SMT solver and logs the declaration.
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
    Checks satisfiability of the asserted formulas and logs the commands.
    Returns the solver's satisfiability result.
    """
    smt_file.write("(check-sat)\n")
    result = solver.checkSat()
    if result.isSat():
        smt_file.write("(get-model)\n")
    return result

def ultsmt_operation(X, Y, n):
    """
    Performs the unsigned less-than (bvult) operation on two n-bit integers X and Y
    using the SMTLIB bit-vector theory.
    
    The procedure is as follows:
      1. Represent each integer as a bit-vector variable of width n.
      2. Assert that these variables equal the bit-vector constants corresponding to X and Y.
      3. Create the predicate (bvult x y) using the built-in BITVECTOR_ULT operator.
      4. Declare a Boolean variable r to store the result and assert r = (bvult x y).
      5. Check satisfiability and extract the value of r.
    """
    filename = f"ultsmt_{X}_{Y}_{n}.smt2"
    solver, tm, smt_file = create_solver_and_logger(filename)
    
    # Create the bit-vector sort of width n.
    bv_sort = tm.mkBitVectorSort(n)
    
    # Declare bit-vector variables for X and Y.
    x = declareConst(tm, smt_file, bv_sort, "x")
    y = declareConst(tm, smt_file, bv_sort, "y")
    
    # Create bit-vector constants for X and Y.
    x_val = tm.mkBitVector(n, X)
    y_val = tm.mkBitVector(n, Y)
    
    # Assert that x equals X and y equals Y.
    assertFormula(solver, smt_file, tm.mkTerm(Kind.EQUAL, x, x_val))
    assertFormula(solver, smt_file, tm.mkTerm(Kind.EQUAL, y, y_val))
    
    # Create the unsigned less-than predicate using the BITVECTOR_ULT operator.
    ult_term = tm.mkTerm(Kind.BITVECTOR_ULT, x, y)
    
    # Declare a Boolean variable r to store the result.
    bool_sort = solver.getBooleanSort()
    r = declareConst(tm, smt_file, bool_sort, "r")
    
    # Assert that r equals the unsigned less-than predicate.
    assertFormula(solver, smt_file, tm.mkTerm(Kind.EQUAL, r, ult_term))
    
    # Check satisfiability.
    result = checkSat(solver, smt_file)
    
    if result.isSat():
        model_r = solver.getValue(r)
        result_str = str(model_r)
        print(f"Unsigned less-than Operation Result for X={X}, Y={Y}, n={n}: {result_str}")
    else:
        print("SMT constraints are unsatisfiable. Something went wrong.")
    
    smt_file.close()
    shutil.move(filename, f"tests/{filename}")

def run_tests():
    print("Test 1: ultsmt_operation(2, 5, 4)")
    ultsmt_operation(2, 5, 4)
    
    print("\nTest 2: ultsmt_operation(7, 3, 4)")
    ultsmt_operation(7, 3, 4)
    
    print("\nTest 3: ultsmt_operation(1, 1, 4)")
    ultsmt_operation(1, 1, 4)
    
    print("\nTest 4: ultsmt_operation(3, 8, 4)")
    ultsmt_operation(3, 8, 4)
   
    print("\nTest 5: ultsmt_operation(0, 1, 8)")
    ultsmt_operation(0, 1, 8)
    
    print("\nTest 6: ultsmt_operation(16, 15, 8)")
    ultsmt_operation(16, 15, 8)
    
    print("\nTest 7: ultsmt_operation(100, 200, 16)")
    ultsmt_operation(100, 200, 16)
    
    print("\nTest 8: ultsmt_operation(200, 100, 16)")
    ultsmt_operation(200, 100, 16)
    
    print("\nTest 9: ultsmt_operation(2147483647, 2147483648, 32)")
    ultsmt_operation(2147483647, 2147483648, 32)
    
    print("\nTest 10: ultsmt_operation(9223372036854775807, 9223372036854775808, 64)")
    ultsmt_operation(9223372036854775807, 9223372036854775808, 64)

if __name__ == "__main__":
    run_tests()
