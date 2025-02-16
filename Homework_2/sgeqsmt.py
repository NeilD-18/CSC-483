#!/usr/bin/env python3
import sys
import cvc5
import shutil
from cvc5 import Kind

def create_solver_and_logger(filename):
    """
    Creates a cvc5 solver with its TermManager and opens an SMTLIB log file.
    Returns a tuple (solver, term_manager, smt_file).
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
    Checks the satisfiability of the asserted formulas and logs the command.
    Returns the solver's result.
    """
    smt_file.write("(check-sat)\n")
    result = solver.checkSat()
    if result.isSat():
        smt_file.write("(get-model)\n")
    return result

def sgeqsmt_operation(X, Y, n):
    """
    Performs the signed greater-than or equal-to (≥ₛ) comparison on two n-bit integers X and Y
    using SMTLIB bit-vector operations.
    
    This function uses the built-in signed comparison operator (BITVECTOR_SGE) to compare
    the two bit-vectors (interpreted in two's complement). The result is a Boolean value.
    """
    filename = f"sgeqsmt_{X}_{Y}_{n}.smt2"
    solver, tm, smt_file = create_solver_and_logger(filename)
    
    # Create the bit-vector sort of width n.
    bv_sort = tm.mkBitVectorSort(n)
    
    # Declare bit-vector variables for X and Y.
    x = declareConst(tm, smt_file, bv_sort, "x")
    y = declareConst(tm, smt_file, bv_sort, "y")
    
    # Create bit-vector constants for the given integers.
    x_val = tm.mkBitVector(n, X)
    y_val = tm.mkBitVector(n, Y)
    
    # Assert that x equals the constant for X and y equals the constant for Y.
    assertFormula(solver, smt_file, tm.mkTerm(Kind.EQUAL, x, x_val))
    assertFormula(solver, smt_file, tm.mkTerm(Kind.EQUAL, y, y_val))
    
    # Create the signed greater than or equal to predicate using the BITVECTOR_SGE operator.
    ge_term = tm.mkTerm(Kind.BITVECTOR_SGE, x, y)
    
    # Declare a Boolean variable r to store the result.
    bool_sort = solver.getBooleanSort()
    r = declareConst(tm, smt_file, bool_sort, "r")
    
    # Assert that r equals the signed comparison result.
    assertFormula(solver, smt_file, tm.mkTerm(Kind.EQUAL, r, ge_term))
    
    # Check satisfiability and extract the model.
    result = checkSat(solver, smt_file)
    
    if result.isSat():
        model_r = solver.getValue(r)
        result_str = str(model_r)
        print(f"Signed Greater-Than or Equal Operation Result for X={X}, Y={Y}, n={n}: {result_str}")
    else:
        print("SMT constraints are unsatisfiable. Something went wrong.")
    
    smt_file.close()
    shutil.move(filename, f"tests/{filename}")

def run_tests():
    print("Test 1: sgeqsmt_operation(5, 3, 4)  // 5 >= 3 should be true")
    sgeqsmt_operation(5, 3, 4)
    
    print("\nTest 2: sgeqsmt_operation(-2, -1, 4)  // -2 >= -1 should be false")
    sgeqsmt_operation(-2, -1, 4)
    
    print("\nTest 3: sgeqsmt_operation(-1, -1, 4)  // -1 >= -1 should be true")
    sgeqsmt_operation(-1, -1, 4)
    
    print("\nTest 4: sgeqsmt_operation(3, -2, 4)  // 3 >= -2 should be true")
    sgeqsmt_operation(3, -2, 4)
    
    print("\nTest 5: sgeqsmt_operation(100, 50, 8)  // 100 >= 50 should be true")
    sgeqsmt_operation(100, 50, 8)
    
    print("\nTest 6: sgeqsmt_operation(-100, -50, 8)  // -100 >= -50 should be false")
    sgeqsmt_operation(-100, -50, 8)
    
    print("\nTest 7: sgeqsmt_operation(-50, -100, 8)  // -50 >= -100 should be true")
    sgeqsmt_operation(-50, -100, 8)
    
    print("\nTest 8: sgeqsmt_operation(32767, -32768, 16)  // 32767 >= -32768 should be true")
    sgeqsmt_operation(32767, -32768, 16)
    
    print("\nTest 9: sgeqsmt_operation(-32768, 32767, 16)  // -32768 >= 32767 should be false")
    sgeqsmt_operation(-32768, 32767, 16)
    
    print("\nTest 10: sgeqsmt_operation(0, -1, 8)  // 0 >= -1 should be true")
    sgeqsmt_operation(0, -1, 8)

if __name__ == "__main__":
    run_tests()
