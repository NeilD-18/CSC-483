#!/usr/bin/env python3
import sys
import cvc5
import shutil
import re
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

def and_operation(X, Y, n):
    """
    Computes the bitwise AND of two n-bit integers X and Y using SMTLIB bit-vector operations.
    
    Steps:
      1. Create a unique SMTLIB file and initialize the solver, term manager, and logger.
      2. Create a bit-vector sort for n-bit integers.
      3. Declare bit-vector variables for the inputs (x and y) and the result (r).
      4. Convert X and Y into bit-vector constants of width n.
      5. Assert that the declared variables x and y are equal to their corresponding constants.
      6. Compute the bitwise AND using the built-in BITVECTOR_AND operator.
      7. Assert that the result variable r is equal to the computed bitwise AND term.
      8. Check the satisfiability of the SMT constraints.
      9. Extract and format the result from the model in both binary (MSB-first and LSB-first) and decimal forms.
      10. Output the results and move the SMTLIB log file to a designated folder.
    """
    filename = f"andsmt_{X}_{Y}_{n}.smt2"
    solver, tm, smt_file = create_solver_and_logger(filename)
    
    # Create a bit-vector sort of width n.
    bv_sort = tm.mkBitVectorSort(n)
    
    # Declare bit-vector variables for the two inputs and the result.
    x = declareConst(tm, smt_file, bv_sort, "x")
    y = declareConst(tm, smt_file, bv_sort, "y")
    r = declareConst(tm, smt_file, bv_sort, "r")
    
    # Create bit-vector constants for X and Y.
    x_val = tm.mkBitVector(n, X)
    y_val = tm.mkBitVector(n, Y)
    
    # Assert that x equals the constant for X and y equals the constant for Y.
    assertFormula(solver, smt_file, tm.mkTerm(Kind.EQUAL, x, x_val))
    assertFormula(solver, smt_file, tm.mkTerm(Kind.EQUAL, y, y_val))
    
    # Compute the bitwise AND using the built-in BITVECTOR_AND operator.
    and_term = tm.mkTerm(Kind.BITVECTOR_AND, x, y)
    
    # Assert that r equals the computed bitwise AND.
    assertFormula(solver, smt_file, tm.mkTerm(Kind.EQUAL, r, and_term))
    
    result = checkSat(solver, smt_file)
    
    if result.isSat():
        model_r = solver.getValue(r)
        bv_str = str(model_r)
        # Expecting a string in the form "#bXXXX"
        m = re.search(r"#b([01]+)", bv_str)
        if m:
            bit_str = m.group(1)
            # Ensure the binary string has length n.
            bit_str = bit_str.zfill(n)
            int_value = int(bit_str, 2)
            binary_msb = bit_str  # MSB-first representation.
            binary_lsb = binary_msb[::-1]  # LSB-first is the reverse.
            
            print("Bitwise AND Operation Result:")
            print("Binary (MSB-first):", binary_msb)
            print("Binary (LSB-first):", binary_lsb)
            print("Decimal:", int_value)
        else:
            print("Could not parse bit-vector value:", bv_str)
    else:
        print("SMT constraints are unsatisfiable. Something went wrong.")
    
    smt_file.close()
    shutil.move(filename, f"tests/{filename}")

def run_tests():
    print("Test 1: and_operation(2, 3, 4)")
    and_operation(2, 3, 4)
    
    print("\nTest 2: and_operation(7, 3, 4)")
    and_operation(7, 3, 4)
    
    print("\nTest 3: and_operation(15, 8, 4)")
    and_operation(15, 8, 4)
    
    print("\nTest 4: and_operation(100, 50, 8)")
    and_operation(100, 50, 8)

if __name__ == "__main__":
    run_tests()
