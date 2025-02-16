#!/usr/bin/env python3
import sys
import cvc5
import shutil
import re
from cvc5 import Kind

def create_solver_and_logger(filename):
    """
    Creates a cvc5 solver with its TermManager and opens an SMTLIB log file.
    Returns a tuple (solver, term_manager, smt_file).
    """
    tm = cvc5.TermManager()
    solver = cvc5.Solver(tm)
    smt_file = open(filename, "w")
    
    # Set logic to quantifier-free bit-vectors.
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

def or_operation(X, Y, n):
    """
    Performs the bitwise OR operation on two n-bit integers X and Y using SMTLIB bit-vector operations.
    
    Steps:
      1. Create a bit-vector constant for each input.
      2. Declare bit-vector variables for x, y, and result r.
      3. Assert that x equals the constant for X and y equals the constant for Y.
      4. Compute r = (bvor x y) using the BITVECTOR_OR operator.
      5. Check satisfiability and extract the model for r.
      6. Parse and output the result in binary (MSB-first and LSB-first) and in decimal.
    """
    filename = f"orsmt_{X}_{Y}_{n}.smt2"
    solver, tm, smt_file = create_solver_and_logger(filename)
    
    # Create the bit-vector sort of width n.
    bv_sort = tm.mkBitVectorSort(n)
    
    # Declare bit-vector variables for inputs x, y and for the result r.
    x = declareConst(tm, smt_file, bv_sort, "x")
    y = declareConst(tm, smt_file, bv_sort, "y")
    r = declareConst(tm, smt_file, bv_sort, "r")
    
    # Create bit-vector constants for X and Y.
    x_val = tm.mkBitVector(n, X)
    y_val = tm.mkBitVector(n, Y)
    
    # Assert that x equals X and y equals Y.
    assertFormula(solver, smt_file, tm.mkTerm(Kind.EQUAL, x, x_val))
    assertFormula(solver, smt_file, tm.mkTerm(Kind.EQUAL, y, y_val))
    
    # Compute the bitwise OR using the built-in BITVECTOR_OR operator.
    or_term = tm.mkTerm(Kind.BITVECTOR_OR, x, y)
    
    # Assert that r equals the bitwise OR of x and y.
    assertFormula(solver, smt_file, tm.mkTerm(Kind.EQUAL, r, or_term))
    
    
    result = checkSat(solver, smt_file)
    
    if result.isSat():
        model_r = solver.getValue(r)
        bv_str = str(model_r)
        # Expect output like "#b1010". Use regex to extract the binary string.
        m = re.search(r"#b([01]+)", bv_str)
        if m:
            bit_str = m.group(1).zfill(n)  # Ensure the string has exactly n bits.
            int_value = int(bit_str, 2)
            binary_msb = bit_str            # MSB-first representation.
            binary_lsb = binary_msb[::-1]     # LSB-first is the reverse.
            
            print("Bitwise OR Operation Result:")
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
    print("Test 1: or_operation(2, 3, 4)")
    or_operation(2, 3, 4)
    
    print("\nTest 2: or_operation(7, 3, 4)")
    or_operation(7, 3, 4)
    
    print("\nTest 3: or_operation(15, 8, 4)")
    or_operation(15, 8, 4)
    
    print("\nTest 4: or_operation(100, 50, 8)")
    or_operation(100, 50, 8)

if __name__ == "__main__":
    run_tests()
