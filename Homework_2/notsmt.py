#!/usr/bin/env python3
import sys
import cvc5
import shutil
import re
from cvc5 import Kind

def create_solver_and_logger(filename):
    """
    Creates a cvc5 solver, initializes its TermManager, and opens an SMTLIB log file.
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

def not_operation(X, n):
    """
    Performs the bitwise NOT operation on an n-bit integer X using SMTLIB bit-vector operations.
    
    Steps:
      1. Convert X to a bit-vector constant of width n.
      2. Declare a bit-vector variable x for the input.
      3. Assert that x equals the constant for X.
      4. Compute the bitwise NOT of x using the BITVECTOR_NOT operator.
      5. Declare a bit-vector variable r for the result and assert that r equals the NOT of x.
      6. Check satisfiability and extract the model for r.
      7. Output the result in binary (MSB-first and LSB-first) and decimal.
      8. Log the SMTLIB commands to an .smt2 file, then move it to a designated folder.
    """
    filename = f"notsmt_{X}_{n}.smt2"
    solver, tm, smt_file = create_solver_and_logger(filename)
    
    # Create the bit-vector sort of width n.
    bv_sort = tm.mkBitVectorSort(n)
    
    # Declare bit-vector variable for the input x and for the result r.
    x = declareConst(tm, smt_file, bv_sort, "x")
    r = declareConst(tm, smt_file, bv_sort, "r")
    
    # Create a bit-vector constant for the input integer X.
    x_val = tm.mkBitVector(n, X)
    
    # Assert that x equals the constant for X.
    assertFormula(solver, smt_file, tm.mkTerm(Kind.EQUAL, x, x_val))
    
    # Compute the bitwise NOT of x using BITVECTOR_NOT.
    not_term = tm.mkTerm(Kind.BITVECTOR_NOT, x)
    
    # Assert that r equals the computed bitwise NOT.
    assertFormula(solver, smt_file, tm.mkTerm(Kind.EQUAL, r, not_term))
    
    result = checkSat(solver, smt_file)
    
    if result.isSat():
        model_r = solver.getValue(r)
        bv_str = str(model_r)
        # Expecting a string in the format "#bXXXX..."
        m = re.search(r"#b([01]+)", bv_str)
        if m:
            bit_str = m.group(1).zfill(n)  # Ensure the string has n bits.
            int_value = int(bit_str, 2)
            binary_msb = bit_str  # MSB-first representation.
            binary_lsb = binary_msb[::-1]  # LSB-first is the reverse.
            
            print("Bitwise NOT Operation Result:")
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
    print("Test 1: not_operation(2, 4)")
    not_operation(2, 4)
    
    print("\nTest 2: not_operation(7, 4)")
    not_operation(7, 4)
    
    print("\nTest 3: not_operation(15, 4)")
    not_operation(15, 4)
    
    print("\nTest 4: not_operation(100, 8)")
    not_operation(100, 8)

if __name__ == "__main__":
    run_tests()
