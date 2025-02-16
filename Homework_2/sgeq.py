import cvc5
import shutil
from cvc5 import Kind

def int_to_bits(x, n):
    """
    Converts an integer x to its n-bit two's complement binary representation as a list of booleans.
    For negative numbers, we compute x modulo 2^n to get the correct two's complement representation.
    The least significant bit (LSB) is at index 0.
    """
    # Adjust x to be in the range 0 to 2^n - 1
    x = x % (1 << n)
    bits = []
    for i in range(n):
        bits.append(((x >> i) & 1) == 1)
    return bits

def create_solver_and_logger(filename):
    """
    Creates a cvc5 solver, initializes its TermManager, and logs commands to an SMTLIB file.
    Returns a tuple (solver, term manager, smt_file).
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
    Declares a constant of the given sort in the SMT solver and logs the declaration.
    Returns the created constant term.
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
    Checks the satisfiability of the asserted formulas and logs the command.
    Returns the solver's result.
    """
    smt_file.write("(check-sat)\n")
    result = solver.checkSat()
    if result.isSat():
        smt_file.write("(get-model)\n")
    return result

def build_ult_formula(x_vars, y_vars, tm, n):
    """
    Builds the unsigned less-than formula for the bit-vectors x_vars and y_vars.
    The formula represents:
       X <_u Y  if and only if
       ∨[for k=0 to n-1] { (∧[j=k+1 to n-1] (x_j = y_j)) ∧ (¬x_k ∧ y_k) }.
    """
    conditions = []
    for k in range(n):
        equal_conditions = []
        for j in range(k+1, n):
            equal_conditions.append(tm.mkTerm(Kind.EQUAL, x_vars[j], y_vars[j]))
        if equal_conditions:
            if len(equal_conditions) == 1:
                prefix = equal_conditions[0]
            else:
                prefix = tm.mkTerm(Kind.AND, *equal_conditions)
        else:
            prefix = tm.mkBoolean(True)
        bit_condition = tm.mkTerm(Kind.AND, tm.mkTerm(Kind.NOT, x_vars[k]), y_vars[k])
        cond_k = tm.mkTerm(Kind.AND, prefix, bit_condition)
        conditions.append(cond_k)
    if conditions:
        return tm.mkTerm(Kind.OR, *conditions)
    else:
        return tm.mkBoolean(False)

def sgeq_operation(X, Y, n):
    """
    Performs the signed greater-than or equal-to (≥ₛ) comparison on two n-bit integers X and Y.
    
    The numbers are represented in two's complement. The comparison is encoded as follows:
      - If X is non-negative and Y is negative, then X ≥ Y holds.
      - If X is negative and Y is non-negative, then X ≥ Y does not hold.
      - If both X and Y have the same sign:
          * For non-negative numbers, X ≥ Y holds if X is NOT less than Y (unsigned).
          * For negative numbers, X ≥ Y holds if X is NOT less than Y (unsigned).
    
    In both same-sign cases, we use the unsigned less-than predicate on X and Y directly.
    """
    # Create a unique SMTLIB log file.
    filename = f"sgeq_{X}{Y}{n}.smt2"
    solver, tm, smt_file = create_solver_and_logger(filename)
    
    bool_sort = solver.getBooleanSort()
    x_bits = int_to_bits(X, n)
    y_bits = int_to_bits(Y, n)
    
    # Declare Boolean variables for bits of X and Y.
    x_vars = []
    y_vars = []
    for i in range(n):
        x_var = declareConst(tm, smt_file, bool_sort, f"x{i}")
        y_var = declareConst(tm, smt_file, bool_sort, f"y{i}")
        x_vars.append(x_var)
        y_vars.append(y_var)
    
    # Assert the bit values for X and Y.
    for i in range(n):
        x_val = solver.mkBoolean(x_bits[i])
        y_val = solver.mkBoolean(y_bits[i])
        assertFormula(solver, smt_file, tm.mkTerm(Kind.EQUAL, x_vars[i], x_val))
        assertFormula(solver, smt_file, tm.mkTerm(Kind.EQUAL, y_vars[i], y_val))
    
    # Identify the sign bits (most significant bits).
    s_x = x_vars[n-1]
    s_y = y_vars[n-1]
    
    # Build unsigned less-than formula for X <_u Y.
    ult_formula_XY = build_ult_formula(x_vars, y_vars, tm, n)
    
    # Case 1: X is non-negative and Y is negative -> X ≥ Y holds.
    case1 = tm.mkTerm(Kind.AND, tm.mkTerm(Kind.NOT, s_x), s_y)
    # Case 2: Both are non-negative -> X ≥ Y holds if X is NOT less than Y (unsigned).
    case2 = tm.mkTerm(Kind.AND, tm.mkTerm(Kind.NOT, s_x), tm.mkTerm(Kind.NOT, s_y), tm.mkTerm(Kind.NOT, ult_formula_XY))
    # Case 3: Both are negative -> X ≥ Y holds if X is NOT less than Y (unsigned).
    case3 = tm.mkTerm(Kind.AND, s_x, s_y, tm.mkTerm(Kind.NOT, ult_formula_XY))
    
    # Combine the cases with OR.
    r_formula = tm.mkTerm(Kind.OR, case1, case2, case3)
    
    # Declare the result variable r and assert its value.
    r = declareConst(tm, smt_file, bool_sort, "r")
    assertFormula(solver, smt_file, tm.mkTerm(Kind.EQUAL, r, r_formula))
    
    smt_file.write("(check-sat)\n")
    smt_file.write("(get-model)\n")
    
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
    """
    Runs a series of test cases for the signed greater-than or equal-to operation.
    Tests include small and large numbers with various bit-widths (n ≤ 64).
    """
    print("Test 1: sgeq_operation(5, 3, 4)  // 5 >= 3 should be true")
    sgeq_operation(5, 3, 4)
    
    print("\nTest 2: sgeq_operation(-2, -1, 4)  // -2 >= -1 should be false")
    sgeq_operation(-2, -1, 4)
    
    print("\nTest 3: sgeq_operation(-1, -1, 4)  // -1 >= -1 should be true")
    sgeq_operation(-1, -1, 4)
    
    print("\nTest 4: sgeq_operation(3, -2, 4)  // 3 >= -2 should be true")
    sgeq_operation(3, -2, 4)
    
    print("\nTest 5: sgeq_operation(100, 50, 8)  // 100 >= 50 should be true")
    sgeq_operation(100, 50, 8)
    
    print("\nTest 6: sgeq_operation(-100, -50, 8)  // -100 >= -50 should be false")
    sgeq_operation(-100, -50, 8)
    
    print("\nTest 7: sgeq_operation(-50, -100, 8)  // -50 >= -100 should be true")
    sgeq_operation(-50, -100, 8)
    
    print("\nTest 8: sgeq_operation(32767, -32768, 16)  // 32767 >= -32768 should be true")
    sgeq_operation(32767, -32768, 16)
    
    print("\nTest 9: sgeq_operation(-32768, 32767, 16)  // -32768 >= 32767 should be false")
    sgeq_operation(-32768, 32767, 16)
    
    print("\nTest 10: sgeq_operation(123456789012345, 123456789012345, 64)  // equal numbers should be true")
    sgeq_operation(123456789012345, 123456789012345, 64)
    
    print("\nTest 11: sgeq_operation(-9223372036854775808, 9223372036854775807, 64)  // min < max, should be false")
    sgeq_operation(-9223372036854775808, 9223372036854775807, 64)
    
    print("\nTest 12: sgeq_operation(9223372036854775807, -9223372036854775808, 64)  // max >= min, should be true")
    sgeq_operation(9223372036854775807, -9223372036854775808, 64)
    
    print("\nTest 13: sgeq_operation(-1000, -1000, 16)  // equal negative numbers, should be true")
    sgeq_operation(-1000, -1000, 16)
    
    print("\nTest 14: sgeq_operation(0, 0, 8)  // 0 >= 0 should be true")
    sgeq_operation(0, 0, 8)
    
    print("\nTest 15: sgeq_operation(-1, 0, 8)  // -1 >= 0 should be false")
    sgeq_operation(-1, 0, 8)
    
    print("\nTest 16: sgeq_operation(0, -1, 8)  // 0 >= -1 should be true")
    sgeq_operation(0, -1, 8)


if __name__ == "__main__":
    run_tests()
