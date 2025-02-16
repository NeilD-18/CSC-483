import cvc5
import shutil
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
    Creates a new cvc5 solver with its TermManager and opens an SMTLIB log file.
    Returns the tuple (solver, term_manager, smt_file).
    """
    tm = cvc5.TermManager()
    solver = cvc5.Solver(tm)
    smt_file = open(filename, "w")
    
    # Set logic and options
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
    If SAT, logs the get-model command.
    Returns the solver result.
    """
    smt_file.write("(check-sat)\n")
    result = solver.checkSat()
    if result.isSat():
        smt_file.write("(get-model)\n")
    return result

def or_operation(X, Y, n):
    """
    Performs the bitwise OR operation on two n-bit integers X and Y using cvc5's propositional logic encoding.
    
    Steps:
      1. Convert X and Y to their n-bit binary representations (LSB at index 0).
      2. Declare Boolean variables x0, x1, ..., x(n-1) and y0, y1, ..., y(n-1) for the input bits.
      3. Assert that each variable equals its corresponding Boolean value.
      4. Declare Boolean variables r0, r1, ..., r(n-1) for the result.
      5. For each i, assert that r_i = x_i OR y_i.
      6. Check satisfiability and extract the model for r bits.
      7. Output the result in binary (LSB-first and MSB-first) and in decimal.
      8. Log the SMTLIB commands to an .smt2 file, then move it to a designated folder.
    """
    # Create a unique SMT file for this operation
    filename = f"or_{X}_{Y}_{n}.smt2"
    solver, tm, smt_file = create_solver_and_logger(filename)
    
    # Get the Boolean sort and convert integers to n-bit binary representations.
    bool_sort = solver.getBooleanSort()
    x_bits = int_to_bits(X, n)
    y_bits = int_to_bits(Y, n)
    
    # Declare Boolean variables for each bit of X and Y.
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
    
    # Declare Boolean variables for the result bits r.
    r_vars = []
    for i in range(n):
        r_var = declareConst(tm, smt_file, bool_sort, f"r{i}")
        r_vars.append(r_var)
    
    # Encode the bitwise OR operation: for each bit, assert r_i = x_i OR y_i.
    for i in range(n):
        or_term = tm.mkTerm(Kind.OR, x_vars[i], y_vars[i])
        eq_term = tm.mkTerm(Kind.EQUAL, r_vars[i], or_term)
        assertFormula(solver, smt_file, eq_term)
    
    # Check satisfiability.
    result = checkSat(solver, smt_file)
    
    if result.isSat():
        # Extract result bits from the model.
        result_bits = []
        for i in range(n):
            model_val = solver.getValue(r_vars[i])
            bit = 1 if str(model_val) == "true" else 0
            result_bits.append(bit)
        
        # The result is in LSB-first order.
        binary_lsb = "".join(str(bit) for bit in result_bits)
        binary_msb = "".join(str(bit) for bit in reversed(result_bits))
        decimal_result = sum(bit * (1 << i) for i, bit in enumerate(result_bits))
        
        print("Bitwise OR Operation Result:")
        print("Binary (LSB-first):", binary_lsb)
        print("Binary (MSB-first):", binary_msb)
        print("Decimal:", decimal_result)
    else:
        print("SMT constraints are unsatisfiable. Something went wrong.")
    
    # Close the SMT file and move it to the tests folder.
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
