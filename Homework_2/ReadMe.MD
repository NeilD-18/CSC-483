# CSC 483 - Homework 2

This directory contains Python scripts that generate SMT-LIB (`.smt2`) files for various logical operations using the **cvc5** SMT solver.

---

## 📂 Files Description

Each file generates a corresponding `.smt2` file and saves it in the `tests/` directory.

### **Propositional Logic Implementations**
- `and.py` – Computes bitwise AND of two n-bit integers.
- `eq.py` – Checks equality of two n-bit integers.
- `not.py` – Computes bitwise NOT of an n-bit integer.
- `or.py` – Computes bitwise OR of two n-bit integers.
- `sgeq.py` – Checks signed greater-than-or-equal (`≥s`) of two n-bit integers.
- `ult.py` – Checks unsigned less-than (`<u`) of two n-bit integers.

### **Bit-Vector Theory Implementations**
- `andsmt.py` – Bitwise AND using bit-vectors.
- `eqsmt.py` – Equality check using bit-vectors.
- `notsmt.py` – Bitwise NOT using bit-vectors.
- `orsmt.py` – Bitwise OR using bit-vectors.
- `sgeqsmt.py` – Signed greater-than-or-equal using bit-vectors.
- `ultsmt.py` – Unsigned less-than using bit-vectors.

---

## ⚙️ Setup & Installation

### **1. Clone the Repository**
```bash
git clone https://github.com/NeilD-18/CSC-483.git
cd CSC-483/Homework_2
```

### **2. Install Dependencies**
Ensure you have Python 3 installed, then install `cvc5`:
```bash
pip install cvc5
```

### **3. Ensure the `tests/` Directory Exists**
Since `.smt2` files are stored in `tests/`, make sure the directory exists:
```bash
mkdir -p tests
```

---

## 🚀 Running a Script

To execute any script and generate an SMT-LIB file:

```bash
python <filename>.py
```

### **Example Usage**
```bash
python and.py
```
This will generate `tests/and.smt2` containing the SMTLIB encoding.

To run a bit-vector theory-based script:
```bash
python andsmt.py
```

---

## 🛠️ Troubleshooting

### **ModuleNotFoundError: No module named 'cvc5'**
Ensure `cvc5` is installed:
```bash
pip install cvc5
```

### **Missing `tests/` Directory**
If `.smt2` files are not generated, manually create the directory:
```bash
mkdir -p tests
```


