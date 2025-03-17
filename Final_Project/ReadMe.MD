# Automated Trading Strategy Verification Project

## 📖 Table of Contents
- [Overview](#overview)
- [Project Summary & Evaluation](#project-summary--evaluation)
  - [Objective](#1️⃣-what-was-the-objective-of-your-project)
  - [Did You Achieve the Objective?](#2️⃣-did-you-achieve-the-objective)
  - [How to Verify the Project](#3️⃣-how-can-you-verify-these-results)
  - [Challenges](#4️⃣-what-were-the-challenges)
- [How SMT Verification Works](#how-smt-verification-works)
- [How to Run the Code](#🚀-how-to-run-the-code)
- [Final Thoughts](#final-thoughts)
- [Credits](#credits)

## Overview
This project integrates **algorithmic trading strategies** with **formal verification using SMT (Satisfiability Modulo Theories)**. The implemented strategies include:

- **Moving Average Crossover (MAC)** → Trend-following strategy using short/long-term moving averages.
- **Mean Reversion (MR)** → Assumes price reverts to historical mean.
- **Pairs Trading (PT)** → Market-neutral strategy based on correlated asset spreads.

Each strategy is:

✅ **Backtested** using historical market data.  
✅ **Verified** using an SMT solver (Z3) to enforce logical constraints **at each time step**.  
✅ **Documented** with a **PDF report** showing performance and verification results.  

---

## **Project Summary & Evaluation**

### **1️⃣ What was the objective of your project?**
The initial goal of this project was to **investigate whether formal verification using SMT solvers can enhance backtesting** by identifying **logical flaws in quantitative trading strategies**.

However, **SMT solvers are not suitable for predictive modeling**, so the project focus shifted. Instead, I developed a **trading strategy verification system** where:
1. A **backtesting engine** generates trading signals and performance metrics.
2. An **SMT solver verifies the logical correctness** of those trades at **each time step**.
3. A **report generator** visualizes backtest performance and SMT validation results.

Thus, while the **original predictive SMT approach was abandoned**, the project successfully evolved into an **automated trading strategy verification system**.

### **2️⃣ Did you achieve the objective?**
✅ **Yes, but with refinements.**  
- **Successfully implemented a full backtesting system** for MAC, MR, and PT strategies.  
- **Integrated SMT verification** to check constraints at **each time step** (e.g., buy/sell logic, stop-loss conditions).  
- **Created automated pipelines** to run backtests, verify results, and generate reports.  
- **Generated reports that highlight SMT constraint failures** when rules are violated.

🟡 **However, the original plan to use SMT as a predictive tool was infeasible.** Instead, SMT is used **after** backtesting to validate that trades adhere to strategy rules.

### **3️⃣ How can you verify these results?**
To verify the project, follow these steps:

#### **1️⃣ Check the Code Structure**
📁 **Key Directories**:
- `PairsTrading/` → `pt_backtest.py`, `pt_smt_verification.py`, `pt_report.py`
- `MeanReversion/` → `mr_backtest.py`, `mr_smt_verification.py`, `mr_report.py`
- `MovingAverage/` → `mac_backtest.py`, `mac_smt_verification.py`, `mac_report.py`
- `test_*` → Synthetic test cases designed to **force SMT failures**.

#### **2️⃣ Run the Pipelines**
Each pipeline performs **backtesting, SMT verification, and report generation**.

```bash
python PairsTrading/pt_pipeline.py
python MeanReversion/mr_pipeline.py
python MovingAverage/mac_pipeline.py
```
✅ Fetches real historical data.  
✅ Runs a backtest to generate **step-by-step trading metrics**.  
✅ Feeds metrics into **Z3 SMT solver** for constraint checking.  
✅ Generates a **PDF report** with:
   - Performance metrics (profit, Sharpe ratio, win rate).
   - Trade execution graph.
   - SMT verification results.


#### 3️⃣ **Forcing SMT to Fail**
Each pipeline supports **synthetic test cases** that deliberately **violate SMT constraints**, ensuring the solver correctly detects logical flaws in strategy execution.

#### **Method 1: Manually Modifying Pipeline Code**
You can modify the pipeline script to use **synthetic test cases** instead of real market data. For example:

```python
fake_data_metrics = get_invalid_buy_condition_metrics()
smt_results = run_smt_verification(fake_data_metrics)
generate_pdf_report(fake_data_metrics, smt_results)
```
✔ **Expected Output (Failure Example):**
```
SMT Verification Failed!
Debugging Failing Constraints:
- c1_Buy_Condition_0
```
This confirms that the SMT solver **correctly fails** when constraints are violated.

---

#### **Method 2: Running the Test Scripts Directly**
Each `test_*` file contains **predefined failing test cases** designed to trigger SMT failures. These files contain an `if __name__ == "__main__"` block, so you can run them directly to observe constraint failures.

#### **Run a Specific Test Case**
```bash
python PairsTrading/test_pt_smt_verification.py  # Tests Pairs Trading SMT constraints
python MeanReversion/test_mr_smt_verification.py  # Tests Mean Reversion SMT constraints
python MovingAverageCrossover/test_mac_smt_verification.py  # Tests Moving Average Crossover SMT constraints
```

✔ **Expected Output Example:**
```
SMT Verification Failed!
Debugging Failing Constraints:
- c5b_Stop_Loss_NoTrigger_Long_0
```

This method ensures you can **quickly test individual constraints** and verify that SMT correctly catches invalid trading signals.

### **4️⃣ What were the challenges?**

✅ **Pairs Trading Complexity** → Originally, verifying **two separate stock price movements** was complex, but simplifying to **spread-based verification** reduced overhead and made SMT validation more efficient.  
✅ **Edge Case Handling** → Some trades were incorrectly classified as profitable due to **stop-loss conditions not triggering correctly**, requiring extra testing.  
✅ **Trade Direction Consistency** → Ensuring that a **long trade was always exited with a sell signal** (and vice versa) required additional constraints to prevent trades from persisting incorrectly.  


Despite these challenges, the project **successfully implemented automated verification for algorithmic trading strategies**.

---

## **How SMT Verification Works**
Each strategy was verified using **Z3 SMT constraints** to ensure logical correctness **at each time step**.

### **1️⃣ Moving Average Crossover (MAC) Verification**
The **Moving Average Crossover** strategy is verified using the following constraints:

- **C1: Buy Condition** → Buy signal must only trigger if the short-term moving average is above the long-term moving average.
- **C2: Sell Condition** → Sell signal must only trigger if the short-term moving average is below the long-term moving average.
- **C3: No Conflicting Trades** → Ensures there is no simultaneous buy and sell signal.
- **C4: Stop-Loss Validation** → A buy signal cannot have a stop-loss trigger on the same bar.
- **C5: Stop-Loss Handling** → Ensures stop-losses trigger **only when price moves beyond a certain threshold**.

✔ Example SMT Constraint:
```python
solver.assert_and_track(Implies(step_buy_signal, step_sma_short > step_sma_long), f"c1_Buy_Condition_{i}")
```

---

### **2️⃣ Mean Reversion (MR) Verification**
The **Mean Reversion** strategy is verified using the following constraints:

- **C1: Buy Condition** → Buy signal must only trigger if the stock price is significantly below the mean.
- **C2: Sell Condition** → Sell signal must only trigger if the stock price is significantly above the mean.
- **C3: No Conflicting Trades** → Ensures there is no simultaneous buy and sell signal.
- **C4: Stop-Loss Validation** → A buy signal cannot have a stop-loss trigger on the same bar.
- **C5: Stop-Loss Handling** → Ensures stop-losses trigger **only when the price moves significantly below its expected threshold**.

✔ Example SMT Constraint:
```python
solver.assert_and_track(Implies(step_buy_signal, step_zscore < -z_threshold), f"c1_Buy_Condition_{i}")
```

---

### **3️⃣ Pairs Trading (PT) Verification**
The **Pairs Trading** strategy is verified using the following constraints:

- **C1: Buy Condition** → Buy signal must trigger only when the spread between two stocks is significantly negative.
- **C2: Sell Condition** → Sell signal must trigger only when the spread between two stocks is significantly positive.
- **C3: No Conflicting Trades** → Ensures no simultaneous buy and sell signals.
- **C4: Stop-Loss Validation** → A buy signal cannot have a stop-loss trigger on the same bar.
- **C5: Stop-Loss Handling** → Stop-loss should trigger if price moves significantly beyond expected bounds.
- **C6: Drawdown Limit** → Ensures that the **maximum drawdown does not exceed** 20%.

✔ Example SMT Constraint:
```python
solver.assert_and_track(max_drawdown <= 0.20, "c6_Max_Drawdown")
```

Each strategy was **tested against synthetic data** designed to fail SMT constraints, ensuring robustness.

---


## 🚀 **How to Run the Code**
1️⃣ **Clone the Repository**
```bash
git clone https://github.com/NeilD-18/CSC-483.git
cd CSC-483/Final_Project
```

2️⃣ **Set Up a Virtual Environment**
```bash
python -m venv env
source env/bin/activate  # On Windows: env\Scripts\activate
```

3️⃣ **Install Dependencies**
```bash
pip install -r requirements.txt
```

4️⃣ **Run the Pipelines**
Each pipeline runs a **backtest**, verifies the results using **SMT**, and generates a **PDF report**.

```bash
python PairsTrading/pt_pipeline.py
python MeanReversion/mr_pipeline.py
python MovingAverage/mac_pipeline.py
```

5️⃣ **Check the Generated Reports**  
Reports will be saved in the same directory where the pipeline was executed.

For example:
- Running `python PairsTrading/pt_pipeline.py` → Report appears in `PairsTrading/`
- Running `python MeanReversion/mr_pipeline.py` → Report appears in `MeanReversion/`
- Running `python MovingAverage/mac_pipeline.py` → Report appears in `MovingAverage/`
---

## **Final Thoughts**
This project successfully **combined backtesting + SMT verification** to enforce **correct trade logic at each time step**. By testing **real and synthetic data**, we ensured **strict logical constraints were followed**, making trading strategies safer for real-world use.

---

## **Credits**
Developed by **Neil Daterao**, using:
- **Python** for backtesting & verification.
- **Z3 SMT Solver** for trade logic enforcement.
- **Matplotlib + ReportLab** for visualizations & PDFs.

