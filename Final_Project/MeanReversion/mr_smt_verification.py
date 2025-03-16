from z3 import *
from mr_backtest import run_mr_backtest

def run_smt_verification(metrics):
    print("\n🔍 Backtest Metrics:", metrics)

    solver = Solver()
    failing_constraints = []
    num_steps = len(metrics["zscore_values"])
    z_threshold = metrics["z_threshold"]  # from the strategy

    for i in range(num_steps):
        zscore_val = metrics["zscore_values"][i]
        close_val = metrics["close_prices"][i]
        buy_signal_val = metrics["buy_signals"][i]
        sell_signal_val = metrics["sell_signals"][i]
        stop_loss_val = metrics["stop_loss_triggers"][i]
        entry_price_val = metrics["entry_prices"][i]

        # Define Z3 variables
        step_zscore = Real(f'zscore_{i}')
        step_close = Real(f'close_{i}')
        step_buy_signal = Bool(f'buy_signal_{i}')
        step_sell_signal = Bool(f'sell_signal_{i}')
        step_stop_loss = Bool(f'stop_loss_{i}')
        step_entry_price = Real(f'entry_price_{i}')

        # Constraint 1: If a buy signal, then zscore < -z_threshold
        c1 = Implies(step_buy_signal, step_zscore < -z_threshold)
        solver.assert_and_track(c1, f"c1_Buy_Condition_{i}")

        # Constraint 2: If a sell signal, then zscore > z_threshold
        c2 = Implies(step_sell_signal, step_zscore > z_threshold)
        solver.assert_and_track(c2, f"c2_Sell_Condition_{i}")

        # Constraint 3: No simultaneous buy & sell
        c3 = Not(And(step_buy_signal, step_sell_signal))
        solver.assert_and_track(c3, f"c3_No_Conflicting_Trades_{i}")

        # Constraint 4: If buy signal, stop-loss should not trigger on the same bar
        c4 = Implies(step_buy_signal, Not(step_stop_loss))
        solver.assert_and_track(c4, f"c4_Stop_Loss_Not_Immediate_{i}")

        # Constraint 5: Stop-loss validation (only if entry_price > 0)
        if entry_price_val > 0:
            c5 = And(
                Implies(step_stop_loss, step_close < 0.95 * step_entry_price),
                Implies(Not(step_stop_loss), step_close >= 0.95 * step_entry_price)
            )
            solver.assert_and_track(c5, f"c5_Stop_Loss_Correct_{i}")

        # Assign the real data
        solver.add(step_zscore == zscore_val)
        solver.add(step_close == close_val)
        solver.add(step_buy_signal == buy_signal_val)
        solver.add(step_sell_signal == sell_signal_val)
        solver.add(step_stop_loss == stop_loss_val)
        solver.add(step_entry_price == entry_price_val)

    # Constraint 6: Overall risk constraint on max drawdown
    max_drawdown = Real('max_drawdown')
    c6 = max_drawdown <= 0.16
    solver.assert_and_track(c6, "c6_Max_Drawdown")
    solver.add(max_drawdown == metrics["max_drawdown"])

    # Solve
    result = solver.check()
    if result == sat:
        print("SMT Verification Passed!")
        return {"SMT Verification": "Passed", "Failing Constraints": []}
    else:
        print("SMT Verification Failed!\nDebugging Failing Constraints:")
        unsat_core = solver.unsat_core()
        if unsat_core:
            failing_constraints = [str(constraint) for constraint in unsat_core]
            for constraint in failing_constraints:
                print(f"- {constraint}")
        else:
            print("⚠ No specific conflicting constraints found, but verification is UNSAT.")

        return {"SMT Verification": "Failed", "Failing Constraints": failing_constraints}

if __name__ == "__main__":
    real_metrics = run_mr_backtest("AAPL")
    verification_results = run_smt_verification(real_metrics)
    print("Verification Results:", verification_results)
