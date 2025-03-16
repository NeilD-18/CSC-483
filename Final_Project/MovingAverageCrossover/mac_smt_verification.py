from z3 import *
from mac_backtest import run_mac_backtest

def run_smt_verification(metrics):
    """ Runs SMT verification and returns results with failing constraints for debugging. """
    
    print("\n🔍 Backtest Metrics:", metrics)  # Debugging output

    solver = Solver()
    failing_constraints = []
    num_steps = len(metrics["sma_short_values"])

    for i in range(num_steps):
        # Retrieve values for this step
        sma_short_val = metrics["sma_short_values"][i]
        sma_long_val = metrics["sma_long_values"][i]
        buy_signal_val = metrics["buy_signals"][i]
        sell_signal_val = metrics["sell_signals"][i]
        stop_loss_val = metrics["stop_loss_triggers"][i]
        entry_price_val = metrics["entry_prices"][i]
        current_price_val = metrics["close_prices"][i]

        # Define Z3 variables for this step
        step_sma_short = Real(f'sma_short_{i}')
        step_sma_long = Real(f'sma_long_{i}')
        step_buy_signal = Bool(f'buy_signal_{i}')
        step_sell_signal = Bool(f'sell_signal_{i}')
        step_stop_loss = Bool(f'stop_loss_{i}')
        step_entry_price = Real(f'entry_price_{i}')
        step_current_price = Real(f'current_price_{i}')

        # Constraint 1: If a buy signal is triggered, then sma_short > sma_long.
        c1 = Implies(step_buy_signal, step_sma_short > step_sma_long)
        solver.assert_and_track(c1, f"c1_Buy_Condition_{i}")

        # Constraint 2: If a sell signal is triggered, then sma_short < sma_long.
        c2 = Implies(step_sell_signal, step_sma_short < step_sma_long)
        solver.assert_and_track(c2, f"c2_Sell_Condition_{i}")

        # Constraint 3: No simultaneous buy & sell signals.
        c3 = Not(And(step_buy_signal, step_sell_signal))
        solver.assert_and_track(c3, f"c3_No_Conflicting_Trades_{i}")

        # Constraint 4: If a buy signal is triggered, stop-loss should not trigger immediately.
        c4 = Implies(step_buy_signal, Not(step_stop_loss))
        solver.assert_and_track(c4, f"c4_Stop_Loss_Not_Immediate_{i}")

        # Constraint 5: Stop-loss validation (only if entry price > 0)
        if entry_price_val > 0:
            c5 = And(
                Implies(step_stop_loss, step_current_price < 0.95 * step_entry_price),
                Implies(Not(step_stop_loss), step_current_price >= 0.95 * step_entry_price)
            )
            solver.assert_and_track(c5, f"c5_Stop_Loss_Correct_{i}")

        # Assign real values to Z3 variables
        solver.add(step_sma_short == sma_short_val)
        solver.add(step_sma_long == sma_long_val)
        solver.add(step_buy_signal == buy_signal_val)
        solver.add(step_sell_signal == sell_signal_val)
        solver.add(step_stop_loss == stop_loss_val)
        solver.add(step_entry_price == entry_price_val)
        solver.add(step_current_price == current_price_val)

    # Overall risk constraint: max_drawdown ≤ 0.16
    max_drawdown = Real('max_drawdown')
    c6 = max_drawdown <= 0.16
    solver.assert_and_track(c6, "c6_Max_Drawdown")
    solver.add(max_drawdown == metrics["max_drawdown"])

    # Run Solver
    result = solver.check()

    if result == sat:
        print("SMT Verification Passed!")
        return {"SMT Verification": "Passed", "Failing Constraints": []}
    
    else:
        print("SMT Verification Failed!\n Debugging Why Verification Failed:")
        unsat_core = solver.unsat_core()
        
        if unsat_core:
            print("Conflicting Constraints Found:")
            failing_constraints = [str(constraint) for constraint in unsat_core]
            for constraint in failing_constraints:
                print(f"- {constraint}")
        else:
            print("⚠ No specific conflicting constraints found, but verification is UNSAT.")

        return {"SMT Verification": "Failed", "Failing Constraints": failing_constraints}

if __name__ == "__main__":
    real_metrics = run_mac_backtest("AAPL")
    verification_results = run_smt_verification(real_metrics)
    print("Verification Results:", verification_results)
