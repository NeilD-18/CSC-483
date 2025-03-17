from z3 import *
from pt_backtest import run_pt_backtest

def run_smt_verification(metrics):
    """
    Runs SMT verification on pairs trading metrics.
    Returns a dict with verification result and any failing constraints.
    Assumes metrics include a 'directions' list with values:
      1 for long trades, -1 for short trades, 0 for flat.
    """
    print("\n🔍 Pairs Trading Metrics:", metrics)
    solver = Solver()
    failing_constraints = []
    
    num_steps = len(metrics["zscore_values"])
    z_threshold = metrics["z_threshold"]

    for i in range(num_steps):
        # Retrieve metric values for this time step.
        zscore_val = metrics["zscore_values"][i]
        spread_val = metrics["close_prices"][i]  # spread series
        buy_signal_val = metrics["buy_signals"][i]
        sell_signal_val = metrics["sell_signals"][i]
        stop_loss_val = metrics["stop_loss_triggers"][i]
        entry_price_val = metrics["entry_prices"][i]
        direction_val = metrics.get("directions", [0]*num_steps)[i]  # default 0 if not provided

        # Define Z3 variables for this time step.
        step_zscore = Real(f'zscore_{i}')
        step_spread = Real(f'spread_{i}')
        step_buy_signal = Bool(f'buy_signal_{i}')
        step_sell_signal = Bool(f'sell_signal_{i}')
        step_stop_loss = Bool(f'stop_loss_{i}')
        step_entry_price = Real(f'entry_price_{i}')
        step_direction = Int(f'direction_{i}')  # 1 for long, -1 for short, 0 for none

        # Constraint 1: Buy signal implies zscore < -z_threshold.
        solver.assert_and_track(Implies(step_buy_signal, step_zscore < -z_threshold), f"c1_Buy_Condition_{i}")
        # Constraint 2: Sell signal implies zscore > z_threshold.
        solver.assert_and_track(Implies(step_sell_signal, step_zscore > z_threshold), f"c2_Sell_Condition_{i}")
        # Constraint 3: No simultaneous buy and sell.
        solver.assert_and_track(Not(And(step_buy_signal, step_sell_signal)), f"c3_No_Conflicting_Trades_{i}")
        # Constraint 4: If a buy signal is triggered, stop-loss should not trigger on the same bar.
        solver.assert_and_track(Implies(step_buy_signal, Not(step_stop_loss)), f"c4_Stop_Loss_Not_Immediate_{i}")

        # Constraint 5: Stop-loss validation if an entry exists.
        if entry_price_val != 0:
            if direction_val == 1:
                # For a long trade:
                solver.assert_and_track(Implies(step_stop_loss, step_spread < 0.95 * step_entry_price),
                                          f"c5a_Stop_Loss_Trigger_Long_{i}")
                solver.assert_and_track(Implies(Not(step_stop_loss), step_spread >= 0.95 * step_entry_price),
                                          f"c5b_Stop_Loss_NoTrigger_Long_{i}")
            elif direction_val == -1:
                # For a short trade:
                solver.assert_and_track(Implies(step_stop_loss, step_spread > 1.05 * step_entry_price),
                                          f"c5a_Stop_Loss_Trigger_Short_{i}")
                solver.assert_and_track(Implies(Not(step_stop_loss), step_spread <= 1.05 * step_entry_price),
                                          f"c5b_Stop_Loss_NoTrigger_Short_{i}")
            # (If direction is 0, skip stop-loss constraints)

        # Assign concrete values.
        solver.add(step_zscore == zscore_val)
        solver.add(step_spread == spread_val)
        solver.add(step_buy_signal == buy_signal_val)
        solver.add(step_sell_signal == sell_signal_val)
        solver.add(step_stop_loss == stop_loss_val)
        solver.add(step_entry_price == entry_price_val)
        solver.add(step_direction == direction_val)

    # Constraint 6: Overall risk constraint on max drawdown.
    max_drawdown = Real('max_drawdown')
    solver.assert_and_track(max_drawdown <= 0.20, "c6_Max_Drawdown")
    solver.add(max_drawdown == metrics["max_drawdown"])

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
    # Run the pairs trading backtest on two symbols (e.g., AAPL and MSFT) and verify.
    real_metrics = run_pt_backtest("AAPL", "MSFT")
    verification_results = run_smt_verification(real_metrics)
    print("Verification Results:", verification_results)
