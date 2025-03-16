from mr_smt_verification import run_smt_verification

# 1. Valid Case (Should Pass)
def get_valid_metrics():
    return {
        "max_drawdown": 0.1,  # Below threshold (≤ 0.16)
        "stop_loss_triggered": False,
        "stop_loss_triggers": [False, False, False, False, False, False],
        # zscore values computed from (close - SMA)/std.
        # Here, -2.5 < -2.0 so a buy signal is valid at step 0,
        # and 2.1 > 2.0 so a sell signal is valid at step 4.
        "zscore_values": [-2.5, -2.2, -1.8, 0.5, 2.1, 1.8],
        "buy_signals":      [True,  False, False, False, False, False],
        "sell_signals":     [False, False, False, False, True,  False],
        "entry_prices":     [90, 90, 90, 90, 90, 90],
        "close_prices":     [90, 91, 92, 93, 95, 96],
        "total_profit":     5.0,
        "win_rate":         1.0,
        "sharpe_ratio":     1.25,
        "z_threshold":      2.0  # The threshold used in the strategy.
    }

# 2. Conflicting Signals (Should Fail)
def get_conflicting_signals_metrics():
    return {
        "max_drawdown": 0.1,
        "stop_loss_triggered": False,
        "stop_loss_triggers": [False, False, False, False, False, False],
        "zscore_values": [-2.5, -2.0, -1.5, -2.1, 2.2, 1.5],
        # Both buy and sell are True at steps 3 and 4 (conflict).
        "buy_signals":      [False, False, False, True, True, False],
        "sell_signals":     [False, False, False, True, True, False],
        "entry_prices":     [90, 90, 90, 90, 90, 90],
        "close_prices":     [90, 91, 92, 93, 94, 95],
        "total_profit":     0.0,
        "win_rate":         0.0,
        "sharpe_ratio":     0.0,
        "z_threshold":      2.0
    }

# 3. Invalid Buy Condition (Should Fail)
def get_invalid_buy_condition_metrics():
    return {
        "max_drawdown": 0.1,
        "stop_loss_triggered": False,
        "stop_loss_triggers": [False, False, False, False, False, False],
        # Buy signal triggered when zscore is not < -z_threshold.
        # Here at step 0, zscore is -1.5 (which is not less than -2.0).
        "zscore_values": [-1.5, -1.2, -1.0, 0.5, 2.1, 1.8],
        "buy_signals":      [True, False, False, False, False, False],
        "sell_signals":     [False, False, False, False, True, False],
        "entry_prices":     [90, 90, 90, 90, 90, 90],
        "close_prices":     [90, 91, 92, 93, 95, 96],
        "total_profit":     0.0,
        "win_rate":         0.0,
        "sharpe_ratio":     0.0,
        "z_threshold":      2.0
    }

# 4. Invalid Sell Condition (Should Fail)
def get_invalid_sell_condition_metrics():
    return {
        "max_drawdown": 0.1,
        "stop_loss_triggered": False,
        "stop_loss_triggers": [False, False, False, False, False, False],
        # Sell signal triggered when zscore is not > z_threshold.
        # At step 2, zscore is 1.9 which is not > 2.0.
        "zscore_values": [-2.5, -2.2, 1.9, 0.5, 2.1, 1.8],
        "buy_signals":      [True, False, False, False, False, False],
        "sell_signals":     [False, False, True, False, False, False],
        "entry_prices":     [90, 90, 90, 90, 90, 90],
        "close_prices":     [90, 91, 92, 93, 95, 96],
        "total_profit":     5.0,
        "win_rate":         1.0,
        "sharpe_ratio":     1.0,
        "z_threshold":      2.0
    }

# 5. Invalid Stop-Loss Trigger (Should Fail)
def get_invalid_stop_loss_metrics():
    return {
        "max_drawdown": 0.1,
        "stop_loss_triggered": True,
        # At step 5, stop-loss is triggered but the close price is not < 0.95 * entry_price.
        "stop_loss_triggers": [False, False, False, False, False, True],
        "zscore_values":     [-2.5, -2.2, -1.8, 0.5, 2.1, 1.8],
        "buy_signals":       [True, False, False, False, False, False],
        "sell_signals":      [False, False, False, False, False, False],
        "entry_prices":      [100, 100, 100, 100, 100, 100],
        # At step 5, close is 97 which is not less than 95 (0.95 * 100).
        "close_prices":      [94, 95, 96, 97, 98, 97],
        "total_profit":      -4.0,
        "win_rate":          0.0,
        "sharpe_ratio":      -1.0,
        "z_threshold":       2.0
    }

# 6. High Drawdown (Should Fail)
def get_high_drawdown_metrics():
    return {
        "max_drawdown": 0.20,  # Exceeds the risk threshold (0.16)
        "stop_loss_triggered": False,
        "stop_loss_triggers": [False, False, False, False, False, False],
        "zscore_values":      [-2.5, -2.2, -1.8, 0.5, 2.1, 1.8],
        "buy_signals":       [True, False, False, False, False, False],
        "sell_signals":      [False, False, False, False, False, False],
        "entry_prices":      [90, 90, 90, 90, 90, 90],
        "close_prices":      [90, 91, 92, 93, 94, 95],
        "total_profit":      5.0,
        "win_rate":          1.0,
        "sharpe_ratio":      1.5,
        "z_threshold":       2.0
    }
    
def run_all_tests():
    test_cases = {
        "Valid Metrics": get_valid_metrics,
        "Conflicting Signals": get_conflicting_signals_metrics,
        "Invalid Buy Condition": get_invalid_buy_condition_metrics,
        "Invalid Sell Condition": get_invalid_sell_condition_metrics,
        "Invalid Stop Loss Trigger": get_invalid_stop_loss_metrics,
        "High Drawdown": get_high_drawdown_metrics
    }

    for name, func in test_cases.items():
        print(f"\n=== Testing {name} ===")
        metrics = func()
        result = run_smt_verification(metrics)
        print(f"Test {name} Result:", result)
        print("\n" + "=" * 50 + "\n")

if __name__ == "__main__":
    run_all_tests()
