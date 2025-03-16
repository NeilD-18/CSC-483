from mac_smt_verification import run_smt_verification

# 1. Valid Case (Should Pass)
def get_valid_metrics():
    return {
        "max_drawdown": 0.12,  # Below threshold
        "stop_loss_triggered": True,  
        "stop_loss_triggers": [False, False, False, False, True, False],  # Correct stop-loss trigger at step 4
        "sma_short_values": [102, 103, 104, 105, 106, 107],
        "sma_long_values":  [100, 104, 102, 103, 104, 105],
        "buy_signals":      [True, False, False, False, False, False],  # Buy only at step 0
        "sell_signals":     [False, True, False, False, False, False],  # Sell at step 1
        "entry_prices":     [100, 100, 100, 100, 100, 100],
        "close_prices":     [102, 103, 104, 100, 80, 107],
        "total_profit":     3.00,   # One trade: profit = 103 - 100 = 3
        "win_rate":         1.0,    # 100% win rate (one trade, positive profit)
        "sharpe_ratio":     1.25    # Dummy Sharpe ratio
    }

# 2. Conflicting Signals (Should Fail)
def get_conflicting_signals_metrics():
    return {
        "max_drawdown": 0.10,
        "stop_loss_triggered": False,
        "stop_loss_triggers": [False, False, False, False, False, False],
        "sma_short_values": [105, 106, 107, 108, 109, 110],
        "sma_long_values":  [100, 101, 102, 103, 104, 105],
        # Both buy and sell are true at steps 3 and 4, which is conflicting.
        "buy_signals":      [False, False, False, True, True, False],
        "sell_signals":     [False, False, False, True, True, False],
        "entry_prices":     [100, 100, 100, 100, 100, 100],
        "close_prices":     [101, 102, 103, 104, 105, 106],
        "total_profit":     2.00,
        "win_rate":         0.5,
        "sharpe_ratio":     0.75
    }

# 3. Invalid Buy Signal (Should Fail)
def get_invalid_buy_signal_metrics():
    return {
        "max_drawdown": 0.15,
        "stop_loss_triggered": False,
        "stop_loss_triggers": [False, False, False, False, False, False],
        # Buy signal is true at step 0 even though sma_short (95) is below sma_long (100)
        "sma_short_values": [95, 96, 97, 98, 99, 100],
        "sma_long_values":  [100, 100, 100, 100, 100, 100],
        "buy_signals":      [True, False, False, False, False, False],
        "sell_signals":     [False, False, False, False, False, False],
        "entry_prices":     [100, 100, 100, 100, 100, 100],
        "close_prices":     [101, 102, 103, 104, 105, 106],
        "total_profit":     -2.00,   # Negative profit since the trade was executed in error.
        "win_rate":         0.0,
        "sharpe_ratio":     -0.5
    }

# 4. Invalid Stop-Loss Trigger (Should Fail)
def get_invalid_stop_loss_metrics():
    return {
        "max_drawdown": 0.14,
        "stop_loss_triggered": True,
        # At step 5, stop-loss is triggered, but the close price (97) is not < 95 (0.95*100)
        "stop_loss_triggers": [False, False, False, False, False, True],
        "sma_short_values": [105, 106, 107, 108, 109, 110],
        "sma_long_values":  [100, 101, 102, 103, 104, 105],
        "buy_signals":      [True, False, False, False, False, False],
        "sell_signals":     [False, False, False, False, False, False],
        "entry_prices":     [100, 100, 100, 100, 100, 100],
        "close_prices":     [101, 102, 103, 98, 97, 97],  # At step 5: 97 is not < 95
        "total_profit":     5.00,
        "win_rate":         1.0,
        "sharpe_ratio":     1.50
    }

# 5. Missing Stop-Loss (Should Fail)
def get_missing_stop_loss_metrics():
    return {
        "max_drawdown": 0.17,
        "stop_loss_triggered": False,
        # None of the steps trigger stop-loss, even though they should.
        "stop_loss_triggers": [False, False, False, False, False, False],
        "sma_short_values": [105, 106, 107, 108, 109, 110],
        "sma_long_values":  [100, 101, 102, 103, 104, 105],
        "buy_signals":      [True, False, False, False, False, False],
        "sell_signals":     [False, False, False, False, False, False],
        "entry_prices":     [100, 100, 100, 100, 100, 100],
        # At step 5, close price is 90, so stop-loss should trigger.
        "close_prices":     [101, 102, 103, 99, 98, 90],
        "total_profit":     3.00,
        "win_rate":         1.0,
        "sharpe_ratio":     1.00
    }

# 6. High Drawdown (Should Fail)
def get_high_drawdown_metrics():
    return {
        "max_drawdown": 0.20,  # Too high (threshold is 0.16)
        "stop_loss_triggered": False,
        "stop_loss_triggers": [False, False, False, False, False, False],
        "sma_short_values": [110, 109, 108, 107, 106, 105],
        "sma_long_values":  [100, 100, 100, 100, 100, 100],
        "buy_signals":      [True, False, False, False, False, False],
        "sell_signals":     [False, False, False, False, False, False],
        "entry_prices":     [100, 100, 100, 100, 100, 100],
        "close_prices":     [101, 102, 103, 99, 98, 95],
        "total_profit":     10.00,
        "win_rate":         1.0,
        "sharpe_ratio":     2.00
    }
    
def run_all_tests():
    test_cases = {
        "Valid Metrics": get_valid_metrics,
        "Conflicting Signals": get_conflicting_signals_metrics,
        "Invalid Buy Signal": get_invalid_buy_signal_metrics,
        "Invalid Stop Loss Trigger": get_invalid_stop_loss_metrics,
        "Missing Stop Loss": get_missing_stop_loss_metrics,
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
