from pt_smt_verification import run_smt_verification

# 1. Valid Metrics (all long trade, valid signals)
def get_valid_metrics():
    return {
        "max_drawdown": 0.1,
        "zscore_values": [-2.5, -2.2, -1.8, 0.2, 2.1, 1.8],
        "buy_signals":    [True, False, False, False, False, False],
        "sell_signals":   [False, False, False, False, True, False],
        "entry_prices":   [90, 90, 90, 0, 0, 0],
        "close_prices":   [90, 91, 95, 95, 95, 96],
        "total_profit":   5.0,
        "win_rate":       1.0,
        "sharpe_ratio":   1.25,
        "z_threshold":    2.0,
        # Directions: trade open (long) on bars 0-2, then flat.
        "directions":     [1, 1, 1, 0, 0, 0],
        "stop_loss_triggered": False,
        "stop_loss_triggers": [False, False, False, False, False, False]
    }

# 2. Conflicting Signals (should fail: buy and sell true on same bar)
def get_conflicting_signals_metrics():
    return {
        "max_drawdown": 0.1,
        "zscore_values": [-2.5, -2.0, -1.5, -2.1, 2.2, 1.5],
        "buy_signals":    [False, False, False, True, True, False],
        "sell_signals":   [False, False, False, True, True, False],
        "entry_prices":   [90, 90, 90, 90, 90, 90],
        "close_prices":   [90, 91, 92, 93, 94, 95],
        "total_profit":   0.0,
        "win_rate":       0.0,
        "sharpe_ratio":   0.0,
        "z_threshold":    2.0,
        "directions":     [1, 1, 1, 1, 1, 1],
        "stop_loss_triggered": False,
        "stop_loss_triggers": [False]*6
    }

# 3. Invalid Buy Condition (should fail: buy signal when zscore is not low enough)
def get_invalid_buy_condition_metrics():
    return {
        "max_drawdown": 0.1,
        "zscore_values": [-1.5, -1.2, -1.0, 0.5, 2.1, 1.8],  # -1.5 is not < -2.0
        "buy_signals":    [True, False, False, False, False, False],
        "sell_signals":   [False, False, False, False, True, False],
        "entry_prices":   [90]*6,
        "close_prices":   [90, 91, 92, 93, 95, 96],
        "total_profit":   5.0,
        "win_rate":       1.0,
        "sharpe_ratio":   1.0,
        "z_threshold":    2.0,
        "directions":     [1]*6,
        "stop_loss_triggered": False,
        "stop_loss_triggers": [False]*6
    }

# 4. Invalid Sell Condition (should fail: sell signal when zscore is not high enough)
def get_invalid_sell_condition_metrics():
    return {
        "max_drawdown": 0.1,
        "zscore_values": [-2.5, -2.2, 1.9, 0.5, 2.1, 1.8],  # 1.9 is not > 2.0
        "buy_signals":    [True, False, False, False, False, False],
        "sell_signals":   [False, False, True, False, False, False],
        "entry_prices":   [90]*6,
        "close_prices":   [90, 91, 92, 93, 95, 96],
        "total_profit":   5.0,
        "win_rate":       1.0,
        "sharpe_ratio":   1.0,
        "z_threshold":    2.0,
        "directions":     [1]*6,
        "stop_loss_triggered": False,
        "stop_loss_triggers": [False]*6
    }

# 5. Invalid Stop-Loss Trigger (should fail for long trade: stop-loss triggered when spread is not below 0.95*entry)
def get_invalid_stop_loss_metrics():
    return {
        "max_drawdown": 0.1,
        "zscore_values": [-2.5, -2.2, -1.8, 0.5, 2.1, 1.8],
        "buy_signals":    [True, False, False, False, False, False],
        "sell_signals":   [False]*6,
        "entry_prices":   [100]*6,
        # For a long trade, if stop loss triggers, the close must be below 95 (0.95*100).
        # Here, at bar 3, close is 97.
        "close_prices":   [94, 95, 96, 97, 98, 97],
        "total_profit":   -4.0,
        "win_rate":       0.0,
        "sharpe_ratio":   -1.0,
        "z_threshold":    2.0,
        "directions":     [1]*6,
        "stop_loss_triggered": True,
        "stop_loss_triggers": [False, False, False, True, False, False]
    }

# 6. High Drawdown (should fail: overall risk violation)
def get_high_drawdown_metrics():
    return {
        "max_drawdown": 0.25,  # Exceeds 0.20 threshold
        "zscore_values": [-2.5, -2.2, -1.8, 0.5, 2.1, 1.8],
        "buy_signals":    [True, False, False, False, False, False],
        "sell_signals":   [False]*6,
        "entry_prices":   [90]*6,
        "close_prices":   [90, 91, 92, 93, 94, 95],
        "total_profit":   5.0,
        "win_rate":       1.0,
        "sharpe_ratio":   1.5,
        "z_threshold":    2.0,
        "directions":     [1]*6,
        "stop_loss_triggered": False,
        "stop_loss_triggers": [False]*6
    }

# 7. Mixed Trades (long then short) - edited to fail the short trade stop-loss condition.
def get_mixed_trades_metrics():
    # Trade 1: Long trade from bar 0 to 2 (profit = 95-90 = 5)
    # Trade 2: Short trade from bar 3 to 5 should have profit = 110-108 = 2.
    # To force a failure on the short trade, we change bar 3 close to 116.
    return {
        "max_drawdown": 0.1,
        "zscore_values": [-2.5, -2.3, 0.2, 2.1, 2.3, -0.5],
        "buy_signals":    [True, False, False, False, False, False],
        "sell_signals":   [False, False, False, True, False, False],
        "entry_prices":   [90, 90, 0, 110, 110, 0],
        "close_prices":   [90, 91, 95, 116, 112, 108],  # Bar 3: 116 > 1.05*110 (115.5) with no stop-loss trigger.
        "total_profit":   7.0,
        "win_rate":       1.0,
        "sharpe_ratio":   1.5,
        "z_threshold":    2.0,
        "directions":     [1, 1, 0, -1, -1, 0],
        "stop_loss_triggered": False,
        "stop_loss_triggers": [False]*6
        
    }


# 8. Long Trade with Stop-Loss Triggered (should fail)
def get_long_stop_loss_metrics():
    # For a long trade, if stop-loss is triggered, close must be < 0.95*entry.
    # With entry=90, threshold = 85.5. Here we set close=90, which violates the condition.
    return {
        "max_drawdown": 0.1,
        "zscore_values": [-2.5, -2.3],
        "buy_signals":    [True, False],
        "sell_signals":   [False, False],
        "entry_prices":   [90, 90],  # Keep the trade open.
        "close_prices":   [90, 90],  # 90 is not < 85.5 → violation.
        "total_profit":   -2.0,
        "win_rate":       0.0,
        "sharpe_ratio":   -1.0,
        "z_threshold":    2.0,
        "directions":     [1, 1],
        "stop_loss_triggered": True,
        "stop_loss_triggers": [False, True]
    }

# 9. Short Trade with Stop-Loss Triggered (should fail)
def get_short_stop_loss_metrics():
    # For a short trade, if stop loss is triggered, close must be > 1.05*entry.
    # With entry = 110, threshold = 115.5. We set close = 113, which is not > 115.5 → should fail.
    return {
        "max_drawdown": 0.1,
        "zscore_values": [2.1, 2.3],
        "buy_signals":    [False, False],
        "sell_signals":   [True, False],
        "entry_prices":   [110, 110],  # Keep the trade open for both bars.
        "close_prices":   [110, 113],  # 113 is not greater than 115.5 → violation.
        "total_profit":   -6.0,
        "win_rate":       0.0,
        "sharpe_ratio":   -1.0,
        "z_threshold":    2.0,
        "directions":     [-1, -1],  # Trade remains short on both bars.
        "stop_loss_triggered": True,
        "stop_loss_triggers": [False, True]
    }


def run_all_tests():
    test_cases = {
        "Valid Metrics": get_valid_metrics,
        "Conflicting Signals": get_conflicting_signals_metrics,
        "Invalid Buy Condition": get_invalid_buy_condition_metrics,
        "Invalid Sell Condition": get_invalid_sell_condition_metrics,
        "Invalid Stop Loss Trigger": get_invalid_stop_loss_metrics,
        "High Drawdown": get_high_drawdown_metrics,
        "Mixed Trades": get_mixed_trades_metrics,
        "Long Stop-Loss Triggered": get_long_stop_loss_metrics,
        "Short Stop-Loss Triggered": get_short_stop_loss_metrics,
    }

    for name, func in test_cases.items():
        print(f"\n=== Testing {name} ===")
        metrics = func()
        result = run_smt_verification(metrics)
        print(f"Test {name} Result:", result)
        print("\n" + "=" * 50 + "\n")

if __name__ == "__main__":
    run_all_tests()
