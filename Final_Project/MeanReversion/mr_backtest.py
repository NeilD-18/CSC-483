import backtrader as bt
import yfinance as yf
import pandas as pd
import statistics
import math
from datetime import datetime

class MeanReversionStrategy(bt.Strategy):
    params = (
        ("period", 20),       # Rolling window for mean & std
        ("z_threshold", 2.0)  # Z-score threshold
    )

    def __init__(self):
        # Rolling mean and standard deviation
        self.sma = bt.indicators.SimpleMovingAverage(self.data.close, period=self.params.period)
        self.std = bt.indicators.StandardDeviation(self.data.close, period=self.params.period)

        # Tracking variables
        self.zscore_values = []
        self.buy_signals = []
        self.sell_signals = []
        self.stop_loss_triggers = []
        self.entry_prices = []
        self.close_prices = []
        self.trade_profits = []
        self.max_drawdown = 0
        self.entry_price = None

    def next(self):
        current_close = self.data.close[0]
        current_sma = self.sma[0]
        current_std = self.std[0] if self.std[0] != 0 else 1e-9  # Avoid div by zero

        # Calculate z-score = (price - mean) / std
        zscore = (current_close - current_sma) / current_std
        self.zscore_values.append(zscore)
        self.close_prices.append(current_close)

        buy_signal = False
        sell_signal = False

        # 1) Buy if no position and zscore < -z_threshold
        if not self.position and zscore < -self.params.z_threshold:
            self.buy()
            self.entry_price = current_close
            buy_signal = True

        # 2) Sell if in position and zscore > z_threshold
        elif self.position and zscore > self.params.z_threshold:
            profit = current_close - self.entry_price
            self.trade_profits.append(profit)
            self.sell()
            sell_signal = True

        self.buy_signals.append(buy_signal)
        self.sell_signals.append(sell_signal)

        # Record entry price if in position, else 0
        if self.position and self.entry_price is not None:
            self.entry_prices.append(self.entry_price)
        else:
            self.entry_prices.append(0)

        # Compute rolling max drawdown over last 100 bars
        recent_prices = self.data.close.get(size=100)
        peak = max(recent_prices) if recent_prices else current_close
        drawdown = (peak - current_close) / peak
        self.max_drawdown = max(self.max_drawdown, drawdown)

        # Simple stop-loss: if price falls below 95% of entry price
        stop_loss_triggered = False
        if self.entry_price and current_close < self.entry_price * 0.95:
            stop_loss_triggered = True
        self.stop_loss_triggers.append(stop_loss_triggered)


def fetch_yfinance_data(ticker, start="2023-01-01", end="2024-01-01"):
    df = yf.download(ticker, start=start, end=end, auto_adjust=False)

    print("Downloaded Data (First 5 Rows):\n", df.head())
    print("DataFrame Columns Before Fix:", df.columns)

    # Flatten MultiIndex if needed
    if isinstance(df.columns, pd.MultiIndex):
        df.columns = [col[0] for col in df.columns]

    print("DataFrame Columns After Fix:", df.columns)

    required_cols = ['Open', 'High', 'Low', 'Close', 'Volume']
    available_cols = [col for col in required_cols if col in df.columns]
    if len(available_cols) < len(required_cols):
        raise ValueError(f"Missing required columns. Available: {available_cols}, Required: {required_cols}")

    df = df[available_cols]
    rename_map = {'Open': 'open', 'High': 'high', 'Low': 'low', 'Close': 'close', 'Volume': 'volume'}
    df.rename(columns=rename_map, inplace=True)
    df.index = pd.to_datetime(df.index)
    return df

def run_mr_backtest(stock_ticker="AAPL"):
    cerebro = bt.Cerebro()
    df = fetch_yfinance_data(stock_ticker)
    print("Final DataFrame Shape:", df.shape)
    if df.empty:
        raise ValueError("Error: DataFrame is empty!")

    bt_data = bt.feeds.PandasData(dataname=df)
    cerebro.adddata(bt_data)
    cerebro.addstrategy(MeanReversionStrategy)
    results = cerebro.run()
    strat = results[0]

    # Close any open position at final price
    if strat.position:
        final_profit = strat.close_prices[-1] - strat.entry_price
        strat.trade_profits.append(final_profit)

    # Calculate cumulative profit
    total_profit = sum(strat.trade_profits)

    # Calculate win rate
    num_trades = len(strat.trade_profits)
    num_wins = len([p for p in strat.trade_profits if p > 0])
    win_rate = (num_wins / num_trades) if num_trades > 0 else 0

    # Compute daily returns for Sharpe ratio
    returns = []
    for i in range(1, len(strat.close_prices)):
        ret = (strat.close_prices[i] / strat.close_prices[i-1]) - 1
        returns.append(ret)
    if returns:
        mean_ret = statistics.mean(returns)
        stdev_ret = statistics.stdev(returns) if len(returns) > 1 else 0
        sharpe_ratio = (mean_ret / stdev_ret * math.sqrt(252)) if stdev_ret != 0 else 0
    else:
        sharpe_ratio = 0

    # Return metrics for verification
    return {
        "zscore_values": strat.zscore_values,
        "buy_signals": strat.buy_signals,
        "sell_signals": strat.sell_signals,
        "stop_loss_triggered": any(strat.stop_loss_triggers),
        "stop_loss_triggers": strat.stop_loss_triggers,
        "entry_prices": strat.entry_prices,
        "close_prices": strat.close_prices,
        "trade_profits": strat.trade_profits,
        "max_drawdown": strat.max_drawdown,
        "total_profit": total_profit,
        "win_rate": win_rate,
        "sharpe_ratio": sharpe_ratio,
        "z_threshold": MeanReversionStrategy.params.z_threshold,
    }

if __name__ == "__main__":
    metrics = run_mr_backtest("AAPL")
    print("🔍 Backtest Metrics:")
    print(metrics)
