import backtrader as bt
import yfinance as yf
import pandas as pd
from datetime import datetime
import statistics
import math

# Define the Moving Average Crossover Strategy
class MACrossover(bt.Strategy):
    params = (('short_period', 10), ('long_period', 50))
    
    def __init__(self):
        self.short_ma = bt.indicators.SimpleMovingAverage(self.data.close, period=self.params.short_period)
        self.long_ma = bt.indicators.SimpleMovingAverage(self.data.close, period=self.params.long_period)

        # Track metrics over time
        self.sma_short_values = []
        self.sma_long_values = []
        self.buy_signals = []
        self.sell_signals = []
        self.stop_loss_triggers = []
        self.entry_prices = []     # Track entry price at each time step
        self.close_prices = []     # Track closing prices
        self.max_drawdown = 0
        self.entry_price = None
        self.trade_profits = []    # NEW: List to store profit for each completed trade

    def next(self):
        # Record moving averages and close price at this step.
        self.sma_short_values.append(self.short_ma[0])
        self.sma_long_values.append(self.long_ma[0])
        self.close_prices.append(self.data.close[0])
        
        buy_signal = False
        sell_signal = False

        # Check for trade signals
        if self.short_ma[0] > self.long_ma[0] and not self.position:
            self.buy()
            self.entry_price = self.data.close[0]
            buy_signal = True
        elif self.short_ma[0] < self.long_ma[0] and self.position:
            # Compute profit for the trade before selling
            profit = self.data.close[0] - self.entry_price
            self.trade_profits.append(profit)
            self.sell()
            sell_signal = True

        self.buy_signals.append(buy_signal)
        self.sell_signals.append(sell_signal)
        
        # Record the entry price (if in a trade, record the entry price; otherwise, record 0)
        if self.position and self.entry_price is not None:
            self.entry_prices.append(self.entry_price)
        else:
            self.entry_prices.append(0)
        
        # Compute max drawdown over last 100 bars
        recent_prices = self.data.close.get(size=100)
        peak = max(recent_prices) if recent_prices else self.data.close[0]
        drawdown = (peak - self.data.close[0]) / peak
        self.max_drawdown = max(self.max_drawdown, drawdown)

        # Stop-loss check: if current price < 95% of entry price, flag stop-loss.
        stop_loss_triggered = False
        if self.entry_price and self.data.close[0] < self.entry_price * 0.95:
            stop_loss_triggered = True
        self.stop_loss_triggers.append(stop_loss_triggered)

# Fetch data using yfinance and format for Backtrader
def fetch_yfinance_data(ticker, start="2023-01-01", end="2024-01-01"):
    df = yf.download(ticker, start=start, end=end, auto_adjust=False)

    # Debug: print original DataFrame structure
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

def run_mac_backtest(stock_ticker):
    cerebro = bt.Cerebro()
    df = fetch_yfinance_data(stock_ticker)
    print("Final DataFrame Shape:", df.shape)
    if df.empty:
        raise ValueError("Error: DataFrame is empty!")

    bt_data = bt.feeds.PandasData(dataname=df)
    cerebro.adddata(bt_data)
    cerebro.addstrategy(MACrossover)
    results = cerebro.run()
    strat = results[0]

    # If a trade is still open at the end, close it using the last close price.
    if strat.position:
        final_profit = strat.close_prices[-1] - strat.entry_price
        strat.trade_profits.append(final_profit)

    # Calculate cumulative profit.
    total_profit = sum(strat.trade_profits)

    # Calculate win rate.
    num_trades = len(strat.trade_profits)
    num_wins = len([p for p in strat.trade_profits if p > 0])
    win_rate = (num_wins / num_trades) if num_trades > 0 else 0

    # Calculate Sharpe Ratio from daily returns.
    # Daily return = (today's close / yesterday's close) - 1
    returns = []
    for i in range(1, len(strat.close_prices)):
        ret = (strat.close_prices[i] / strat.close_prices[i-1]) - 1
        returns.append(ret)
    if returns:
        mean_ret = statistics.mean(returns)
        stdev_ret = statistics.stdev(returns) if len(returns) > 1 else 0
        # Annualize the Sharpe ratio assuming 252 trading days.
        sharpe_ratio = (mean_ret / stdev_ret * math.sqrt(252)) if stdev_ret != 0 else 0
    else:
        sharpe_ratio = 0

    # Return all metrics
    return {
        "max_drawdown": strat.max_drawdown,
        "stop_loss_triggered": any(strat.stop_loss_triggers),
        "stop_loss_triggers": strat.stop_loss_triggers,
        "sma_short_values": strat.sma_short_values,
        "sma_long_values": strat.sma_long_values,
        "buy_signals": strat.buy_signals,
        "sell_signals": strat.sell_signals,
        "entry_prices": strat.entry_prices,
        "close_prices": strat.close_prices,
        "total_profit": total_profit,
        "win_rate": win_rate,
        "sharpe_ratio": sharpe_ratio
    }

if __name__ == "__main__":
    metrics = run_mac_backtest("AAPL")
    print("🔍 Backtest Metrics:")
    print(metrics)
