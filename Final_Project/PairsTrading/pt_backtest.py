import backtrader as bt
import yfinance as yf
import pandas as pd
import statistics
import math
from datetime import datetime

class PairsTradingStrategy(bt.Strategy):
    """
    A simple pairs trading strategy:
      - spread = Y - X
      - rolling mean & std of the spread over 'period'
      - z-score = (spread - mean) / std
      - if z-score < -z_threshold => long spread (buy Y, sell X)
      - if z-score >  z_threshold => short spread (sell Y, buy X)
      - exit when z-score crosses ~0
    """
    params = (
        ("period", 20),
        ("z_threshold", 2.0),
    )

    def __init__(self):
        # We'll track everything in Python lists to return as "metrics" later
        self.zscore_values = []
        self.buy_signals = []
        self.sell_signals = []
        self.stop_loss_triggers = []
        self.entry_prices = []    # Spread at entry
        self.close_prices = []    # Spread over time
        self.trade_profits = []
        self.max_drawdown = 0

        # We'll store the "spread_position" as +1 (long), -1 (short), or 0 (flat).
        self.spread_position = 0
        self.entry_spread = None

        # For rolling mean/std of the spread, define lines in Backtrader:
        # spread = data1.close - data0.close
        self.spread = self.datas[1].close - self.datas[0].close
        self.rolling_mean = bt.indicators.SimpleMovingAverage(self.spread, period=self.params.period)
        self.rolling_std = bt.indicators.StandardDeviation(self.spread, period=self.params.period)

    def next(self):
        current_spread = self.spread[0]
        current_mean = self.rolling_mean[0]
        current_std = self.rolling_std[0] if self.rolling_std[0] != 0 else 1e-9

        # Compute z-score of the spread
        zscore = (current_spread - current_mean) / current_std
        self.zscore_values.append(zscore)
        self.close_prices.append(current_spread)  # We treat "close_prices" as the spread's time series

        buy_signal = False
        sell_signal = False

        # Determine if we have an open position in the spread
        if self.spread_position == 0:
            # No current position => check if we should open one
            if zscore < -self.params.z_threshold:
                # Long the spread => buy Y, sell X
                self.buy(data=self.datas[1])   # Buy Y
                self.sell(data=self.datas[0])  # Sell X
                self.spread_position = 1
                self.entry_spread = current_spread
                buy_signal = True

            elif zscore > self.params.z_threshold:
                # Short the spread => sell Y, buy X
                self.sell(data=self.datas[1])  # Sell Y
                self.buy(data=self.datas[0])   # Buy X
                self.spread_position = -1
                self.entry_spread = current_spread
                sell_signal = True

        else:
            # Already in a spread trade => check if we should exit
            # We exit if z-score crosses near 0 (or you could choose a smaller threshold).
            # For simplicity, exit when zscore has the opposite sign or is near 0.
            if (self.spread_position == 1 and zscore >= 0) or \
               (self.spread_position == -1 and zscore <= 0):
                # Close positions
                if self.spread_position == 1:
                    # We were long the spread => close by selling Y, buying X
                    self.sell(data=self.datas[1])
                    self.buy(data=self.datas[0])
                    profit = current_spread - self.entry_spread
                else:
                    # We were short the spread => close by buying Y, selling X
                    self.buy(data=self.datas[1])
                    self.sell(data=self.datas[0])
                    profit = self.entry_spread - current_spread

                self.trade_profits.append(profit)
                self.spread_position = 0
                self.entry_spread = None

        # Mark buy/sell signals in arrays
        self.buy_signals.append(buy_signal)
        self.sell_signals.append(sell_signal)

        # Record the entry price if in a trade, otherwise 0
        if self.spread_position != 0 and self.entry_spread is not None:
            self.entry_prices.append(self.entry_spread)
        else:
            self.entry_prices.append(0)

        # Simple stop-loss check: if the spread moves 5% in the wrong direction from entry
        # while still in a trade, we flag it. (We won't forcibly close here, but you could.)
        stop_loss_triggered = False
        if self.entry_spread is not None:
            # If we are long and the spread is 5% below entry, or short and 5% above entry
            if (self.spread_position == 1 and current_spread < 0.95 * self.entry_spread) or \
               (self.spread_position == -1 and current_spread > 1.05 * self.entry_spread):
                stop_loss_triggered = True
        self.stop_loss_triggers.append(stop_loss_triggered)

        # Rolling max drawdown over the last 100 bars of the spread
        recent_spreads = self.spread.get(size=100)
        peak = max(recent_spreads) if recent_spreads else current_spread
        drawdown = (peak - current_spread) / peak
        self.max_drawdown = max(self.max_drawdown, drawdown)


def fetch_yfinance_data(ticker1, ticker2, start="2023-01-01", end="2024-01-01"):
    """
    Fetch daily data for two tickers from yfinance and return as two DataFrames.
    We'll later feed each DataFrame into Backtrader as a separate data feed.
    """
    df1 = yf.download(ticker1, start=start, end=end, auto_adjust=False)
    df2 = yf.download(ticker2, start=start, end=end, auto_adjust=False)

    if df1.empty or df2.empty:
        raise ValueError("Error: One of the DataFrames is empty!")

    # Flatten multi-index if needed
    if isinstance(df1.columns, pd.MultiIndex):
        df1.columns = [col[0] for col in df1.columns]
    if isinstance(df2.columns, pd.MultiIndex):
        df2.columns = [col[0] for col in df2.columns]

    # Rename columns to lowercase for Backtrader
    rename_map = {'Open': 'open', 'High': 'high', 'Low': 'low', 'Close': 'close', 'Volume': 'volume'}
    df1.rename(columns=rename_map, inplace=True)
    df2.rename(columns=rename_map, inplace=True)

    df1.index = pd.to_datetime(df1.index)
    df2.index = pd.to_datetime(df2.index)

    return df1, df2


def run_pt_backtest(ticker_x="AAPL", ticker_y="MSFT"):
    """
    Run a pairs trading backtest on two tickers and return performance metrics.
    """
    cerebro = bt.Cerebro()

    # Fetch data for both tickers
    df_x, df_y = fetch_yfinance_data(ticker_x, ticker_y)
    
    # Feed data into Backtrader
    data_x = bt.feeds.PandasData(dataname=df_x)
    data_y = bt.feeds.PandasData(dataname=df_y)
    cerebro.adddata(data_x)  # self.datas[0]
    cerebro.adddata(data_y)  # self.datas[1]

    # Add the strategy
    cerebro.addstrategy(PairsTradingStrategy)
    results = cerebro.run()
    strat = results[0]

    # If a position is still open at the end, close it manually
    if strat.spread_position != 0 and strat.entry_spread is not None:
        final_spread = strat.close_prices[-1]
        if strat.spread_position == 1:
            # Long the spread => profit = final_spread - entry_spread
            profit = final_spread - strat.entry_spread
        else:
            # Short the spread => profit = entry_spread - final_spread
            profit = strat.entry_spread - final_spread
        strat.trade_profits.append(profit)

    # Calculate total profit
    total_profit = sum(strat.trade_profits)

    # Calculate win rate
    num_trades = len(strat.trade_profits)
    num_wins = len([p for p in strat.trade_profits if p > 0])
    win_rate = (num_wins / num_trades) if num_trades > 0 else 0

    # Calculate Sharpe Ratio from daily changes in the spread
    returns = []
    for i in range(1, len(strat.close_prices)):
        prev_spread = strat.close_prices[i - 1]
        curr_spread = strat.close_prices[i]
        if prev_spread != 0:
            ret = (curr_spread / prev_spread) - 1
            returns.append(ret)

    if returns:
        mean_ret = statistics.mean(returns)
        stdev_ret = statistics.stdev(returns) if len(returns) > 1 else 0
        sharpe_ratio = (mean_ret / stdev_ret * math.sqrt(252)) if stdev_ret != 0 else 0
    else:
        sharpe_ratio = 0

    # Return metrics in a dictionary
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
        "z_threshold": PairsTradingStrategy.params.z_threshold,
    }


if __name__ == "__main__":
    metrics = run_pt_backtest("AAPL", "MSFT")
    print("🔍 Pairs Trading Backtest Metrics:")
    print(metrics)
