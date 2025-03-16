from reportlab.lib.pagesizes import letter
from reportlab.pdfgen import canvas
from reportlab.lib.utils import ImageReader
import matplotlib.pyplot as plt
import os

def generate_chart(metrics, filename="chart.png"):
    """Generate an SMA Crossover Chart with Buy/Sell points."""
    plt.figure(figsize=(8, 4))
    plt.plot(metrics["sma_short_values"], label="SMA Short", linestyle="--", color="blue")
    plt.plot(metrics["sma_long_values"], label="SMA Long", linestyle="-", color="orange")

    # Mark Buy and Sell signals based on close prices
    buy_signals = [metrics["close_prices"][i] if metrics["buy_signals"][i] else None for i in range(len(metrics["buy_signals"]))]
    sell_signals = [metrics["close_prices"][i] if metrics["sell_signals"][i] else None for i in range(len(metrics["sell_signals"]))]
    
    plt.scatter(range(len(metrics["buy_signals"])), buy_signals, label="Buy Signal", color="green", marker="^")
    plt.scatter(range(len(metrics["sell_signals"])), sell_signals, label="Sell Signal", color="red", marker="v")
    
    plt.legend()
    plt.xlabel("Time Step")
    plt.ylabel("Price")
    plt.title("SMA Crossover Strategy - Buy/Sell Signals")
    plt.savefig(filename)
    plt.close()

def generate_pdf_report(backtest_metrics, smt_results, filename="MovingAverageCrossover/Report.pdf"):
    """Generate a PDF summarizing the backtest and SMT verification results."""
    # Generate chart for visualization
    chart_filename = "chart.png"
    generate_chart(backtest_metrics, chart_filename)

    c = canvas.Canvas(filename, pagesize=letter)
    width, height = letter

    # Title
    c.setFont("Helvetica-Bold", 16)
    c.drawString(50, height - 50, "📊 Backtest and SMT Verification Report")

    # Backtest Summary
    c.setFont("Helvetica-Bold", 14)
    c.drawString(50, height - 80, "🔍 Backtest Summary:")

    c.setFont("Helvetica", 12)
    # Display metrics: max drawdown, stop-loss, total profit, win rate, and Sharpe ratio.
    c.drawString(50, height - 100, f"📉 Max Drawdown: {backtest_metrics['max_drawdown']:.2%}")
    c.drawString(50, height - 120, f"🚨 Stop-Loss Triggered: {backtest_metrics['stop_loss_triggered']}")
    c.drawString(50, height - 140, f"💰 Total Profit: {backtest_metrics['total_profit']:.2f}")
    c.drawString(50, height - 160, f"📈 Win Rate: {backtest_metrics['win_rate']*100:.1f}%")
    c.drawString(50, height - 180, f"📊 Sharpe Ratio: {backtest_metrics['sharpe_ratio']:.2f}")

    # SMT Verification Results
    c.setFont("Helvetica-Bold", 14)
    c.drawString(50, height - 210, "✅ SMT Verification Results:")

    c.setFont("Helvetica", 12)
    verification_result = smt_results["SMT Verification"]
    failing_constraints = smt_results.get("Failing Constraints", [])

    if verification_result == "✅ Passed":
        c.setFillColorRGB(0, 0.6, 0)  # Green
        c.drawString(50, height - 230, "✅ SMT Verification: PASSED")
        c.setFillColorRGB(0, 0, 0)
    else:
        c.setFillColorRGB(1, 0, 0)  # Red
        c.drawString(50, height - 230, "❌ SMT Verification: FAILED")
        c.setFillColorRGB(0, 0, 0)

        if failing_constraints:
            c.setFont("Helvetica", 12)
            c.drawString(50, height - 250, "🚨 Failing Constraints:")
            y_offset = height - 270
            for constraint in failing_constraints:
                if y_offset < 100:  # Create a new page if space is low
                    c.showPage()
                    y_offset = height - 50
                    c.setFont("Helvetica", 12)
                    c.drawString(50, y_offset, "🚨 Failing Constraints (Continued):")
                    y_offset -= 20
                c.drawString(70, y_offset, f"- {constraint}")
                y_offset -= 20

    
    c.drawImage(ImageReader(chart_filename), 50, 50, width=500, height=250)
    c.save()
    os.remove(chart_filename)

if __name__ == "__main__":
    from mac_backtest import run_mac_backtest
    from mac_smt_verification import run_smt_verification

    metrics = run_mac_backtest("AAPL")
    smt_results = run_smt_verification(metrics)
    generate_pdf_report(metrics, smt_results)
    print("📄 Report Generated: Backtest_Report.pdf")
