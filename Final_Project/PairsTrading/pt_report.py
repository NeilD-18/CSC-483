import os
from reportlab.lib.pagesizes import letter
from reportlab.pdfgen import canvas
from reportlab.lib.utils import ImageReader
import matplotlib.pyplot as plt

def generate_chart(metrics, filename="chart.png"):
    """
    Generate a chart for pairs trading that plots the z-score time series,
    with horizontal lines for the z-threshold (sell threshold) and its negative (buy threshold),
    and marks the buy and sell signals.
    """
    plt.figure(figsize=(8, 4))
    # Plot the z-score values.
    plt.plot(metrics["zscore_values"], label="Z-Score", linestyle="--", color="blue")
    
    # Draw threshold lines.
    z_thresh = metrics["z_threshold"]
    plt.axhline(y=z_thresh, color='red', linestyle=':', label=f"Sell Threshold ({z_thresh})")
    plt.axhline(y=-z_thresh, color='green', linestyle=':', label=f"Buy Threshold (-{z_thresh})")
    
    # Mark buy and sell signals on the zscore series.
    buy_signals = [metrics["zscore_values"][i] if metrics["buy_signals"][i] else None 
                   for i in range(len(metrics["buy_signals"]))]
    sell_signals = [metrics["zscore_values"][i] if metrics["sell_signals"][i] else None 
                    for i in range(len(metrics["sell_signals"]))]
    plt.scatter(range(len(metrics["buy_signals"])), buy_signals, label="Buy Signal", color="green", marker="^")
    plt.scatter(range(len(metrics["sell_signals"])), sell_signals, label="Sell Signal", color="red", marker="v")
    
    plt.legend()
    plt.xlabel("Time Step")
    plt.ylabel("Z-Score")
    plt.title("Pairs Trading Strategy - Z-Score Signals")
    plt.savefig(filename)
    plt.close()

def generate_pdf_report(backtest_metrics, smt_results, filename="PairsTrading/Report.pdf"):
    """
    Generate a PDF report summarizing the pairs trading backtest and SMT verification results.
    The report includes key performance metrics and embeds the chart.
    """
    # Ensure the target directory exists.
    report_dir = os.path.dirname(filename)
    if report_dir and not os.path.exists(report_dir):
        os.makedirs(report_dir)
        
    # Generate the chart image.
    chart_filename = "chart.png"
    generate_chart(backtest_metrics, chart_filename)
    
    c = canvas.Canvas(filename, pagesize=letter)
    width, height = letter

    # Title Section.
    c.setFont("Helvetica-Bold", 16)
    c.drawString(50, height - 50, "Pairs Trading Backtest and SMT Verification Report")

    # Backtest Metrics Section.
    c.setFont("Helvetica-Bold", 14)
    c.drawString(50, height - 80, "Backtest Summary:")

    c.setFont("Helvetica", 12)
    c.drawString(50, height - 100, f"Max Drawdown: {backtest_metrics['max_drawdown']:.2%}")
    c.drawString(50, height - 120, f"Stop-Loss Triggered: {backtest_metrics['stop_loss_triggered']}")
    c.drawString(50, height - 140, f"Total Profit: {backtest_metrics['total_profit']:.2f}")
    c.drawString(50, height - 160, f"Win Rate: {backtest_metrics['win_rate']*100:.1f}%")
    c.drawString(50, height - 180, f"Sharpe Ratio: {backtest_metrics['sharpe_ratio']:.2f}")
    c.drawString(50, height - 200, f"Z-Threshold: {backtest_metrics['z_threshold']}")

    # SMT Verification Results Section.
    c.setFont("Helvetica-Bold", 14)
    c.drawString(50, height - 230, "SMT Verification Results:")

    c.setFont("Helvetica", 12)
    verification_result = smt_results["SMT Verification"]
    failing_constraints = smt_results.get("Failing Constraints", [])
    if verification_result == "Passed":
        c.setFillColorRGB(0, 0.6, 0)  # Green for passed.
        c.drawString(50, height - 250, "SMT Verification: PASSED")
        c.setFillColorRGB(0, 0, 0)
    else:
        c.setFillColorRGB(1, 0, 0)  # Red for failure.
        c.drawString(50, height - 250, "SMT Verification: FAILED")
        c.setFillColorRGB(0, 0, 0)
        if failing_constraints:
            c.drawString(50, height - 270, "Failing Constraints:")
            y_offset = height - 290
            for constraint in failing_constraints:
                if y_offset < 100:
                    c.showPage()
                    y_offset = height - 50
                c.drawString(70, y_offset, f"- {constraint}")
                y_offset -= 20

    # Embed the chart image.
    c.drawImage(ImageReader(chart_filename), 50, 50, width=500, height=250)
    c.save()
    os.remove(chart_filename)

if __name__ == "__main__":
    from pt_backtest import run_pt_backtest
    from pt_smt_verification import run_smt_verification

    # Run the pairs trading backtest on two symbols (for example, AAPL and MSFT)
    metrics = run_pt_backtest("AAPL", "MSFT")
    smt_results = run_smt_verification(metrics)
    generate_pdf_report(metrics, smt_results)
    print("📄 Report Generated: PairsTrading/Report.pdf")
