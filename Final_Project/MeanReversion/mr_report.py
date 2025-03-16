from reportlab.lib.pagesizes import letter
from reportlab.pdfgen import canvas
from reportlab.lib.utils import ImageReader
import matplotlib.pyplot as plt
import os

def generate_chart(metrics, filename="chart.png"):
    """Generate a Z-Score Mean Reversion Chart with Buy/Sell points."""
    plt.figure(figsize=(8, 4))
    
    # Plot the z-score values.
    plt.plot(metrics["zscore_values"], label="Z-Score", linestyle="--", color="blue")
    
    # Plot horizontal lines at the buy and sell thresholds.
    z_threshold = metrics["z_threshold"]
    plt.axhline(y=z_threshold, color='red', linestyle=':', label=f"Sell Threshold ({z_threshold})")
    plt.axhline(y=-z_threshold, color='green', linestyle=':', label=f"Buy Threshold (-{z_threshold})")
    
    # Mark Buy and Sell signals using the z-score values.
    buy_signals = [metrics["zscore_values"][i] if metrics["buy_signals"][i] else None 
                   for i in range(len(metrics["buy_signals"]))]
    sell_signals = [metrics["zscore_values"][i] if metrics["sell_signals"][i] else None 
                    for i in range(len(metrics["sell_signals"]))]
    
    plt.scatter(range(len(metrics["buy_signals"])), buy_signals, label="Buy Signal", color="green", marker="^")
    plt.scatter(range(len(metrics["sell_signals"])), sell_signals, label="Sell Signal", color="red", marker="v")
    
    plt.legend()
    plt.xlabel("Time Step")
    plt.ylabel("Z-Score")
    plt.title("Z-Score Mean Reversion Strategy - Buy/Sell Signals")
    plt.savefig(filename)
    plt.close()

def generate_pdf_report(backtest_metrics, smt_results, filename="MeanReversion/Report.pdf"):
    """Generate a PDF summarizing the mean reversion backtest and SMT verification results."""
    # Ensure the report directory exists.
    report_dir = os.path.dirname(filename)
    if report_dir and not os.path.exists(report_dir):
        os.makedirs(report_dir)
    
    # Generate the chart image.
    chart_filename = "chart.png"
    generate_chart(backtest_metrics, chart_filename)
    
    c = canvas.Canvas(filename, pagesize=letter)
    width, height = letter

    # Report Title
    c.setFont("Helvetica-Bold", 16)
    c.drawString(50, height - 50, "Mean Reversion Backtest and SMT Verification Report")

    # Backtest Summary Section
    c.setFont("Helvetica-Bold", 14)
    c.drawString(50, height - 80, "Backtest Summary:")

    c.setFont("Helvetica", 12)
    c.drawString(50, height - 100, f"Max Drawdown: {backtest_metrics['max_drawdown']:.2%}")
    c.drawString(50, height - 120, f"Stop-Loss Triggered: {backtest_metrics['stop_loss_triggered']}")
    c.drawString(50, height - 140, f"Total Profit: {backtest_metrics['total_profit']:.2f}")
    c.drawString(50, height - 160, f"Win Rate: {backtest_metrics['win_rate']*100:.1f}%")
    c.drawString(50, height - 180, f"Sharpe Ratio: {backtest_metrics['sharpe_ratio']:.2f}")

    # SMT Verification Results Section
    c.setFont("Helvetica-Bold", 14)
    c.drawString(50, height - 210, "SMT Verification Results:")

    c.setFont("Helvetica", 12)
    verification_result = smt_results["SMT Verification"]
    failing_constraints = smt_results.get("Failing Constraints", [])

    if verification_result == "Passed":
        c.setFillColorRGB(0, 0.6, 0)  # Green for pass.
        c.drawString(50, height - 230, "SMT Verification: PASSED")
        c.setFillColorRGB(0, 0, 0)
    else:
        c.setFillColorRGB(1, 0, 0)  # Red for failure.
        c.drawString(50, height - 230, "SMT Verification: FAILED")
        c.setFillColorRGB(0, 0, 0)
        if failing_constraints:
            c.setFont("Helvetica", 12)
            c.drawString(50, height - 250, "Failing Constraints:")
            y_offset = height - 270
            for constraint in failing_constraints:
                if y_offset < 100:  # Start a new page if needed.
                    c.showPage()
                    y_offset = height - 50
                    c.setFont("Helvetica", 12)
                    c.drawString(50, y_offset, "🚨 Failing Constraints (Continued):")
                    y_offset -= 20
                c.drawString(70, y_offset, f"- {constraint}")
                y_offset -= 20

    # Embed the chart image in the PDF.
    c.drawImage(ImageReader(chart_filename), 50, 50, width=500, height=250)
    c.save()
    os.remove(chart_filename)

if __name__ == "__main__":
    from mr_backtest import run_mr_backtest
    from mr_smt_verification import run_smt_verification

    metrics = run_mr_backtest("AAPL")
    smt_results = run_smt_verification(metrics)
    generate_pdf_report(metrics, smt_results)
    print("📄 Report Generated: MeanReversion/Report.pdf")
