from pt_backtest import run_pt_backtest
from pt_smt_verification import run_smt_verification
from pt_report import generate_pdf_report
from test_pt_smt_verification import (
    get_valid_metrics,
    get_conflicting_signals_metrics,
    get_high_drawdown_metrics,
    get_invalid_buy_condition_metrics,
    get_invalid_stop_loss_metrics,
    get_mixed_trades_metrics,
    get_long_stop_loss_metrics,
    get_short_stop_loss_metrics,
)

def run_pipeline():
    print("Running Backtest...")
    # Run backtest with real data for two stocks (e.g., AAPL and MSFT)
    #real_data_metrics = run_pt_backtest("AAPL", "MSFT")
    # Alternatively, to test with synthetic metrics, uncomment one of these:
    # fake_data_metrics = get_valid_metrics()
    #fake_data_metrics = get_invalid_buy_condition_metrics()
    #fake_data_metrics = get_invalid_stop_loss_metrics()
    fake_data_metrics = get_mixed_trades_metrics()

    print("Running SMT Verification...")
    # Use the real data metrics for SMT verification:
    #smt_results = run_smt_verification(real_data_metrics)
    # Or, to test with synthetic metrics, uncomment the following line:
    smt_results = run_smt_verification(fake_data_metrics)

    print("Generating PDF Report...")
    # Generate report based on the real data:
    #generate_pdf_report(real_data_metrics, smt_results)
    # Alternatively, to generate report for synthetic metrics, uncomment:
    generate_pdf_report(fake_data_metrics, smt_results)

    print("Pipeline Completed Successfully!")

if __name__ == "__main__":
    run_pipeline()
