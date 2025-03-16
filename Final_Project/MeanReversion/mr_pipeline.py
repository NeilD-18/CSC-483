from mr_backtest import run_mr_backtest
from mr_smt_verification import run_smt_verification
from mr_report import generate_pdf_report
from test_mr_smt_verification import (
    get_valid_metrics,
    get_conflicting_signals_metrics,
    get_high_drawdown_metrics,
    get_invalid_buy_condition_metrics,
    get_invalid_stop_loss_metrics,
    # Uncomment the next line if you have a "missing stop-loss" test for MR.
    # get_missing_stop_loss_metrics,
)

def run_pipeline():
    print("Running Backtest...")
    real_data_metrics = run_mr_backtest("AAPL")
    # Uncomment one of the following to test with synthetic metrics:
    # fake_data_metrics = get_valid_metrics()
    # fake_data_metrics = get_invalid_buy_condition_metrics()
    
    print("Running SMT Verification...")
    smt_results = run_smt_verification(real_data_metrics)
    # To test with fake metrics, uncomment the next line:
    # smt_results = run_smt_verification(fake_data_metrics)
    
    print("Generating PDF Report...")
    generate_pdf_report(real_data_metrics, smt_results)
    # To generate report for synthetic metrics, uncomment the next line:
    # generate_pdf_report(fake_data_metrics, smt_results)

    print("Pipeline Completed Successfully!")

if __name__ == "__main__":
    run_pipeline()
