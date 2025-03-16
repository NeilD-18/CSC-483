from mac_backtest import run_mac_backtest
from mac_smt_verification import run_smt_verification
from mac_report import generate_pdf_report
from test_mac_smt_verification import (
    get_valid_metrics,
    get_conflicting_signals_metrics,
    get_high_drawdown_metrics,
    get_invalid_buy_signal_metrics,
    get_invalid_stop_loss_metrics,
    get_missing_stop_loss_metrics,
)

def run_pipeline():
    print("Running Backtest...")
    #real_data_metrics = run_mac_backtest("AAPL")
    #fake_data_metrics = get_valid_metrics()
    fake_data_metrics = get_invalid_buy_signal_metrics()
    
    
    print("Running SMT Verification...")
    #smt_results = run_smt_verification(real_data_metrics)
    smt_results = run_smt_verification(fake_data_metrics)
    
  

    
    print("Generating PDF Report...")
    #generate_pdf_report(real_data_metrics, smt_results)
    generate_pdf_report(fake_data_metrics, smt_results)

    print("Pipeline Completed Successfully!")

if __name__ == "__main__":
    run_pipeline()
