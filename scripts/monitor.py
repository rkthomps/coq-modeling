


import sys, os
import argparse
import datetime


from util.util import parse_logs, get_outstanding_dp_ends, get_outstanding_dp_loads, get_num_dps_processed



if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("err", help="Error file")
    args = parser.parse_args(sys.argv[1:])

    logs = parse_logs(args.err)
    num_processed = get_num_dps_processed(logs)
    print("Number of dps processed: ", num_processed)

    waiting_loads = get_outstanding_dp_loads(logs)
    print("Outstading loads:")
    for f_name, t in waiting_loads:
        print("\t{:70s}; {:.2f}".format(f_name, (datetime.datetime.now() - t).total_seconds()))

    waiting_lms = get_outstanding_dp_ends(logs)
    print("Outstading lm_examples:")
    for f_name, t in waiting_lms:
        print("\t{:70s}; {:.2f}".format(f_name, (datetime.datetime.now() - t).total_seconds()))

