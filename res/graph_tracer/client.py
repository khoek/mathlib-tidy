import os
import time
import sys
import subprocess
from importlib import util

FIFO_PATH = "rewrite_search.fifo"

SUCCESS_CHAR = "S"
ERROR_CHAR = "E"

if __name__ == "__main__":
    if util.find_spec("pygame") is None:
        print(ERROR_CHAR + "pygame missing, please install it with \"pip3 install pygame\" (you'll need pip3), or similar")
        sys.stdout.flush()
    else:
        dir_path = os.path.dirname(os.path.realpath(__file__))
        subprocess.Popen(["python3", dir_path + "/server.py"])

        while not os.path.exists(FIFO_PATH):
            time.sleep(0.05)

        print(SUCCESS_CHAR)
        sys.stdout.flush()

        fifo = open(FIFO_PATH, "w", encoding = "utf-8")
        for line in sys.stdin:
            fifo.write(line)
            fifo.flush()