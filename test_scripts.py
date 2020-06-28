import sys
sys.path.append(".")
from var import VariableInfusion
### FILE PATH HOUSEKEEPING ###
SCRIPT_PATH = "data/script_paths.txt"

def get_scripts(file):
    result = []
    for line in file:
        line = line.strip("\n")
        with open(line, "r") as fp:
            result.append(fp.read())
            f = VariableInfusion(result[-1])
            print(f.symbols)
    return result

if __name__ == "__main__":

    with open(SCRIPT_PATH, 'r') as fp:
        get_scripts(fp)
