from octopus.platforms.EOS.cfg import EosCFG
from octopus.platforms.EOS.analyzer import EosAnalyzer

# complete wasm module
file_name = "./eosbet.wasm"

# read file
with open(file_name, 'rb') as f:
    raw = f.read()

# create the cfg
# cfg = EosCFG(raw)
analyzer=EosAnalyzer(raw)

print(analyzer.func_prototypes)
print(analyzer.exports)
# visualize
# cfg.visualize_call_flow()
