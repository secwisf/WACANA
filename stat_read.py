import pstats
from pstats import SortKey

p=pstats.Stats('./memory.prof')
p.strip_dirs().sort_stats(-1).print_stats()
