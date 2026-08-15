import random, sys
from decomp import setup
from facewalk import run
for n,cnt in ((6,4000),(7,2500),(8,1500),(9,700),(10,400)):
    E,m,_,_ = setup(n)
    random.seed(101+n)
    ms=[random.getrandbits(m) for _ in range(cnt)]
    st,bad = run(n, ms)
    print(f"n={n} ({cnt} random): denominators {dict(sorted(st['den'].items()))}  "
          f"max leaves {max(st['leaves']) if st['leaves'] else 0}  violations {len(bad)}")
    sys.stdout.flush()
