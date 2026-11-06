import sys, os
# usage: python3 mkfold.py <repo-root>
root = sys.argv[1]
al = os.path.join(root, 'probes', 'OCF', 'Align')
src = open(os.path.join(al, 'HtTowerFFold.lagda.md')).read().split('\n')
L = lambda a, b: '\n'.join(src[a-1:b])
sig_run = L(248, 313)
walk = L(319, 352)
runm = L(358, 390)
kd = L(407, 408)
assert sig_run.startswith('Run   :') and walk.startswith('Walk₁ ac') and runm.startswith('RunM ac') and kd.startswith('κΔ₁ ac')
sig_run = sig_run.replace("→ ℕ → Cl₁ W W₀ ly", "→ ℕ → ClZ W W₀ ly")
assert "ClZ W W₀ ly" in sig_run
old = "(κc₁ ac zy u q₀ lW ll A₀ w Y n)"
assert runm.count(old) == 5
runm = runm.replace(old, "(toCl lW (κc₁ ac zy u q₀ lW ll A₀ w Y n))")
parts = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'fold_parts.txt')).read().split('@@@\n')
head, mid1, mid2, kc = parts
out = head + sig_run + mid1 + walk + mid2 + runm + kc + kd + '\n```\n'
open(os.path.join(al, 'ChainZFold.lagda.md'), 'w').write(out)
