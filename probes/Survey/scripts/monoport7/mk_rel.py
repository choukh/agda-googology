# 从 MonoPort6Rel 生成 MonoPort7Rel: 第 ≥1 层的结构关系推广到 hl 层 (只改代码块, 讲解另写)
# 用法: python3 mk_rel.py <仓库根>
import re, sys, os
root = sys.argv[1]
src = open(os.path.join(root, 'probes/OCF/Align/MonoPort6Rel.lagda.md')).read()
code = src[src.index('```agda'):]
code = code.replace('module OCF.Align.MonoPort6Rel', 'module OCF.Align.MonoPort7Rel')
code = code.replace('Fin (hl f) = ⊥', 'Fin (hl f) = ∀ n → Fin (f n)')
code = code.replace('fin⊲ (hlim n P) ()', 'fin⊲ (hlim n P) f = fin⊲ P (f n)')
code = code.replace('Rel (hl f) _ _ = ⊤', 'Rel (hl f) = RelN (hl f)')
code = code.replace('Rel (hs b) = RelM._⊑_ (hs b) (LowT (hs b))', 'Rel (hs b) = RelN (hs b)')
code = code.replace('LowT (hs b) (ss P) = CtxP b P', 'LowT hz ()\nLowT (hs b) (ss P) = CtxP b P')
code = code.replace('Ctx (hs b) x x′ = Rel (hs b) x x′ × (RelM.Ok (hs b) (LowT (hs b)) x × RelM.Ok (hs b) (LowT (hs b)) x′)',
                    'Ctx (hs b) = CxN (hs b)')
code = code.replace('Ctx (hl f) _ _ = ⊤', 'Ctx (hl f) = CxN (hl f)')
code = code.replace('Rel  : ∀ L → D L W → D L W → Set\n',
  'Rel  : ∀ L → D L W → D L W → Set\nRelN : ∀ L → D L W → D L W → Set\nCxN  : ∀ L → D L W → D L W → Set\n')
code = code.replace('Rel hz x x′ = x ⊑₀ x′\n',
  'RelN L = RelM._⊑_ L (LowT L)\nCxN L x x′ = RelN L x x′ × (RelM.Ok L (LowT L) x × RelM.Ok L (LowT L) x′)\n\nRel hz x x′ = x ⊑₀ x′\n', 1)
code = code.replace('module R (b : H) = RelM (hs b) (LowT (hs b))',
  'module RL (L : H) = RelM L (LowT L)\nmodule R (b : H) = RL (hs b)')
code = code.replace('R.OkRf b o′', 'RL.OkRf (hs b) o′').replace('R.OkRf b o', 'RL.OkRf (hs b) o')
code = code.replace('## 1 有限的层', '## 1 不含 Ω-极限的层').replace('换算是一行 (`MonoPort6Lay`)', '换算是一行 (`MonoPort7Lay`)')
lines = code.split('\n')
out = []
for i, ln in enumerate(lines):
    m = re.match(r'^(\S+) \(hl f\)( .*)? = tt$', ln)
    if m and m.group(1) not in ('rΩ',):
        name = m.group(1)
        j = i - 1
        while not (lines[j].startswith(name + ' (hs b)') or lines[j].startswith(name + ' (hs _)')):
            j -= 1
        h = lines[j].replace('(hs b)', '(hl f)').replace('(hs _)', '(hl f)')
        out.append(h)
    elif ln == 'rΩ (hl f) = tt':
        out.append('rΩ (hl f) = RelM.⨾⊑ RelM.n1⊑ RelM.n1⊑ RelM.n1⊑ (RelM.nl⊑ (λ n → ni₁ n) (λ n → ni₁ n) (λ n → ni₁ n))')
        out.append('  where')
        out.append('  ni₁ : ∀ n → RelN (hl f) (ni (sl n hself) (λ _ _ _ → n1)) (ni (sl n hself) (λ _ _ _ → n1))')
        out.append('  ni₁ n = RelM.ni⊑ (sl n hself) (λ _ _ _ → RelM.n1⊑) (λ _ _ _ → RelM.n1⊑) (λ _ _ _ → RelM.n1⊑)')
    else:
        out.append(ln)
code = '\n'.join(out)
hdr = open(os.path.join(root, 'probes/Survey/scripts/monoport7/rel_header.md')).read()
open(os.path.join(root, 'probes/OCF/Align/MonoPort7Rel.lagda.md'), 'w').write(hdr + code)
