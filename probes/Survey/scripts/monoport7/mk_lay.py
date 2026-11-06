# 从 MonoPort6Lay 生成 MonoPort7Lay: 层 L 的核实例对任意层写一次 (原来对 hs b)
# 用法: python3 mk_lay.py <仓库根>
import sys, os
root = sys.argv[1]
src = open(os.path.join(root, 'probes/OCF/Align/MonoPort6Lay.lagda.md')).read()
code = src[src.index('```agda'):]
code = code.replace('module OCF.Align.MonoPort6Lay', 'module OCF.Align.MonoPort7Lay')
code = code.replace('open import OCF.Align.MonoPort6Rel Λ lΛ lW t₀', 'open import OCF.Align.MonoPort7Rel Λ lΛ lW t₀')
code = code.replace('InS : ∀ b → D (hs b) W → D (hs b) W → Set\nInS b x x′ = Rel (hs b) x x′ × (Rf (hs b) x × Rf (hs b) x′)',
  'InS : ∀ L → D L W → D L W → Set\nInS L x x′ = RelN L x x′ × (RelN L x x × RelN L x′ x′)\n\n'
  '-- 上下文取 CxN 的动作前提 (对 hs b 与 hl f 定义性地就是 HAK)\n'
  'HAKN : ∀ L → P.Ig L W → P.Ig L W → Set\n'
  'HAKN L A₀ A₁ = ∀ w w′ c c′ Y Y′ → CxN L w w′ → Good Y → Good Y′ → SRel Y Y′ → c ≤ c′ → Obs c c′ (A₀ C.self lW w Y) (A₁ C.self lW w′ Y′)')
code = code.replace('module L (b : H) (ac : AccY (hs b)) (ll : hs b ⊲[ W ] Λ) where', 'module L (b : H) (ac : AccY b) (ll : b ⊲[ W ] Λ) where')
code = code.replace('open R b using', 'open RL b using')
code = code.replace('HAK (hs b)', 'HAKN b').replace('Ctx (hs b)', 'CxN b').replace('Rel (hs b)', 'RelN b').replace('Rf (hs b)', 'RL.Rf b')
code = code.replace('D (hs b)', 'D b').replace('O (hs b) ac ll', 'O b ac ll')
code = code.replace('module Ch (snd : ∀ {x x′} → RelN b x x′ → SemS x x′) (i j : K.Act)', 'module Ch (snd : ∀ {x x′} → RelN b x x′ → SemS x x′) (tN : ∀ {x x′} → Rel b x x′ → RelN b x x′) (i j : K.Act)')
code = code.replace('(λ h → h ll)', '(λ h → tN (h ll))')
hdr = open(os.path.join(root, 'probes/Survey/scripts/monoport7/lay_header.md')).read()
open(os.path.join(root, 'probes/OCF/Align/MonoPort7Lay.lagda.md'), 'w').write(hdr + code)
