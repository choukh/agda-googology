# 从 MonoPort6Int 生成 MonoPort7Int: 源层带节点的 Int 单调对任意层 L (hs 与 hl) 写一次
# 用法: python3 mk_int.py <仓库根>
import sys, os
root = sys.argv[1]
src = open(os.path.join(root, 'probes/OCF/Align/MonoPort6Int.lagda.md')).read()
code = src[src.index('```agda'):]
code = code.replace('module OCF.Align.MonoPort6Int', 'module OCF.Align.MonoPort7Int')
code = code.replace('using (hs; hl; hΩ; ss; StH;', 'using (hs; hl; hΩ; ss; sl; sL; StH;')
code = code.replace('open import OCF.Align.MonoPort6Rel Λ lΛ lW t₀', 'open import OCF.Align.MonoPort7Rel Λ lΛ lW t₀')
# CxS 对层 L
a = code.index('module CxS (b : H) where')
b = code.index('U : H → H → Set')
cx = code[a:b]
cx = cx.replace('module CxS (b : H) where\n  open R b hiding (Rf)\n',
                'module CxS (L : H) where\n  open RL L hiding (Rf)\n\n  Rf′ : D L W → Set\n  Rf′ x = RelN L x x\n')
cx = cx.replace('C = Ctx (hs b)', 'C = CxN L')
cx = cx.replace('Rf (hs b)', 'Rf′').replace('Rel (hs b)', 'RelN L').replace('D (hs b)', 'D L')
code = code[:a] + cx + code[b:]
code = code.replace('cx00 (hl f) = tt', 'cx00 (hl f) = RelM.n0⊑ , (RelM.n0⊑ , RelM.n0⊑)')
# IntMK / IntMS
a = code.index('IntMK : ')
head, tail = code[:a], code[a:]
tail = tail.replace('IntMS : ∀ b → Fin b → (ac : AccY (hs b))', 'IntMS : ∀ L → Fin L → (ac : AccY L)')
tail = tail.replace('Mk (hs b) ly', 'Mk L ly').replace('U (hs b) ly', 'U L ly').replace('Mo (hs b) ly', 'MoN L ly')
tail = tail.replace('Rel (hs b) x x′ → Ctx (hs b) w w′', 'RelN L x x′ → CxN L w w′')
tail = tail.replace('IntMK (hs b) fk ac zy mk mu mu′ cr hx hw = IntMS b fk ac zy mk mu mu′ cr (proj₁ hx) hw',
  'IntMK (hs b) fk ac zy mk mu mu′ cr hx hw = IntMS (hs b) fk ac zy mk mu mu′ cr (proj₁ hx) hw\n'
  'IntMK (hl f) fk ac zy mk mu mu′ cr hx hw = IntMS (hl f) fk ac zy mk mu mu′ cr (proj₁ hx) hw')
tail = tail.replace('IntMS b fb', 'IntMS L fb')
tail = tail.replace('cxL (hs b)', 'cxLN L').replace('cxR (hs b)', 'cxRN L')
tail = tail.replace('CxS.cx⨾ b', 'CxS.cx⨾ L').replace('CxS.cx0l b', 'CxS.cx0l L').replace('CxS.cx0r b', 'CxS.cx0r L')
tail = tail.replace('CxS.cxas b', 'CxS.cxas L').replace('CxS.cxas′ b', 'CxS.cxas′ L').replace('CxS.ctxN b', 'CxS.ctxN L')
tail = tail.replace('CxS.cxPre b', 'CxS.cxPre L').replace('CxS.okRf b', 'CxS.okRf L').replace('CxS.preM b', 'CxS.preM L')
tail = tail.replace('CxS.preR b', 'CxS.preR L').replace('R.rPre b', 'RL.rPre L').replace('R.rnw b', 'RL.rnw L')
tail = tail.replace('Ctx (hs b)', 'CxN L')
tail = tail.replace('(RelM.ni⊑ {k = j} (ss P) {u = v}', '(RelM.ni⊑ {k = j} r {u = v}')
tail = tail.replace('lowIn (hs b) (ss P)', 'lowIn L r').replace('Kup C.self (ss P)', 'Kup C.self r')
tail = tail.replace('g (ss P)', 'g r').replace('mkOf (ss P) C.self', 'mkOf r C.self').replace('Mk j (hs b)', 'Mk j L')
tail = tail.replace('fj = fin⊲ P fb', 'fj = finS r fb').replace('Vs (hs b) (ss P)', 'Vs L r').replace('LowT (hs b) (ss P)', 'LowT L r')
tail = tail.replace('inS (ss P)', 'inS r').replace('Rel (hs b)', 'RelN L').replace('Mo j (hs b)', 'Mo j L')
tail = tail.replace('(g r) tt mkR', '(g r) (NZ-S r) mkR').replace('Vs L r W′ → D (hs b) W′', 'Vs L r W′ → D L W′')
extra = '''-- 一般层的分支单调 (上下文取 CxN), 上下文两边自比, 节点子层的有限
MoN : ∀ L ly → U L ly → U L ly → Set
MoN L ly u u′ = ∀ (z z′ : D L W) → CxN L z z′ → Rel ly (u C.self lW z) (u′ C.self lW z′)

cxLN : ∀ L {z z′} → CxN L z z′ → CxN L z z
cxLN L (_ , (o , _)) = RL.OkRf L o , (o , o)

cxRN : ∀ L {z z′} → CxN L z z′ → CxN L z′ z′
cxRN L (_ , (_ , o′)) = RL.OkRf L o′ , (o′ , o′)

finS : ∀ {L j} → StH W j L → Fin L → Fin j
finS (ss P) f = fin⊲ P f
finS (sl n P) f = fin⊲ P (f n)
finS (sL e P) ()

-- 带节点的层上 Rel 就是 RelN (两个方向, 定义性)
toN : ∀ L → NZ L → Fin L → ∀ {x y} → Rel L x y → RelN L x y
toN (hs b) _ _ h = h
toN (hl f) _ _ h = h

fromN : ∀ L → NZ L → Fin L → ∀ {x y} → RelN L x y → Rel L x y
fromN (hs b) _ _ h = h
fromN (hl f) _ _ h = h

'''
tail = tail.replace('(IntMK j fj', '(toN L (NZ-S r) fb (IntMK j fj').replace('(cx00 j))', '(cx00 j)))')
tail = tail.replace('moV h z z′ c = h (inS r z) (inS r z′) (lowIn L r c)', 'moV h z z′ c = fromN L (NZ-S r) fb (h (inS r z) (inS r z′) (lowIn L r c))')
head = head.replace('源层 `hs b` 的关系只在世界', '源层 $L$ (`hs b` 或 `hl f`) 的关系只在世界')
code = head + extra + tail
hdr = open(os.path.join(root, 'probes/Survey/scripts/monoport7/int_header.md')).read()
open(os.path.join(root, 'probes/OCF/Align/MonoPort7Int.lagda.md'), 'w').write(hdr + code)
