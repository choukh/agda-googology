# 统一 Int 的实际生成族与单侧迁回

源族是原全部 H₀ 编码及原 Ωd one；外回调逐字 identity。
这是统一 preserve 的实例，不替换原 Int 或原 read/drp。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EventReturnCtxActual where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import OCF.Align.CumReadCF using (Lg; lg⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.EvFoldTree
open import OCF.Align.EvFoldRead
open import OCF.Align.EventReturnCoordBuild using (encoded₀)
import OCF.Align.EventReturnCoordBuild as E
open import OCF.Align.EventReturnCodeIf using (Code; cz; co; ca; cl; ck; Shape; sz; ss; sl; so)
open import OCF.Align.EventReturnCodeBuild using (encoded; shape-self; nb-shape)
open import OCF.Align.EventReturnCtxIf
open import OCF.Align.EventReturnCtxBuild
open import OCF.Align.EventReturnInt using (one-acc)

code : ∀ {a H H′ x y} → Code a H H′ x y → R₁ a H H′ x y
code cz = rz
code co = ro
code (ca p q) = ra (code p) (code q)
code (cl p) = rl (λ n → code (p n))
code (ck p) = rk (λ q lc → code (p q lc))

left : ∀ {a H H′ J x y} → R₁ a H H′ x y → R₁ a J H′ (drp₁ x) y
left rz = rz
left ro = ro
left (ra p q) = ra (left p) (left q)
left (rl p) = rl (λ n → left (p n))
left (rw p s s′ r) = rw p here s′ (left r)
left (rk p) = rk (λ q lc → left (p q lc))
left (ri p) = ri (λ q s s′ lc r → left (p q (tp-suf s _) s′ lc (E.drop-left r)))

right : ∀ {a H H′ J x y} → R₁ a H H′ x y → R₁ a H J x (drp₁ y)
right rz = rz
right ro = ro
right (ra p q) = ra (right p) (right q)
right (rl p) = rl (λ n → right (p n))
right (rw p s s′ r) = rw p s here (right r)
right (rk p) = rk (λ q lc → right (p q lc))
right (ri p) = ri (λ q s s′ lc r → right (p q s (tp-suf s′ _) lc (E.drop-right r)))

mutual
  observe : ∀ {a H H′ x y b b′} → (la : Lg a) → R₁ a H H′ x y → Shape b b′ →
    Shape (rd₁ (la , tt) b x) (rd₁ (la , tt) b′ y)
  observe la rz p = p
  observe la ro p = ss p
  observe la (ra {x} {y} {x′} {y′} r s) p =
    observe {x = y} {y = y′} la s (observe {x = x} {y = x′} la r p)
  observe la (rl r) p = sl (λ n → partials la r p n)
  observe la (rw q s s′ r) p = observe (lg⊲ q la) r p
  observe {a} la (rk r) p = so (nb-shape p (λ c q → observe (lwκ c la) (r (pwκ a c) (lwκ c la)) q))
  observe la (ri r) p = so (nb-shape p (λ c q → observe la (r C.self here here la (encoded₀ c)) q))

  partials : ∀ {a H H′ f g b b′} → (la : Lg a) →
    (∀ n → R₁ a H H′ (f n) (g n)) → Shape b b′ →
    ∀ n → Shape (rdp₁ (la , tt) b f n) (rdp₁ (la , tt) b′ g n)
  partials la r p zero = p
  partials la r p (suc n) = observe la (r n) (partials la r p n)

identity : ∀ {a H H′} → UH {a} {H} {H′} (λ _ _ z → z) (λ _ _ z → z)
identity p s s′ lc r = r

run : ∀ {W} → LgWε W → D₁ W → D₁ W → D₁ W
run lw z w = Int one-acc z ≤rf lw tt (λ _ p → p) (λ _ r → r) (λ _ _ x → x) w

run-related : ∀ {a H H′ x y w w′} → (la : Lg a) → R₁ a H H′ x y → R₁ a H H′ w w′ →
  R₁ a H H′ (run (la , tt) x w) (run (la , tt) y w′)
run-related la r q = preserve one-acc one-acc r C.self here here la (λ _ r → r) (λ _ r → r) identity q

encoded-run : ∀ {a H H′} (la : Lg a) x w →
  R₁ a H H′ (run (la , tt) (toD₁ x) (toD₁ w)) (run (la , tt) (toD₁ x) (toD₁ w))
encoded-run la x w = run-related la (code (encoded x)) (code (encoded w))

omega-run : ∀ {a H H′} (la : Lg a) w →
  R₁ a H H′ (run (la , tt) (Ωd (hs hz)) (toD₁ w)) (run (la , tt) (Ωd (hs hz)) (toD₁ w))
omega-run la w = run-related la (ra ro (ri (λ _ _ _ _ _ → ro))) (code (encoded w))

-- 全编码源含 nκ，实际 Int 会走 IW₀/Cut₀；单侧迁回后原读回不变。
encoded-return : ∀ {a H H′} (la : Lg a) b x w →
  Shape (rd₁ {a , H′} (la , tt) b (drp₁ (run {a , H} (la , tt) (toD₁ x) (toD₁ w))))
        (rd₁ {a , H} (la , tt) b (run (la , tt) (toD₁ x) (toD₁ w)))
encoded-return la b x w = observe la (left (encoded-run la x w)) (shape-self b)
```

这些实例实填 UH 与全部关系前提；含 Ω 的编码源并未被改成纯可数源。
目前只完成第一层。第二层的 nε 与事件载荷相关仍须另证，不能从这里推广。
