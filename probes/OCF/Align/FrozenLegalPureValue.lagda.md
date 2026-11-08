# 实际中间值与旧第一层轨道的尾部

使用逐构造子关系比较全部轨道，避免函数外延。参考树为原 Fold1.TΩ1
回灌输出删去第零项后的部分和；不是新造的常值样本。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.FrozenLegalPureValue where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (mul; _≤ᵛ_; z≤; s≤s; ≤s; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans; ≤⊞)
open import OCF.Lean.FrozenOmegaIf
open import OCF.Lean.FrozenOmegaRun using (chain)
open import OCF.Lean.FrozenOmegaClosed using (U; w; intermediate)
open import OCF.Lean.FrozenLegalIf using (act)
open import OCF.Lean.FrozenLegalClosed using (next)
open import OCF.Lean.TowerCollapseIf using (module Ops)
import OCF.Align.FrozenValueFirst as V
import OCF.Lean.Fold1 as Original

-- 两边均只含可数构造子；右侧允许处于任意种类结构。
data Rel {S : KS} : Cd → HB S → Set where
  rz : Rel hz hz
  rs : ∀ {a b} → Rel a b → Rel (hs a) (hs b)
  rl : ∀ {f g} → (∀ n → Rel (f n) (g n)) → Rel (hl f) (hl g)

add-rel : ∀ {S a b} {c d : HB S} → Rel a c → Rel b d → Rel (a ⊞ b) (c ⊞ d)
add-rel p rz = p
add-rel p (rs q) = rs (add-rel p q)
add-rel p (rl q) = rl (λ n → add-rel p (q n))

partial-rel : ∀ {S} f g → (∀ n → Rel {S} (f n) (g n)) → ∀ n →
  Rel (Ops.partial S⊥ f n) (Ops.partial S g n)
partial-rel f g p zero = p zero
partial-rel f g p (suc n) = add-rel (partial-rel f g p n) (p (suc n))

erase-rel : ∀ {S v m a b} → Rel a b → Rel a (erase {S} {v} {m} b)
erase-rel rz = rz
erase-rel (rs p) = rs (erase-rel p)
erase-rel (rl p) = rl (λ n → erase-rel (p n))

repeat-rel : ∀ {S a} {b : HB S} → Rel a b → ∀ n → Rel (mul a n) (Ops.partial S (λ _ → b) n)
repeat-rel p zero = p
repeat-rel p (suc n) = add-rel (repeat-rel p n) p

act-rel : ∀ W {a b} → Rel a b → Rel (V.F W a) (act b)
act-rel W rz = rs rz
act-rel W (rs p) = rl (repeat-rel (act-rel W p))
act-rel W (rl p) = rl (λ n → act-rel W (p n))

coordinate-rel : ∀ n → Rel (V.O.ce (suc n)) (chain {B = SafeTw U w hz} next n)
coordinate-rel zero = rs rz
coordinate-rel (suc n) = add-rel (coordinate-rel n)
  (erase-rel (act-rel (V.O.cw (suc n)) (coordinate-rel n)))

output-rel : ∀ n → Rel (V.O.oo (suc n)) (act (chain {B = SafeTw U w hz} next n))
output-rel n = act-rel (V.O.cw (suc n)) (coordinate-rel n)

tail : Cd
tail = hl (Ops.partial S⊥ (λ n → V.O.oo (suc n)))

tail-rel : Rel tail intermediate
tail-rel = erase-rel (rl (partial-rel _ _ output-rel))

forward : ∀ {a b} → Rel a b → up a ≤ᵛ b
forward rz = z≤
forward (rs p) = s≤s (forward p)
forward (rl p) = l≤ (λ n → ≤l n (forward (p n)))
backward : ∀ {a b} → Rel a b → b ≤ᵛ up a
backward rz = z≤
backward (rs p) = s≤s (backward p)
backward (rl p) = l≤ (λ n → ≤l n (backward (p n)))

up-tail≤intermediate : up tail ≤ᵛ intermediate
up-tail≤intermediate = forward tail-rel
intermediate≤up-tail : intermediate ≤ᵛ up tail
intermediate≤up-tail = backward tail-rel
```

## 尾部与原树同值

旧解释器在不同世界的纯坐标上联合单调，故输出序列单调。
逐项错位比较部分和，不需要函数外延或把该值识别为某个记号。

```agda
module Self = V.Compare V.pure-F V.pure-F

output-step : ∀ n → V.O.oo n ≤ᵛ V.O.oo (suc n)
output-step n = Self.mono (V.O.cw n) (V.O.cw (suc n)) (≤⊞ (V.O.ce n) (V.O.oo n))

full≤tail-sum : ∀ n → V.O.oO n ≤ᵛ Ops.partial S⊥ (λ k → V.O.oo (suc k)) n
full≤tail-sum zero = output-step zero
full≤tail-sum (suc n) = V.add-mono (full≤tail-sum n) (output-step (suc n))

right-inclusion : ∀ (a b : Cd) → b ≤ᵛ a ⊞ b
right-inclusion a hz = z≤
right-inclusion a (hs b) = s≤s (right-inclusion a b)
right-inclusion a (hl f) = l≤ (λ n → ≤l n (right-inclusion a (f n)))

tail≤full-sum : ∀ n → Ops.partial S⊥ (λ k → V.O.oo (suc k)) n ≤ᵛ V.O.oO (suc n)
tail≤full-sum zero = right-inclusion (V.O.oo zero) (V.O.oo 1)
tail≤full-sum (suc n) = V.add-mono (tail≤full-sum n) (≤-refl (V.O.oo (suc (suc n))))

original≤tail : Original.TΩ1 ≤ᵛ tail
original≤tail = l≤ (λ n → ≤l n (full≤tail-sum n))
tail≤original : tail ≤ᵛ Original.TΩ1
tail≤original = l≤ (λ n → ≤l (suc n) (tail≤full-sum n))

up-mono : ∀ {a b : Cd} → a ≤ᵛ b → up {S⊥} a ≤ᵛ up b
up-mono z≤ = z≤
up-mono (s≤s p) = s≤s (up-mono p)
up-mono (≤s p) = ≤s (up-mono p)
up-mono (l≤ p) = l≤ (λ n → up-mono (p n))
up-mono (≤l n p) = ≤l n (up-mono p)

original≤intermediate : up Original.TΩ1 ≤ᵛ intermediate
original≤intermediate = ≤-trans (up-mono original≤tail) up-tail≤intermediate
intermediate≤original : intermediate ≤ᵛ up Original.TΩ1
intermediate≤original = ≤-trans intermediate≤up-tail (up-mono tail≤original)
```

结论是实际中间树与原第一层闭项嵌入同值；因此其合法性补齐并没有
证得新强度。最终 T 还经过另一次低层折叠，不在这两个定理的范围内。
