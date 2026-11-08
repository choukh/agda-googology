# 原 Q 生成片段中，累计以后再完成确会增值

本例使用原 ψ̄ᵠ 的 qs、ql，而不是另造一个观察回调。
对每个原高度结构及其行参数，源都是 ql (λ _ → qs q0)。
新 run 的内项是累计的完整自然数列，外项再累计常值内项。
最后的第一位置完成严格增加其值。因此，不能仅由输出来自原 Q
或已经累计，推出最高闭项的完成保值。这不是最高闭项的反例。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TotalValueTailGenerated where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; mul; s≤s; ≤l)
open import OCF.Lean.NegFold1Base using (≤ᵛ-refl; ≤ᵛ-trans)
open import OCF.Lean.NegFold1If using (¬s≤ᵛ)
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; same-value; same-sym)
import OCF.Free.LiteralCompletion as C
import OCF.Free.Level as L
import OCF.Free.Prefix as P
open import OCF.BTBO using (module Ord-Ord)
import OCF.Free.TotalOrbitRun as R
open import OCF.Free.Tree using (Fl)
open import OCF.Align.LadderOrdBase using (HtB)
import OCF.Align.LadderOrdTree as T
open import OCF.Align.TotalOrbitSource using (ev₀)
open import OCF.Align.RadicalValueNativeFinal using (forget)
import OCF.Align.TotalValueTailRepeat as Strict

self : ∀ (a : Cd) → Same a a
self hz = zz
self (hs a) = ss (self a)
self (hl f) = ll (λ n → self (f n))
self (hΩ () g)
add-shape : ∀ {a b c d : Cd} → Same a b → Same c d → Same (a ⊞ c) (b ⊞ d)
add-shape p zz = p
add-shape p (ss q) = ss (add-shape p q)
add-shape p (ll q) = ll (λ n → add-shape p (q n))
sums-shape : ∀ {f g : ℕ → Cd} → (∀ n → Same (f n) (g n)) →
  ∀ n → Same (C.Σ₀ f n) (C.Σ₀ g n)
sums-shape p zero = p zero
sums-shape p (suc n) = add-shape (sums-shape p n) (p (suc n))
leg-shape : ∀ {a b : Cd} → Same a b → Same (C.leg a) (C.leg b)
leg-shape zz = zz
leg-shape (ss p) = ss (leg-shape p)
leg-shape (ll p) = ll (sums-shape (λ n → leg-shape (p n)))

forget-add : ∀ a b → Same (forget (R.add a b)) (forget a ⊞ forget b)
forget-add a L.zero = self _
forget-add a (L.suc b) = ss (forget-add a b)
forget-add a (L.lim f st) = ll (λ n → forget-add a (f n))

-- 常值累计的每一项，保留原 add 的证书，而非函数外延。
constant-sums : ∀ a n → Same (forget (R.sum (λ _ → a) n)) (mul (forget a) n)
constant-sums a zero = self _
constant-sums a (suc n) = compose (forget-add (R.sum (λ _ → a) n) a)
  (add-shape (constant-sums a n) (self _))
  where
  compose : ∀ {a b c : Cd} → Same a b → Same b c → Same a c
  compose zz zz = zz
  compose (ss p) (ss q) = ss (compose p q)
  compose (ll p) (ll q) = ll (λ n → compose (p n) (q n))

module Actual (S : HtB) (m : T.Ht S) where
  open T S
  inner : Q m L.zero Fl (κ Fl)
  inner = qs q0
  outer : Q m L.zero Fl (κ Fl)
  outer = ql (λ _ → inner)
  inner-source : P.Z
  inner-source = P.toZ (ψ̄ᵠ ok₀ (λ i h r → ok₀ i) inner ev₀ L.zero)
  source : P.Z
  source = P.toZ (ψ̄ᵠ ok₀ (λ i h r → ok₀ i) outer ev₀ L.zero)
  native : L.Ordᴵ
  native = R.run inner-source
  terms : ℕ → L.Ordᴵ
  terms n = R.run (P.toZ (Ord-Ord.iter (P._+ˢ_ (P.Ωˢ L.zero))
    P.Ord₊ˢ.zero n))
  branches : ℕ → Cd
  branches n = forget (R.sum terms n)
  native-shape : forget native ≡ hl branches
  native-shape = refl
  positive : hs hz ≤ᵛ hl branches
  positive = ≤l (suc zero) (≤ᵛ-refl _)
  raw : Cd
  raw = forget (R.run source)
  raw-shape : Same raw (Strict.repeat (hl branches))
  raw-shape = ll (constant-sums native)
  strict : hs raw ≤ᵛ C.leg raw
  strict = ≤ᵛ-trans (s≤s (same-value raw-shape))
    (≤ᵛ-trans (Strict.strict-repeat branches positive)
      (same-value (leg-shape (same-sym raw-shape))))
  no-upper : C.leg raw ≤ᵛ raw → ⊥
  no-upper p = ¬s≤ᵛ raw (≤ᵛ-trans strict p)
  lawful-completion : LgB (C.leg raw)
  lawful-completion = C.Lg-leg raw
```

strict 的输入逐字为原解释器产生的完整 ql/qs 源，经新的原 run 后
再忘到 Cd。证明覆盖其全部基本列；不是有限测试。这里没有 Ω 高反馈，
所以该反例只排除「整个原 Q 生成域的完成均保值」这一过强简化。
最高端行仍可能通过其实际回灌获得额外吸收，尚须独立证明。
