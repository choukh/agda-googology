# 实际槽位链的第 0 步
不读记号；编译的值界只覆盖第 0→1 点与每个实际链点的继承底界，尚未给出相邻链点的值增长。
实际底、起点及链公式逐字重建自 `YiGIInst`、`YiFRStep`；本模块不导入两者，对接见 `YiSLCheck`。
`feed-form`、`out-form` 只是展开等式；不计作原简报第 1 步。n=1 的第 1→2 点尚未走通，未否定路线。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSLStart where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiTBRow using (ψ; mono)
open import OCF.Lean.YiMTTab using (rbᶻ)
import OCF.Lean.YiVWVal as V

FΛ : ℕ → Tr Λ
FΛ n = proj₁ (upz {s = sL} {h = tw} n (Ωt (tw n)))

pre : ℕ → Tr Λ
pre zero = zero
pre (suc n) = cum FΛ n

baseᴱ : ∀ n → Base (tw n)
baseᴱ n i u = ψ Λ Ok-Λ (rbᶻ Λ) (B₀ Λ) i (inc n u) (Ωt i) (pre n)

betaᴱ : ∀ n → Tr⁺ zero
betaᴱ n = ψ Λ Ok-Λ (rbᶻ Λ) (B₀ Λ) zero (z≤ Λ) (Ωt zero) (pre n)

module Step (n : ℕ) where
  ℓ = tw (suc n)
  k = tw n

  child : Tr k → L
  child c = k ⊕ ↑ k c

  g : Tr k → Tr ℓ
  g c = proj₁ (upz {s = sΩ k} {h = child} c (Ωt (child c)))

  feed⁺ : Tr k → Tr⁺ k
  feed⁺ c = ψ ℓ (Ok-tw (suc n)) (rbᶻ ℓ) (baseᴱ (suc n)) k (ink self)
    (baseᴱ (suc n) k (ink self)) (g c)

  feed : Tr k → Tr k
  feed c = proj₁ (feed⁺ c)

  out : Tr k → Tr⁺ zero
  out c = ψ ℓ (Ok-tw (suc n)) (rbᶻ ℓ) (baseᴱ (suc n)) zero (z≤ ℓ)
    (betaᴱ (suc n)) (g c)

  chain : ℕ → Tr k
  chain = iter feed zero

  Bchild : (c : Tr k) → Base (child c)
  Bchild c i u = baseᴱ (suc n) i (inc c u)

  feed-form : (q : ℕ) → chain (suc q) ≡
    proj₁ (ψ (child (chain q)) (proj₂ (Ok-tw (suc n)) (chain q))
      (rbᶻ (child (chain q))) (Bchild (chain q)) k
      (self ∙ lift k (↑ k (chain q))) (baseᴱ (suc n) k (ink self))
      (proj₁ (Ωt (child (chain q)))))
  feed-form q = refl

  out-form : (q : ℕ) → out (chain q) ≡
    ψ (child (chain q)) (proj₂ (Ok-tw (suc n)) (chain q))
      (rbᶻ (child (chain q))) (Bchild (chain q)) zero (z≤ (child (chain q)))
      (betaᴱ (suc n)) (proj₁ (Ωt (child (chain q))))
  out-form q = refl

  chain0 : chain 0 ≡ zero
  chain0 = refl

  chain1 : chain 1 ≡ proj₁ (ψ k (Ok-tw n) (rbᶻ k) (Bchild zero)
    k self (baseᴱ (suc n) k (ink self)) (proj₁ (Ωt k)))
  chain1 = refl

  point-base : (q : ℕ) → V.val k (proj₁ (baseᴱ (suc n) k (ink self)))
    V.◁ V.val k (chain (suc q))
  point-base q = V.val-mono k
    (mono ℓ (Ok-tw (suc n)) (rbᶻ ℓ) (baseᴱ (suc n)) k (ink self)
      (baseᴱ (suc n) k (ink self))
      (◃u zero (chain q) (proj₁ (Ωt (child (chain q))))
        (proj₂ (Ωt (child (chain q))))))

  out-base : (q : ℕ) → V.val zero (proj₁ (betaᴱ (suc n)))
    V.◁ V.val zero (proj₁ (out (chain q)))
  out-base q = V.val-mono zero
    (mono ℓ (Ok-tw (suc n)) (rbᶻ ℓ) (baseᴱ (suc n)) zero (z≤ ℓ)
      (betaᴱ (suc n))
      (◃u zero (chain q) (proj₁ (Ωt (child (chain q))))
        (proj₂ (Ωt (child (chain q))))))

-- 仅合并第 0→1 点的证明；q 固定为 0，不外推到 q > 0。
growth0 : ∀ n → V.val (tw n) (Step.chain n 0) V.◁ V.val (tw n) (Step.chain n 1)
growth0 n = V.val-mono (tw n) (proj₂ (Step.feed⁺ n zero))

growth10 : V.val (tw 1) (Step.chain 1 0) V.◁ V.val (tw 1) (Step.chain 1 1)
growth10 = growth0 1

growth20 : V.val (tw 2) (Step.chain 2 0) V.◁ V.val (tw 2) (Step.chain 2 1)
growth20 = growth0 2
```
