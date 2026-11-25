# 任意底的第一孩子下降与 Ω 结点的行
验收文件（经 `OCF.Align.Value` 读第 0 层的值，导入闭包含记号模块）；编译定理，无前提：`descᴮ` 把 `YiMTKeel.descᶻ` 推广到满足 `Hi`（底不低于 Ω 树）的任意底与起点，`rowsᴮ` 把 `rowsΩᶻ` 推广到任意底。
来源：证明照 `YiMTKeel.step¹ᶻ`、`rowsΩᶻ`；后继形状一步多用 `Hi`。树、折叠、表一行不改。
不否定什么；入口 `YiSYReduce`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSYDesc where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; kp)
open import OCF.Lean.YiTBRow using (ψ; mono)
open import OCF.Lean.YiMTTab using (rbᶻ)
open import OCF.Lean.YiBRValue using (readRW)
open import OCF.Lean.YiKSDesc using (_⊑¹_; r¹; n¹; ok¹; ◃≼ᴿ; plusᴿ; rowN)
open import OCF.Align.Value using (_≼_; ≼l; ≼-refl; ≼-trans)

Fd : (ℓ : L) → Ok ℓ → Base ℓ → Tr⁺ zero → Tr zero
Fd ℓ o B β = proj₁ (ψ ℓ o (rbᶻ ℓ) B zero (z≤ ℓ) β (proj₁ (Ωt ℓ)))

dn : ∀ {s h} → Base (nd s h) → (c : Ch s) → Base (h c)
dn B c i u = B i (inc c u)

Hi : ∀ {ℓ} → Base ℓ → Set
Hi {ℓ} B = ∀ i (u : i ≤ ℓ) {z} → i ⊢ proj₁ (B i u) ◃ z → i ⊢ proj₁ (Ωt i) ◃ z

stepᴮ : (s : Sh) (h : Ch s → L) (o : Ok (nd s h)) (B : Base (nd s h)) (β : Tr⁺ zero) → Hi B
  → readRW (Fd (h (c₀ s)) (proj₂ o (c₀ s)) (dn B (c₀ s)) β) ≼ readRW (Fd (nd s h) o B β)
stepᴮ sS h o B β hi = ≼l 1 (plusᴿ _ _ (◃≼ᴿ (◃t
  (mono (h tt) (proj₂ o tt) (rbᶻ (h tt)) (dn B tt) zero (z≤ (h tt)) β (hi (h tt) (inc tt self) (◃l zero)))
  (◃l zero))))
stepᴮ sL g o B β hi = ◃≼ᴿ (◃l zero)
stepᴮ (sΩ k) h o B β hi =
  ◃≼ᴿ (mono (nd (sΩ k) h) o (rbᶻ (nd (sΩ k) h)) B zero (z≤ (nd (sΩ k) h)) β (◃w {p = inj₁ (inj₁ tt)}))

dn¹ : ∀ {j ℓ} → j ⊑¹ ℓ → Base ℓ → Base j
dn¹ r¹         B = B
dn¹ (n¹ {s} p) B = dn¹ p (dn B (c₀ s))

descᴮ : ∀ {j ℓ} (p : j ⊑¹ ℓ) (o : Ok ℓ) (B : Base ℓ) (β : Tr⁺ zero) → Hi B
  → readRW (Fd j (ok¹ p o) (dn¹ p B) β) ≼ readRW (Fd ℓ o B β)
descᴮ {j} r¹ o B β hi = ≼-refl (readRW (Fd j o B β))
descᴮ (n¹ {s} {h} p) o B β hi =
  ≼-trans (descᴮ p (proj₂ o (c₀ s)) (dn B (c₀ s)) β (λ i u → hi i (inc (c₀ s) u))) (stepᴮ s h o B β hi)
```

Ω 形状层号（下标层 k）朝第 0 层：链在第 k 层，经 `ink self` 以底为起点回灌；第 n 行是链点那个孩子上的折叠。

```agda
module Node (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h)) (B : Base (nd (sΩ k) h)) (β : Tr⁺ zero) where
  g : Tr k → Tr (nd (sΩ k) h)
  g z = proj₁ (upz {s = sΩ k} {h = h} z (Ωt (h z)))

  out : Tr k → Tr⁺ zero
  out z = ψ (nd (sΩ k) h) o (rbᶻ (nd (sΩ k) h)) B zero (z≤ (nd (sΩ k) h)) β (g z)

  feed : Tr k → Tr k
  feed z = proj₁ (ψ (nd (sΩ k) h) o (rbᶻ (nd (sΩ k) h)) B k (ink self) (B k (ink self)) (g z))

  chain : ℕ → Tr k
  chain = iter feed zero

  out-child : ∀ z → proj₁ (out z) ≡ Fd (h z) (proj₂ o z) (dn B z) β
  out-child z = refl

  rowsᴮ : ∀ n → readRW (proj₁ (out (chain n))) ≼ readRW (Fd (nd (sΩ k) h) o B β)
  rowsᴮ n = rowN (kp (nd (sΩ k) h) o (inj₁ (inj₁ tt)) (z≤ (nd (sΩ k) h))) out feed n
    (≼-refl (readRW (proj₁ (out (chain n)))))
```
