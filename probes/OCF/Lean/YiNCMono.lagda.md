# 颈结点弱链的记号侧前提
验收文件；编译定理：`fsT` 在 Ω 共尾前提下严格及非严格单调，不要求标准形。
最小颈结点的 Leaf 读法 `neck-a = Ω_Ω`、其 ψ₀ 折叠及 γ 链满足 `NF₁`；`YiBVDomain.slot` 也满足 `NF₁` 与 Ω₁ 共尾。
单调性复用 `EboLeanView.vΩ/fΩ-mono/fΩ-eq`，标准形实例复用 `EmbVVLZStandardOmega`；不修改树、折叠或合法性。
这解决单调性前提，不构造迭代的精确读回；第一阻点见 `YiNCFirst.FirstExact`。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNCMono where
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst₂)
import OCF.Align.EboLeanDef as E
open import OCF.Align.EboLeanBase using (_≤ᵀ_)
open import OCF.Align.EboLeanView using (vΩ; fΩ-mono; fΩ-eq)
import OCF.Align.EmbVVLZStandardOmega as Z
open import OCF.Align.Standard using (c[]; c∷)
import OCF.Lean.YiBVDomain as D

fsT-mono : ∀ {d ν η η′} → E.cof d ≡ E.cΩ ν → η E.<ᵀ η′ → E.fsT d η E.<ᵀ E.fsT d η′
fsT-mono {d} {η = η} {η′} e p = subst₂ E._<ᵀ_
  (sym (fΩ-eq (vΩ d e) η)) (sym (fΩ-eq (vΩ d e) η′)) (fΩ-mono (vΩ d e) p)

fsT-mono≤ : ∀ {d ν η η′} → E.cof d ≡ E.cΩ ν → η ≤ᵀ η′ → E.fsT d η ≤ᵀ E.fsT d η′
fsT-mono≤ e (inj₁ p) = inj₁ (fsT-mono e p)
fsT-mono≤ e (inj₂ refl) = inj₂ refl

neck-a : E.T
neck-a = E.ΩTower 2

neck-NF₁ : Z.NF₁ neck-a
neck-NF₁ = Z.nfβᴱ

neck-cof : E.cof neck-a ≡ E.cΩ []
neck-cof = refl

neck-fsT : ∀ η → E.fsT neck-a η ≡ E.Ωt η
neck-fsT η = refl

neck-collapse-NF₁ : Z.NF₁ (E.ψ [] neck-a ∷ [])
neck-collapse-NF₁ = Z.n∷ (Z.nψ Z.n[] (Z.sC c[]) neck-NF₁
  (Z.flatBnd (Z.f∷ Z.fΩ Z.f[]))) Z.n[] tt

neck-γ-NF₁ : ∀ n → Z.NF₁ (E.γT neck-a [] n)
neck-γ-NF₁ = Z.NF₁-γ neck-NF₁ neck-cof Z.n[] (Z.sC c[])
  (Z.flatBnd (Z.f∷ Z.fΩ Z.f[]))

slot-NF₁ : Z.NF₁ D.slot
slot-NF₁ = Z.n∷ (Z.nψ Z.nf1 (Z.sC (c∷ c[])) Z.nfβᴱ
  (Z.flatBnd (Z.f∷ Z.fΩ Z.f[]))) Z.n[] tt

slot-cof : E.cof D.slot ≡ E.cΩ []
slot-cof = refl

slot-mono₁ : ∀ {η η′} → η E.<ᵀ η′ → E.fsT D.slot η E.<ᵀ E.fsT D.slot η′
slot-mono₁ = Z.fsT-mono₁ slot-NF₁ slot-cof
```
