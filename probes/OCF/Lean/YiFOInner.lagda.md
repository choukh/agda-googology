# 候选首链点读回层的内部缺格
验收文件，不读记号；a 是候选第 3 站首链点的孩子层，内链用它实际继承的底。
编译目标为层号分解、合法折叠生成的首内链点及该点上的空格；没有完整闭项请求踪迹的证据。
来源：YiCWActual 的真实底与链；不因此判定 rbᵗ 在完整请求域上不完全，也不判定值损失。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFOInner where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Maybe using (nothing)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiTBRow using (Rb; ψ)
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiCWTable as CW
import OCF.Lean.YiCWActual as CA
idx : L → L
idx (nd (sΩ k) h) = k
idx _ = zero
kids : (a : L) → Tr (idx a) → L
kids (nd (sΩ k) h) c = h c
kids zero c = zero
kids (nd sS h) c = zero
kids (nd sL h) c = zero
opaque
  a : L
  a = CW.hᵗ 2 CA.c₁
  actual : a ≡ CW.hᵗ 2 CA.c₁
  actual = refl
  k : L
  k = idx a
  h : Tr k → L
  h = kids a
  eq : a ≡ nd (sΩ k) h
  eq = refl
  o : Ok (nd (sΩ k) h)
  o = subst Ok eq (proj₂ (Ok-tw 3) CA.c₁)
  BB : Base (nd (sΩ k) h)
  BB = subst Base eq (λ i u → CA.baseᴱ 3 i (inc CA.c₁ u))
  g : Tr k → Tr (nd (sΩ k) h)
  g c = proj₁ (upz {s = sΩ k} {h = h} c (Ωt (h c)))
  feed : Tr k → Tr k
  feed c = proj₁ (ψ (nd (sΩ k) h) o (MT.rbᶻ (nd (sΩ k) h)) BB k (ink self) (BB k (ink self)) (g c))
  feed-positive : ∀ c → k ⊢ zero ◃ feed c
  feed-positive c = proj₂ (ψ (nd (sΩ k) h) o (MT.rbᶻ (nd (sΩ k) h)) BB k (ink self) (BB k (ink self)) (g c))
  c₁ : Tr k
  c₁ = feed zero
  miss : MT.tbᶻ k h zero c₁ ≡ nothing
  miss = refl
```
