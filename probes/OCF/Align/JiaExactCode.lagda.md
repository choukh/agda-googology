# 新 ψ 所用的 EBO 基本列等式

第 4 层脚手架。这里对有限码分情况，只证明已有 EBO 定义的运算等式，
不参与原树或新版 ψ 的定义，也不改 Rep。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.JiaExactCode where

open import Data.Nat.Base using (ℕ)
open import Data.List.Base using ([]; _∷_; replicate)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; trans)
open import OCF.Align.EboLeanDef
  using (T; ψ; sucT; pred; cof; Cof; c1; cω; cΩ; cofA; cofψ₊;
         Cmp; cmpᵀ; fsn; fsn₊; fsnc; fsT; fsT₊; fsTc)
open import OCF.Align.JiaAuditClosure using (cof-suc; pred-suc)

Ψ : T → T → T
Ψ i c = ψ i c ∷ []

cof-ψ-1 : ∀ i c → cof c ≡ c1 → cof (Ψ i c) ≡ cω
cof-ψ-1 i [] ()
cof-ψ-1 i c@(_ ∷ _) e = cong (cofA i) e

cof-ψ-ω : ∀ i c → cof c ≡ cω → cof (Ψ i c) ≡ cω
cof-ψ-ω i [] ()
cof-ψ-ω i c@(_ ∷ _) e = cong (cofA i) e

fsn-ψ-1 : ∀ i c → cof c ≡ c1 → ∀ n →
  fsn (Ψ i c) n ≡ replicate n (ψ i (pred c))
fsn-ψ-1 i [] () n
fsn-ψ-1 i c@(_ ∷ _) e n = cong (λ k → fsn₊ i c k n) e

fsn-ψ-suc : ∀ i c n → fsn (Ψ i (sucT c)) n ≡ replicate n (ψ i c)
fsn-ψ-suc i c n = trans (fsn-ψ-1 i (sucT c) (cof-suc c) n)
  (cong (λ d → replicate n (ψ i d)) (pred-suc c))

fsn-ψ-ω : ∀ i c → cof c ≡ cω → ∀ n →
  fsn (Ψ i c) n ≡ Ψ i (fsn c n)
fsn-ψ-ω i [] () n
fsn-ψ-ω i c@(_ ∷ _) e n = cong (λ k → fsn₊ i c k n) e

cof-ψ-Ω : ∀ i c j m → cof c ≡ cΩ j → cmpᵀ (sucT j) i ≡ m →
  cof (Ψ i c) ≡ cofψ₊ i j m
cof-ψ-Ω i [] j m () em
cof-ψ-Ω i c@(_ ∷ _) j m e em =
  trans (cong (cofA i) e) (cong (cofψ₊ i j) em)

fsn-ψ-Ω : ∀ i c j m → cof c ≡ cΩ j → cmpᵀ (sucT j) i ≡ m → ∀ n →
  fsn (Ψ i c) n ≡ fsnc i c j m n
fsn-ψ-Ω i [] j m () em n
fsn-ψ-Ω i c@(_ ∷ _) j m e em n =
  trans (cong (λ k → fsn₊ i c k n) e) (cong (λ k → fsnc i c j k n) em)

fsT-ψ-Ω : ∀ i c j m → cof c ≡ cΩ j → cmpᵀ (sucT j) i ≡ m → ∀ d →
  fsT (Ψ i c) d ≡ fsTc i c j m d
fsT-ψ-Ω i [] j m () em d
fsT-ψ-Ω i c@(_ ∷ _) j m e em d =
  trans (cong (λ k → fsT₊ i c k d) e) (cong (λ k → fsTc i c j k d) em)
```
