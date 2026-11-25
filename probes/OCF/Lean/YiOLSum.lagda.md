# 旧链拼接技巧在实际累计行上的单侧移植
验收文件；实际链点1的输出支配实际底的ω次累加，不声称Ω₂里程碑。
来源：EmbVV 的 ValLabPos.Chain.vv-chain 逐项取上界技巧；累计和改用当前 limc⁺。
加法读回复用 YiKidGen.read-+ᴿ，双向桥用 YiKQSuff.read≤/YiKCSem.rr≼，结合律用 YiL1Base.+-assoc。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiOLSum where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiKidGen as KG
import OCF.Lean.YiL1Base as A
import OCF.Lean.YiKQSuff as QS
import OCF.Lean.YiAZStart as AZ
import OCF.Lean.YiAZLocal as AL
import OCF.Lean.YiKCSem as CS
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≼-refl; ≅→≼; ≼l; l≼) renaming (+-mono to +ᵛ-mono)

rd-plus : ∀ x y → K.readRW (x O.+ y) ≼ (K.readRW x L.+ K.readRW y)
rd-plus x y = ≼-trans (QS.read≤ (x O.+ y))
  (≼-trans (≅→≼ (KG.read-+ᴿ x y)) (+ᵛ-mono (CS.rr≼ x) (CS.rr≼ y)))
rd-plus-back : ∀ x y → (K.readRW x L.+ K.readRW y) ≼ K.readRW (x O.+ y)
rd-plus-back x y = ≼-trans (+ᵛ-mono (QS.read≤ x) (QS.read≤ y))
  (≼-trans (≅→≼ (L.≅-sym (KG.read-+ᴿ x y))) (CS.rr≼ (x O.+ y)))

module Uniform (b : O.Tr⁺ B.zero) (F : ℕ → O.Tr⁺ B.zero)
  (low : ∀ n → K.readRW (proj₁ b) ≼ K.readRW (proj₁ (F n))) where
  v = K.readRW (proj₁ b)
  I : ℕ → L.Ordᶜ L.zero
  I = O.iter (v L.+_) v
  rotation : ∀ n → I (suc n) ≼ I n L.+ v
  rotation zero = ≼-refl _
  rotation (suc n) = ≼-trans (+ᵛ-mono (≼-refl v) (rotation n))
    (≅→≼ (L.≅-sym (A.+-assoc v (I n) v)))
  iter-read : ∀ n → K.readRW (O.iter (proj₁ b O.+_) (proj₁ b) n) ≼ I n
  iter-read zero = ≼-refl v
  iter-read (suc n) = ≼-trans (rd-plus (proj₁ b) (O.iter (proj₁ b O.+_) (proj₁ b) n))
    (+ᵛ-mono (≼-refl v) (iter-read n))
  partial : ∀ n → I n ≼ K.readRW (O.cum (λ i → proj₁ (F i)) n)
  partial zero = low zero
  partial (suc n) = ≼-trans (rotation n)
    (≼-trans (+ᵛ-mono (partial n) (low (suc n)))
      (rd-plus-back (O.cum (λ i → proj₁ (F i)) n) (proj₁ (F (suc n)))))
  bound : K.readRW (proj₁ (O.next⁺ b)) ≼ K.readRW (proj₁ (O.limc⁺ F))
  bound = l≼ (λ n → ≼l n (≼-trans (iter-read n) (partial n)))
module U = Uniform AZ.D.β AZ.G (λ n → AL.out-base (AZ.N.Inner.chain n))
next-output : K.readRW (proj₁ (O.next⁺ AZ.D.β)) ≼ K.readRW (proj₁ AZ.D.output)
next-output = subst (λ x → K.readRW (proj₁ (O.next⁺ AZ.D.β)) ≼ K.readRW (proj₁ x)) (sym AZ.whole-row) U.bound
```
