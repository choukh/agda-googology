# 精确对应的 ω 孩子实例
验收文件；编译定理：S.child ω 的 Corr、NoΩ 与 notBelow 前提全部实填。
对应选择为 suc (lim (n ↦ n+2))；不声称 EboLean 精确标签或 Need。
来源：YiSQOmega.ω 与 YiBVSmall.child；Corr 使用 YiGCCorr。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiGCOmega where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiNRHit using (NoΩ)
open import OCF.Lean.YiGCCorr
import OCF.Align.Level as L
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiCLFam as H
import OCF.Lean.YiBVSmall as S
import OCF.Lean.YiSQOmega as W
ref : ℕ → L.Ordᴵ
ref zero = L.natᴵ 2
ref (suc n) = L.suc (ref n)
ref-step : ∀ n → ref n L.⊑ᴵ ref (suc n)
ref-step n = L.Sim→⊑ᴵ L.suc
ref-strict : ∀ n → ref n L.≺ᴵ ref (suc n)
ref-strict n = L.via (L.≅ᴵ-refl _) L.zero
corr-nat : ∀ n → Corr (ref n) (K.two ⊕ ↑ zero (H.nat n))
corr-nat zero = cs (cs cz)
corr-nat (suc n) = cs (corr-nat n)
ω-index : L.Ordᴵ
ω-index = L.suc (L.lim ref ref-step)
ω-corr : Corr ω-index (S.child W.ω)
ω-corr = cs (cl corr-nat ref-strict)
ω-noΩ : NoΩ (S.child W.ω)
ω-noΩ _ n = fin n
  where
  fin : ∀ n → NoΩ (K.two ⊕ ↑ zero (H.nat n))
  fin zero _ _ = tt
  fin (suc n) _ = fin n
ω-notBelow : ¬ (ω-index L.≺ᴵ L.natᴵ 1)
ω-notBelow = notBelow (S.lower W.ω) ω-noΩ (cs cz) ω-corr
```
