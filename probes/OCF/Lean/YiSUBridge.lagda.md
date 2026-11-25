# 两种补充在原归约处的检查
验收文件；编译否定：补整条分支律仍有反例；原 `OK B` 与原 `Bdᵍ` 都不能提供 `PrefixU`。
后一个否定给原前提的明确实例，失败的是指定槽位底的前缀关系，不是否定 `LowKeep` 本身。
`PrefixU` 非空：空前缀用规范底，前缀 1 用逐点 `next⁺` 的底；均有最小层步进。
入口：`no-whole`、`no-OK-prefix`、`no-Bd-prefix`、`linked-step`。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSUBridge where
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁)
open import Data.List using ([]; _++_)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiTBRow using (rb-no)
open import OCF.Lean.YiLKIface using (OK; feed)
open import OCF.Lean.YiKVRel using (⊴◃)
open import OCF.Lean.YiGIInst using (Bdᵍ)
open import OCF.Lean.YiSUBound using (fin-bound; fs; fz; no-ω²)
open import OCF.Lean.YiSUNeg
open import OCF.Lean.YiSUIface
open import OCF.Lean.YiSUMin using (rd-zero; step′-one)
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiMTTab as MT
import OCF.Align.EboLeanDef as E
open import OCF.Align.EboLeanBase using (<-≤; <ᵀ-irrefl)

no-whole : WholeU ℓ → ⊥
no-whole st = no-ω² (st o (rb-no ℓ) (B₀ ℓ) okB t a p ν nu cof-a g whole-branch 0 c low)

no-prefix-one : PrefixU (B₀ ℓ) t → ⊥
no-prefix-one pref = <ᵀ-irrefl (<-≤ (E.hd< (E.ar< E.[]<))
  (fin-bound (pref p [] (GR.c0 refl)) (fs fz)))

no-OK-prefix : ((B : Base ℓ) → OK B → PrefixU B t) → ⊥
no-OK-prefix link = no-prefix-one (link (B₀ ℓ) okB)

bd : Bdᵍ (o , MT.rbᶻ ℓ , B₀ ℓ) (z≤ ℓ) (next⁺ (Ωt zero)) t
bd = small-step , okB

no-Bd-prefix :
  (Bdᵍ (o , MT.rbᶻ ℓ , B₀ ℓ) (z≤ ℓ) (next⁺ (Ωt zero)) t → PrefixU (B₀ ℓ) t) → ⊥
no-Bd-prefix link = no-prefix-one (link bd)

Bnext : Base ℓ
Bnext j u = next⁺ (Ωt j)

ok-next : OK Bnext
ok-next j u = ⊴◃ (◃l 0)

prefix-next : PrefixU Bnext t
prefix-next (inj₂ (tt , inj₁ tt)) κ q with rd-zero q
... | refl = H.G⁰.m-next (Ωt zero) refl (λ n → refl) (H.m1 refl H.mz)
prefix-next (inj₂ (tt , inj₂ ())) κ q

linked-step : GR.Low ℓ p (E.γT (t ++ a) ν 1)
  (feed ℓ o (rb-no ℓ) Bnext p g c)
linked-step = step′-one o (rb-no ℓ) Bnext ok-next t prefix-next a p ν nu cof-a g 0 c low branch
```
