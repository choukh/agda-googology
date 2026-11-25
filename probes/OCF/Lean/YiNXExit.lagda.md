# 相邻层非标准形见证项接回出口
> 验收文件（读记号），编译定理：`exitW` 在见证项 `W k` 上不要求标准形；`exitNX` 把它接入既有 `M̂` 的叶子。
> `ExNX` 仍是叶子条件：参照项是标准形，见证项或为可数标准形，或为 `W k`。不声称完整 `low0` 满足此条件。
> 极限行直接复用 `YiKSRead.fs-sup`；标准形叶子沿用 `YiMHRel.exit̂` 的证明，非标准形叶子用 `YiNXNote.monoW`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNXExit where

open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Align.EboLeanDef using (T; HC)
open import OCF.Align.EboLeanBase using (NF; Ctbl; _≤ᵀ_)
open import OCF.Align.EboLeanTree using (hc)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans)
open import OCF.Lean.YiRefTw2 using (Rt; hω-inv)
open import OCF.Lean.YiCFMono using (mono≤ⁿ)
open import OCF.Lean.YiKSRead using (fs-sup)
open import OCF.Lean.YiMHRel using (M̂; ĉ; l̂; All; Ex)
open import OCF.Lean.YiNXNote using (W; hW; monoW)

exitW : ∀ {X : Set} {R : T → X → Set} (v : X → L.Ordᶜ L.zero)
      → (∀ {t x} → R t x → (h : HC t) → Rt h ≼ v x)
      → ∀ k {s x} → NF s → s ≤ᵀ W k → R (W k) x → (h : HC s) → Rt h ≼ v x
exitW v low k ns le m h = ≼-trans (monoW k ns le h (hW k)) (low m (hW k))

LeafNX : T → T → Set
LeafNX s t = (NF s × NF t × Ctbl t) ⊎ Σ ℕ (λ k → NF s × t ≡ W k)

ExNX : ∀ {X : Set} {R : T → X → Set} {s x} → M̂ R s x → Set
ExNX = All LeafNX

oldNX : ∀ {X : Set} {R : T → X → Set} {s x} (m : M̂ R s x) → Ex m → ExNX m
oldNX (ĉ _ _) ex = inj₁ ex
oldNX (l̂ _ f) ex n = oldNX (f n) (ex n)

exitNX : ∀ {X : Set} {R : T → X → Set} (v : X → L.Ordᶜ L.zero)
       → (∀ {t x} → R t x → (h : HC t) → Rt h ≼ v x)
       → ∀ {s x} (m : M̂ R s x) → ExNX m → (h : HC s) → Rt h ≼ v x
exitNX v low (ĉ le m) (inj₁ (ns , nt , ct)) h =
  ≼-trans (mono≤ⁿ ns nt ct h (hc nt ct) le) (low m (hc nt ct))
exitNX v low (ĉ le m) (inj₂ (k , ns , refl)) h = exitW v low k ns le m h
exitNX v low (l̂ e f) ex h = fs-sup h e (λ n → exitNX v low (f n) (ex n) (hω-inv h e n))
```
