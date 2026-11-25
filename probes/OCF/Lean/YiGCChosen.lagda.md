# 全部规范孩子的精确对应与 Level 下界
验收文件；编译定理：对每个第 0 层树 d，实填 child d 的 Corr、NoΩ、参照路径与 lower-one。
来源：YiC0Pad.corr-↑ 的 two 偏移形状；第 0 层复制与严格步进分别复用 YiPVZero 与 YiLSRead。
这里的结论是 Level 关系，不是 YiQLRead.Need 或 MinimalGoal。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiGCChosen where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.YiRWBlock renaming (L to LF)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiNRHit using (NoΩ)
open import OCF.Lean.YiFPFrames using (can; run)
open import OCF.Lean.YiGCCorr
open import OCF.Lean.YiGCRel using (Rel)
import OCF.Lean.YiGCFold as G
open import OCF.Lean.YiKCStep using (OKB)
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiPVZero as C
import OCF.Lean.YiLSRead as R
import OCF.Lean.YiPEStep as PS
import OCF.Lean.YiBVSmall as S
import OCF.Lean.YiBVDomain as D
import OCF.Lean.YiTBRow as TB
import OCF.Align.Level as L

L₂ : L.Ordᴵ
L₂ = L.natᴵ 2
shift : Tr zero → LF
shift x = K.two ⊕ ↑ zero x
index : Tr zero → L.Ordᴵ
index x = PS._⊕_ L₂ (L.toLevel (R.read (C.copy x)) (R.HSr (C.copy x)))
noΩ : ∀ x → NoΩ (shift x)
noΩ zero _ _ = tt
noΩ (suc x) _ = noΩ x
noΩ (lim f a) n = noΩ (f n)
corr : ∀ x (h : L.HS (R.read (C.copy x))) → Corr (PS._⊕_ L₂ (L.toLevel (R.read (C.copy x)) h)) (shift x)
corr zero h = cs (cs cz)
corr (suc x) h = cs (corr x (L.hs⁻ h))
corr (lim f a) h = cl (λ n → corr (f n) (L.hl₁ h n))
  (λ n → PS.⊕-≺ L₂ (L.toLevel-≺ (L.hl₁ h n) (L.hl₁ h (suc n)) (R.◃→≺ (C.copyD (a n)))))
child-corr : ∀ d → Corr (index (suc d)) (S.child d)
child-corr d = corr (suc d) (R.HSr (C.copy (suc d)))
child-noΩ : ∀ d → NoΩ (S.child d)
child-noΩ d = noΩ (suc d)
one-below : ∀ x (h : L.HS (R.read (C.copy x))) → L.natᴵ 1 L.<ᴵ PS._⊕_ L₂ (L.toLevel (R.read (C.copy x)) h)
one-below zero h = L.zero
one-below (suc x) h = L.suc (one-below x (L.hs⁻ h))
one-below (lim f a) h = L.lim 0 (one-below (f 0) (L.hl₁ h 0))
p : ∀ d → L.natᴵ 1 L.<ᴵ L.suc (index (suc d))
p d = L.suc (one-below (suc d) (R.HSr (C.copy (suc d))))
Reference : Tr zero → L.Ordᶜ (L.natᴵ 1)
Reference d = L.ψ (p d) (λ q → L.suc q) (L.Ω (index (suc d)))
all-lower : ∀ d (o : Ok (S.child d)) (r : TB.Rb (S.child d)) (B : Base (S.child d)) → OKB B
  → Rel K.one (Reference d) (proj₁ (TB.ψ (S.child d) o r B K.one (S.lower d) (B K.one (S.lower d)) (proj₁ (Ωt (S.child d)))))
all-lower d o r B ok = G.lower-one (child-noΩ d) (o , r , B) ok (child-corr d) (S.lower d) (p d)
minimal-lower : ∀ d → Rel K.one (Reference d) (proj₁ (S.Small.child-out d))
minimal-lower d = all-lower d (proj₂ S.okay d) (proj₂ (D.Input.table S.minimal) d) (S.Small.child-base d) (λ i u → K.⊴r)
```
