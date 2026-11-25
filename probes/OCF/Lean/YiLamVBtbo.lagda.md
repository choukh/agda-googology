# BTBO 是 YiLamFold 的闭项 `TΛ` 的下界 (无前提)

验收文件. 编译定理 `btbo-Tw2 : D.BTBOᴵ ≼ NA.read (W.Tw 2)`, `btbo-Tw3`, `btbo-TΛ : D.BTBOᴵ ≼ NA.read W.TΛ`, 都无前提, 只用下界. 办法: `W.Tw 2` 的链点与观察和主线 `T₃` 的逐项结构互模拟 (`ptRʷ`, `obs≅`, 经 [YiLamVRel](YiLamVRel.lagda.md)), 新折叠的观察多取部分和 (`psum≽`), 再接 [YiBtboLower](YiBtboLower.lagda.md) 的 `btbo`.
`W.Tw 2` 是 `W.Tw 3` 链上的第 0 项 (`Tw2≼Tw3`), `W.TΛ` 是 `W.Tw` 的部分和的极限 (`TΛ-form`). 不涉及上界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLamVBtbo where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
import OCF.Lean.YiLeanCore as M
import OCF.Lean.YiLeanFold as MF
import OCF.Lean.YiLeanTw3 as MT
import OCF.Lean.YiLeanAccFin as MA
import OCF.Lean.YiNextCore as N
import OCF.Lean.YiNextBase as NB
import OCF.Lean.YiNextTower as T
import OCF.Lean.YiNextAcc as NA
import OCF.Lean.YiLamFold as W
open import OCF.Lean.YiNextValRel
open import OCF.Lean.YiNextValPath
open import OCF.Lean.YiNextValLgl
open import OCF.Lean.YiLamVRel
import OCF.Lean.YiBtboLower as YB
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≼l; l≼; ≅→≼)
open import OCF.Align.YiBtValBT using (module D)
```

## 1 第 0 层的树作层号

`lgl→Lw` 在第 0 层的合法树上的极限处用 `cps ∘ cp→CP` 搬运位置, 与主线 `sh` 走同一条路径.

```agda
shRʷ : ∀ {a a′ b b′} → RR M.zero N.zero b b′ → (p : M.Cp M.zero a b) (p′ : N.Cp N.zero a′ b′) →
  pCᴹ M.zero p ≡ pCᴺ N.zero p′ → ∀ q q′ → PR (MT.⌜ a ⌝) (NB.⌜ a′ ⌝) q q′ →
  PR (MT.⌜ b ⌝) (NB.⌜ b′ ⌝) (proj₁ (MT.sh b p q)) (proj₁ (W.cps (T.cp→CP N.zero p′) q′))
shRʷ d (inj₁ refl) (inj₁ refl) eq q q′ e = e
shRʷ d (inj₁ refl) (inj₂ p′) ()
shRʷ d (inj₂ p) (inj₁ refl) ()
shRʷ (rs d) (inj₂ p) (inj₂ p′) eq q q′ e = shRʷ d p p′ (cong (λ z → tl (tl z)) eq) q q′ e
shRʷ (rl d) (inj₂ (n , p)) (inj₂ (n′ , p′)) eq q q′ e with cong (λ z → ix (tl z)) eq
... | refl = refl , shRʷ (d n) p p′ (cong (λ z → tl (tl z)) eq) q q′ e
shRʷ (rc {r = ()} _ _) (inj₂ p) (inj₂ p′) eq q q′ e

Vw : (η : NB.R) → N.Lgl N.zero η → W.Lw NB.⌜ η ⌝
Vw η l = W.lgl→Lw N.zero tt W.w0 η l

lvRʷ : ∀ {a a′} → RR M.zero N.zero a a′ → ∀ l l′ → LglR M.zero N.zero a a′ l l′ → VRʷ (MT.lv a l) (Vw a′ l′)
lvRʷ rz l l′ lr = w0R
lvRʷ (rs d) l l′ lr = wsR (lvRʷ d l l′ lr)
lvRʷ (rl d) l l′ lr = wlR (λ n → lvRʷ (d n) (proj₂ l n) (proj₂ l′ n) (proj₂ lr n))
  (λ n q q′ e → shRʷ (d (suc n)) (proj₁ l n) (proj₁ l′ n) (proj₁ lr n) q q′ e)
lvRʷ (rc {r = ()} q h) l l′ lr
lvRʷ rt l l′ lr = wsR w0R
```

## 2 `W.Tw 2` 的链点与观察

链点下一步的派发是 `dfin zero _`, 观察的派发是外部的折叠; 两者在目标层 0 上都是折叠, 所以对任意与主线的折叠相关的派发陈述.

```agda
FRʷ : ∀ {a a′} → RR M.zero N.zero a a′ → ∀ l l′ → LglR M.zero N.zero a a′ l l′ → ∀ {x′} →
  XR M.zero N.zero MT.⌜ a ⌝ NB.⌜ a′ ⌝ (λ _ → MF.fold) x′ →
  RR M.zero N.zero (MT.F a l) (W.Ψ N.zero (Vw a′ l′) x′ N.G.top)
FRʷ d l l′ lr xr = ΨRʷ lz (lvRʷ d l l′ lr) xr rt

FLRʷ : ∀ {a a′} (d : RR M.zero N.zero a a′) l l′ (lr : LglR M.zero N.zero a a′ l l′) → ∀ {x′}
  (xr : XR M.zero N.zero MT.⌜ a ⌝ NB.⌜ a′ ⌝ (λ _ → MF.fold) x′) →
  LglR M.zero N.zero (MT.F a l) (W.Ψ N.zero (Vw a′ l′) x′ N.G.top) (MT.F-lgl a l) (W.Ψ-lgl N.zero (Vw a′ l′) x′ N.G.top tt)
FLRʷ d l l′ lr xr = ΨLglRʷ lz (lvRʷ d l l′ lr) xr rt tt

P : ℕ → W.Pk N.zero
P = W.ptsΩ N.zero NB.⌜_⌝ Vw

ptRʷ : ∀ n → Σ (RR M.zero N.zero (MT.Pt.co (MT.pts n)) (W.Pk.co (P n)))
  λ _ → LglR M.zero N.zero (MT.Pt.co (MT.pts n)) (W.Pk.co (P n)) (MT.Pt.lw (MT.pts n)) (W.Pk.lw (P n))
ptRʷ zero = rt , tt
ptRʷ (suc n) = plusR lz d (FRʷ d _ _ lr (λ _ _ _ → tt)) , plusLglR lz d (FRʷ d _ _ lr (λ _ _ _ → tt)) lr (FLRʷ d _ _ lr (λ _ _ _ → tt))
  where
  d = proj₁ (ptRʷ n)
  lr = proj₂ (ptRʷ n)

obs : ℕ → NB.R
obs n = W.Ψ N.zero (Vw (W.Pk.co (P n)) (W.Pk.lw (P n))) (λ _ → NB.fold) N.G.top

obs≅ : ∀ n → MA.read (MT.obs (MT.pts n)) L.≅ NA.read (obs n)
obs≅ n = read≅ (FRʷ (proj₁ (ptRʷ n)) _ _ (proj₂ (ptRʷ n)) (λ _ _ _ → tt))
```

## 3 下界

```agda
psum≽ : ∀ h n → NA.read (h n) ≼ NA.read (NB.psum N.zero h n)
psum≽ h zero = ≼-refl _
psum≽ h (suc n) = NA.plus≽ (NB.psum N.zero h n) (h (suc n)) (≼-refl _)

Tw2-form : W.Tw 2 ≡ N.G.lim (NB.psum N.zero obs)
Tw2-form = refl

T₃≼Tw2 : MA.read MT.T₃ ≼ NA.read (W.Tw 2)
T₃≼Tw2 = l≼ (λ n → ≼l n (≼-trans (≅→≼ (obs≅ n)) (psum≽ obs n)))

btbo-Tw2 : D.BTBOᴵ ≼ NA.read (W.Tw 2)
btbo-Tw2 = ≼-trans YB.btbo T₃≼Tw2

Tw2≼Tw3 : NA.read (W.Tw 2) ≼ NA.read (W.Tw 3)
Tw2≼Tw3 = ≼l 0 (≼-refl _)

btbo-Tw3 : D.BTBOᴵ ≼ NA.read (W.Tw 3)
btbo-Tw3 = ≼-trans btbo-Tw2 Tw2≼Tw3

Tw≼TΛ : ∀ n → NA.read (W.Tw n) ≼ NA.read W.TΛ
Tw≼TΛ n = ≼l n (psum≽ W.Tw n)

btbo-TΛ : D.BTBOᴵ ≼ NA.read W.TΛ
btbo-TΛ = ≼-trans btbo-Tw2 (Tw≼TΛ 2)
```
