# 第 1 层的下界的链点部件 (搬到收缩见证的折叠)

验收文件. [YiL1Chain](YiL1Chain.lagda.md) 逐字搬到 [YiWitFold](YiWitFold.lagda.md): 只换模块名与导入, 链内模块换成 `YiWit` 的搬运件, 塔的 `Lw-tw`, `lgl→Lw`, `Tw`, `T⁺ʷ`, `TΛ` 取 `WF` (YiWitFold), 折叠 `W.Ψ` 仍是 YiDlFold 的 `Fold dl`. 定理与原文同名; 下文的讲解是原文.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiWitL1Chain where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore hiding (Le)
open import OCF.Lean.YiNextBase
import OCF.Lean.YiLamFold as WL
import OCF.Lean.YiDlFold as W
import OCF.Lean.YiWitFold as WF
open import OCF.Lean.YiWitVOne using (V2; Ψ₀; topᶜʷ; Tt)
open import OCF.Lean.YiWitShpOmega using (cpT)
import OCF.Lean.YiWitVBtbo as DB
open import OCF.Lean.YiWitShpSq using (G₂; gm₂)
open import OCF.Lean.YiWitShpEps using (K₁)
open import OCF.Lean.YiWitL1Stmt using (δq)
open import OCF.Lean.YiWitL1Read using (κ₁)
import OCF.Lean.YiLeanFold as MF
import OCF.Lean.YiLeanTw3 as MT
open MT.Pt using (co; lw)
open import OCF.Lean.YiLeanAccFin using () renaming (read to readM)
open import OCF.Lean.YiLeanValFin using (κ; chain-cum; HS-read)
open import OCF.Lean.YiFlatChain using (Z-top)
open import OCF.Lean.YiPEStep using (Fκ; _⊕_; ⊕-≺; ⊑⊕; toLevel-+; HS-≅)
open import OCF.Align.YiBtValBT using (module D)
open import OCF.Align.BTBOFullEmb using (PEmb)
import OCF.Align.Level as L
```

## 1 主线链点的层号在 1 之上

```agda
eκ : ∀ m → (κ m ⊕ Fκ m) L.≅ᴵ κ (suc m)
eκ m = L.≅ᴵ-trans
  (L.≅ᴵ-sym (toLevel-+ (readM (co (MT.pts m))) (readM (MT.obs (MT.pts m)))
    (HS-read (co (MT.pts m)) (lw (MT.pts m)))
    (HS-read (MT.obs (MT.pts m)) (MT.F-lgl (co (MT.pts m)) (lw (MT.pts m)))) hsum))
  (L.toLevel-≅ hsum (HS-read (co (MT.pts (suc m))) (lw (MT.pts (suc m)))) (L.≅-sym (chain-cum m)))
  where
  hsum : L.HS (readM (co (MT.pts m)) L.+ readM (MT.obs (MT.pts m)))
  hsum = HS-≅ (HS-read (co (MT.pts (suc m))) (lw (MT.pts (suc m)))) (chain-cum m)

z≺F : ∀ m → L.zero L.≺ᴵ Fκ m
z≺F m = L.toLevel-≺ L.hz (HS-read (MT.obs (MT.pts m)) (MT.F-lgl (co (MT.pts m)) (lw (MT.pts m))))
  (Z-top (MT.lv (co (MT.pts m)) (lw (MT.pts m))) (λ _ → MF.fold))

≺⊑ : ∀ {c b a} → c L.≺ᴵ b → b L.⊑ᴵ a → c L.≺ᴵ a
≺⊑ (L.via e q) k = L.≺ᴵ-respˡ e (L.sim k q)

one≺κ : ∀ m → L.suc L.zero L.≺ᴵ κ (suc m)
one≺κ zero = L.≺ᴵ-respʳ (⊕-≺ (κ 0) (z≺F 0)) (eκ 0)
one≺κ (suc m) = L.≺ᴵ-respʳ (≺⊑ (one≺κ m) (⊑⊕ (κ (suc m)) (Fκ (suc m)))) (eκ (suc m))
```

## 2 一致折叠一侧的链点在 `δq` 的第 1 点之下

```agda
cpδ : ∀ k → Cp zero (G.suc (plus zero G.top (psum zero DB.obs k))) (δq 1)
cpδ k = add-cp zero G.lc dnLc G.top (cpT zero c₁ c₂)
  where
  c₁ : Cp zero (G.suc (psum zero DB.obs k)) (WF.Tw 2)
  c₁ = inj₂ (suc k , add-cp zero G.lc dnLc (psum zero DB.obs k)
    (topᶜʷ zero (DB.Vw (WL.Pk.co (DB.P (suc k))) (WL.Pk.lw (DB.P (suc k)))) (λ _ → fold) G.top))
  c₂ : Cp zero (WF.Tw 2) (Ψ₀ (G₂ (plus (suc zero) G.top (K₁ G.top))))
  c₂ = W.Ψ-cp zero V2 (λ _ → fold)
    (plus-weak (tw 2) G.top (plus (tw 2) (Tt G.top) (gm₂ (plus (suc zero) G.top (K₁ G.top)))))
```

## 3 目标层号

```agda
tgt : ℕ → L.Ordᴵ
tgt k = κ₁ (WL.nrmk zero (plus zero G.top (psum zero DB.obs k))) (WL.nrmk-lgl zero (plus zero G.top (psum zero DB.obs k)))

sucT : ∀ {a c} → PEmb a c → PEmb a (L.suc c)
PEmb.map (sucT Q) = PEmb.map Q
PEmb.bnd (sucT Q) r = L.≺-suc (PEmb.bnd Q r)
PEmb.mono (sucT Q) = PEmb.mono Q
PEmb.coh (sucT Q) = PEmb.coh Q
```
