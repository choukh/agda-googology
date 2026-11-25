# 第 1 层的 BTBO 下界 (无前提) (搬到收缩见证的折叠)

验收文件. [YiL1Base](YiL1Base.lagda.md) 逐字搬到 [YiWitFold](YiWitFold.lagda.md): 只换模块名与导入, 链内模块换成 `YiWit` 的搬运件, 塔的 `Lw-tw`, `lgl→Lw`, `Tw`, `T⁺ʷ`, `TΛ` 取 `WF` (YiWitFold), 折叠 `W.Ψ` 仍是 YiDlFold 的 `Fold dl`. 定理与原文同名; 下文的讲解是原文.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiWitL1Base where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (tt)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore hiding (Le)
open import OCF.Lean.YiNextBase
import OCF.Lean.YiLamFold as WL
import OCF.Lean.YiDlFold as W
import OCF.Lean.YiWitFold as WF
import OCF.Lean.YiNextAcc as NA
open NA using (_⊴_; ⊴l)
open import OCF.Lean.YiWitShpEps using (Tψ; K₁)
open import OCF.Lean.YiWitShpSq using (node≼T)
open import OCF.Lean.YiWitShpOne using (σA)
open import OCF.Lean.YiWitShpTwo using (σB)
import OCF.Align.Stage2 as S2
open import OCF.Align.Value using (_≼_; ≼l; l≼)
open import OCF.Lean.YiWitL1Stmt using (F₁; δq; Base₁; point→base)
open import OCF.Lean.YiWitL1Read using (κ₁)
open import OCF.Lean.YiWitL1Emb using (module Fix01; lower₁ᴱ; base₁-0; one≺; ⊴-cp; ℓ₀≅)
open import OCF.Lean.YiWitL1Chain using (one≺κ; ≺⊑; cpδ; tgt; sucT)
open import OCF.Lean.YiL1NrmEmb using (ℓv; nrmkE; fix1; ZF; ZF-psum; ZF-fold)
import OCF.Lean.YiWitVBtbo as DB
import OCF.Lean.YiLeanTw3 as MT
open MT.Pt using () renaming (co to coM; lw to lwM)
import OCF.Lean.YiLeanValFin as MV
open import OCF.Lean.YiLeanValFin using (κ)
open import OCF.Lean.YiNextValFin using (HS-readⁿ; toM; toM-R; toM-lgl)
open import OCF.Lean.YiNextValRel using (read≅)
open import OCF.Lean.YiPEStep using (⊑⊕; PEmb-≅ʳ)
import OCF.Lean.YiBtboLower as YB
open import OCF.Align.YiBtValBT using (module D)
open import OCF.Align.BTBOFullEmb using (PEmb; module PE)
open import OCF.Align.YiMonoEmb using (PEmb-⊑; PEmb-∘)
import OCF.Align.BTBOFullLe as BL
import OCF.Align.Level as L
```

## 1 一致折叠的链点: 结合律与不含零

```agda
ξ : ℕ → R
ξ m = plus zero G.top (psum zero DB.obs m)

lobs : ∀ n → Lgl zero (DB.obs n)
lobs n = W.Ψ-lgl zero (DB.Vw (WL.Pk.co (DB.P n)) (WL.Pk.lw (DB.P n))) (λ _ → fold) G.top tt

lξ : ∀ m → Lgl zero (ξ m)
lξ m = plus-lgl zero G.top (psum zero DB.obs m) tt (proj₂ (psum-lgl zero DB.obs lobs) m)

zfo : ∀ m → ZF (psum zero DB.obs m)
zfo m = ZF-psum DB.obs (λ n → ZF-fold (DB.Vw (WL.Pk.co (DB.P n)) (WL.Pk.lw (DB.P n))) (λ _ → fold) G.top) m

+-assoc : ∀ (a b c : L.Ordᶜ L.zero) → ((a L.+ b) L.+ c) L.≅ (a L.+ (b L.+ c))
+-assoc a b L.zero = L.≅-refl⁰ (a L.+ b)
+-assoc a b (L.suc c) = L.s≅ (+-assoc a b c)
+-assoc a b (L.lim f) = L.l≅ (λ n → +-assoc a b (f n))
+-assoc a b (L.limᵢ () f)
+-assoc a b (L.up () x)

assoc-read : ∀ m → NA.read (WL.Pk.co (DB.P (suc m))) L.≅ NA.read (ξ m)
assoc-read zero = L.≅-refl⁰ _
assoc-read (suc m) = L.≅-trans (NA.read-plus (WL.Pk.co (DB.P (suc m))) (DB.obs (suc m)))
  (L.≅-trans (L.add-≅ {σ = λ q → q} {σ′ = λ q → q} (assoc-read m) (L.≅-refl⁰ (NA.read (DB.obs (suc m)))))
  (L.≅-trans (L.add-≅ {σ = λ q → q} {σ′ = λ q → q} (NA.read-plus G.top (psum zero DB.obs m)) (L.≅-refl⁰ (NA.read (DB.obs (suc m)))))
  (L.≅-trans (+-assoc (L.suc L.zero) (NA.read (psum zero DB.obs m)) (NA.read (DB.obs (suc m))))
  (L.≅-trans (L.add-≅ {σ = λ q → q} {σ′ = λ q → q} (L.≅-refl⁰ (L.suc L.zero))
      (L.≅-sym (NA.read-plus (psum zero DB.obs m) (DB.obs (suc m)))))
    (L.≅-sym (NA.read-plus G.top (psum zero DB.obs (suc m))))))))
```

## 2 主线链点的层号嵌进 `nrmk (ξ m)` 的层号, 1 不动

```agda
Q : ∀ m → PEmb (κ (suc m)) (tgt m)
Q m = PEmb-∘ Q₁ (PEmb-∘ Q₂ (PEmb-∘ (nrmkE (ξ m) (lξ m)) Q₄))
  where
  hN = HS-readⁿ (WL.Pk.co (DB.P (suc m))) (WL.Pk.lw (DB.P (suc m)))
  Q₁ : PEmb (κ (suc m)) (ℓv (WL.Pk.co (DB.P (suc m))) (WL.Pk.lw (DB.P (suc m))))
  Q₁ = PEmb-≅ʳ (PEmb-⊑ L.⊑ᴵ-refl)
    (L.toLevel-≅ (MV.HS-read (coM (MT.pts (suc m))) (lwM (MT.pts (suc m)))) hN (read≅ (proj₁ (DB.ptRʷ (suc m)))))
  Q₂ : PEmb (ℓv (WL.Pk.co (DB.P (suc m))) (WL.Pk.lw (DB.P (suc m)))) (ℓv (ξ m) (lξ m))
  Q₂ = PEmb-≅ʳ (PEmb-⊑ L.⊑ᴵ-refl) (L.toLevel-≅ hN (HS-readⁿ (ξ m) (lξ m)) (assoc-read m))
  Q₄ : PEmb (ℓv (WL.nrmk zero (ξ m)) (WL.nrmk-lgl zero (ξ m))) (tgt m)
  Q₄ = PEmb-≅ʳ (PEmb-⊑ L.⊑ᴵ-refl)
    (L.toLevel-≅ (HS-readⁿ (WL.nrmk zero (ξ m)) (WL.nrmk-lgl zero (ξ m)))
      (MV.HS-read (toM (WL.nrmk zero (ξ m))) (toM-lgl (WL.nrmk zero (ξ m)) (WL.nrmk-lgl zero (ξ m))))
      (L.≅-sym (read≅ (toM-R (WL.nrmk zero (ξ m))))))

fixQ : ∀ m (r : L.suc L.zero L.≺ᴵ κ (suc m)) → PEmb.map (Q m) r L.≅ᴵ L.suc L.zero
fixQ m r = fix1 (psum zero DB.obs m) (lξ m) (zfo m) _
```

## 3 第 1 层的 BTBO 下界

```agda
chain₁ : ∀ n → F₁ (suc n) ⊴ K₁ (δq 1)
chain₁ n = ⊴-cp (⊴l 1 (lower₁ᴱ (WL.nrmk zero (G.suc (ξ m))) (WL.nrmk-lgl zero (G.suc (ξ m))) P₂ r₁ e11
    (ℓ₀≅ (suc n)) _ (λ q → L.lim (suc n) q) (WL.Kfk zero Tψ (ξ m))))
  (WL.Kfk-cp zero Tψ (cpδ m))
  where
  m₀ = proj₁ (YB.chainV n)
  m = proj₁ (YB.chainV (suc n))
  E₀ = YB.emb (suc n) m (proj₂ (YB.chainV (suc n)))
  hE : ∀ {c} (r : c L.≺ᴵ D.L (suc n)) → L.suc L.zero L.≺ᴵ PEmb.map E₀ r
  hE r = ≺⊑ (one≺κ (suc m₀)) (⊑⊕ (κ m) _)
  P₁ = Fix01.P′ E₀ hE
  P₂ = PEmb-∘ P₁ (sucT (Q m))
  r₁ = one≺ (D.L n) (D.cert (suc n))
  e11 : PEmb.map P₂ r₁ L.≅ᴵ L.suc L.zero
  e11 = fixQ m (PEmb.bnd P₁ r₁)

base₁ : Base₁
base₁ zero ζ = base₁-0 ζ
base₁ (suc n) ζ = point→base (suc n) (1 , chain₁ n) ζ
```

## 4 推论: ψ₀(Ω_Ω+ψ₁(Ω_Ω))

参照 `Xψ₁ = ψ⁰ (Ω_{ℓ₀} ⊕ ψ₁ᴸ(Ω_{ℓ₀}))`, 读作 ψ₀(Ω_Ω+ψ₁(Ω_Ω)) (读法是判断, 没有逐项一致证明).

```agda
Xψ₁ : L.Ordᶜ L.zero
Xψ₁ = L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σA (L.ψ (σB L.zero) (λ r → r) (L.Ω S2.ℓ₀)))

Xψ₁≼ʷ : Xψ₁ ≼ NA.read WF.T⁺ʷ
Xψ₁≼ʷ = node≼T (≼l 0 (l≼ (λ n → base₁ n G.top)))
```
