# 产出端折叠: 读法 ψ₀(Ω_{Ω+1}) 的闭项不高于 `Twᵖ 3` 与 `TΛᵖ` (无前提)

验收文件. 编译定理 `T⁺ʷᵖ≼Tw3 : NA.read P.T⁺ʷᵖ ≼ NA.read (P.Twᵖ 3)`, `T⁺ʷᵖ≼TΛᵖ`, 无前提, 只是下界. [YiIntoTw3](YiIntoTw3.lagda.md) 搬到 [YiProdFold](YiProdFold.lagda.md): 从 `Twᵖ 3` 沿观察项下降同一条 `path₃`, 到达的就是 `T⁺ʷᵖ` (`at-T⁺ʷᵖ`, `refl`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiWayInto where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (nothing)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using (R; psum)
open import OCF.Lean.YiLamFold using (Lw; w0; ws; wl; wΩ; Pk; Lw-tw)
open import OCF.Lean.YiZipWay using (Way′; keep′; fold′; ΩT′)
open import OCF.Lean.YiZipFold using (rootZ)
open import OCF.Lean.YiCtxAnn using (noM; noP)
open import OCF.Lean.YiProdFold using (Xm; Ψᵖ; ptsΩ; noS; fx; Twᵖ; TΛᵖ; T⁺ʷᵖ)
import OCF.Lean.YiNextAcc as NA
open import OCF.Lean.YiDlVBtbo using (psum≽)
open import OCF.Lean.YiWayBtbo using (Twᵖ≼TΛᵖ)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≼l)
open Pk
```

## 1 观察项的一步下降

```agda
record St : Set₁ where
  constructor st
  field
    ly  : LF
    lw′ : Lw ly
    sb  : Pre ly → Set
    dx  : Xm zero ly sb
open St

Ψ₀ : St → R
Ψ₀ s = Ψᵖ zero (lw′ s) (sb s) (dx s) G.top noM noP

child : ∀ {k} → Lw k → (Sb : Pre k → Set) → Xm zero k Sb → ℕ → St
child (wΩ {k} {g} V w) Sb x n =
  st (g (co (ptsΩ k g V n))) (V (co (ptsΩ k g V n)) (lw (ptsΩ k g V n)))
     (λ r → Sb (co (ptsΩ k g V n) , lw (ptsΩ k g V n) , r)) (λ r → x (co (ptsΩ k g V n) , lw (ptsΩ k g V n) , r))
child (wl {f} V s) Sb x n = st (f n) (V n) (λ r → Sb (n , r)) (λ r → x (n , r))
child {k} V Sb x n = st k V Sb x

ΩT₀ : ∀ {j} (u : Way′ zero j) K (o : ℕ → R) n {ℓ} {X : L.Ordᶜ ℓ} →
  X ≼ NA.read (o n) → X ≼ NA.read (ΩT′ zero j u K o)
ΩT₀ (keep′ () t) K o n q
ΩT₀ fold′ K o n q = ≼l n q

child≼ : ∀ {k} (V : Lw k) Sb x n {ℓ} {X : L.Ordᶜ ℓ} →
  X ≼ NA.read (Ψ₀ (child V Sb x n)) → X ≼ NA.read (Ψ₀ (st k V Sb x))
child≼ (wΩ {k} {g} V w) Sb x n q = ΩT₀ (rootZ zero k g w (λ r → x r nothing)) _ _ n (≼-trans q (psum≽ (λ i →
  Ψᵖ zero (V (co (ptsΩ k g V i)) (lw (ptsΩ k g V i))) (λ r → Sb (co (ptsΩ k g V i) , lw (ptsΩ k g V i) , r))
    (λ r → x (co (ptsΩ k g V i) , lw (ptsΩ k g V i) , r)) G.top noM noP) n))
child≼ (wl V s) Sb x n q = ≼l n (≼-trans q (psum≽ (λ i → Ψᵖ zero (V i) (λ r → Sb (i , r)) (λ r → x (i , r)) G.top noM noP) n))
child≼ w0 Sb x n q = q
child≼ (ws V) Sb x n q = q

desc : List ℕ → St → St
desc [] s = s
desc (n ∷ ns) s = desc ns (child (lw′ s) (sb s) (dx s) n)

desc≼ : ∀ ns s {ℓ} {X : L.Ordᶜ ℓ} → X ≼ NA.read (Ψ₀ (desc ns s)) → X ≼ NA.read (Ψ₀ s)
desc≼ [] s q = q
desc≼ (n ∷ ns) s q = child≼ (lw′ s) (sb s) (dx s) n (desc≼ ns (child (lw′ s) (sb s) (dx s) n) q)
```

## 2 位置与定理

```agda
path₃ : List ℕ
path₃ = 1 ∷ 0 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []

s₃ : St
s₃ = st (tw 3) (Lw-tw 3) noS (fx zero (tw 3))

ly-T⁺ʷᵖ : ly (desc path₃ s₃) ≡ suc (tw 2)
ly-T⁺ʷᵖ = refl

at-T⁺ʷᵖ : Ψ₀ (desc path₃ s₃) ≡ T⁺ʷᵖ
at-T⁺ʷᵖ = refl

T⁺ʷᵖ≼Tw3 : NA.read T⁺ʷᵖ ≼ NA.read (Twᵖ 3)
T⁺ʷᵖ≼Tw3 = desc≼ path₃ s₃ (≼-refl (NA.read T⁺ʷᵖ))

T⁺ʷᵖ≼TΛᵖ : NA.read T⁺ʷᵖ ≼ NA.read TΛᵖ
T⁺ʷᵖ≼TΛᵖ = ≼-trans T⁺ʷᵖ≼Tw3 (Twᵖ≼TΛᵖ 3)
```
