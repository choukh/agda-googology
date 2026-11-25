# 裸折叠的 `T⁺ʷᵇ` 严格高过 BTBO, 不低于 ψ₀(Ω_Ω+1) 与 ψ₀(Ω_Ω+Ω₁) (无前提)

验收文件. 编译定理 `aboveʷ`, `ΩΩ+1ʷ`, `χ₁≼ʷ : S2.χ 1 ≼ NA.read W.T⁺ʷᵇ`, `aboveΛ`, 只是下界. [YiDlVOne](YiDlVOne.lagda.md) 搬到 [YiBareFold](YiBareFold.lagda.md): §0 到 §2 逐字, 只有 `c₁` 多一层 `0 ,`.
§3 改写: 根 `p₀` 不再保留, 根链第 1 点是 ℕ-极限, 第 0 项 `plus top (Tt top)` 就是 Ω₁ 结点 `G.lc p₀ gK`, 分支 `gK ξ = top + gm₀ ξ` (原文是 `top + Kfk Tt ξ`). `ctx` 的证明形状不变.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBareVOne where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase
import OCF.Lean.YiLamFold as WL
import OCF.Lean.YiBareFold as W
import OCF.Lean.YiNextAcc as NA
open import OCF.Lean.YiNextValFin using (cp⊑ⁿ)
open import OCF.Lean.YiAboveCtx using (ΩT-top)
open import OCF.Lean.YiBareVBtbo using (Vw; btbo-Tw2; psum≽; Tw2≼Tw3)
import OCF.Align.Level as L
import OCF.Align.Value as V
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≅→≼; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼; ⊑→≼)
open import OCF.Align.YiBtValBT using (module D)
import OCF.Align.Stage2 as S2

V2 : WL.Lw (tw 2)
V2 = W.Lw-twᵇ 2

Ψ₀ : Raw (tw 2) → R
Ψ₀ = W.Ψ zero V2 (λ _ → fold)

Φ₂ : Raw (tw 2) → Raw (tw 2)
Φ₂ = W.Ψ (tw 2) V2 (self (tw 2))

p₀ : Pre (tw 2)
p₀ = G.top , tt , inj₁ tt

T⁺-form : W.T⁺ʷᵇ ≡ G.lim (λ n → Ψ₀ (chain (tw 2) Φ₂ n))
T⁺-form = refl

term₀ : Ψ₀ G.top ≡ W.Twᵇ 2
term₀ = refl
```

## 1 `top` 是新折叠一切值的第一位置

```agda
topᶜʷ : ∀ m {k} (V : WL.Lw k) x ξ → Cp m G.top (W.Ψ m V x ξ)
topᶜʷ m V x G.zero = inj₁ refl
topᶜʷ m V x (G.suc a) = inj₂ (0 , topᶜʷ m V x a)
topᶜʷ m V x (G.lim f) = inj₂ (0 , topᶜʷ m V x (f 0))
topᶜʷ m {k} V x (G.lc r g) = inj₂ (ΨN-dn m k r (x r) (λ η → W.Ψ m V x (g η)) (λ η → W.Ψ (lev k r) V (W.cmpw V r) (g η))
  (topᶜʷ m V x (g (Lay.tp (Lo k r)))))
topᶜʷ m WL.w0 x (G.em () a)
topᶜʷ m (WL.ws V) x (G.em _ a) = topᶜʷ m V (λ r → x (inj₂ r)) a
topᶜʷ m (WL.wl V st) x (G.em n a) = topᶜʷ m (V n) (λ r → x (n , r)) a
topᶜʷ m (WL.wΩ V w) x (G.em (η , l) a) = topᶜʷ m (V η l) (λ r → x (η , l , r)) a
topᶜʷ m WL.w0 x G.top = inj₂ (0 , inj₁ refl)
topᶜʷ m {suc k} (WL.ws V) x G.top = inj₂ (Ψn-dn m k (x (inj₁ tt)) (λ η → W.Ψ m V (λ r → x (inj₂ r)) η) (λ η → W.Ψ k V (self k) η)
  (topᶜʷ m V (λ r → x (inj₂ r)) G.top))
topᶜʷ m (WL.wl V st) x G.top = inj₂ (0 , topᶜʷ m (V 0) (λ r → x (0 , r)) G.top)
topᶜʷ m (WL.wΩ {k} {g} V w) x G.top = ΩT-top m k (WL.rootW m k g w x)
  (WL.Kfk k (λ η → W.Ψ m (V (WL.nrmk k η) (WL.nrmk-lgl k η)) (λ r → x (WL.nrmk k η , WL.nrmk-lgl k η , r)) G.top))
  (psum m (λ n → W.Ψ m (V (WL.Pk.co (W.ptsΩ k g V n)) (WL.Pk.lw (W.ptsΩ k g V n)))
    (λ r → x (WL.Pk.co (W.ptsΩ k g V n) , WL.Pk.lw (W.ptsΩ k g V n) , r)) G.top))
  (topᶜʷ m (V G.top tt) (λ r → x (G.top , tt , r)) G.top) (topᶜʷ m (V G.top tt) (λ r → x (G.top , tt , r)) G.top)

cp≼ : ∀ {a b} → Cp zero a b → NA.read a ≼ NA.read b
cp≼ {a} {b} c = ⊑→≼ (NA.read a) (cp⊑ⁿ a b c)

up≼ : ∀ {A B} → Cp (tw 2) A B → NA.read (Ψ₀ A) ≼ NA.read (Ψ₀ B)
up≼ c = cp≼ (W.Ψ-cp zero V2 (λ _ → fold) c)
```

## 2 ψ₀(Ω_Ω+1)

```agda
c₁ : Cp (tw 2) (G.suc G.top) (chain (tw 2) Φ₂ 1)
c₁ = inj₂ (0 , inj₂ (inj₂ (0 , inj₁ refl)))

s≼ : NA.read (succ zero (W.Twᵇ 2)) ≼ NA.read W.T⁺ʷᵇ
s≼ = ≼l 1 (up≼ c₁)

one : L.suc (L.𝟎 {L.zero}) ≼ NA.read (W.Twᵇ 2)
one = ≼l 0 (≼l 0 (≼l 0 (s≼s z≼)))

aboveʷ : L.suc D.BTBOᴵ ≼ NA.read W.T⁺ʷᵇ
aboveʷ = ≼-trans (s≼s btbo-Tw2) (≼-trans (≼l 1 (≼-trans (V.+-mono (≼-refl (NA.read (W.Twᵇ 2))) one)
  (≅→≼ (L.≅-sym (NA.read-plus (W.Twᵇ 2) (W.Twᵇ 2)))))) s≼)

ΩΩ+1ʷ : L.ψ⁰ (L.suc (L.Ω S2.ℓ₀)) ≼ NA.read W.T⁺ʷᵇ
ΩΩ+1ʷ = ≼-trans (NA.suc-lower {x = L.Ω S2.ℓ₀} (W.Twᵇ 2) btbo-Tw2) s≼

-- TΛ 的部分和第 3 项 = (Tw 0 + Tw 1 + Tw 2) + Tw 3
aboveΛ : L.suc D.BTBOᴵ ≼ NA.read W.TΛᵇ
aboveΛ = ≼l 3 (≼-trans (V.+-mono (≼-trans btbo-Tw2 (psum≽ W.Twᵇ 2)) (≼-trans one Tw2≼Tw3))
  (≅→≼ (L.≅-sym (NA.read-plus (psum zero W.Twᵇ 2) (W.Twᵇ 3)))))
```

## 3 ψ₀(Ω_Ω+Ω₁): 根链第 1 点第 0 项的结点与上下文引理

```agda
Tt : R → Raw (tw 2)
Tt η = W.Ψ (tw 2) (Vw (WL.nrmk zero η) (WL.nrmk-lgl zero η)) (λ r → keep (WL.nrmk zero η , WL.nrmk-lgl zero η , r) refl) G.top

gm₀ : R → Raw (tw 2)
gm₀ ζ = W.Ψ (tw 2) WL.w0 (λ r → keep (G.top , tt , inj₂ r) refl) ζ

Tt-top : Tt G.top ≡ G.lc p₀ gm₀
Tt-top = refl

gK : R → Raw (tw 2)
gK ξ = plus (tw 2) G.top (gm₀ ξ)

-- 根链第 1 点是部分和的 ℕ-极限; 第 0 项是 top + Tt top.
F₁ : ℕ → Raw (tw 2)
F₁ n = plus (tw 2) G.top (psum (tw 2) (λ i → W.Ψ (tw 2) (Vw (WL.Pk.co (W.ptsΩ zero (up zero) Vw i)) (WL.Pk.lw (W.ptsΩ zero (up zero) Vw i)))
  (λ r → keep (WL.Pk.co (W.ptsΩ zero (up zero) Vw i) , WL.Pk.lw (W.ptsΩ zero (up zero) Vw i) , r) refl) G.top) n)

term₁ : chain (tw 2) Φ₂ 1 ≡ G.lim F₁
term₁ = refl

term₁₀ : F₁ 0 ≡ G.lc p₀ gK
term₁₀ = refl

sucK : ∀ a → Cp (tw 2) (G.suc (gK a)) (gK (G.suc a))
sucK a = inj₂ (1 , add-cp (tw 2) G.lc dnLc G.top (add-cp (tw 2) G.lc dnLc (gm₀ a)
  (topᶜʷ (tw 2) WL.w0 (λ r → keep (G.top , tt , inj₂ r) refl) a)))

topStep : NA.read (Ψ₀ (G.suc (gK G.zero))) ≼ NA.read (Ψ₀ (gK G.top))
topStep = ≼l 1 (≼-refl _)

ctx : ∀ {y b : L.Ordᶜ L.zero} → y ≼ b → ∀ ξ → b ≡ NA.read ξ →
  L.ψ⁰ (L.add (L.Ω S2.ℓ₀) S2.σ₁ y) ≼ NA.read (Ψ₀ (gK ξ))
ctx z≼ ξ q = ≼-trans btbo-Tw2 (up≼ (plus-weak (tw 2) G.top (gm₀ ξ)))
ctx (s≼s p) (G.suc a) refl = ≼-trans (NA.suc-lower (Ψ₀ (gK a)) (ctx p a refl)) (up≼ (sucK a))
ctx (s≼s p) G.top refl = ≼-trans (NA.suc-lower (Ψ₀ (gK G.zero)) (ctx p G.zero refl)) topStep
ctx (≼l n p) (G.lim f) refl = ≼l n (ctx p (f n) refl)
ctx (l≼ h) ξ q = l≼ (λ n → ctx (h n) ξ q)
ctx (≼i {p = ()} x ex p) ξ q
ctx (i≼ {p = ()} h) ξ q
ctx (≼u {r = ()} p) ξ q
ctx (u≼ {r = ()} p) ξ q

gk₁ : R → R
gk₁ ζ = W.Ψ zero V2 (W.cmpw V2 p₀) (gK ζ)

d : ℕ → R
d = chain zero gk₁

ch≼ : ∀ m → S2.ch m ≼ NA.read (d m)
ch≼ zero = ≼-refl _
ch≼ (suc m) = ≼-trans
  (≅→≼ (L.≅-sym (L.ψ⁰≅ψ {p = L.lim 0 L.zero} {σ = λ r → r}
    (L.add-≅ {σ = S2.σ₁} {σ′ = S2.σ₁} (L.Ω-refl S2.ℓ₀) (L.≅-refl⁰ (S2.ch m))))))
  (NA.plus≽ (d m) (gk₁ (d m)) (ctx (ch≼ m) (d m) refl))

χ₁≼ʷ : S2.χ 1 ≼ NA.read W.T⁺ʷᵇ
χ₁≼ʷ = ≼l 1 (≼l 0 (l≼ (λ m → ≼l m (ctx (ch≼ m) (d m) refl))))
```
