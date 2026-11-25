# 第 1 层的读回关系对分支族参数化

验收文件. 编译定理 (模块 `P1`, 参数是分支族记录 `Pfx`): `fold0ᴳ`, `fold1ᴳ` (目标层 0), `Fold₀ᴳ`, `Fold₁ᴳ` (目标层 1, 关系 `⊴⁺`), 部件 `CtxAᴳ`, `Z⊴ᴳ`. 推广 [YiSyncFold](YiSyncFold.lagda.md) 的 `fold1⁺`, `Fold₁ᴾ` 与 [YiShpEps](YiShpEps.lagda.md) 的 `fold0`: 前缀 `G₂` 换成任一满足 `Pfx` 的分支族, 结点上的定义性展开换成字段 (`nd0`, `nd1` 等).
实例 (前提可满足): `P₂` (即 `G₂`, 原来的情形) 与 `P₃′` ([YiStepTree](YiStepTree.lagda.md) 的 `G₃′`, Ω₃ 结点之下的层号 1 嵌入). 只是下界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiStepPfx where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore hiding (Le)
open import OCF.Lean.YiNextBase
import OCF.Lean.YiLamFold as WL
import OCF.Lean.YiDlFold as W
import OCF.Lean.YiNextAcc as NA
open import OCF.Lean.YiDlVOne using (V2; Ψ₀; up≼)
open import OCF.Lean.YiDlVBtbo using (btbo-Tw2)
open import OCF.Lean.YiShpOne using (σA)
open import OCF.Lean.YiShpSq using (s₂; G₂; Asuc; Atop; ψ₁; sucg)
open import OCF.Lean.YiShpEps using (G₂mono; G₂suc)
open import OCF.Lean.YiShpTwo using (σB)
open import OCF.Align.YiLvVal2 using (T₀; T₁; s≅⁻; l≅⁻; lᵢ≅⁻; tr⁻≼)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≅→≼; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼)
import OCF.Align.Stage2 as S2
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using () renaming (iter to iterᴸ)
open import OCF.Lean.YiSyncRel
open import OCF.Lean.YiSyncDiag using (Diag)
open import OCF.Lean.YiSyncFold using (ψ₀ᴿ-self; ψ₁ᴿ-≅)
open import OCF.Lean.YiStepTree using (K₀; gm₃′; G₃′)
```

## 1 分支族

`G` 把第 1 层的树放进 `tw 2` (前缀 Ω_Ω 之上). 字段: `top` 是一切分支的第一位置 (`b0`), 单调 (`mG`), 后继 (`sG`, 嵌入上的 `sA`, `tA`); 层号 0 的结点与 `top` 在目标层 0 上展开成链 (`nd0`, `nt0`), 在目标层 1 上保留 (`nd1`, `nt1`).

```agda
record Pfx : Set where
  field
    G : NA.R₁ → Raw (tw 2)
    b0 : ∀ η → Cp (tw 2) G.top (G η)
    mG : ∀ {a b} → Cp (suc zero) a b → Cp (tw 2) (G a) (G b)
    sG : ∀ η → Cp (tw 2) (G.suc (G η)) (G (G.suc η))
    sA : ∀ a → Cp (tw 2) (G.suc (G (G.em tt a))) (G (G.em tt (G.suc a)))
    tA : Cp (tw 2) (G.suc (G (G.em tt G.zero))) (G (G.em tt G.top))
    nd0 : ∀ g n → NA.read (Ψ₀ (G (g (chain zero (λ ζ → Ψ₀ (G (g ζ))) n)))) ≼ NA.read (Ψ₀ (G (G.lc (inj₁ tt) g)))
    nt0 : ∀ n → NA.read (Ψ₀ (G (G.em tt (chain zero (λ ζ → Ψ₀ (G (G.em tt ζ))) n)))) ≼ NA.read (Ψ₀ (G G.top))
    nd1 : ∀ g {x} → x ⊴⁺ G.lc (inj₁ tt) (λ ζ → ψ₁ (G (g ζ))) → x ⊴⁺ ψ₁ (G (G.lc (inj₁ tt) g))
    nt1 : ∀ {x} → x ⊴⁺ G.lc (inj₁ tt) (λ ζ → ψ₁ (G (G.em tt ζ))) → x ⊴⁺ ψ₁ (G G.top)
```

## 2 目标层 0

```agda
module P1 (P : Pfx) where
  open Pfx P

  ψ1 : Raw (tw 2) → NA.R₁
  ψ1 = W.Ψ (suc zero) V2 (W.cmpw V2 s₂)

  module NodeG (f : T₀ → T₁) (same : ∀ y → f y L.≅ f y) (g : R → NA.R₁)
    (hm : ∀ (y : T₀) a → y ≼ NA.read a → L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σA (f y)) ≼ NA.read (Ψ₀ (G (g a)))) where
    c : ℕ → T₀
    c = iterᴸ (λ z → L.ψ (L.lim 0 L.zero) (λ r → r) (L.add (L.Ω S2.ℓ₀) σA (f z))) (L.suc L.zero)

    δ : ℕ → R
    δ = chain zero (λ ζ → Ψ₀ (G (g ζ)))

    sync : ∀ n → c n ≼ NA.read (δ n)
    sync zero = ≼-refl _
    sync (suc n) = ≼-trans
      (≅→≼ (L.≅-sym (L.ψ⁰≅ψ {p = L.lim 0 L.zero} {σ = λ r → r}
        (L.add-≅ {σ = σA} {σ′ = σA} (L.Ω-refl S2.ℓ₀) (same (c n))))))
      (NA.plus≽ (δ n) (Ψ₀ (G (g (δ n)))) (hm (c n) (δ n) (sync n)))

    result : L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σA (L.limᵢ {i = L.zero} L.zero f)) ≼ L.lim (λ n → NA.read (Ψ₀ (G (g (δ n)))))
    result = l≼ (λ n → ≼l n (hm (c n) (δ n) (sync n)))

  ctxAᴳ : ∀ {y b : T₀} → y ≼ b → ∀ a → b ≡ NA.read a → L.ψ⁰ (L.add (L.Ω S2.ℓ₀) S2.σ₁ y) ≼ NA.read (Ψ₀ (G (G.em tt a)))
  ctxAᴳ z≼ a q = ≼-trans btbo-Tw2 (up≼ (b0 _))
  ctxAᴳ (s≼s p) (G.suc a) refl = ≼-trans (NA.suc-lower (Ψ₀ (G (G.em tt a))) (ctxAᴳ p a refl)) (up≼ (sA a))
  ctxAᴳ (s≼s p) G.top refl = ≼-trans (NA.suc-lower (Ψ₀ (G (G.em tt G.zero))) (ctxAᴳ p G.zero refl)) (up≼ tA)
  ctxAᴳ (≼l n p) (G.lim f) refl = ≼-trans (ctxAᴳ p (f n) refl) (up≼ (mG (inj₂ (refl , n , inj₁ refl))))
  ctxAᴳ (l≼ h) a q = l≼ (λ n → ctxAᴳ (h n) a q)
  ctxAᴳ (≼i {p = ()} x ex p) a q
  ctxAᴳ (i≼ {p = ()} h) a q
  ctxAᴳ (≼u {r = ()} p) a q
  ctxAᴳ (u≼ {r = ()} p) a q

  fold0ᴳ : ∀ {y : T₀} {η} → y NA.⊴ η → L.ψ⁰ (L.add (L.Ω S2.ℓ₀) S2.σ₁ y) ≼ NA.read (Ψ₀ (G η))
  fold0ᴳ {η = η} NA.z⊴ = ≼-trans btbo-Tw2 (up≼ (b0 η))
  fold0ᴳ {η = G.suc η} (NA.s⊴s p) = ≼-trans (NA.suc-lower (Ψ₀ (G η)) (fold0ᴳ p)) (up≼ (sG η))
  fold0ᴳ {η = G.suc η} (NA.⊴s p) = ≼-trans (fold0ᴳ p) (up≼ (mG {a = η} {b = G.suc η} (inj₂ (inj₁ refl))))
  fold0ᴳ {η = G.lim H} (NA.⊴l n p) = ≼-trans (fold0ᴳ p) (up≼ (mG {a = H n} {b = G.lim H} (inj₂ (n , inj₁ refl))))
  fold0ᴳ (NA.l⊴ h) = l≼ (λ n → fold0ᴳ (h n))
  fold0ᴳ {η = G.lc (inj₁ _) g} (NA.⊴b h) = ≼-trans (fold0ᴳ h) (up≼ (mG {a = g G.top} {b = G.lc (inj₁ tt) g} (inj₂ (inj₁ refl))))
  fold0ᴳ (NA.em⊴ {a = a} q) = ctxAᴳ q a refl

  fold1ᴳ : ∀ {X : T₁} {η} → X ⊴⁺ η → X L.≅ X → L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σA X) ≼ NA.read (Ψ₀ (G η))
  fold1ᴳ {η = η} z⊴ s = ≼-trans btbo-Tw2 (up≼ (b0 η))
  fold1ᴳ {η = G.suc η} (s⊴s p) s = ≼-trans (NA.suc-lower (Ψ₀ (G η)) (fold1ᴳ p (s≅⁻ s))) (up≼ (sG η))
  fold1ᴳ {η = G.suc η} (⊴s p) s = ≼-trans (fold1ᴳ p s) (up≼ (mG {a = η} {b = G.suc η} (inj₂ (inj₁ refl))))
  fold1ᴳ {η = G.lim H} (⊴l n p) s = ≼-trans (fold1ᴳ p s) (up≼ (mG {a = H n} {b = G.lim H} (inj₂ (n , inj₁ refl))))
  fold1ᴳ (l⊴ h) s = l≼ (λ n → fold1ᴳ (h n) (l≅⁻ s n))
  fold1ᴳ {η = G.lc (inj₁ _) g} (⊴b h) s = ≼-trans (fold1ᴳ h s) (up≼ (mG {a = g G.top} {b = G.lc (inj₁ tt) g} (inj₂ (inj₁ refl))))
  fold1ᴳ {η = G.lc (inj₁ _) g} (nd {f = f} h) s =
    ≼-trans (NodeG.result f (lᵢ≅⁻ s) g (λ y a q → fold1ᴳ (h y a q) (lᵢ≅⁻ s y))) (l≼ (λ n → nd0 g n))
  fold1ᴳ (nt {f = f} h) s =
    ≼-trans (NodeG.result f (lᵢ≅⁻ s) (λ a → G.em tt a) (λ y a q → fold1ᴳ (h y a q) (lᵢ≅⁻ s y))) (l≼ (λ n → nt0 n))
  fold1ᴳ (u⊴ p) s = fold0ᴳ p
  fold1ᴳ {η = G.lc (inj₁ _) g} (dg h) s = l≼ (λ n → ≼-trans (fold1ᴳ (h n _
    (add-cp zero G.lc dnLc G.top (W.Ψ-cp zero V2 (λ _ → fold) (b0 (g G.top))))) (l≅⁻ s n)) (nd0 g 1))
  fold1ᴳ (≅⊴ e p) s = ≼-trans (≅→≼ (L.ψ⁰-≅ (L.add-≅ {σ = σA} {σ′ = σA} (L.Ω-refl S2.ℓ₀) e)))
    (fold1ᴳ p (L.≅-trans (L.≅-sym e) e))
```

## 3 目标层 1

```agda
  Z⊴ᴳ : ∀ η → L.ψ (σB L.zero) (λ r → r) (L.Ω S2.ℓ₀) ⊴⁺ ψ1 (G η)
  Z⊴ᴳ η = ⊴⁺-cp Diag (W.Ψ-cp (suc zero) V2 (W.cmpw V2 s₂) (b0 η))

  cpψ : ∀ {a b} → Cp (suc zero) a b → Cp (suc zero) (ψ1 (G a)) (ψ1 (G b))
  cpψ c = W.Ψ-cp (suc zero) V2 (W.cmpw V2 s₂) (mG c)

  CtxAᴳ : ∀ {y b : T₀} → y ≼ b → ∀ a → b ≡ NA.read a →
    L.ψ (σB L.zero) (λ r → r) (L.add (L.Ω S2.ℓ₀) S2.σ₁ y) ⊴⁺ ψ1 (G (G.em tt a))
  CtxAᴳ z≼ a q = Z⊴ᴳ _
  CtxAᴳ {L.suc y} (s≼s p) (G.suc a) refl =
    ⊴⁺-cp (suc-step⁺ (ψ₀ᴿ-self y) (CtxAᴳ p a refl)) (W.Ψ-cp (suc zero) V2 (W.cmpw V2 s₂) (sA a))
  CtxAᴳ {L.suc y} (s≼s p) G.top refl =
    ⊴⁺-cp (suc-step⁺ (ψ₀ᴿ-self y) (CtxAᴳ p G.zero refl)) (W.Ψ-cp (suc zero) V2 (W.cmpw V2 s₂) tA)
  CtxAᴳ (≼l n p) (G.lim f) refl = ⊴⁺-cp (CtxAᴳ p (f n) refl) (cpψ (inj₂ (refl , n , inj₁ refl)))
  CtxAᴳ (l≼ h) a q = l⊴ (λ n → CtxAᴳ (h n) a q)
  CtxAᴳ (≼i {p = ()} x ex p) a q
  CtxAᴳ (i≼ {p = ()} h) a q
  CtxAᴳ (≼u {r = ()} p) a q
  CtxAᴳ (u≼ {r = ()} p) a q

  Fold₀ᴳ : ∀ {y : T₀} {η} → y NA.⊴ η → L.ψ (σB L.zero) (λ r → r) (L.add (L.Ω S2.ℓ₀) S2.σ₁ y) ⊴⁺ ψ1 (G η)
  Fold₀ᴳ NA.z⊴ = Z⊴ᴳ _
  Fold₀ᴳ {L.suc y} {G.suc η} (NA.s⊴s p) =
    ⊴⁺-cp (suc-step⁺ (ψ₀ᴿ-self y) (Fold₀ᴳ p)) (W.Ψ-cp (suc zero) V2 (W.cmpw V2 s₂) (sG η))
  Fold₀ᴳ {η = G.suc η} (NA.⊴s p) = ⊴⁺-cp (Fold₀ᴳ p) (cpψ {a = η} {b = G.suc η} (inj₂ (inj₁ refl)))
  Fold₀ᴳ {η = G.lim H} (NA.⊴l n p) = ⊴⁺-cp (Fold₀ᴳ p) (cpψ {a = H n} {b = G.lim H} (inj₂ (n , inj₁ refl)))
  Fold₀ᴳ (NA.l⊴ h) = l⊴ (λ n → Fold₀ᴳ (h n))
  Fold₀ᴳ {η = G.lc (inj₁ _) g} (NA.⊴b h) = ⊴⁺-cp (Fold₀ᴳ h) (cpψ {a = g G.top} {b = G.lc (inj₁ tt) g} (inj₂ (inj₁ refl)))
  Fold₀ᴳ (NA.em⊴ {a = a} q) = CtxAᴳ q a refl

  Fold₁ᴳ : ∀ {X : T₁} {η} → X ⊴⁺ η → X L.≅ X →
    L.ψ (σB L.zero) (λ r → r) (L.add (L.Ω S2.ℓ₀) σA X) ⊴⁺ ψ1 (G η)
  Fold₁ᴳ z⊴ s = Z⊴ᴳ _
  Fold₁ᴳ {L.suc X} {G.suc η} (s⊴s p) s =
    ⊴⁺-cp (suc-step⁺ (ψ₁ᴿ-≅ (s≅⁻ s)) (Fold₁ᴳ p (s≅⁻ s))) (W.Ψ-cp (suc zero) V2 (W.cmpw V2 s₂) (sG η))
  Fold₁ᴳ {η = G.suc η} (⊴s p) s = ⊴⁺-cp (Fold₁ᴳ p s) (cpψ {a = η} {b = G.suc η} (inj₂ (inj₁ refl)))
  Fold₁ᴳ {η = G.lim H} (⊴l n p) s = ⊴⁺-cp (Fold₁ᴳ p s) (cpψ {a = H n} {b = G.lim H} (inj₂ (n , inj₁ refl)))
  Fold₁ᴳ (l⊴ h) s = l⊴ (λ n → Fold₁ᴳ (h n) (l≅⁻ s n))
  Fold₁ᴳ {η = G.lc (inj₁ _) g} (⊴b h) s = ⊴⁺-cp (Fold₁ᴳ h s) (cpψ {a = g G.top} {b = G.lc (inj₁ tt) g} (inj₂ (inj₁ refl)))
  Fold₁ᴳ {η = G.lc (inj₁ _) g} (nd h) s = nd1 g (nd (λ y a q →
    Fold₁ᴳ (h (L.tr⁻ L.z≅ y) a (≼-trans (tr⁻≼ y) q)) (lᵢ≅⁻ s (L.tr⁻ L.z≅ y))))
  Fold₁ᴳ (nt h) s = nt1 (nd (λ y a q →
    Fold₁ᴳ (h (L.tr⁻ L.z≅ y) a (≼-trans (tr⁻≼ y) q)) (lᵢ≅⁻ s (L.tr⁻ L.z≅ y))))
  Fold₁ᴳ (u⊴ p) s = Fold₀ᴳ p
  Fold₁ᴳ {η = G.lc (inj₁ _) g} (dg h) s = nd1 g (dg (λ n a c → Fold₁ᴳ (h n a c) (l≅⁻ s n)))
  Fold₁ᴳ (≅⊴ e p) s = ≅⊴ (ψ₁ᴿ-≅ e) (Fold₁ᴳ p (L.≅-trans (L.≅-sym e) e))
```

## 4 实例

```agda
P₂ : Pfx
P₂ = record
  { G = G₂ ; b0 = λ η → plus-weak (tw 2) G.top _ ; mG = G₂mono ; sG = G₂suc ; sA = Asuc ; tA = Atop
  ; nd0 = λ g n → ≼l n (≼-refl _) ; nt0 = λ n → ≼l n (≼-refl _) ; nd1 = λ g h → h ; nt1 = λ h → h }

mG₃′ : ∀ {a b} → Cp (suc zero) a b → Cp (tw 2) (G₃′ a) (G₃′ b)
mG₃′ c = add-cp (tw 2) G.lc dnLc G.top (add-cp (tw 2) G.lc dnLc K₀ (W.Ψ-cp (tw 2) (WL.ws WL.w0) _ c))

P₃′ : Pfx
P₃′ = record
  { G = G₃′ ; b0 = λ η → plus-weak (tw 2) G.top _ ; mG = mG₃′
  ; sG = λ η → add-cp (tw 2) G.lc dnLc G.top (add-cp (tw 2) G.lc dnLc K₀ (sucg (WL.ws WL.w0) _ η))
  ; sA = λ a → add-cp (tw 2) G.lc dnLc G.top (add-cp (tw 2) G.lc dnLc K₀ (sucg WL.w0 _ a))
  ; tA = inj₂ (1 , inj₁ refl)
  ; nd0 = λ g n → ≼l n (≼-refl _) ; nt0 = λ n → ≼l n (≼-refl _) ; nd1 = λ g h → h ; nt1 = λ h → h }
```
