# YiFunc 后继：`CRUX` 归约到折叠链的单块

**验收文件，档位：编译定理与条件定理。** `L⁺ (suc c)` 是折叠链各项 `Λ c m` 的极限。链逐项严格 (`ChainStr c`) 时，同一个边界粘接给出 `crux-red : FB Q → ChainStr c → (∀ m → NEXT c′ cs m) → FB (PEmb-suc Q)`：第 0 块用 `FB Q`，第 m+1 块只要一个嵌入 `Λ c (m+1) → Λ c′ (m+1)`，把前一项 `Λ c m` 送到不低于 `Λ c′ m` 处 (`NEXT`)。于是 `func-red₂ : NEXTall → HSt a → (P : PEmb a b) → FB P` (`HSt`：沿极限与后继都严格)。
`ChainStr 0` 与 `HSt (D.L 0)` 是定理 (§5)；不证 `NEXT`，不证 c ≥ 1 的 `ChainStr`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFuncCrux where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
import OCF.Align.Level as L
open L using (Ordᴵ; _≅ᴵ_; _⊑ᴵ_; _≺ᴵ_; via; _[_]ᴵ)
import OCF.Align.Uniform as Un
open import OCF.Align.Value using (_≼_)
open import OCF.Align.BTBOFullEmb using (PEmb)
open PEmb
open import OCF.Align.BTBOFullLe using (⊑≅)
open import OCF.Align.YiMonoEmb using (PEmb-⊑; PEmb-∘; PEmb-suc)
open import OCF.Lean.YiPEStep using (L⁺; PEmb-≅ʳ; PEmb-≅ˡ; KEY; shift-κ)
open import OCF.Lean.YiPEStair using (≺⊑; tri; irr; ge-lt)
open import OCF.Lean.YiFuncBase using (PEmb-res)
open import OCF.Lean.YiFuncLim using (FB; module BG; module Ext; L⁺<; L⁺≅; ≅⊑; fb-zero; fb-suc₁; module LimCase)
open FB
open import OCF.Lean.YiPEKey using (KEYsuc; SpineT; key-from; ψ⁰-≺)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using () renaming (iter to iterᴸ)
open import OCF.Lean.YiPEBase using (EmbTⁿ; btbo-emb⁺)
open import OCF.Align.YiBtValBT using (module D)
open import OCF.Lean.YiLeanValFin using (κ)
import OCF.Lean.YiNextTop as NT
import OCF.Lean.YiNextAcc as NA
```

## 1 折叠链的各项

```agda
stepᴵ : ∀ (x : Ordᴵ) n → x [ n ]ᴵ ⊑ᴵ x [ suc n ]ᴵ
stepᴵ L.zero n = L.⊑ᴵ-refl
stepᴵ (L.suc x) n = L.⊑ᴵ-refl
stepᴵ (L.lim g s) n = s n

belowᴵ : ∀ (x : Ordᴵ) n → x [ n ]ᴵ ⊑ᴵ x
belowᴵ L.zero n = L.⊑ᴵ-refl
belowᴵ (L.suc x) n = L.⊑ᴵ-refl
belowᴵ (L.lim g s) n = L.Sim→⊑ᴵ (L.lim n)

Λ : Ordᴵ → ℕ → Ordᴵ
Λ c m = L⁺ (L.suc c) [ m ]ᴵ

Λ0 : ∀ c → Λ c 0 ≅ᴵ L⁺ c
Λ0 c = L.toLevel-≅ _ (Un.Uniform c) (L.≅-refl⁰ (L.ψ⁰ (L.Ω c)))

ChainStr : Ordᴵ → Set
ChainStr c = ∀ m → Λ c m ≺ᴵ Λ c (suc m)

NEXT : ∀ {c} (c′ : Ordᴵ) → ChainStr c → ℕ → Set
NEXT {c} c′ cs m = Σ (PEmb (Λ c (suc m)) (Λ c′ (suc m))) λ R → Λ c′ m ⊑ᴵ map R (cs m)
```

## 2 一般的边界粘接链

`LimCase` 的骨架，抽出来：各块 `R n : F n → B n`，上限逐块不降，下一块把分界送到不低于上一块的上限。`floor0`：不在 `F 0` 之下的前驱，像不低于 `B 0`；`low0`：`F 0` 之下的前驱，像就是第 0 块的像。

```agda
module GL {F : ℕ → Ordᴵ} (sF : ∀ n → F n ⊑ᴵ F (suc n)) {Bt : Ordᴵ} (B : ℕ → Ordᴵ)
  (w : ∀ n → F n ≺ᴵ F (suc n)) (TT : ∀ n → B n ⊑ᴵ B (suc n)) (Bb : ∀ n → B n ⊑ᴵ Bt)
  (R : ∀ n → PEmb (F n) (B n)) (bw : ∀ n → B n ⊑ᴵ map (R (suc n)) (w n)) where

  Q : ∀ n → PEmb (F n) (B n)
  Q zero = R zero
  Q (suc n) = BG.emb (Q n) (R (suc n)) (w n) (TT n) (bw n)

  Q′ : ∀ n → PEmb (F n) Bt
  Q′ n = PEmb-∘ (Q n) (PEmb-⊑ (Bb n))

  ext′ : ∀ {c} n (r : c ≺ᴵ F n) (r′ : c ≺ᴵ F (suc n)) → map (Q′ (suc n)) r′ ≅ᴵ map (Q′ n) r
  ext′ n r r′ = BG.ext (Q n) (R (suc n)) (w n) (TT n) (bw n) r r′

  emb : PEmb (L.lim F sF) Bt
  emb = Ext.limPE sF Q′ ext′

  B0⊑ : ∀ n → B 0 ⊑ᴵ B n
  B0⊑ zero = L.⊑ᴵ-refl
  B0⊑ (suc n) = L.⊑ᴵ-trans (B0⊑ n) (TT n)

  F0⊑ : ∀ n → F 0 ⊑ᴵ F n
  F0⊑ zero = L.⊑ᴵ-refl
  F0⊑ (suc n) = L.⊑ᴵ-trans (F0⊑ n) (sF n)

  floor0 : ∀ m {d} (r : d ≺ᴵ F (suc m)) → (F 0 ≺ᴵ d) ⊎ (d ≅ᴵ F 0) → B 0 ⊑ᴵ map (Q (suc m)) r
  flH : ∀ m {d} (r : d ≺ᴵ F (suc m)) → (F 0 ≺ᴵ d) ⊎ (d ≅ᴵ F 0) → ∀ y →
    B 0 ⊑ᴵ BG.mp (Q m) (R (suc m)) (w m) (TT m) (bw m) r y
  floor0 m r h = flH m r h (tri r (w m))
  flH zero r h (inj₁ q) = ge-lt h q
  flH (suc m) r h (inj₁ q) = floor0 m q h
  flH m r h (inj₂ u) =
    L.⊑ᴵ-trans (B0⊑ m) (L.⊑ᴵ-trans (bw m) (BG.up⊑ (Q m) (R (suc m)) (w m) (TT m) (bw m) r u))

  low0 : ∀ m {d} (r0 : d ≺ᴵ F 0) (r : d ≺ᴵ F m) → map (Q m) r ≅ᴵ map (R 0) r0
  low0 zero r0 r = coh (R 0) r r0 (L.≅ᴵ-refl _)
  low0 (suc m) r0 r =
    L.≅ᴵ-trans (BG.ext (Q m) (R (suc m)) (w m) (TT m) (bw m) r₁ r) (low0 m r0 r₁)
    where r₁ = ≺⊑ r0 (F0⊑ m)
```

## 3 `CRUX` 的归约

```agda
module CruxRed {c c′ : Ordᴵ} (Q : PEmb c c′) (X : FB Q) (cs : ChainStr c) (nx : ∀ m → NEXT c′ cs m) where
  Rb : ∀ m → PEmb (Λ c m) (Λ c′ m)
  Rb zero = PEmb-≅ˡ (Λ0 c) (PEmb-≅ʳ (R X) (L.≅ᴵ-sym (Λ0 c′)))
  Rb (suc m) = proj₁ (nx m)

  module G = GL {F = Λ c} (stepᴵ (L⁺ (L.suc c))) {Bt = L⁺ (L.suc c′)} (Λ c′) cs (stepᴵ (L⁺ (L.suc c′)))
    (belowᴵ (L⁺ (L.suc c′))) Rb (λ m → proj₂ (nx m))

  fb : FB (PEmb-suc Q)
  R fb = G.emb
  bd fb (via e L.zero) (via e′ (L.lim zero q′)) =
    irr (L.≺ᴵ-respˡ (L.≅ᴵ-trans (Λ0 c) (L.≅ᴵ-sym (L⁺≅ e))) (via e′ q′))
  bd fb (via e L.zero) (via e′ (L.lim (suc m) q′)) =
    ≅⊑ (L.≅ᴵ-sym (Λ0 c′)) (G.floor0 m (via e′ q′) (inj₂ (L.≅ᴵ-trans (L⁺≅ e) (L.≅ᴵ-sym (Λ0 c)))))
  bd fb (via e (L.suc q)) (via e′ (L.lim m q′)) =
    ⊑≅ (bd X (via e q) (L.≺ᴵ-respʳ r0 (Λ0 c))) (L.≅ᴵ-sym (G.low0 m r0 (via e′ q′)))
    where r0 = L.≺ᴵ-respʳ (L⁺< (via e q)) (L.≅ᴵ-sym (Λ0 c))

crux-red : ∀ {c c′} (Q : PEmb c c′) → FB Q → (cs : ChainStr c) → (∀ m → NEXT c′ cs m) → FB (PEmb-suc Q)
crux-red Q X cs nx = CruxRed.fb Q X cs nx
```

## 4 全归约与接线

```agda
data HSt : Ordᴵ → Set where
  hz : HSt L.zero
  hs : ∀ {c} → HSt c → ChainStr c → HSt (L.suc c)
  hl : ∀ {f s} → (∀ n → f n ≺ᴵ f (suc n)) → (∀ n → HSt (f n)) → HSt (L.lim f s)

NEXTall : Set
NEXTall = ∀ {c c′} → PEmb c c′ → (cs : ChainStr c) → ∀ m → NEXT c′ cs m

func-red₂ : NEXTall → ∀ {a} → HSt a → ∀ {b} (P : PEmb a b) → FB P
func-red₂ nx hz P = fb-zero P
func-red₂ nx (hs {c} h cs) P = fb-suc₁ P (crux-red Q (func-red₂ nx h Q) cs (nx Q cs))
  where Q = PEmb-res P (via (L.≅ᴵ-refl c) L.zero)
func-red₂ nx (hl st h) P = LimCase.fb st P (λ n → func-red₂ nx (h n) (PEmb-res P (L.≺-lim (suc n) (st n))))

module FromNX (nx : NEXTall) (hd : ∀ n → HSt (D.L n)) (key : KEY) where
  emb : ∀ n → PEmb (D.L n) (κ n)
  emb zero = PEmb-⊑ L.⊑ᴵ-refl
  emb (suc n) = PEmb-∘ (R (func-red₂ nx (hd n) (emb n))) (PEmb-∘ (key n) (shift-κ n))

btbo-NX⁺ : NEXTall → (∀ n → HSt (D.L n)) → KEYsuc → SpineT → D.BTBOᴵ ≼ NA.read NT.T⁺
btbo-NX⁺ nx hd ks sp = btbo-emb⁺ (λ n → n , FromNX.emb nx hd (key-from ks sp) n)
```

## 5 第 0 层的折叠链严格

`ChainStr 0` 是定理：第 0 层上链的下一项与 ψ⁰ 结构相等 (`L.ψ⁰≅ψ`)，第 0 层的 ψ⁰ 结构严格单调 (`YiPEKey.ψ⁰-≺`)。于是 `HSt (D.L 0)`。

```agda
γ₀ : ℕ → L.Ordᶜ L.zero
γ₀ = iterᴸ (λ x → L.ψ {i = L.zero} {k = L.suc L.zero} {ℓ = L.suc L.zero} L.zero (λ r → r) (L.up L.zero x)) (L.Ω L.zero)

γ-eq : ∀ m → L.ψ⁰ (γ₀ m) L.≅ γ₀ (suc m)
γ-eq m = L.ψ⁰≅ψ (L.≅-refl⁰ (γ₀ m))

γ-step : ∀ m → γ₀ m L.≺ γ₀ (suc m)
γ-step zero = L.≺l 2 (L.≺z (L.≅-refl⁰ (L.suc L.zero)))
γ-step (suc m) = L.≺-respʳ (L.≺-respˡ (γ-eq m) (ψ⁰-≺ (γ-step m))) (γ-eq (suc m))

chainStr₀ : ChainStr L.zero
chainStr₀ m = L.toLevel-≺ _ _ (ψ⁰-≺ (γ-step m))

hst₀ : HSt (D.L 0)
hst₀ = hs hz chainStr₀
```
