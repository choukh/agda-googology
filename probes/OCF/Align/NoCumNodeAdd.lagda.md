# 第 0 层是值: 加法保 `Gd`

> 不含记号. 结论写在 [NoCumNode](NoCumNode.lagda.md). `AddG.Add`: $W$ 对 $\mathcal A$ 好, $\mathcal A$ 对 "地板压过 $W$" 封闭, $W$ 诚实 (`hoA`), $x$ 对 $C\circ(W\oplus)$ 好, 则 $W\oplus x$ 好. 与 `OCF.Free.ClassF` 的 `AddM.Add` 同形, 少了层的下移.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NoCumNodeAdd where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.BTBO using (module Trich)
open Trich renaming (_<_ to _<ᴺ_) using (zero; suc)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; Strict; ⊲-tr; z⊲; ≪S; ≪∘)
import OCF.Align.CumReadCF as C
open import OCF.Align.NoCumLit using (_⊴₀_; Ord₀)
open import OCF.Align.NoCumW
open import OCF.Align.NoCumEq
open import OCF.Align.NoCumLe
open import OCF.Align.NoCumMain using (WF)
open import OCF.Align.NoCumForce using (Fp; fq; fs; fl; Fp-mono; ⊴→Fp)
open import OCF.Align.NoCumNodeE
open import OCF.Align.Om1HnCx using (⊴₀-tr; ≅₀-refl; ≅₀-sym; ≅₀-trans; Fp-z)
open import OCF.Align.NoCumNodeCx
open import OCF.Align.NoCumNodeGd
```

## §1 地板

```agda
module AddG {pw aw u₀} (W₁ : 𝓞 pw aw u₀) (gu : Gw u₀) (E : W₁ ≈ W₁) (𝓐 : Cl) (gW : Gd 𝓐 W₁)
            (clA : ∀ {O C″} → 𝓐 O → FlOver W₁ O C″ → 𝓐 C″)
            (hoA : ∀ {C} → 𝓐 C → ∀ {y : Tm} → Rn C W₁ y → (d : GT y) → Fp u₀ (vT y d) × Fp aw (vT y d)) where

  Fᵃ : Cx → Cx
  Fᵃ C = Fa C W₁ gu E

  W⊴ : ∀ {p₁ b w} (L : Rel p₁ b pw aw) (x : 𝓞 p₁ b w) (gx : Gw w) v (gv : Gw v) (uv : u₀ ⊲ v) (xv : w ⊲ v) (bv : bw L ⊲ v) → W₁ ⊴ add W₁ gu L x gx v gv uv xv bv
  W⊴ L x gx v gv uv xv bv = AddF.add⊴ W₁ gu (rf E) L x gx v gv uv xv bv

  -- 压过 W 的运行都能读回 W
  down : ∀ (C : Cx) {p₁ b w} (L : Rel p₁ b pw aw) (x : 𝓞 p₁ b w) (gx : Gw w) v (gv : Gw v) (uv : u₀ ⊲ v) (xv : w ⊲ v) (bv : bw L ⊲ v) {y : Tm} →
         Rn C (add W₁ gu L x gx v gv uv xv bv) y → (d : GT y) → Σ Tm λ y₀ → Rn C W₁ y₀ × Σ (GT y₀) λ d₀ → vT y₀ d₀ ⊴₀ vT y d
  down C L x gx v gv uv xv bv r d = dn C hom gu (W⊴ L x gx v gv uv xv bv) uv r d

  honW : ∀ {C} → 𝓐 C → ∀ {p₁ b w} (L : Rel p₁ b pw aw) (x : 𝓞 p₁ b w) (gx : Gw w) v (gv : Gw v) (uv : u₀ ⊲ v) (xv : w ⊲ v) (bv : bw L ⊲ v) {y : Tm} →
         Rn C (add W₁ gu L x gx v gv uv xv bv) y → (d : GT y) → Fp u₀ (vT y d) × Fp aw (vT y d)
  honW {C} c L x gx v gv uv xv bv r d with down C L x gx v gv uv xv bv r d
  ... | _ , r₀ , d₀ , s₉ = Fp-mono (proj₁ (hoA c r₀ d₀)) s₉ , Fp-mono (proj₂ (hoA c r₀ d₀)) s₉

  -- 上下文的运行都是 C 上加法的运行, 则 C′ 压过 W
  flOv : ∀ {C C′ D h₀ k} → (∀ {p a u} {z : 𝓞 p a u} {y : Tm} → Rn D z y → Tr (Fᵃ C) y) → Over pw h₀ k C′ D → FlOver W₁ C C′
  flr (flOv {C} wfD o) t r d with wfD (Ov.rz (ovr o t r))
  ... | tr t′ (ra L gx v gv uv xv bv r′) = down C L t′ gx v gv uv xv bv r′ d
  flb (flOv wfD o) i = ovb o i

  lift : ∀ {C p a u} {t : 𝓞 p a u} {y : Tm} → Rn (Fᵃ C) t y → Tr C y
  lift (ra L gx v gv uv xv bv r) = tr _ r

  ovF : ∀ {q₁ q₁′ h₀ k} → (∀ {p′} → p′ <ᴺ q₁ → p′ <ᴺ q₁′) → q₁′ ≡ pw → ∀ {C′ D} → Over q₁′ h₀ k C′ D → Over q₁ h₀ k (Fᵃ C′) D
  ovF lt refl o = over (λ { t (ra L gx v gv uv xv bv r) → ovr o _ r }) (λ i → lt i)

  Rel-lt : ∀ {p₁ b p′} → Rel p₁ b pw aw → p′ <ᴺ p₁ → p′ <ᴺ pw
  Rel-lt (sa P) i₁ = i₁
  Rel-lt (lw i₂) i₁ = <tr i₁ i₂

  bwF : ∀ {p₁ b} (L : Rel p₁ b pw aw) {y : Ord₀} → Fp b y → Fp (bw L) y
  bwF (sa P) {y} f = Fp-z y
  bwF (lw i) f = f

  mxF : ∀ {m u t a} {y : Ord₀} → Mis m u t a → Fp u y → Fp t y → Fp a y → Fp m y
  mxF (iu refl) a b c = a
  mxF (it refl) a b c = b
  mxF (ia refl) a b c = c
```

## §2 主定理

```agda
  Add : ∀ {p₁ b w} (L : Rel p₁ b pw aw) (x : 𝓞 p₁ b w) (gx : Gw w) v (gv : Gw v) (uv : u₀ ⊲ v) (xv : w ⊲ v) (bv : bw L ⊲ v) (𝓐₁ 𝓧₁ : Cl) →
        (∀ {C} → 𝓐₁ C → 𝓐 C) → (∀ {C} → 𝓐₁ C → 𝓧₁ (Fᵃ C)) → Gd 𝓧₁ x → Gd 𝓐₁ (add W₁ gu L x gx v gv uv xv bv)
  Add⁰ : ∀ {p₁ b w} (L : Rel p₁ b pw aw) (x : 𝓞 p₁ b w) (gx : Gw w) m (gm : Gw m) (um : u₀ ⊲ m) (tm : w ⊲ m) (am : bw L ⊲ m) → Mis m u₀ w (bw L) → (𝓐₁ 𝓧₁ : Cl) →
         (∀ {C} → 𝓐₁ C → 𝓐 C) → (∀ {C} → 𝓐₁ C → 𝓧₁ (Fᵃ C)) → Gd 𝓧₁ x → Gd 𝓐₁ (add⁰ W₁ gu L x gx m gm um tm am)
  AddL : ∀ {p₁ h k w} (t : h <ᴺ pw) (j : h <ᴺ p₁) (x : Low p₁ j k w) (gx : Gw w) m (gm : Gw m) (um : u₀ ⊲ m) (tm : w ⊲ m) (km : k ⊲ m) (𝓐₁ 𝓧₁ : Cl) →
         (∀ {C} → 𝓐₁ C → 𝓐 C) → (∀ {C} → 𝓐₁ C → 𝓧₁ (Fᵃ C)) → GdL j 𝓧₁ x → Gd 𝓐₁ (addL W₁ gu t j x gx m gm um tm km)

  Add L x gx v gv uv xv bv 𝓐₁ 𝓧₁ i H g with mx gu gv uv xv bv | mx-is gu gv uv xv bv
  ... | mx′ m gm um tm am mv | is = Add⁰ L x gx m gm um tm am is 𝓐₁ 𝓧₁ i H g

  Add⁰ L o0 gx m gm um tm am is 𝓐₁ 𝓧₁ i H g = Gd-mono i W₁ gW
  Add⁰ L (os x) gx m gm um tm am is 𝓐₁ 𝓧₁ i H (osr 𝓚 inc gK clk hon) =
    osr (λ C → 𝓐 C × 𝓚 (Fᵃ C)) (λ c → i c , inc (H c))
      (Add L x gx m gm um tm am (λ C → 𝓐 C × 𝓚 (Fᵃ C)) 𝓚 proj₁ proj₂ gK)
      (λ {O} {C″} (cO , kO) f →
        clA cO (flo (λ t r d → let y₀ , r₀ , d₀ , s₀ = flr f t r d in
                          let y₁ , r₁ , d₁ , s₁ = down O L x gx m gm um tm am r₀ d₀ in y₁ , r₁ , d₁ , ⊴₀-tr s₁ s₀) (flb f)) ,
        clk kO (flo (λ { t (ra L₂ g₂ v₂ gv₂ uv₂ xv₂ bv₂ r) d → let y₀ , r₀ , d₀ , s₀ = flr f _ r d in y₀ , ra L gx m gm um tm am r₀ , d₀ , s₀ }) (λ i₁ → Rel-lt L i₁)))
      (λ { (cA , kA) r d one₁ →
        let hw = honW cA L x gx m gm um tm am r d
            hx = hon kA (ra L gx m gm um tm am r) d one₁
        in mxF is (proj₁ hw) (proj₁ hx) (bwF L (proj₂ hx)) , proj₂ hw })
  Add⁰ L (ol F) gx m gm um tm am is 𝓐₁ 𝓧₁ i H g = λ n → Add L (F n) gx m gm um tm am 𝓐₁ 𝓧₁ i H (g n)
  Add⁰ (sa P) (oi {k = k} r h) gx m gm um tm am is 𝓐₁ 𝓧₁ i H g =
    brMap g Fᵃ 𝓐 lift (λ c → i c , H c)
      (λ a c o → clA a (flOv (λ r₁ → BrR.wf g c r₁) o))
      (ovF (λ q → q) refl)
      (λ y → inS (≪S r) (outS (≪S (≪∘ r P)) y)) (λ q → ⊲-tr tm q) (λ y → out-inS (≪S r) (outS (≪S (≪∘ r P)) y))
      (λ 𝓓 y z → S→G (≪S (≪∘ r P)) 𝓓 y z) (λ 𝓓 y z → G→S (≪S r) 𝓓 y z)
      (λ 𝓔 {v} q g₁ y e w sub gf → Add (sa P) (h (⊲-tr tm q) g₁ (inS (≪S r) (outS (≪S (≪∘ r P)) y))) g₁ v g₁ (⊲-tr um q) C.self (z⊲ v) 𝓔 (Im Fᵃ 𝓔) (λ c → proj₁ (sub c)) (λ c → im _ c refl) gf)
  Add⁰ (lw i′) (oi {k = k} r h) gx m gm um tm am is 𝓐₁ 𝓧₁ i H g =
    brMap g Fᵃ 𝓐 lift (λ c → i c , H c)
      (λ a c o → clA a (flOv (λ r₁ → BrR.wf g c r₁) o))
      (ovF (λ q → <tr q i′) refl)
      (λ y → inS (≪S r) (outL i′ y)) (λ q → ⊲-tr tm q) (λ y → out-inS (≪S r) (outL i′ y))
      (λ 𝓓 y z → L→G i′ 𝓓 y z) (λ 𝓓 y z → G→S (≪S r) 𝓓 y z)
      (λ 𝓔 {v} q g₁ y e w sub gf → Add (lw i′) (h (⊲-tr tm q) g₁ (inS (≪S r) (outL i′ y))) g₁ v g₁ (⊲-tr um q) C.self (⊲-tr am q) 𝓔 (Im Fᵃ 𝓔) (λ c → proj₁ (sub c)) (λ c → im _ c refl) gf)
  Add⁰ (sa P) (od j k r h) gx m gm um tm am is 𝓐₁ 𝓧₁ i H g =
    brMap g Fᵃ 𝓐 lift (λ c → i c , H c)
      (λ a c o → clA a (flOv (λ r₁ → BrR.wf g c r₁) o))
      (ovF (λ q → q) refl)
      (λ y → inL j (outL j y)) (λ q → ⊲-tr tm q) (λ y → out-inL j (outL j y))
      (λ 𝓓 y z → L→G j 𝓓 y z) (λ 𝓓 y z → G→L j 𝓓 y z)
      (λ 𝓔 {v} q g₁ y e w sub gf → Add (sa P) (h (⊲-tr tm q) g₁ (inL j (outL j y))) g₁ v g₁ (⊲-tr um q) C.self (z⊲ v) 𝓔 (Im Fᵃ 𝓔) (λ c → proj₁ (sub c)) (λ c → im _ c refl) gf)
  Add⁰ (lw i′) (od j k r h) gx m gm um tm am is 𝓐₁ 𝓧₁ i H g =
    brMap g Fᵃ 𝓐 lift (λ c → i c , H c)
      (λ a c o → clA a (flOv (λ r₁ → BrR.wf g c r₁) o))
      (ovF (λ q → <tr q i′) refl)
      (λ y → inL j (outL (<tr j i′) y)) (λ q → ⊲-tr tm q) (λ y → out-inL j (outL (<tr j i′) y))
      (λ 𝓓 y z → L→G (<tr j i′) 𝓓 y z) (λ 𝓓 y z → G→L j 𝓓 y z)
      (λ 𝓔 {v} q g₁ y e w sub gf → Add (lw i′) (h (⊲-tr tm q) g₁ (inL j (outL (<tr j i′) y))) g₁ v g₁ (⊲-tr um q) C.self (⊲-tr am q) 𝓔 (Im Fᵃ 𝓔) (λ c → proj₁ (sub c)) (λ c → im _ c refl) gf)
  Add⁰ L (oc x h) gx m gm um tm am is 𝓐₁ 𝓧₁ i H (ocr 𝓑 g₁ gH gd ch₀ chS) =
    ocr (λ v C → 𝓑 v (Fᵃ C))
      (Add L x gx m gm um tm am 𝓐₁ 𝓧₁ i H g₁)
      (λ {v} q g → Add L (h (⊲-tr tm q) g) g v g (⊲-tr um q) C.self (⊲-tr am q) _ (𝓧₁ ∧ 𝓑 v) (λ (c , b) → i c) (λ (c , b) → H c , b) (gH (⊲-tr tm q) g))
      (λ c r d →
        let hw = honW (i c) L x gx m gm um tm am r d
            hx = gd (H c) (ra L gx m gm um tm am r) d
        in mxF is (proj₁ hw) (proj₁ hx) (bwF L (proj₂ hx)) , proj₂ hw)
      (λ c r d gv₁ t q → ch₀ (H c) (ra L gx m gm um tm am r) d gv₁ t (⊲-tr tm q))
      (λ {C} {v} q g c b r d gv₁ t q′ → chS (⊲-tr tm q) g (H c) b (ra L g v g (⊲-tr um q) C.self (⊲-tr am q) r) d gv₁ t q′)
  Add⁰ (sa P) (oe es x) gx m gm um tm am is 𝓐₁ 𝓧₁ i H g = Add (sa (⊲-tr (C.suc C.self) P)) x gx m gm um tm am 𝓐₁ 𝓧₁ i H g
  Add⁰ (lw i′) (oe es x) gx m gm um tm am is 𝓐₁ 𝓧₁ i H g = Add (lw i′) x gx m gm um tm (⊲-tr (C.suc C.self) am) 𝓐₁ 𝓧₁ i H g
  Add⁰ (sa P) (oe (el n) x) gx m gm um tm am is 𝓐₁ 𝓧₁ i H g = Add (sa (⊲-tr (C.lim n C.self) P)) x gx m gm um tm am 𝓐₁ 𝓧₁ i H g
  Add⁰ (lw i′) (oe (el n) x) gx m gm um tm am is 𝓐₁ 𝓧₁ i H g = Add (lw i′) x gx m gm um tm (⊲-tr (C.lim n C.self) am) 𝓐₁ 𝓧₁ i H g
  Add⁰ (sa P) (oL j k e x) gx m gm um tm am is 𝓐₁ 𝓧₁ i H g = AddL j j x gx m gm um tm (⊲-tr e tm) 𝓐₁ 𝓧₁ i H g
  Add⁰ (lw i′) (oL j k e x) gx m gm um tm am is 𝓐₁ 𝓧₁ i H g = AddL (<tr j i′) j x gx m gm um tm (⊲-tr e tm) 𝓐₁ 𝓧₁ i H g
  Add⁰ L (ow w′ g′ x) gx m gm um tm am is 𝓐₁ 𝓧₁ i H g = Add L x g′ m gm um (⊲-tr w′ tm) am 𝓐₁ 𝓧₁ i H g

  AddL t zero x gx m gm um tm km 𝓐₁ 𝓧₁ i H g = Add (lw t) x gx m gm um tm km 𝓐₁ 𝓧₁ i H g
  AddL t (suc j) x gx m gm um tm km 𝓐₁ 𝓧₁ i H g = AddL t j x gx m gm um tm km 𝓐₁ 𝓧₁ i H g
```
