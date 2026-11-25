# YiFunc 极限：严格极限的源上，`FUNC` 归约到后继情形

**验收文件，档位：编译定理与条件定理。** `FB P`：`L⁺ a` 到 `L⁺ b` 的嵌入，外加边界性质 "前驱 `L⁺ x` 的像不低于 `L⁺ (P x)`" (`bd`)。`func-red : CRUX → Str a → (P : PEmb a b) → FB P`：源的极限逐项严格 (`Str`) 时，极限情形由边界粘接 (`BG`) 给出，不要求各块嵌入一致；剩下的只有后继情形 `CRUX` (带边界的 ψ⁰∘Ω 对 `PEmb-suc`)。
不证 `CRUX`；它的实例与链上的接线见 [YiFuncChain](YiFuncChain.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFuncLim where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
import OCF.Align.Level as L
open L using (Ordᴵ; _<ᴵ_; _≅ᴵ_; _⊑ᴵ_; _≺ᴵ_; via)
import OCF.Align.Uniform as Un
open import OCF.Align.BTBOFullEmb using (PEmb)
open PEmb
open import OCF.Align.BTBOFullLe using (⊑≅)
open import OCF.Align.YiMonoEmb using (PEmb-⊑; PEmb-∘; PEmb-limˡ; PEmb-suc)
open import OCF.Align.YiVmConExact using (⊑ᵇ)
open import OCF.Lean.YiPEStep using (L⁺; func-⊑; PEmb-≅ˡ)
open import OCF.Lean.YiPEStair using (≺⊑; tri; irr; ge-lt; _⊞_; cmpℕ)
open import OCF.Lean.YiPEKey using (ψ⁰Ω-≺)
open import OCF.Lean.YiFuncBase using (PEmb-res)
```

## 1 `L⁺` 的单调与反射

```agda
L⁺< : ∀ {a b} → a ≺ᴵ b → L⁺ a ≺ᴵ L⁺ b
L⁺< {a} {b} r = L.toLevel-≺ (Un.Uniform a) (Un.Uniform b) (ψ⁰Ω-≺ r)

L⁺≅ : ∀ {a b} → a ≅ᴵ b → L⁺ a ≅ᴵ L⁺ b
L⁺≅ {a} {b} e = L.toLevel-≅ (Un.Uniform a) (Un.Uniform b) (L.ψ⁰-≅ (L.Ω-≅ e))

≅⊑ : ∀ {a b c} → a ≅ᴵ b → b ⊑ᴵ c → a ⊑ᴵ c
≅⊑ e k = L.⊑ᴵ-trans (⊑≅ L.⊑ᴵ-refl e) k

L⁺-refl : ∀ {x y z} → x ≺ᴵ z → y ≺ᴵ z → L⁺ x ≺ᴵ L⁺ y → x ≺ᴵ y
L⁺-refl rx ry l with tri rx ry
... | inj₁ xy = xy
... | inj₂ (inj₁ yx) = irr (L.≺ᴵ-trans l (L⁺< yx))
... | inj₂ (inj₂ e) = irr (L.≺ᴵ-respˡ (L.≅ᴵ-sym (L⁺≅ e)) l)
```

## 2 带边界的嵌入

```agda
record FB {a b : Ordᴵ} (P : PEmb a b) : Set where
  field
    R  : PEmb (L⁺ a) (L⁺ b)
    bd : ∀ {x} (r : x ≺ᴵ a) (r′ : L⁺ x ≺ᴵ L⁺ a) → L⁺ (map P r) ⊑ᴵ map R r′
open FB

CRUX : Set
CRUX = ∀ {c c′} (Q : PEmb c c′) → FB (PEmb-suc Q)
```

## 3 边界粘接

`a` 的前驱用 `Q` (像在 `T` 之下)，其余用 `R`；`R` 把分界 `a` 映到不低于 `T` 处 (`bw`)，于是跨块的单调由 `T` 传递，不必比较两个嵌入。对照 `YiPEStair.Gl`：那里目标逐块累加，这里只要边界。

```agda
module BG {a a′ T T′ : Ordᴵ} (Q : PEmb a T) (R : PEmb a′ T′) (w : a ≺ᴵ a′)
  (TT : T ⊑ᴵ T′) (bw : T ⊑ᴵ map R w) where
  Side : Ordᴵ → Set
  Side c = (c ≺ᴵ a) ⊎ ((a ≺ᴵ c) ⊎ (c ≅ᴵ a))

  mp : ∀ {c} → c ≺ᴵ a′ → Side c → Ordᴵ
  mp r (inj₁ q) = map Q q
  mp r (inj₂ _) = map R r

  bndH : ∀ {c} (r : c ≺ᴵ a′) x → mp r x ≺ᴵ T′
  bndH r (inj₁ q) = ≺⊑ (bnd Q q) TT
  bndH r (inj₂ _) = bnd R r

  up⊑ : ∀ {d} (s : d ≺ᴵ a′) → (a ≺ᴵ d) ⊎ (d ≅ᴵ a) → map R w ⊑ᴵ map R s
  up⊑ s (inj₁ ad) = ⊑ᵇ (inj₁ (mono R w s ad))
  up⊑ s (inj₂ da) = ⊑ᵇ (inj₂ (coh R w s (L.≅ᴵ-sym da)))

  monoH : ∀ {c d} (r : c ≺ᴵ a′) (s : d ≺ᴵ a′) → c ≺ᴵ d → ∀ x y → mp r x ≺ᴵ mp s y
  monoH r s lt (inj₁ q) (inj₁ q′) = mono Q q q′ lt
  monoH r s lt (inj₁ q) (inj₂ u) = ≺⊑ (≺⊑ (bnd Q q) bw) (up⊑ s u)
  monoH r s lt (inj₂ u) (inj₁ q′) = ge-lt u (L.≺ᴵ-trans lt q′)
  monoH r s lt (inj₂ _) (inj₂ _) = mono R r s lt

  cohH : ∀ {c d} (r : c ≺ᴵ a′) (s : d ≺ᴵ a′) → c ≅ᴵ d → ∀ x y → mp r x ≅ᴵ mp s y
  cohH r s e (inj₁ q) (inj₁ q′) = coh Q q q′ e
  cohH r s e (inj₁ q) (inj₂ u) = ge-lt u (L.≺ᴵ-respˡ (L.≅ᴵ-sym e) q)
  cohH r s e (inj₂ u) (inj₁ q′) = ge-lt u (L.≺ᴵ-respˡ e q′)
  cohH r s e (inj₂ _) (inj₂ _) = coh R r s e

  emb : PEmb a′ T′
  map emb r = mp r (tri r w)
  bnd emb r = bndH r (tri r w)
  mono emb r s lt = monoH r s lt (tri r w) (tri s w)
  coh emb r s e = cohH r s e (tri r w) (tri s w)

  extH : ∀ {c} (r′ : c ≺ᴵ a′) x (r : c ≺ᴵ a) → mp r′ x ≅ᴵ map Q r
  extH r′ (inj₁ q) r = coh Q q r (L.≅ᴵ-refl _)
  extH r′ (inj₂ u) r = ge-lt u r

  ext : ∀ {c} (r : c ≺ᴵ a) (r′ : c ≺ᴵ a′) → map emb r′ ≅ᴵ map Q r
  ext r r′ = extH r′ (tri r′ w) r
```

## 4 逐块延拓的族给出极限的嵌入

与 `YiPEStair.Stair` 的 `far`/`cohQ` 同一个论证，只用 "后一块在前一块的前驱上延拓它"。

```agda
module Ext {B : Ordᴵ} {g : ℕ → Ordᴵ} (sg : ∀ n → g n ⊑ᴵ g (suc n)) (Q : ∀ n → PEmb (g n) B)
  (ext : ∀ {c} n (r : c ≺ᴵ g n) (r′ : c ≺ᴵ g (suc n)) → map (Q (suc n)) r′ ≅ᴵ map (Q n) r) where

  ups : ∀ {c} n k → c ≺ᴵ g n → c ≺ᴵ g (n ⊞ k)
  ups n zero r = r
  ups n (suc k) r = ≺⊑ (ups n k r) (sg (n ⊞ k))

  far : ∀ {c} n k (r : c ≺ᴵ g n) (u : c ≺ᴵ g (n ⊞ k)) → map (Q (n ⊞ k)) u ≅ᴵ map (Q n) r
  far n zero r u = coh (Q n) u r (L.≅ᴵ-refl _)
  far n (suc k) r u = L.≅ᴵ-trans (ext (n ⊞ k) (ups n k r) u) (far n k r (ups n k r))

  tr≡ : ∀ {c n m} (e : n ≡ m) (u : c ≺ᴵ g n) → map (Q n) u ≅ᴵ map (Q m) (subst (λ i → c ≺ᴵ g i) e u)
  tr≡ {n = n} refl u = coh (Q n) u u (L.≅ᴵ-refl _)

  cohQ : ∀ n m {c} (r : c ≺ᴵ g n) (u : c ≺ᴵ g m) → map (Q n) r ≅ᴵ map (Q m) u
  cohQ n m {c} r u with cmpℕ n m
  ... | inj₁ (k , e) = L.≅ᴵ-sym (L.≅ᴵ-trans (tr≡ e u) (far n k r (subst (λ i → c ≺ᴵ g i) e u)))
  ... | inj₂ (k , e) = L.≅ᴵ-trans (tr≡ e r) (far m k u (subst (λ i → c ≺ᴵ g i) e r))

  limPE : PEmb (L.lim g sg) B
  limPE = PEmb-limˡ {s = sg} Q cohQ
```

## 5 三种情形

`Str a`：沿极限的分支走下去，每个极限的相邻两项严格上升；遇到后继就停 (后继交给 `CRUX`)。

```agda
data Str : Ordᴵ → Set where
  sz : Str L.zero
  ss : ∀ {c} → Str (L.suc c)
  sl : ∀ {f s} → (∀ n → f n ≺ᴵ f (suc n)) → (∀ n → Str (f n)) → Str (L.lim f s)

fb-zero : ∀ {b} (P : PEmb L.zero b) → FB P
R (fb-zero P) = func-⊑ L.z⊑
bd (fb-zero P) (via e ()) r′

fb-suc₁ : ∀ {c b} (P : PEmb (L.suc c) b) → FB (PEmb-suc (PEmb-res P (via (L.≅ᴵ-refl c) L.zero))) → FB P
fb-suc₁ {c} {b} P X = record { R = PEmb-∘ (R X) (func-⊑ (L.s⊑′ (bnd P r₀))) ; bd = bd′ }
  where
  r₀ : c ≺ᴵ L.suc c
  r₀ = via (L.≅ᴵ-refl c) L.zero
  bd′ : ∀ {x} (r : x ≺ᴵ L.suc c) (r′ : L⁺ x ≺ᴵ L⁺ (L.suc c)) → L⁺ (map P r) ⊑ᴵ map (R X) r′
  bd′ (via e L.zero) r′ = ≅⊑ (L⁺≅ (coh P (via e L.zero) r₀ e)) (bd X (via e L.zero) r′)
  bd′ (via e (L.suc q)) r′ =
    ≅⊑ (L⁺≅ (coh P (via e (L.suc q)) (L.≺ᴵ-trans (via e q) r₀) (L.≅ᴵ-refl _))) (bd X (via e (L.suc q)) r′)

fb-suc : CRUX → ∀ {c b} (P : PEmb (L.suc c) b) → FB P
fb-suc cr P = fb-suc₁ P (cr _)
```

极限情形：第 n 块是 `P` 限制到 `f n` 之下的 `FB`，目标是 `L⁺ (P (f n))`；分界 `L⁺ (f n)` 由下一块的边界性质送到不低于 `L⁺ (P (f n))` 处。

```agda
module LimCase {f : ℕ → Ordᴵ} {s : ∀ n → f n ⊑ᴵ f (suc n)} {b : Ordᴵ}
  (st : ∀ n → f n ≺ᴵ f (suc n)) (P : PEmb (L.lim f s) b)
  (IH : ∀ n → FB (PEmb-res P (L.≺-lim (suc n) (st n)))) where

  pn : ∀ n → f n ≺ᴵ L.lim f s
  pn n = L.≺-lim (suc n) (st n)

  B : ℕ → Ordᴵ
  B n = L⁺ (map P (pn n))

  w : ∀ n → L⁺ (f n) ≺ᴵ L⁺ (f (suc n))
  w n = L⁺< (st n)

  TT : ∀ n → B n ⊑ᴵ B (suc n)
  TT n = ⊑ᵇ (inj₁ (L⁺< (mono P (pn n) (pn (suc n)) (st n))))

  bw : ∀ n → B n ⊑ᴵ map (R (IH (suc n))) (w n)
  bw n = ≅⊑ (L⁺≅ (coh P (pn n) (L.≺ᴵ-trans (st n) (pn (suc n))) (L.≅ᴵ-refl _))) (bd (IH (suc n)) (st n) (w n))

  Q : ∀ n → PEmb (L⁺ (f n)) (B n)
  Q zero = R (IH zero)
  Q (suc n) = BG.emb (Q n) (R (IH (suc n))) (w n) (TT n) (bw n)

  Inv : ℕ → Set
  Inv n = ∀ {x} (r : x ≺ᴵ f n) (r′ : L⁺ x ≺ᴵ L⁺ (f n)) → L⁺ (map P (L.≺ᴵ-trans r (pn n))) ⊑ᴵ map (Q n) r′

  inv : ∀ n → Inv n
  invH : ∀ n {x} (r : x ≺ᴵ f (suc n)) (r′ : L⁺ x ≺ᴵ L⁺ (f (suc n))) y →
    L⁺ (map P (L.≺ᴵ-trans r (pn (suc n)))) ⊑ᴵ BG.mp (Q n) (R (IH (suc n))) (w n) (TT n) (bw n) r′ y
  inv zero r r′ = bd (IH zero) r r′
  inv (suc n) r r′ = invH n r r′ (tri r′ (w n))
  invH n r r′ (inj₁ q) =
    ≅⊑ (L⁺≅ (coh P (L.≺ᴵ-trans r (pn (suc n))) (L.≺ᴵ-trans r₀ (pn n)) (L.≅ᴵ-refl _))) (inv n r₀ q)
    where r₀ = L⁺-refl r (st n) q
  invH n r r′ (inj₂ _) = bd (IH (suc n)) r r′

  F : ℕ → Ordᴵ
  F n = L.toLevel (L.ψ⁰ (L.Ω (f n))) (L.hl₁ (Un.Uniform (L.lim f s)) n)

  eF : ∀ n → F n ≅ᴵ L⁺ (f n)
  eF n = L.toLevel-≅ _ (Un.Uniform (f n)) (L.≅-refl⁰ (L.ψ⁰ (L.Ω (f n))))

  Bb : ∀ n → B n ⊑ᴵ L⁺ b
  Bb n = ⊑ᵇ (inj₁ (L⁺< (bnd P (pn n))))

  Q′ : ∀ n → PEmb (F n) (L⁺ b)
  Q′ n = PEmb-∘ (PEmb-≅ˡ (eF n) (Q n)) (PEmb-⊑ (Bb n))

  ext′ : ∀ {c} n (r : c ≺ᴵ F n) (r′ : c ≺ᴵ F (suc n)) → map (Q′ (suc n)) r′ ≅ᴵ map (Q′ n) r
  ext′ n r r′ = BG.ext (Q n) (R (IH (suc n))) (w n) (TT n) (bw n)
    (L.≺ᴵ-respʳ r (eF n)) (L.≺ᴵ-respʳ r′ (eF (suc n)))

  fb : FB P
  R fb = Ext.limPE _ Q′ ext′
  bd fb r (via e′ (L.lim m q′)) =
    ≅⊑ (L⁺≅ (coh P r (L.≺ᴵ-trans r₁ (pn m)) (L.≅ᴵ-refl _))) (inv m r₁ r′′)
    where
    r′′ = L.≺ᴵ-respʳ (via e′ q′) (eF m)
    r₁ = L⁺-refl r (pn m) r′′
```

## 6 归约

```agda
func-red : CRUX → ∀ {a} → Str a → ∀ {b} (P : PEmb a b) → FB P
func-red cr sz P = fb-zero P
func-red cr ss P = fb-suc cr P
func-red cr (sl st h) P = LimCase.fb st P (λ n → func-red cr (h n) (PEmb-res P (L.≺-lim (suc n) (st n))))

func-str : CRUX → ∀ {a b} → Str a → PEmb a b → PEmb (L⁺ a) (L⁺ b)
func-str cr h P = R (func-red cr h P)
```
