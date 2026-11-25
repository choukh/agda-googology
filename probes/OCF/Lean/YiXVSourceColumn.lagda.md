# YiXVSourceColumn
> 验收文件。档位：编译定理。有界显式种子的全部有限层槽位语义，标准实例已填。
> 接 YiXVSourceSem、SourceAffine*、Finite*，有限搬运比较参照 YiXVCan2Embed；未交完整外层链或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVSourceColumn where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁; proj₂)
import Data.Fin as F
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegFold as Fold
open import OCF.Lean.YiASIface using (Sbᶠ; s0; ss)
open import OCF.Lean.YiLSRead using (read)
open import OCF.Lean.YiCeilRead using (folds₀≼)
open import OCF.Lean.YiXVAffine using (pw-add)
import OCF.Align.Level as L
open import OCF.Align.Value using (≼-trans)
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteAdd as Add
import OCF.Lean.YiXVFiniteRight as Right
import OCF.Lean.YiXVFiniteCompose as Compose
import OCF.Lean.YiXVFiniteCanonicalInputs as C
import OCF.Lean.YiXVSourceIndex as J
import OCF.Lean.YiXVSourceFamily as U
import OCF.Lean.YiXVSourceBasics as UB
import OCF.Lean.YiXVSourcePath as P
import OCF.Lean.YiXVSourceSlots as Slots
import OCF.Lean.YiXVSourceNext as Next
import OCF.Lean.YiXVSourceSelfInput as Default
import OCF.Lean.YiXVSourceAffineSelf as Self
import OCF.Lean.YiXVZeroRead as ZR
import OCF.Lean.YiXVSourceWorldInput as W
import OCF.Lean.YiXVSourceWorldRules as Rules
import OCF.Lean.YiXVSourceNodeBody as Body
import OCF.Lean.YiXVSourceSem as Sem
import OCF.Lean.YiXVSourceColumnNode as Node

Column : ℕ → Set
Column n = ∀ {H} (p : P.Path H n) (SrcB : Fold.Base (J.nat n)) (Z : I.T H) → W.World n H p SrcB Z →
  ∀ j (s : Sbᶠ n j) (β : J.Tr j) (nβ : J.nat j S.⊢ S.zero ◃ β) → U.U j β (W.φ p s Z) →
  ∀ {x X} → A.Gd n X → U.U n x X →
  U.U j (Fold.ψs (J.nat n) (Default.ev n) (Default.rt n) SrcB (J.nat j) (Slots.pth s) β nβ x)
    (W.φ p s (L.add Z (P.σ p) X))

base : Column 0
base {H} p SrcB Z world .zero s0 β nβ hβ {x} {X} gx hx = ≼-trans (folds₀≼ SrcB β nβ seed x)
  (≼-trans (pw-add (P.σ p) Z (read x)) (≼-trans tail (proj₂ (ZR.approx (W.pc p s0) (λ q → L.suc q) (L.add Z (P.σ p) X)))))
  where
  seed = ≼-trans hβ (proj₁ (ZR.approx (W.pc p s0) (λ q → L.suc q) Z))
  tail = ZR.mono H (Add.mono H 0 {X = Z} {X′ = Z} (B.rfl H F.zero {X = Z} (W.World.good world)) (P.σ p) (read x) X hx)

module Same {n H} (p : P.Path H (suc n)) (SrcB : Fold.Base (J.nat (suc n))) (Z : I.T H)
  (world : W.World (suc n) H p SrcB Z) (β : J.Tr (suc n)) (nβ : J.nat (suc n) S.⊢ S.zero ◃ β)
  (hβ : U.U (suc n) β (W.φ p s0 Z)) where
  seed = UB.weakU (suc n) hβ (W.φ-mix p s0 p s0 (Right.right H (suc n)
    (B.rfl H F.zero {X = Z} (W.World.good world)) (P.σ p) (L.Ω (L.natᴵ (suc n))) (B.actual (suc n))))
  module Run = Self.Self n H (W.pc p s0) (λ q → L.suc q) (P.σ p) SrcB Z (W.World.good world) β nβ seed
  result = Run.result

module Stage (n : ℕ) (low : Column n) where
  upper : Column (suc n)
  upper p SrcB Z world .(suc n) s0 β nβ hβ gx hx = Same.result p SrcB Z world β nβ hβ gx hx
  upper {H} p SrcB Z world j (ss s) β nβ hβ gx U.Layer.uz = UB.weakU j hβ (W.φ-mix p (ss s) p (ss s)
    (Right.right H (suc n) (B.rfl H F.zero {X = Z} (W.World.good world)) (P.σ p) (L.Ω (L.natᴵ (suc n))) (B.actual (suc n))))
  upper {H} p SrcB Z world j (ss s) β nβ hβ (A.Layer.gs {X = X} gx) (U.Layer.us {x} hx) = Next.next j
    (Fold.nzs (J.nat (suc n)) (Default.ev (suc n)) (Default.rt (suc n)) SrcB (J.nat j) (Slots.pth (ss s)) β nβ x)
    (W.φ-good p (ss s) (Add.good H (suc n) {X = Z} (W.World.good world) (P.σ p) X gx))
    (upper p SrcB Z world j (ss s) β nβ hβ gx hx)
  upper {H} p SrcB Z world j (ss s) β nβ hβ gy (U.Layer.uw {X} {Y} hx t@(A.Layer.pack gx _ _)) = UB.weakU j
    (upper p SrcB Z world j (ss s) β nβ hβ gx hx)
    (W.φ-mix p (ss s) p (ss s) (Add.mono H (suc n) {X = Z} {X′ = Z} (B.rfl H F.zero {X = Z} (W.World.good world)) (P.σ p) X Y t))
  upper p SrcB Z world j (ss s) β nβ hβ gx (U.Layer.ul hx) = UB.limU j (λ k → upper p SrcB Z world j (ss s) β nβ hβ gx (hx k))
  upper p SrcB Z world j (ss s) β nβ hβ (A.Layer.gn law gb) (U.Layer.un i {g} {f} hx) =
    Node.result p SrcB Z world i g f law gb body j (ss s) β nβ ih
    where
    body : Body.Node.Body p SrcB Z world i g f
    Body.Node.Body.u body = hx
    Body.Node.Body.out body a X Y gx gy o ha t = Sem.upper (suc n) p SrcB Z world
      (gb (L.into (L.<→◃ (J.q n i)) Y) (C.At.good-in n (I.rank n i) (J.q n i) Y gy)
        (C.At.floor-in n (I.rank n i) (J.q n i) Y o)) (hx a X Y gx gy o ha t)
    ih : ∀ a X Y → A.Gd (I.rank n i) X → A.Gd (I.rank n i) Y → A.Le (I.rank n i) (L.Ω (L.natᴵ (I.rank n i))) Y →
      U.UR n i a X → A.Le (I.rank n i) (L.suc X) Y →
      U.U j (Fold.ψs (J.nat (suc n)) (Default.ev (suc n)) (Default.rt (suc n)) SrcB (J.nat j) (Slots.pth (ss s)) β nβ (g (J.inB n i a)))
        (W.φ p (ss s) (L.add Z (P.σ p) (f (L.into (L.<→◃ (J.q n i)) Y))))
    ih a X Y gx gy o ha t = upper p SrcB Z world j (ss s) β nβ hβ
      (gb (L.into (L.<→◃ (J.q n i)) Y) (C.At.good-in n (I.rank n i) (J.q n i) Y gy)
        (C.At.floor-in n (I.rank n i) (J.q n i) Y o)) (hx a X Y gx gy o ha t)
  upper {H} p SrcB Z world j (ss s) β nβ hβ gout (U.Layer.uu {x} {y} {X} {Y} gx hx gy hy) = UB.weakU j lower
    (W.φ-mix (P.down p) s p (ss s) (Compose.compose H (suc n) n Z (P.σ p) X (λ q → L.suc q) Y (W.World.good world) gx gy))
    where
    prefix = Sem.upper (suc n) p SrcB Z world gx hx
    Cworld = Rules.child p SrcB Z world gx prefix
    Cbase = Fold.dS (J.nat n) (Default.ev (suc n)) (Default.rt (suc n)) SrcB x
    β′ = Fold.ψs (J.nat (suc n)) (Default.ev (suc n)) (Default.rt (suc n)) SrcB (J.nat j) (Slots.pth (ss s)) β nβ x
    nβ′ = Fold.nzs (J.nat (suc n)) (Default.ev (suc n)) (Default.rt (suc n)) SrcB (J.nat j) (Slots.pth (ss s)) β nβ x
    hb = UB.weakU j (upper p SrcB Z world j (ss s) β nβ hβ gx hx)
      (W.φ-mix p (ss s) (P.down p) s (B.rfl H F.zero {X = L.add Z (P.σ p) X} (W.World.good Cworld)))
    lower = low (P.down p) Cbase (L.add Z (P.σ p) X) Cworld j s β′ nβ′ hb gy hy

upper : ∀ n → Column n
upper zero = base
upper (suc n) = Stage.upper n (upper n)

actual : ∀ n H (p : P.Path H n) → ∀ j (s : Sbᶠ n j) →
  U.U j (Fold.ψs (J.nat n) (Default.ev n) (Default.rt n) (Fold.B₀ (J.nat n)) (J.nat j) (Slots.pth s)
    (Fold.bs (Fold.B₀ (J.nat n)) (J.nat j) (Slots.pth s)) (Fold.ns (Fold.B₀ (J.nat n)) (J.nat j) (Slots.pth s)) (S.suc S.zero))
    (W.φ p s (L.add (L.Ω (L.natᴵ H)) (P.σ p) (L.suc (L.Ω (L.natᴵ n)))))
actual n H p j s = upper n p (Fold.B₀ (J.nat n)) (L.Ω (L.natᴵ H)) (W.model n H p) j s _ _
  (W.World.slots (W.model n H p) j s) (B.gs n F.zero {X = L.Ω (L.natᴵ n)} (B.actual n)) (UB.sucU n (UB.zeroU n))
```
