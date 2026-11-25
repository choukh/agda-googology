# YiXVSourceFamily
> 验收文件。档位：编译定理。有限层源模拟的坐标、构造与保持工具；未交读回值界、所有 pre n 或 Goal。
> 从 YiXVCan2Rel/Plus/Lift/Self 按有限层统一，参照侧复用 YiXVFinite*；不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVSourceFamily where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
import Data.Fin as F
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
open import OCF.Lean.YiLSRead using (read)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; s≼s)
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteAdd as Add
import OCF.Lean.YiXVSourceIndex as J

module Layer (n : ℕ) (Lo : ∀ i → J.Tr (I.rank n i) → I.T (I.rank n i) → Set) where
  data U : J.Tr (suc n) → I.T (suc n) → Set where
    uz : U S.zero (L.Ω (L.natᴵ (suc n)))
    us : ∀ {x X} → U x X → U (S.suc x) (L.suc X)
    uw : ∀ {x X Y} → U x X → A.Le (suc n) X Y → U x Y
    ul : ∀ {g a X} → (∀ k → U (g k) X) → U (S.lim g a) X
    un : ∀ i {g f} →
      (∀ (a : J.Tr (I.rank n i)) X Y → A.Gd (I.rank n i) X → A.Gd (I.rank n i) Y →
        A.Le (I.rank n i) (L.Ω (L.natᴵ (I.rank n i))) Y → Lo i a X → A.Le (I.rank n i) (L.suc X) Y →
        U (g (J.inB n i a)) (f (L.into (L.<→◃ (J.q n i)) Y))) →
      U (S.Ω (J.slot n i) g) (L.limᵢ (J.q n i) f)
    uu : ∀ {x y ny X Y} → A.Gd (suc n) X → U x X → A.Gd n Y → Lo F.zero y Y →
      U (S.up x tt y ny) (L.add X (λ q → L.suc q) Y)

UR : ∀ n (i : F.Fin (suc n)) → J.Tr (I.rank n i) → I.T (I.rank n i) → Set
UR zero F.zero x X = read x ≼ X
UR zero (F.suc ()) x X
UR (suc n) F.zero x X = Layer.U n (UR n) x X
UR (suc n) (F.suc i) x X = UR n i x X
U : ∀ n → J.Tr n → I.T n → Set
U n = UR n F.zero

module D₁ = Layer 0 (UR 0)
Ω₁ : U 1 (O.Ωt (J.nat 1)) (L.Ω (L.natᴵ 1) L.+ L.Ω (L.natᴵ 1))
Ω₁ = D₁.un F.zero (λ a X Y gx gy o ha t → D₁.uw
  (D₁.uu A.actual₁ D₁.uz tt (s≼s ha))
  (Add.mono 1 0 {X = L.Ω (L.natᴵ 1)} {X′ = L.Ω (L.natᴵ 1)}
    (B.rfl 1 F.zero {X = L.Ω (L.natᴵ 1)} A.actual₁) (λ q → L.suc q) (L.suc X) Y t))
module D₂ = Layer 1 (UR 1)
Ω₂ : U 2 (O.Ωt (J.nat 2)) (L.Ω (L.natᴵ 2) L.+ L.Ω (L.natᴵ 2))
Ω₂ = D₂.un F.zero (λ a X Y gx gy o ha t → D₂.uw
  (D₂.uu A.actual₂ D₂.uz (B.gs 1 F.zero {X = X} gx) (D₁.us ha))
  (Add.mono 2 1 {X = L.Ω (L.natᴵ 2)} {X′ = L.Ω (L.natᴵ 2)}
    (B.rfl 2 F.zero {X = L.Ω (L.natᴵ 2)} A.actual₂) (λ q → L.suc q) (L.suc X) Y t))
```
