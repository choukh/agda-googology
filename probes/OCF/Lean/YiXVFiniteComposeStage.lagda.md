# YiXVFiniteComposeStage
> 验收文件。档位：编译定理。有限层参照侧的加法复合与前缀下界工具。尚无所有 pre n 或 Goal。
> 从 YiXVCan2Rel/Plus/Lift/Self 按有限层统一，参照侧复用 YiXVFinite*；不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVFiniteComposeStage where
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; cong; subst)
import Data.Fin as F
import OCF.Align.Level as L
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteAdd as Add
import OCF.Lean.YiXVFiniteInputs as In
import OCF.Lean.YiXVFiniteGroundCompose as G

coe-compose : ∀ {i a b c} (p : i L.<ᴵ a) (q : i L.<ᴵ b) (r : i L.<ᴵ c) u →
  L.coe (L.<→◃ q) (L.<→◃ r) (L.coe (L.<→◃ p) (L.<→◃ q) u) ≡ L.coe (L.<→◃ p) (L.<→◃ r) u
coe-compose p q r u = cong (L.into (L.<→◃ r)) (L.out-into (L.<→◃ q) (L.out (L.<→◃ p) u))

module Stage (n m : ℕ)
  (low : ∀ k (X : I.T (suc n)) (σ : L.Simᴵ (L.natᴵ k) (L.natᴵ (suc n))) (Y : I.T k)
    (τ : L.Simᴵ (L.natᴵ m) (L.natᴵ k)) (Z : I.T m) → A.Gd (suc n) X → A.Gd k Y → A.Gd m Z →
    A.Le (suc n) (L.add (L.add X σ Y) (λ q → σ (τ q)) Z) (L.add X σ (L.add Y τ Z))) where
  module S = A.Layer m (A.GoFam m) (A.LeFam m)
  module D = A.Layer n (A.GoFam n) (A.LeFam n)
  module At (k : ℕ) (X : I.T (suc n)) (σ : L.Simᴵ (L.natᴵ k) (L.natᴵ (suc n))) (Y : I.T k)
    (τ : L.Simᴵ (L.natᴵ (suc m)) (L.natᴵ k)) (gx : D.Gd X) (gy : A.Gd k Y) where
    left right : I.T (suc m) → I.T (suc n)
    left Z = L.add (L.add X σ Y) (λ q → σ (τ q)) Z
    right Z = L.add X σ (L.add Y τ Z)
    good-left : ∀ {Z} → S.Gd Z → D.Gd (left Z)
    good-left {Z} gZ = Add.good (suc n) (suc m) {X = L.add X σ Y} (Add.good (suc n) k {X = X} gx σ Y gy) (λ q → σ (τ q)) Z gZ
    good-right : ∀ {Z} → S.Gd Z → D.Gd (right Z)
    good-right {Z} gZ = Add.good (suc n) k {X = X} gx σ (L.add Y τ Z) (Add.good k (suc m) {X = Y} gy τ Z gZ)
    result : ∀ {Z} → S.Gd Z → D.Le (left Z) (right Z)
    result S.gz = D.refl (Add.good (suc n) k {X = X} gx σ Y gy)
    result (S.gs gZ) = D.s≤ (result gZ)
    result (S.gl gZ) = D.pack (good-left (S.gl gZ)) (good-right (S.gl gZ))
      (D.ll (λ j → D.pack (good-left (gZ j)) (good-right (S.gl gZ)) (D.lr j (result (gZ j)))))
    result (S.gn {q = q} {f} law gb) = D.pack (good-left (S.gn law gb)) (good-right (S.gn law gb))
      (D.nn (λ u v gu gv o t → subst (λ a → D.Le (left (f (In.Change.pull c u))) (L.add X σ (L.add Y τ (f a))))
        (sym (coe-compose (σ (τ q)) (τ q) q v))
        (D.trans (result (gb (In.Change.pull c u) (In.Change.good c u gu) (In.Change.floor c u o)))
          (Add.mono (suc n) k {X = X} {X′ = X} (D.refl gx) σ _ _
            (Add.mono k (suc m) {X = Y} {X′ = Y} (B.rfl k F.zero {X = Y} gy) τ _ _
              (S.SC.mo law (In.Change.pull c u) (In.Change.pull c v) (In.Change.good c u gu) (In.Change.good c v gv)
                (In.Change.floor c u o) (In.Change.rel c u v t)))))))
      where c = In.change m n q (σ (τ q))
    result (S.gu {X = Z} gZ) = low k X σ Y (λ q → τ (L.suc q)) Z gx gy gZ

module One = Stage 1 0 (λ k X σ Y τ Z gx gy gZ → G.compose 2 k X σ Y τ Z gx gy)
module Model = One.At 1 (L.Ω (L.natᴵ 2)) (λ q → L.suc q) (L.Ω (L.natᴵ 1)) (λ q → q) A.actual₂ A.actual₁
actual : A.Le 2 (Model.left (L.Ω (L.natᴵ 1))) (Model.right (L.Ω (L.natᴵ 1)))
actual = Model.result A.actual₁
```
