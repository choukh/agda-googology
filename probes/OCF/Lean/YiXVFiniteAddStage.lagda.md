# YiXVFiniteAddStage
> 验收文件。档位：编译定理。有限层参照侧的统一比较工具；尚无所有 pre n 或 Goal。
> 证明参照 YiOverOps 与 YiXVCan2* 并按有限层统一，不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVFiniteAddStage where
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (subst; sym)
import Data.Fin as F
import OCF.Align.Level as L
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteCoerce as C
import OCF.Lean.YiXVFiniteInputs as In
import OCF.Lean.YiXVFiniteGroundAdd as G

module Stage (n m : ℕ)
  (lowG : ∀ {X} → A.Gd (suc n) X → (σ : L.Simᴵ (L.natᴵ m) (L.natᴵ (suc n))) →
    (y : I.T m) → A.Gd m y → A.Gd (suc n) (L.add X σ y))
  (lowM : ∀ {X X′} → A.Le (suc n) X X′ → (σ : L.Simᴵ (L.natᴵ m) (L.natᴵ (suc n))) →
    (y y′ : I.T m) → A.Le m y y′ → A.Le (suc n) (L.add X σ y) (L.add X′ σ y′)) where
  module D = A.Layer n (A.GoFam n) (A.LeFam n)
  module S = A.Layer m (A.GoFam m) (A.LeFam m)
  Sim = L.Simᴵ (L.natᴵ (suc m)) (L.natᴵ (suc n))
  proof : ∀ {X Y} → D.Le X Y → D.Step X Y
  proof (D.pack gx gy p) = p

  mutual
    good : ∀ {X Y} → D.Gd X → (σ : Sim) → S.Gd Y → D.Gd (L.add X σ Y)
    good gx σ S.gz = gx
    good gx σ (S.gs gy) = D.gs (good gx σ gy)
    good gx σ (S.gl gy) = D.gl (λ k → good gx σ (gy k))
    good {X} gx σ (S.gn {q = q} {f = a} (S.sc mo db po) ga) = D.gn (D.sc
      (λ u v gu gv o r → mono (D.refl gx) σ (mo (In.Change.pull c u) (In.Change.pull c v)
        (In.Change.good c u gu) (In.Change.good c v gv) (In.Change.floor c u o) (In.Change.rel c u v r)))
      (λ u gu o → subst (λ v → D.Le (L.suc (L.add X σ (a (In.Change.pull c u)))) (L.add X σ (a v)))
        (sym (In.Change.next c u)) (mono (D.refl gx) σ (db (In.Change.pull c u) (In.Change.good c u gu) (In.Change.floor c u o))))
      (subst (λ v → D.Le D.one (L.add X σ (a v))) (sym (In.Change.start c)) (mono (D.z≤ gx) σ po)))
      (λ u gu o → good gx σ (ga (In.Change.pull c u) (In.Change.good c u gu) (In.Change.floor c u o)))
      where c = In.change m n q (σ q)
    good gx σ (S.gu {X = y} gy) = lowG gx (λ q → σ (L.suc q)) y gy

    right : ∀ {X X′ Y} → D.Le X X′ → (σ : Sim) → S.Gd Y → D.Le X (L.add X′ σ Y)
    right p σ S.gz = p
    right p σ (S.gs gy) = D.pack (D.left p) (D.gs (good (D.right p) σ gy)) (D.ws (right p σ gy))
    right p σ (S.gl gy) = D.pack (D.left p) (D.gl (λ k → good (D.right p) σ (gy k))) (D.lr 0 (right p σ (gy 0)))
    right p σ (S.gn {q = q} (S.sc mo db po) ga) = D.pack (D.left p) (good (D.right p) σ (S.gn (S.sc mo db po) ga))
      (D.aa (right p σ (ga (In.Change.pull c (C.start (σ q)))
        (In.Change.good c (C.start (σ q)) (In.At.good-start n (σ q)))
        (In.Change.floor c (C.start (σ q)) (In.At.floor-start n (σ q))))))
      where c = In.change m n q (σ q)
    right p σ (S.gu {X = y} gy) = lowM p (λ q → σ (L.suc q)) L.zero y (B.z≤ m F.zero {Y = y} gy)

    prefix : ∀ {X X′ Y} → D.Le X X′ → (σ : Sim) → S.Gd Y → D.Le (L.add X σ Y) (L.add X′ σ Y)
    prefix p σ S.gz = p
    prefix p σ (S.gs gy) = D.s≤ (prefix p σ gy)
    prefix p σ (S.gl gy) = D.pack (D.gl (λ k → good (D.left p) σ (gy k))) (D.gl (λ k → good (D.right p) σ (gy k)))
      (D.ll (λ k → D.pack (good (D.left p) σ (gy k)) (D.gl (λ j → good (D.right p) σ (gy j))) (D.lr k (prefix p σ (gy k)))))
    prefix p σ (S.gn {q = q} (S.sc mo db po) ga) = D.pack (good (D.left p) σ (S.gn (S.sc mo db po) ga))
      (good (D.right p) σ (S.gn (S.sc mo db po) ga))
      (D.nn (λ u v gu gv o r → mono p σ (mo (In.Change.pull c u) (In.Change.pull c v)
        (In.Change.good c u gu) (In.Change.good c v gv) (In.Change.floor c u o) (In.Change.rel c u v r))))
      where c = In.change m n q (σ q)
    prefix p σ (S.gu {X = y} gy) = lowM p (λ q → σ (L.suc q)) y y (B.rfl m F.zero {X = y} gy)

    mono : ∀ {X X′ Y Y′} → D.Le X X′ → (σ : Sim) → S.Le Y Y′ → D.Le (L.add X σ Y) (L.add X′ σ Y′)
    mono p σ (S.pack gy gy′ q) = D.pack (good (D.left p) σ gy) (good (D.right p) σ gy′) (step p σ gy gy′ q)

    step : ∀ {X X′ Y Y′} → D.Le X X′ → (σ : Sim) → S.Gd Y → S.Gd Y′ → S.Step Y Y′ → D.Step (L.add X σ Y) (L.add X′ σ Y′)
    step p σ gy gy′ S.rr = proof (prefix p σ gy)
    step p σ gy gy′ S.zz = proof (right p σ gy′)
    step p σ gy gy′ (S.ss q) = D.ss (mono p σ q)
    step p σ gy gy′ (S.ws q) = D.ws (mono p σ q)
    step p σ gy gy′ (S.ll h) = D.ll (λ k → mono p σ (h k))
    step p σ gy gy′ (S.lr k q) = D.lr k (mono p σ q)
    step p σ gy gy′ (S.nn {q = q} h) = D.nn (λ u v gu gv o r → mono p σ (h (In.Change.pull c u) (In.Change.pull c v)
      (In.Change.good c u gu) (In.Change.good c v gv) (In.Change.floor c u o) (In.Change.rel c u v r)))
      where c = In.change m n q (σ q)
    step {X} {X′} {Y} p σ gy (S.gn {q = q} {f = a} la ga) (S.aa h) = D.aa
      (subst (λ v → D.Le (L.add X σ Y) (L.add X′ σ (a v))) (sym (In.Change.start c)) (mono p σ h))
      where c = In.change m n q (σ q)
    step p σ (S.gu {X = y} gy) (S.gu {X = y′} gy′) (S.uu q) = proof (lowM p (λ r → σ (L.suc r)) y y′ q)
    step p σ gy gy′ (S.uS {X = y} d) = proof (lowM p (λ q → σ (L.suc q)) (L.suc y) (L.suc y)
      (B.rfl m F.zero {X = L.suc y} (B.gs m F.zero {X = y} d)))
    step p σ gy gy′ (S.uS⁻ {X = y} d) = proof (lowM p (λ q → σ (L.suc q)) (L.suc y) (L.suc y)
      (B.rfl m F.zero {X = L.suc y} (B.gs m F.zero {X = y} d)))
    step p σ gy gy′ S.uZ = proof p
    step p σ gy gy′ S.uZ⁻ = proof p
    step p σ gy gy′ (S.uL {a = a} d) = proof (lowM p (λ q → σ (L.suc q)) (L.lim a) (L.lim a)
      (B.rfl m F.zero {X = L.lim a} (B.gl m F.zero {a = a} d)))
    step p σ gy gy′ (S.uL⁻ {a = a} d) = proof (lowM p (λ q → σ (L.suc q)) (L.lim a) (L.lim a)
      (B.rfl m F.zero {X = L.lim a} (B.gl m F.zero {a = a} d)))
    step p σ gy gy′ (S.uN {q = q} {a = a} d) = proof (lowM p (λ q → σ (L.suc q)) (L.limᵢ q a) (L.limᵢ q a)
      (B.rfl m F.zero {X = L.limᵢ q a} d))
    step p σ gy gy′ (S.uN⁻ {q = q} {a = a} d) = proof (lowM p (λ q → σ (L.suc q)) (L.limᵢ q a) (L.limᵢ q a)
      (B.rfl m F.zero {X = L.limᵢ q a} d))
    step p σ gy gy′ (S.tr q r) = D.tr (mono p σ q) (mono (D.refl (D.right p)) σ r)

module One = Stage 1 0 (λ gx σ y gy → G.good 2 gx σ y)
  (λ p σ y y′ q → G.mono 2 {σ = σ} {τ = σ} p q)
model₁ : A.Gd 2 (L.add (L.Ω (L.natᴵ 2)) (λ q → L.suc q) (L.Ω (L.natᴵ 1)))
model₁ = One.good A.actual₂ (λ q → L.suc q) A.actual₁

module Two = Stage 1 1 (λ gx σ y gy → One.good gx σ gy)
  (λ p σ y y′ q → One.mono p σ q)
model₂ : A.Gd 2 (L.Ω (L.natᴵ 2) L.+ L.Ω (L.natᴵ 2))
model₂ = Two.good A.actual₂ (λ q → q) A.actual₂
```
