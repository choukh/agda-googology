# YiXVFiniteFoldStage
> 验收文件。档位：编译定理。有限层参照侧的统一比较工具；尚无所有 pre n 或 Goal。
> 证明参照 YiOverOps 与 YiXVCan2* 并按有限层统一，不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVFiniteFoldStage where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst₂)
import Data.Fin as F
import OCF.Align.Level as L
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteBridge as E
import OCF.Lean.YiXVFiniteFloor as Floor
import OCF.Lean.YiXVFiniteIter as It
import OCF.Lean.YiXVFiniteFoldInterface as Q
import OCF.Lean.YiXVFiniteFoldNodeGood as NG
import OCF.Lean.YiXVFiniteFoldNodeMono as NM
import OCF.Lean.YiXVFiniteFoldNodeAA as NA
import OCF.Lean.YiXVFiniteFoldNodeOp as NO

module Stage (n : ℕ) (old : Q.Ops n) where
  module D = A.Layer n (A.GoFam n) (A.LeFam n)
  N = L.natᴵ (suc n)
  mutual
    good : ∀ j {a} (p : L.natᴵ j L.<ᴵ a) (σ : L.Simᴵ N a) {X} → D.Gd X → A.Gd j (L.ψ p σ X)
    good j p σ D.gz = proj₁ (B.Ω-model j F.zero)
    good j p σ (D.gs {X} gx) = B.gl j F.zero (It.good j (L.ψ p σ X) (good j p σ gx))
    good j p σ (D.gl {a} gx) = B.gl j F.zero (λ k → good j p σ (gx k))
    good j p σ (D.gn {q = q} {f = f} law gb) = node-good j p σ q f law gb (E.num n q) (E.eq n q)
    good j p σ (D.gu {X} gx) = Q.Ops.good old j p (λ r → σ (L.suc r)) X gx

    body : ∀ m (q : L.natᴵ m L.<ᴵ N) (f : L.U (L.natᴵ m) (L.<→◃ q) → I.T (suc n))
      (law : D.SC q f) (gb : ∀ u → D.GU q u → D.Floor q u → D.Gd (f u)) → NG.Node.Body n m q f
    NG.Node.Body.good (body m q f law gb) j p σ u gu o = good j p σ (gb u gu o)
    NG.Node.Body.mono (body m q f law gb) j p p′ σ τ u v gu gv o t = mono j p p′ σ τ (D.SC.mo law u v gu gv o t)
    NG.Node.Body.step (body m q f law gb) j p σ u gu o = mono j p p σ σ (D.SC.db law u gu o)

    cross : ∀ m (q : L.natᴵ m L.<ᴵ N) (f g : L.U (L.natᴵ m) (L.<→◃ q) → I.T (suc n))
      (lf : D.SC q f) (bf : ∀ u → D.GU q u → D.Floor q u → D.Gd (f u))
      (lg : D.SC q g) (bg : ∀ u → D.GU q u → D.Floor q u → D.Gd (g u))
      (h : ∀ u v → D.GU q u → D.GU q v → D.Floor q u → D.RU q u v → D.Le (f u) (g v)) →
      NM.Node.Cross n m q f g (body m q f lf bf) (body m q g lg bg)
    NM.Node.Cross.mono (cross m q f g lf bf lg bg h) j p p′ σ τ u v gu gv o t = mono j p p′ σ τ (h u v gu gv o t)

    bound : ∀ m (q : L.natᴵ m L.<ᴵ N) X (g : L.U (L.natᴵ m) (L.<→◃ q) → I.T (suc n))
      (lg : D.SC q g) (bg : ∀ u → D.GU q u → D.Floor q u → D.Gd (g u)) →
      D.Le X (g (D.start q)) → NA.Node.Bound n m q X g (body m q g lg bg)
    NA.Node.Bound.alpha (bound m q X g lg bg t) j p p′ σ τ = mono j p p′ σ τ t

    same : ∀ j {a b} (p : L.natᴵ j L.<ᴵ a) (p′ : L.natᴵ j L.<ᴵ b)
      (σ : L.Simᴵ N a) (τ : L.Simᴵ N b) {X} → D.Gd X → A.Le j (L.ψ p σ X) (L.ψ p′ τ X)
    same j p p′ σ τ D.gz = B.rfl j F.zero {X = L.Ω (L.natᴵ j)} (proj₁ (B.Ω-model j F.zero))
    same j p p′ σ τ (D.gs {X} gx) = It.lim-mono j (L.ψ p σ X) (L.ψ p′ τ X) (same j p p′ σ τ gx)
    same j p p′ σ τ (D.gl {a} gx) = B.ll j F.zero {a = λ k → L.ψ p σ (a k)} {Y = L.lim (λ k → L.ψ p′ τ (a k))}
      (λ k → good j p σ (gx k)) (good j p′ τ (D.gl gx))
      (λ k → B.lr j F.zero {X = L.ψ p σ (a k)} {a = λ k → L.ψ p′ τ (a k)}
        (good j p σ (gx k)) (λ k → good j p′ τ (gx k)) k (same j p p′ σ τ (gx k)))
    same j p p′ σ τ (D.gn {q = q} {f} law gb) = node-mono j p p′ σ τ q f f law gb law gb (D.SC.mo law) (E.num n q) (E.eq n q)
    same j p p′ σ τ (D.gu {X} gx) = Q.Ops.mono old j p p′ (λ r → σ (L.suc r)) (λ r → τ (L.suc r)) X X
      (B.rfl n F.zero {X = X} gx)

    mono : ∀ j {a b} (p : L.natᴵ j L.<ᴵ a) (p′ : L.natᴵ j L.<ᴵ b)
      (σ : L.Simᴵ N a) (τ : L.Simᴵ N b) {X Y} → D.Le X Y → A.Le j (L.ψ p σ X) (L.ψ p′ τ Y)
    mono j p p′ σ τ (D.pack gx gy D.rr) = same j p p′ σ τ gx
    mono j p p′ σ τ (D.pack gx gy D.zz) = Floor.floor j p′ τ _ (good j p′ τ gy)
    mono j p p′ σ τ (D.pack gx gy (D.ss {X} {Y} t)) = It.lim-mono j (L.ψ p σ X) (L.ψ p′ τ Y) (mono j p p′ σ τ t)
    mono j p p′ σ τ (D.pack {X} gx (D.gs {X = Y} gy) (D.ws t)) = B.lr j F.zero {X = L.ψ p σ X} {a = _}
      (good j p σ gx) (It.good j (L.ψ p′ τ Y) (good j p′ τ gy)) 1 (mono j p p′ σ τ t)
    mono j p p′ σ τ (D.pack {Y = Y} (D.gl {a} gx) gy (D.ll h)) = B.ll j F.zero {a = λ k → L.ψ p σ (a k)} {Y = L.ψ p′ τ Y}
      (λ k → good j p σ (gx k)) (good j p′ τ gy) (λ k → mono j p p′ σ τ (h k))
    mono j p p′ σ τ (D.pack {X} gx (D.gl {a} gy) (D.lr k t)) = B.lr j F.zero {X = L.ψ p σ X} {a = λ k → L.ψ p′ τ (a k)}
      (good j p σ gx) (λ k → good j p′ τ (gy k)) k (mono j p p′ σ τ t)
    mono j p p′ σ τ (D.pack (D.gn {q = q} {f} lf bf) (D.gn {f = g} lg bg) (D.nn h)) =
      node-mono j p p′ σ τ q f g lf bf lg bg h (E.num n q) (E.eq n q)
    mono j p p′ σ τ (D.pack {X} gx (D.gn {q = q} {f = g} lg bg) (D.aa t)) =
      node-aa j p p′ σ τ q X g lg bg t (E.num n q) (E.eq n q)
    mono j p p′ σ τ (D.pack gx gy (D.uu {X} {Y} t)) = Q.Ops.mono old j p p′
      (λ r → σ (L.suc r)) (λ r → τ (L.suc r)) X Y t
    mono j p p′ σ τ (D.pack gx gy (D.uS {X} d)) = Q.Ops.mono old j p p′
      (λ r → σ (L.suc r)) (λ r → τ (L.suc r)) (L.suc X) (L.suc X)
      (B.rfl n F.zero {X = L.suc X} (B.gs n F.zero {X = X} d))
    mono j p p′ σ τ (D.pack gx gy (D.uS⁻ {X} d)) = Q.Ops.mono old j p p′
      (λ r → σ (L.suc r)) (λ r → τ (L.suc r)) (L.suc X) (L.suc X)
      (B.rfl n F.zero {X = L.suc X} (B.gs n F.zero {X = X} d))
    mono j p p′ σ τ (D.pack gx gy D.uZ) = B.rfl j F.zero {X = L.Ω (L.natᴵ j)} (proj₁ (B.Ω-model j F.zero))
    mono j p p′ σ τ (D.pack gx gy D.uZ⁻) = B.rfl j F.zero {X = L.Ω (L.natᴵ j)} (proj₁ (B.Ω-model j F.zero))
    mono j p p′ σ τ (D.pack gx gy (D.uL {a} d)) = Q.Ops.mono old j p p′
      (λ r → σ (L.suc r)) (λ r → τ (L.suc r)) (L.lim a) (L.lim a)
      (B.rfl n F.zero {X = L.lim a} (B.gl n F.zero {a = a} d))
    mono j p p′ σ τ (D.pack gx gy (D.uL⁻ {a} d)) = Q.Ops.mono old j p p′
      (λ r → σ (L.suc r)) (λ r → τ (L.suc r)) (L.lim a) (L.lim a)
      (B.rfl n F.zero {X = L.lim a} (B.gl n F.zero {a = a} d))
    mono j p p′ σ τ (D.pack gx gy (D.uN {q = q} {a} d)) = Q.Ops.node-plus old j p p′
      (λ r → σ (L.suc r)) τ q a d
    mono j p p′ σ τ (D.pack gx gy (D.uN⁻ {q = q} {a} d)) = Q.Ops.node-minus old j p′ p
      (λ r → τ (L.suc r)) σ q a d
    mono j p p′ σ τ (D.pack gx gy (D.tr t u)) = B.trans j F.zero {X = _} {Y = _} {Z = _}
      (mono j p p′ σ τ t) (mono j p′ p′ τ τ u)

    node-good : ∀ j {a} (p : L.natᴵ j L.<ᴵ a) (σ : L.Simᴵ N a) {i} (q : i L.<ᴵ N)
      (f : L.U i (L.<→◃ q) → I.T (suc n)) (law : D.SC q f)
      (gb : ∀ u → D.GU q u → D.Floor q u → D.Gd (f u)) m → i ≡ L.natᴵ m → A.Gd j (L.ψ p σ (L.limᵢ q f))
    node-good j p σ q f law gb m refl = NG.Node.Run.result n m q f (body m q f law gb) j p σ

    node-mono : ∀ j {a b} (p : L.natᴵ j L.<ᴵ a) (p′ : L.natᴵ j L.<ᴵ b) (σ : L.Simᴵ N a) (τ : L.Simᴵ N b)
      {i} (q : i L.<ᴵ N) (f g : L.U i (L.<→◃ q) → I.T (suc n))
      (lf : D.SC q f) (bf : ∀ u → D.GU q u → D.Floor q u → D.Gd (f u))
      (lg : D.SC q g) (bg : ∀ u → D.GU q u → D.Floor q u → D.Gd (g u))
      (h : ∀ u v → D.GU q u → D.GU q v → D.Floor q u → D.RU q u v → D.Le (f u) (g v)) m → i ≡ L.natᴵ m →
      A.Le j (L.ψ p σ (L.limᵢ q f)) (L.ψ p′ τ (L.limᵢ q g))
    node-mono j p p′ σ τ q f g lf bf lg bg h m refl = subst₂ (A.Le j)
      (NO.Node.normal n m q j p σ f) (NO.Node.normal n m q j p′ τ g)
      (NO.Node.Compare.result n m q f g (body m q f lf bf) (body m q g lg bg)
        (cross m q f g lf bf lg bg h) j p p′ σ τ q q (λ r → r) (λ r → r))

    node-aa : ∀ j {a b} (p : L.natᴵ j L.<ᴵ a) (p′ : L.natᴵ j L.<ᴵ b) (σ : L.Simᴵ N a) (τ : L.Simᴵ N b)
      {i} (q : i L.<ᴵ N) X (g : L.U i (L.<→◃ q) → I.T (suc n))
      (lg : D.SC q g) (bg : ∀ u → D.GU q u → D.Floor q u → D.Gd (g u)) (t : D.Le X (g (D.start q)))
      m → i ≡ L.natᴵ m → A.Le j (L.ψ p σ X) (L.ψ p′ τ (L.limᵢ q g))
    node-aa j p p′ σ τ q X g lg bg t m refl = NA.Node.Run.result n m q X g (body m q g lg bg)
      (bound m q X g lg bg t) j p p′ σ τ

  node-plus : ∀ j {a b} (p : L.natᴵ j L.<ᴵ a) (p′ : L.natᴵ j L.<ᴵ b)
    (σ : L.Simᴵ N a) (τ : L.Simᴵ (L.suc N) b) {i} (q : i L.<ᴵ N) f → D.Gd (L.limᵢ q f) →
    A.Le j (L.ψ p σ (L.limᵢ q f)) (L.ψ p′ τ (L.limᵢ (L.suc q) (λ u → L.up L.zero (f u))))
  node-plus j p p′ σ τ q f (D.gn law gb) = aux q f law gb (E.num n q) (E.eq n q)
    where
    aux : ∀ {i} (q : i L.<ᴵ N) f (law : D.SC q f) (gb : ∀ u → D.GU q u → D.Floor q u → D.Gd (f u)) m → i ≡ L.natᴵ m →
      A.Le j (L.ψ p σ (L.limᵢ q f)) (L.ψ p′ τ (L.limᵢ (L.suc q) (λ u → L.up L.zero (f u))))
    aux q f law gb m refl = subst₂ (A.Le j) (Op.normal j p σ f) (Op.raised j p′ τ f)
      (Cmp.result j p p′ σ (λ r → τ (L.suc r)) q (L.suc q) (λ r → r) (λ r → L.suc r))
      where
      module Op = NO.Node n m q
      module Cmp = Op.Compare f f (body m q f law gb) (body m q f law gb)
        (cross m q f f law gb law gb (D.SC.mo law))
  node-minus : ∀ j {a b} (p : L.natᴵ j L.<ᴵ a) (p′ : L.natᴵ j L.<ᴵ b)
    (σ : L.Simᴵ N a) (τ : L.Simᴵ (L.suc N) b) {i} (q : i L.<ᴵ N) f → D.Gd (L.limᵢ q f) →
    A.Le j (L.ψ p′ τ (L.limᵢ (L.suc q) (λ u → L.up L.zero (f u)))) (L.ψ p σ (L.limᵢ q f))
  node-minus j p p′ σ τ q f (D.gn law gb) = aux q f law gb (E.num n q) (E.eq n q)
    where
    aux : ∀ {i} (q : i L.<ᴵ N) f (law : D.SC q f) (gb : ∀ u → D.GU q u → D.Floor q u → D.Gd (f u)) m → i ≡ L.natᴵ m →
      A.Le j (L.ψ p′ τ (L.limᵢ (L.suc q) (λ u → L.up L.zero (f u)))) (L.ψ p σ (L.limᵢ q f))
    aux q f law gb m refl = subst₂ (A.Le j) (Op.raised j p′ τ f) (Op.normal j p σ f)
      (Cmp.result j p′ p (λ r → τ (L.suc r)) σ (L.suc q) q (λ r → L.suc r) (λ r → r))
      where
      module Op = NO.Node n m q
      module Cmp = Op.Compare f f (body m q f law gb) (body m q f law gb)
        (cross m q f f law gb law gb (D.SC.mo law))

  result : Q.Ops (suc n)
  Q.Ops.good result j p σ X gx = good j p σ gx
  Q.Ops.mono result j p p′ σ τ X Y t = mono j p p′ σ τ t
  Q.Ops.node-plus result = node-plus
  Q.Ops.node-minus result = node-minus

module One = Stage 0 Q.ops₀
actual : A.Gd 2 (L.ψ L.zero (λ q → L.suc (L.suc q)) (L.Ω (L.natᴵ 1)))
actual = One.good 2 L.zero (λ q → L.suc (L.suc q)) A.actual₁
```
