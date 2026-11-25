# YiXVFiniteFoldNodeGood
> 验收文件。档位：编译定理。有限层参照侧的统一比较工具；尚无所有 pre n 或 Goal。
> 证明参照 YiOverOps 与 YiXVCan2* 并按有限层统一，不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVFiniteFoldNodeGood where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
import Data.Fin as F
import OCF.Align.Level as L
open import OCF.Align.Value using (≼-refl)
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteCoerce as C
import OCF.Lean.YiXVFiniteCanonicalInputs as N
import OCF.Lean.YiXVFiniteRetainedInputs as R
import OCF.Lean.YiXVFiniteVia as V
import OCF.Lean.YiXVFiniteChain as Ch
import OCF.Lean.YiXVFiniteIter as It
import OCF.Lean.YiXVFiniteFloor as Floor
import OCF.Lean.YiXVFiniteGroundFold as G

module Node (n m : ℕ) (q : L.natᴵ m L.<ᴵ L.natᴵ (suc n))
  (f : L.U (L.natᴵ m) (L.<→◃ q) → I.T (suc n)) where
  module D = A.Layer n (A.GoFam n) (A.LeFam n)
  module In = N.At n m q
  record Body : Set₁ where
    field
      good : ∀ j {a} (p : L.natᴵ j L.<ᴵ a) (σ : L.Simᴵ (L.natᴵ (suc n)) a) u →
        D.GU q u → D.Floor q u → A.Gd j (L.ψ p σ (f u))
      mono : ∀ j {a b} (p : L.natᴵ j L.<ᴵ a) (p′ : L.natᴵ j L.<ᴵ b)
        (σ : L.Simᴵ (L.natᴵ (suc n)) a) (τ : L.Simᴵ (L.natᴵ (suc n)) b) u v →
        D.GU q u → D.GU q v → D.Floor q u → D.RU q u v → A.Le j (L.ψ p σ (f u)) (L.ψ p′ τ (f v))
      step : ∀ j {a} (p : L.natᴵ j L.<ᴵ a) (σ : L.Simᴵ (L.natᴵ (suc n)) a) u →
        D.GU q u → D.Floor q u → A.Le j (L.ψ p σ (L.suc (f u))) (L.ψ p σ (f (C.next q u)))

  module Run (body : Body) where
    open Body body
    raw : I.T m → I.T (suc n)
    raw X = f (L.into (L.<→◃ q) X)
    inner : ∀ X → A.Gd m X → A.Le m (L.Ω (L.natᴵ m)) X → A.Gd m (L.ψ q (λ r → r) (raw X))
    inner X gx o = good m q (λ r → r) _ (In.good-in X gx) (In.floor-in X o)
    module Chain = Ch.Chain m q (λ r → r) raw inner
    diagonal : ∀ j {a} (p : L.natᴵ j L.<ᴵ a) (σ : L.Simᴵ (L.natᴵ (suc n)) a) →
      A.Gd j (L.lim (λ k → L.ψ p σ (raw (Chain.d k))))
    diagonal j p σ = B.gl j F.zero {a = λ k → L.ψ p σ (raw (Chain.d k))}
      (λ k → good j p σ _ (In.good-in _ (Chain.good k)) (In.floor-in _ (Chain.floor k)))

    retained : ∀ j {a} (p : L.natᴵ (suc j) L.<ᴵ a) (σ : L.Simᴵ (L.natᴵ (suc n)) a)
      (r : L.natᴵ m L.<ᴵ L.natᴵ (suc j)) →
      A.Gd (suc j) (L.limᵢ r (λ u → L.ψ p σ (f (R.At.pull n j m q r u))))
    retained j p σ r = E.gn (E.sc mo db po) gb
      where
      module E = A.Layer j (A.GoFam j) (A.LeFam j)
      module P = R.At n j m q r
      h : L.U (L.natᴵ m) (L.<→◃ r) → I.T (suc j)
      h u = L.ψ p σ (f (P.pull u))
      gb : ∀ u → E.GU r u → E.Floor r u → A.Gd (suc j) (h u)
      gb u gu o = good (suc j) p σ _ (P.good u gu) (P.floor u o)
      mo : ∀ u v → E.GU r u → E.GU r v → E.Floor r u → E.RU r u v → E.Le (h u) (h v)
      mo u v gu gv o t = mono (suc j) p p σ σ _ _ (P.good u gu) (P.good v gv) (P.floor u o) (P.rel u v t)
      db : ∀ u → E.GU r u → E.Floor r u → E.Le (L.suc (h u)) (h (C.next r u))
      db u gu o = E.trans (It.strict (suc j) p σ _ (gb u gu o))
        (subst (λ v → E.Le (L.ψ p σ (L.suc (f (P.pull u)))) (L.ψ p σ (f v))) (sym (P.next u))
          (step (suc j) p σ _ (P.good u gu) (P.floor u o)))
      po : E.Le E.one (h (C.start r))
      po = E.trans (proj₂ (B.Ω-model (suc j) F.zero))
        (Floor.floor (suc j) p σ _ (gb (C.start r)
          (N.At.good-in j m r _ (proj₁ (B.Ω-model m F.zero)))
          (N.At.floor-in j m r _ (B.rfl m F.zero {X = L.Ω (L.natᴵ m)} (proj₁ (B.Ω-model m F.zero))))))

    result : ∀ j {a} (p : L.natᴵ j L.<ᴵ a) (σ : L.Simᴵ (L.natᴵ (suc n)) a) → A.Gd j (L.ψ p σ (L.limᵢ q f))
    result zero p σ with L.<ᴵ-dec (σ q) p
    ... | injᵃ (L.via e ())
    ... | injᵇ w = diagonal zero p σ
    ... | injᶜ e = diagonal zero p σ
    result (suc j) p σ with L.<ᴵ-dec (σ q) p
    ... | injᵃ v with V.exact (I.finite m) v
    ... | r , refl = retained j p σ r
    result (suc j) p σ | injᵇ w = diagonal (suc j) p σ
    result (suc j) p σ | injᶜ e = diagonal (suc j) p σ

module Model = Node 0 0 L.zero (L.up L.zero)
body : Model.Body
Model.Body.good body j p σ u gu o = G.good j p (λ r → σ (L.suc r)) u
Model.Body.mono body j p p′ σ τ u v gu gv o t = G.mono j p p′ (λ r → σ (L.suc r)) (λ r → τ (L.suc r)) t
Model.Body.step body j p σ u gu o = It.lim-mono j (L.ψ p (λ r → σ (L.suc r)) u) (L.ψ p (λ r → σ (L.suc r)) u)
  (B.rfl j F.zero {X = L.ψ p (λ r → σ (L.suc r)) u} (G.good j p (λ r → σ (L.suc r)) u))
actual₀ : A.Gd 0 (L.ψ L.zero (λ q → q) (L.Ω (L.natᴵ 1)))
actual₀ = Model.Run.result body 0 L.zero (λ q → q)
actual₁ : A.Gd 1 (L.ψ L.zero (λ q → L.suc q) (L.Ω (L.natᴵ 1)))
actual₁ = Model.Run.result body 1 L.zero (λ q → L.suc q)
actual₂ : A.Gd 2 (L.ψ L.zero (λ q → L.suc (L.suc q)) (L.Ω (L.natᴵ 1)))
actual₂ = Model.Run.result body 2 L.zero (λ q → L.suc (L.suc q))
```
