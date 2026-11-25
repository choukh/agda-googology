# YiXVFiniteFoldOmega
> 验收文件。档位：编译定理。有限层参照侧的统一比较工具；尚无所有 pre n 或 Goal。
> 证明参照 YiOverOps 与 YiXVCan2* 并按有限层统一，不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVFiniteFoldOmega where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import Data.Unit using (tt)
import Data.Fin as F
import OCF.Align.Level as L
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteAdd as Add
import OCF.Lean.YiXVFiniteIter as It
import OCF.Lean.YiXVFiniteVia as V
import OCF.Lean.YiXVFiniteFold as Fold
import OCF.Lean.YiXVFiniteFoldInterface as Q
import OCF.Lean.YiXVFiniteTransportShape as S
import OCF.Lean.YiXVFiniteTransportInputs as TQ
import OCF.Lean.YiXVFiniteTransport as T

Ω : ∀ j → I.T j
Ω j = L.Ω (L.natᴵ j)
ΨΩ : ∀ j k {a} (p : L.natᴵ j L.<ᴵ a) (σ : L.Simᴵ (L.natᴵ k) a) → I.T j
ΨΩ j k p σ = L.ψ p σ (Ω k)
good : ∀ j k {a} (p : L.natᴵ j L.<ᴵ a) (σ : L.Simᴵ (L.natᴵ k) a) → A.Gd j (ΨΩ j k p σ)
good j k p σ = Q.Ops.good (Fold.ops k) j p σ (Ω k) (proj₁ (B.Ω-model k F.zero))

mutual
  bound : ∀ j k {a} (p : L.natᴵ j L.<ᴵ a) (σ : L.Simᴵ (L.natᴵ k) a) →
    A.Gd j (ΨΩ j k p σ) → A.Le j (Ω j L.+ Ω j) (ΨΩ j k p σ)
  bound j zero p σ gx = B.lr j F.zero {X = Ω j L.+ Ω j} {a = _}
    (Add.plus-good j {X = Ω j} {Y = Ω j} (proj₁ (B.Ω-model j F.zero)) (proj₁ (B.Ω-model j F.zero)))
    (It.good j (Ω j) (proj₁ (B.Ω-model j F.zero))) 2
    (B.rfl j F.zero {X = Ω j L.+ Ω j}
      (Add.plus-good j {X = Ω j} {Y = Ω j} (proj₁ (B.Ω-model j F.zero)) (proj₁ (B.Ω-model j F.zero))))
  bound j (suc k) p σ gx with L.<ᴵ-dec (σ L.zero) p
  ... | injᵃ v with V.exact (I.finite k) v
  ... | r , refl = retained j k p σ r gx
  bound j (suc k) p σ gx | injᵇ w = diagonal j k p σ gx refl
  bound j (suc k) p σ gx | injᶜ e = diagonal j k p σ gx refl

  retained : ∀ j k {a} (p : L.natᴵ j L.<ᴵ a) (σ : L.Simᴵ (L.natᴵ (suc k)) a) (r : L.natᴵ k L.<ᴵ L.natᴵ j) →
    A.Gd j (L.limᵢ r (λ u → L.ψ p (λ q → σ (L.suc q)) (S.τ S.bwd k (L.out (L.<→◃ r) u)))) →
    A.Le j (Ω j L.+ Ω j) (L.limᵢ r (λ u → L.ψ p (λ q → σ (L.suc q)) (S.τ S.bwd k (L.out (L.<→◃ r) u))))
  retained zero k p σ () gx
  retained (suc j) k p σ r gx = D.pack (Add.plus-good (suc j) {X = Ω (suc j)} {Y = Ω (suc j)}
    (proj₁ (B.Ω-model (suc j) F.zero)) (proj₁ (B.Ω-model (suc j) F.zero))) gx
    (D.aa (D.trans (bound (suc j) k p σ′ (good (suc j) k p σ′))
      (subst (λ X → D.Le (L.ψ p σ′ (Ω k)) (L.ψ p σ′ (S.τ S.bwd k X)))
        (sym (L.out-into (L.<→◃ r) (Ω k))) raise)))
    where
    module D = A.Layer j (A.GoFam j) (A.LeFam j)
    σ′ : L.Simᴵ (L.natᴵ k) _
    σ′ q = σ (L.suc q)
    raise = Q.Ops.mono (Fold.ops k) (suc j) p p σ′ σ′ (Ω k) (S.τ S.bwd k (Ω k))
      (proj₁ (TQ.Ops.pair (T.ops k) S.bwd F.zero (Ω k) (proj₁ (B.Ω-model k F.zero))))

  diagonal : ∀ j k {a} (p : L.natᴵ j L.<ᴵ a) (σ : L.Simᴵ (L.natᴵ (suc k)) a)
    {rows : ℕ → I.T j} → A.Gd j (L.lim rows) → rows zero ≡ L.ψ p (λ q → σ (L.suc q)) (Ω k) →
    A.Le j (Ω j L.+ Ω j) (L.lim rows)
  diagonal j k p σ gx eq = B.lr j F.zero {X = Ω j L.+ Ω j} {a = _}
    (Add.plus-good j {X = Ω j} {Y = Ω j} (proj₁ (B.Ω-model j F.zero)) (proj₁ (B.Ω-model j F.zero)))
    (children j gx) 0 (subst (A.Le j (Ω j L.+ Ω j)) (sym eq)
      (bound j k p (λ q → σ (L.suc q)) (good j k p (λ q → σ (L.suc q)))))
    where
    children : ∀ j {rows : ℕ → I.T j} → A.Gd j (L.lim rows) → ∀ k → A.Gd j (rows k)
    children zero gx k = tt
    children (suc j) (A.Layer.gl gs) k = gs k

two : ∀ j k {a} (p : L.natᴵ j L.<ᴵ a) (σ : L.Simᴵ (L.natᴵ k) a) → A.Le j (Ω j L.+ Ω j) (ΨΩ j k p σ)
two j k p σ = bound j k p σ (good j k p σ)
```
