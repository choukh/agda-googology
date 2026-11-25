# YiXVSourceNodeGrowth
> 验收文件。档位：编译定理。从参照 SC 律导出链增长与各目标输出接口。
> 按 YiXVCan2Sem、YiXVSourceAffine* 与 YiXVSourceGrowth 统一；未交实际全基底、所有 pre n、Need1 或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVSourceNodeGrowth where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans; cong; subst; subst₂)
import Data.Fin as F
import OCF.Align.Level as L
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteAdd as Add
import OCF.Lean.YiXVFiniteCanonicalInputs as Canon
import OCF.Lean.YiXVFiniteCoerce as C
import OCF.Lean.YiXVFiniteFoldInterface as Q
import OCF.Lean.YiXVFiniteFold as Fold
import OCF.Lean.YiXVFiniteFloor as Floor
import OCF.Lean.YiXVFiniteIter as It
import OCF.Lean.YiXVZeroRead as ZR
import OCF.Lean.YiXVSourceGrowthInput as Growth
import OCF.Lean.YiXVSourceIndex as J
import OCF.Lean.YiXVSourceFamily as U
import OCF.Lean.YiXVSourceBasics as UB
import OCF.Lean.YiLegOps as O
import OCF.Lean.YiXVSourceNodeEnvelope as E

module At (n : ℕ) where
  module D = A.Layer n (A.GoFam n) (A.LeFam n)
  module Frame (m H : ℕ) (q : L.natᴵ m L.<ᴵ L.natᴵ (suc n)) (ε : L.Simᴵ (L.natᴵ (suc n)) (L.natᴵ H))
    (Z : I.T H) (gz : A.Gd H Z) (f : L.U (L.natᴵ m) (L.<→◃ q) → I.T (suc n))
    (law : D.SC q f) (gb : ∀ u → D.GU q u → D.Floor q u → D.Gd (f u)) where
    module Env = E.Node (suc n) m H q ε Z f
    open Env using (qa; ca; b; P; ν₀)
    module In = Canon.At n m q
    ca-eq : ∀ Y → ca Y ≡ L.into (L.<→◃ q) Y
    ca-eq Y = cong (L.into (L.<→◃ q)) (L.out-into (L.<→◃ qa) Y)
    gd : ∀ Y → A.Gd m Y → D.GU q (ca Y)
    gd Y gy = subst (D.GU q) (sym (ca-eq Y)) (In.good-in Y gy)
    fl : ∀ Y → A.Le m (L.Ω (L.natᴵ m)) Y → D.Floor q (ca Y)
    fl Y o = subst (D.Floor q) (sym (ca-eq Y)) (In.floor-in Y o)
    rel : ∀ X Y → A.Le m X Y → D.RU q (ca X) (ca Y)
    rel X Y t = subst₂ (D.RU q) (sym (ca-eq X)) (sym (ca-eq Y)) (In.rel-in X Y t)
    next : ∀ Y → ca (L.suc Y) ≡ C.next q (ca Y)
    next Y = trans
      (sym (cong (L.coe (L.<→◃ qa) (L.<→◃ q))
        (cong (λ X → L.into (L.<→◃ qa) (L.suc X)) (L.out-into (L.<→◃ qa) Y))))
      (C.coe-next qa q (L.into (L.<→◃ qa) Y))
    high-good : ∀ Y → A.Gd m Y → A.Le m (L.Ω (L.natᴵ m)) Y → A.Gd H (b (L.into (L.<→◃ qa) Y))
    high-good Y gy o = Add.good H (suc n) {X = Z} gz ε _ (gb (ca Y) (gd Y gy) (fl Y o))
    high-mono : ∀ X Y → A.Gd m X → A.Gd m Y → A.Le m (L.Ω (L.natᴵ m)) X → A.Le m X Y →
      A.Le H (b (L.into (L.<→◃ qa) X)) (b (L.into (L.<→◃ qa) Y))
    high-mono X Y gx gy o t = Add.mono H (suc n) {X = Z} {X′ = Z} (B.rfl H F.zero {X = Z} gz) ε _ _
      (D.SC.mo law (ca X) (ca Y) (gd X gx) (gd Y gy) (fl X o) (rel X Y t))
    high-db : ∀ Y → A.Gd m Y → A.Le m (L.Ω (L.natᴵ m)) Y →
      A.Le H (L.suc (b (L.into (L.<→◃ qa) Y))) (b (L.into (L.<→◃ qa) (L.suc Y)))
    high-db Y gy o = Add.mono H (suc n) {X = Z} {X′ = Z} (B.rfl H F.zero {X = Z} gz) ε _ _
      (subst (λ u → D.Le (L.suc (f (ca Y))) (f u)) (sym (next Y)) (D.SC.db law (ca Y) (gd Y gy) (fl Y o)))
    high-po : A.Le H (L.suc Z) (b (L.into (L.<→◃ qa) (L.Ω (L.natᴵ m))))
    high-po = Add.mono H (suc n) {X = Z} {X′ = Z} (B.rfl H F.zero {X = Z} gz) ε _ _
      (subst (λ u → D.Le D.one (f u)) (sym (C.coe-start qa q)) (D.SC.po law))

    growth : Growth.Growth m P
    Growth.Growth.good growth Y gy o = Q.Ops.good (Fold.ops H) m qa (λ r → r) _ (high-good Y gy o)
    Growth.Growth.floor growth Y gy o = Floor.floor m qa (λ r → r) _ (Growth.Growth.good growth Y gy o)
    Growth.Growth.mono growth X Y gx gy o t = Q.Ops.mono (Fold.ops H) m qa qa (λ r → r) (λ r → r) _ _ (high-mono X Y gx gy o t)
    Growth.Growth.db growth Y gy o = Q.Ops.mono (Fold.ops H) m qa qa (λ r → r) (λ r → r) _ _ (high-db Y gy o)
    Growth.Growth.initial growth = B.trans m F.zero {X = L.suc (L.Ω (L.natᴵ m))} {Y = L.suc (L.ψ qa (λ r → r) Z)} {Z = P (L.Ω (L.natᴵ m))}
      (B.s≤ m F.zero {X = L.Ω (L.natᴵ m)} {Y = L.ψ qa (λ r → r) Z}
        (Floor.floor m qa (λ r → r) Z (Q.Ops.good (Fold.ops H) m qa (λ r → r) Z gz)))
      (B.trans m F.zero {X = L.suc (L.ψ qa (λ r → r) Z)} {Y = L.ψ qa (λ r → r) (L.suc Z)} {Z = P (L.Ω (L.natᴵ m))}
        (It.strict m qa (λ r → r) Z (Q.Ops.good (Fold.ops H) m qa (λ r → r) Z gz))
        (Q.Ops.mono (Fold.ops H) m qa qa (λ r → r) (λ r → r) _ _ high-po))
    output₀ : Growth.Output m 0 ν₀
    Growth.Output.good output₀ Y gy o = tt
    Growth.Output.mono output₀ X Y gx gy o t = ZR.mono H (high-mono X Y gx gy o t)
    Growth.Output.db output₀ Y gy o = ZR.mono H (high-db Y gy o)
    output : ∀ j {ambient} (pc : L.natᴵ j L.<ᴵ ambient) (ρ : L.Simᴵ (L.natᴵ H) ambient) → Growth.Output m j (Env.Target.ν j pc ρ)
    Growth.Output.good (output j pc ρ) Y gy o = Q.Ops.good (Fold.ops H) j pc ρ _ (high-good Y gy o)
    Growth.Output.mono (output j pc ρ) X Y gx gy o t = Q.Ops.mono (Fold.ops H) j pc pc ρ ρ _ _ (high-mono X Y gx gy o t)
    Growth.Output.db (output j pc ρ) Y gy o = Q.Ops.mono (Fold.ops H) j pc pc ρ ρ _ _ (high-db Y gy o)

  module Model where
    Ω = L.Ω (L.natᴵ (suc n))
    f : I.T n → I.T (suc n)
    f Y = L.add Ω (λ q → L.suc q) Y
    good : D.Gd (Ω L.+ Ω)
    good = Add.plus-good (suc n) {X = Ω} {Y = Ω} (proj₁ (B.Ω-model (suc n) F.zero)) (proj₁ (B.Ω-model (suc n) F.zero))
    law : D.SC L.zero f
    law with good
    ... | A.Layer.gn slaw gb = slaw
    body : ∀ Y → D.GU L.zero Y → D.Floor L.zero Y → D.Gd (f Y)
    body Y gy o = Add.good (suc n) n {X = Ω} (proj₁ (B.Ω-model (suc n) F.zero)) (λ q → L.suc q) Y gy
    certificate : U.U (suc n) (O.Ωt (J.nat (suc n))) (Ω L.+ Ω)
    certificate = UB.ΩU (suc n)
    module Ref = Frame n (suc (suc n)) L.zero (λ q → L.suc q) (L.Ω (L.natᴵ (suc (suc n))))
      (proj₁ (B.Ω-model (suc (suc n)) F.zero)) f law body
    actual : Growth.Growth n Ref.Env.P
    actual = Ref.growth
```
