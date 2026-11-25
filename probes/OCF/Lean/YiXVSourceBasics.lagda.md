# YiXVSourceBasics
> 验收文件。档位：编译定理。有限层源模拟的坐标、构造与保持工具；未交读回值界、所有 pre n 或 Goal。
> 从 YiXVCan2Rel/Plus/Lift/Self 按有限层统一，参照侧复用 YiXVFinite*；不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVSourceBasics where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Data.Fin as F
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
import OCF.Align.Level as L
open import OCF.Align.Value using (z≼; s≼s; ≼-refl; ≼-suc; ≼-trans; l≼)
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteAdd as Add
import OCF.Lean.YiXVSourceIndex as J
import OCF.Lean.YiXVSourceFamily as U

stable : ∀ n i x X → U.UR n i x X ≡ U.U (I.rank n i) x X
stable zero F.zero x X = refl
stable zero (F.suc ()) x X
stable (suc n) F.zero x X = refl
stable (suc n) (F.suc i) x X = stable n i x X
zeroU : ∀ n → U.U n S.zero (L.Ω (L.natᴵ n))
zeroU zero = z≼
zeroU (suc n) = U.Layer.uz
sucU : ∀ n {x X} → U.U n x X → U.U n (S.suc x) (L.suc X)
sucU zero t = s≼s t
sucU (suc n) t = U.Layer.us t
weakU : ∀ n {x X Y} → U.U n x X → A.Le n X Y → U.U n x Y
weakU zero t p = ≼-trans t p
weakU (suc n) t p = U.Layer.uw t p
limU : ∀ n {g a X} → (∀ k → U.U n (g k) X) → U.U n (S.lim g a) X
limU zero t = l≼ t
limU (suc n) t = U.Layer.ul t

ΩU : ∀ n → U.U n (O.Ωt (J.nat n)) (L.Ω (L.natᴵ n) L.+ L.Ω (L.natᴵ n))
ΩU zero = ≼-suc (≼-refl (L.suc L.zero))
ΩU (suc n) = U.Layer.un F.zero (λ a X Y gx gy o ha t → U.Layer.uw
  (U.Layer.uu (proj₁ (B.Ω-model (suc n) F.zero)) U.Layer.uz (B.gs n F.zero {X = X} gx) (sucU n ha))
  (Add.mono (suc n) n {X = L.Ω (L.natᴵ (suc n))} {X′ = L.Ω (L.natᴵ (suc n))}
    (B.rfl (suc n) F.zero {X = L.Ω (L.natᴵ (suc n))} (proj₁ (B.Ω-model (suc n) F.zero)))
    (λ q → L.suc q) (L.suc X) Y t))
```
