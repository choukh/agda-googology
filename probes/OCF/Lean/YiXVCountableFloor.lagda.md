# YiXVCountableFloor
> 验收文件。档位：编译定理。原折叠只要输出辅助合法，就有目标 Ω 下界。
> 按 YiXVFiniteFold*/FiniteChain/FiniteGamma 推广，搬运与节点比较复用 Countable 接口；未交外层源链上界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVCountableFloor where
open import Data.Product using (proj₁)
import OCF.Align.Level as L
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableOmega as O

floor : ∀ {κ ν a} (p : ν L.<ᴵ a) (σ : L.Simᴵ κ a) (X : L.Ordᶜ κ) →
  A.Gd (L.ψ p σ X) → A.Le (L.Ω ν) (L.ψ p σ X)
floor {ν = ν} p σ L.zero gx = A.Layer.rfl ν A.Gd< A.Le< (proj₁ (O.model ν))
floor {ν = ν} p σ (L.suc X) (A.Layer.gl gb) =
  A.Layer.pack (proj₁ (O.model ν)) (A.Layer.gl gb) (A.Layer.lr 1 (floor p σ X (gb 1)))
floor {ν = ν} p σ (L.lim f) (A.Layer.gl gb) =
  A.Layer.pack (proj₁ (O.model ν)) (A.Layer.gl gb) (A.Layer.lr 0 (floor p σ (f 0) (gb 0)))
floor {ν = ν} p σ (L.limᵢ q f) gx with L.<ᴵ-dec (σ q) p
... | injᵃ (L.via {a′ = j} e r) with gx
... | A.Layer.gn ex law gb =
  A.Layer.pack (proj₁ (O.model ν)) (A.Layer.gn ex law gb)
    (A.Layer.aa (floor p σ (f (L.into (L.<→◃ q) (L.tr⁻ e (L.out (L.<→◃ r) (L.into (L.<→◃ r) (L.Ω j))))))
      (gb (L.Ω j) (A.good-in (L.<→◃ r) (proj₁ (O.model j)))
        (A.le-in (L.<→◃ r) (A.Layer.rfl j A.Gd< A.Le< (proj₁ (O.model j)))))))
floor {ν = ν} p σ (L.limᵢ q f) gx | injᵇ w with gx
... | A.Layer.gl gb =
  A.Layer.pack (proj₁ (O.model ν)) (A.Layer.gl gb)
    (A.Layer.lr 0 (floor p σ (f (L.into (L.<→◃ q) (L.Ω _))) (gb 0)))
floor {ν = ν} p σ (L.limᵢ q f) gx | injᶜ e with gx
... | A.Layer.gl gb =
  A.Layer.pack (proj₁ (O.model ν)) (A.Layer.gl gb)
    (A.Layer.lr 0 (floor p σ (f (L.into (L.<→◃ q) (L.Ω _))) (gb 0)))
floor p σ (L.up L.zero X) gx = floor p (λ q → σ (L.suc q)) X gx
floor p σ (L.up (L.self n) X) gx = floor p (λ q → σ (L.lim n q)) X gx

actual : A.Le (L.Ω L.ωᴵ) (L.ψ L.zero (λ q → L.suc q) (L.zero {ℓ = L.ωᴵ}))
actual = floor L.zero (λ q → L.suc q) L.zero (proj₁ (O.model L.ωᴵ))
```
