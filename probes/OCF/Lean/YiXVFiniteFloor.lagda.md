# YiXVFiniteFloor
> 验收文件。档位：编译定理。有限层参照侧的统一比较工具；尚无所有 pre n 或 Goal。
> 证明参照 YiOverOps 与 YiXVCan2* 并按有限层统一，不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVFiniteFloor where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (proj₁)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
import Data.Fin as F
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼l)
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteInputs as In

floor : ∀ j {k a} (p : L.natᴵ j L.<ᴵ a) (σ : L.Simᴵ k a) (x : L.Ordᶜ k) →
  A.Gd j (L.ψ p σ x) → A.Le j (L.Ω (L.natᴵ j)) (L.ψ p σ x)
floor zero p σ L.zero gx = ≼-refl _
floor zero p σ (L.suc x) gx = ≼l 1 (floor zero p σ x tt)
floor zero p σ (L.lim b) gx = ≼l 0 (floor zero p σ (b 0) tt)
floor zero p σ (L.limᵢ q b) gx with L.<ᴵ-dec (σ q) p
... | injᵃ (L.via e ())
... | injᵇ w = ≼l 0 (floor zero p σ (b (L.into (L.<→◃ q) (L.Ω _))) tt)
... | injᶜ e = ≼l 0 (floor zero p σ (b (L.into (L.<→◃ q) (L.Ω _))) tt)
floor zero p σ (L.up L.zero x) gx = floor zero p (λ q → σ (L.suc q)) x gx
floor zero p σ (L.up (L.self n) x) gx = floor zero p (λ q → σ (L.lim n q)) x gx
floor (suc j) p σ L.zero gx = D.refl (proj₁ (B.Ω-model (suc j) F.zero))
  where module D = A.Layer j (A.GoFam j) (A.LeFam j)
floor (suc j) p σ (L.suc x) (A.Layer.gl gb) = D.pack (proj₁ (B.Ω-model (suc j) F.zero)) (D.gl gb)
  (D.lr 1 (floor (suc j) p σ x (gb 1)))
  where module D = A.Layer j (A.GoFam j) (A.LeFam j)
floor (suc j) p σ (L.lim b) (A.Layer.gl gb) = D.pack (proj₁ (B.Ω-model (suc j) F.zero)) (D.gl gb)
  (D.lr 0 (floor (suc j) p σ (b 0) (gb 0)))
  where module D = A.Layer j (A.GoFam j) (A.LeFam j)
floor (suc j) p σ (L.limᵢ q b) gx with L.<ᴵ-dec (σ q) p
... | injᵃ (L.via e r) with gx
... | A.Layer.gn law gb = D.pack (proj₁ (B.Ω-model (suc j) F.zero)) (D.gn law gb)
  (D.aa (floor (suc j) p σ (b (L.into (L.<→◃ q) (L.tr⁻ e (L.out (L.<→◃ r) (D.start r)))))
    (gb (D.start r) (In.At.good-start j r) (In.At.floor-start j r))))
  where module D = A.Layer j (A.GoFam j) (A.LeFam j)
floor (suc j) p σ (L.limᵢ q b) gx | injᵇ w with gx
... | A.Layer.gl gb = D.pack (proj₁ (B.Ω-model (suc j) F.zero)) (D.gl gb)
  (D.lr 0 (floor (suc j) p σ (b (L.into (L.<→◃ q) (L.Ω _))) (gb 0)))
  where module D = A.Layer j (A.GoFam j) (A.LeFam j)
floor (suc j) p σ (L.limᵢ q b) gx | injᶜ e with gx
... | A.Layer.gl gb = D.pack (proj₁ (B.Ω-model (suc j) F.zero)) (D.gl gb)
  (D.lr 0 (floor (suc j) p σ (b (L.into (L.<→◃ q) (L.Ω _))) (gb 0)))
  where module D = A.Layer j (A.GoFam j) (A.LeFam j)
floor (suc j) p σ (L.up L.zero x) gx = floor (suc j) p (λ q → σ (L.suc q)) x gx
floor (suc j) p σ (L.up (L.self n) x) gx = floor (suc j) p (λ q → σ (L.lim n q)) x gx

actual : ∀ j → A.Le j (L.Ω (L.natᴵ j)) (L.ψ L.zero (λ q → L.suc q) (L.zero {ℓ = L.natᴵ j}))
actual j = floor j L.zero (λ q → L.suc q) L.zero (proj₁ (B.Ω-model j F.zero))
```
