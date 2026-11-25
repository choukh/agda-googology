# YiXVReadRouteInput
> 验收文件。档位：编译定理。原层间路径的实际读回证据 Route，含原 wh 的零、一层与自然极限完整实例。
> 从 SourceWorld*/ReadAffineLift 推广，树、原折叠与 UR 未改；未交自然极限跨分支和节点的完整世界输出、原 n=2 读回界或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadRouteInput where
open import Data.Nat using (ℕ; zero; suc)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegPath as Path
import OCF.Lean.YiLSTw1 as T
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadOmegaInput as Ω

data Route : ∀ (top y : S.Tr S.zero) → J.ℓ y Path.≤ J.ℓ top → Set where
  here : ∀ {r : S.Tr S.zero} → Route r r Path.self
  ins : ∀ {r y : S.Tr S.zero} {v : J.ℓ y Path.≤ J.ℓ r} → Route r y v → Route (S.suc r) y (Path.ins v)
  inl : ∀ {f : ℕ → S.Tr S.zero} {d : ∀ n → S.zero S.⊢ f n ◃ f (suc n)}
    {y : S.Tr S.zero} n {v : J.ℓ y Path.≤ J.ℓ (f n)} → Route (f n) y v → Route (S.lim f d) y (Path.inl n v)
  inlu : ∀ {f : ℕ → S.Tr S.zero} {d : ∀ n → S.zero S.⊢ f n ◃ f (suc n)}
    {y : S.Tr S.zero} {vs : ∀ n → J.ℓ y Path.≤ J.ℓ (f n)} →
    (∀ n → Route (f n) y (vs n)) → Route (S.lim f d) y (Path.inlu vs)

model₀ : Route S.zero S.zero (T.wh S.zero)
model₀ = here
model₁ : Route (S.suc S.zero) S.zero (T.wh (S.suc S.zero))
model₁ = ins here
finite : ∀ n → Route (Ω.nat n) S.zero (T.wh (Ω.nat n))
finite zero = model₀
finite (suc n) = ins (finite n)
model-ω : Route Ω.ω S.zero (T.wh Ω.ω)
model-ω = inlu finite
```
