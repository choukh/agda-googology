# 两份合法证之间的规范坐标运输

验收专用。两端是同一原Cd高度B，低层坐标按B的结构匹配；
不比较裸层号，不要求LgB证明相等。只要求canonical读回的运输，
不顺带量化任意ambient映射。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableTypedProofIf where
open import Data.Product using (proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; oo)
import OCF.Align.Level as L
open import OCF.Align.GeneralOmegaCountableTypedHeight using (height; height-shape)
open import OCF.Align.GeneralOmegaCountableTypedIf

self-height : ∀ (B : Cd) → Same B B
self-height hz = zz
self-height (hs B) = ss (self-height B)
self-height (hl f) = ll (λ n → self-height (f n))
self-height (hΩ () f)

proof-shape : ∀ B l₁ l₂ → height B l₁ L.≅ᴵ height B l₂
proof-shape B l₁ l₂ = height-shape (self-height B) l₁ l₂

record CanonicalProofTransport : Set₁ where
  field
    transport : ∀ B l₁ l₂ {x e} → Read B l₂ (canonical B l₂) x e →
      Read B l₁ (canonical B l₁) (L.tr⁻ (proof-shape B l₁ l₂) x) e
```

记录本身尚未实填。原全B地板已有Read实例；本轮须检验运输实际
作用于这些实例，并保留原tr⁻及异坐标分支证书，不将高层Same当同余。
