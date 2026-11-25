# 字面第一位置：合法公共界存在性的精确化简

本篇只用树侧接口。两个合法层号有同一个合法 CP 公共界，当且仅当
它们本身沿 CP 可比：正向使用有界比较，反向取两者中较大的合法层号。
不引入世界更新，不比较合法性证明，也不读记号码。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiSpineCommon where

open import Data.Product.Base using (Σ; _×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import OCF.Align.LevelFixVal using (CP; self)
open import OCF.Align.YiLevelBase using (Level; tree; legal)
open import OCF.Align.YiLevelCompare using (compare)

Common : Level → Level → Set
Common a b = Σ Level (λ bound → CP (tree a) (tree bound) × CP (tree b) (tree bound))

Spinal : Level → Level → Set
Spinal a b = CP (tree a) (tree b) ⊎ CP (tree b) (tree a)

common→spinal : ∀ {a b} → Common a b → Spinal a b
common→spinal (bound , pa , pb) = compare (tree bound) pa pb (legal bound)

spinal→common : ∀ {a b} → Spinal a b → Common a b
spinal→common {a} {b} (inj₁ ab) = b , ab , self
spinal→common {a} {b} (inj₂ ba) = a , self , ba
```

因此，如果某两个具体层号的两种 CP 方向都已被排除，仅另换一个
更大的合法 CP 公共界也不能修补这对原树。改变具体树的前缀或位置域
属于另外的构造义务；上述等价并未否定那些方案。
