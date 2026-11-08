# 稳定树的世界搬运会遗忘低坐标

本例否定的仅是：稳定树的搬运可按逐支互模拟消去。
两棵树分支都不读证据，抬升后互模拟，抬升前不互模拟。
不声称它们序数值不同，不否定其他下降或折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.WorldObstructionLift where

open import Data.Empty using (⊥)
open import OCF.Lean.Fab6Base using (Cd; hz; hs; hl; _⊲_; hself; hsuc)
open import OCF.Lean.NegFab6Idx
open import OCF.Lean.WorldCompose
open import OCF.Lean.WorldStable

spike : (e : Cd) → hz ⊲ e → W (hs e)
spike hz p = ws wz
spike (hs e) p = wz
spike (hl f) p = wz

low flat : W hz
low = wn spike
flat = wn (λ e p → wz)

stable-low : Stable low
stable-low = stn children uniform
  where
  children : ∀ e p → Stable (spike e p)
  children hz p = sts stz
  children (hs e) p = stz
  children (hl f) p = stz
  uniform : ∀ e p q → spike e p ≈ spike e q
  uniform hz p q = s≈ z≈
  uniform (hs e) p q = z≈
  uniform (hl f) p q = z≈

stable-flat : Stable flat
stable-flat = stn (λ e p → stz) (λ e p q → z≈)

rise : hz ⊲ hs hz
rise = hsuc hself

lift-collision : lift rise low ≈ lift rise flat
lift-collision = n≈ agree
  where
  agree : ∀ e p → spike e (OCF.Lean.Fab6Base.⊲ᴮ-tr rise p) ≈ wz
  agree hz ()
  agree (hs e) p = z≈
  agree (hl f) p = z≈

low-not-flat : low ≈ flat → ⊥
low-not-flat (n≈ f) with f hz hself
... | ()

no-stable-cancel :
  (∀ {a b : W hz} → Stable a → Stable b →
    lift rise a ≈ lift rise b → a ≈ b) → ⊥
no-stable-cancel cancel = low-not-flat (cancel stable-low stable-flat lift-collision)
```

前提实例已全部列出；上抬证据是 `rise`，比较都在同一个目标世界。
翻译账：无新树构造子，反例只读坐标的零/非零形状，不读记号。
