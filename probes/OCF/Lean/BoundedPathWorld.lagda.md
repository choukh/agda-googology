# 路径进入之后的真实 KS 世界

路径 Ad V c 的方向是 V⊲c，不能把它当作当前 KS 界的 c⊲V。
本篇在 next=c 的世界给出真实可入，并通过实际 ext 搬到源指标copy。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.BoundedPathWorld where
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecLay
open import OCF.Lean.LHRecLeg using (w₀L; lw₀L; rfL)
open import OCF.Lean.BoundedFoldIf using (k; P; T)
open import OCF.Lean.ThirdPS using (PS)
open import OCF.Lean.BoundedPathMoving using (Q)
import OCF.Lean.BoundedFoldWorld as FW
import OCF.Lean.BoundedFoldIndexKeep as IK

world : HB S⊥ → Wd (T hz)
world V (inj₁ _) = tt , V
world V (inj₂ c) = w₀L (ls lz ⊕L upL lz c)

world-legal : ∀ V → LgB V → LgW (T hz) (world V)
world-legal V l (inj₁ _) = tt , l
world-legal V l (inj₂ c) = lw₀L (ls lz ⊕L upL lz c)

world-up : ∀ {V C} → V ⊲[ tt ] C → _≤w_ (T hz) (world V) (world C)
world-up p (inj₁ _) = tt , p
world-up p (inj₂ c) = rfL (ls lz ⊕L upL lz c) (w₀L (ls lz ⊕L upL lz c))

-- 从非平凡路径可入取得下一步真实合法世界与旧世界到它的路径。
admitted-next : ∀ V c → PS.Ad Q V (inj₁ tt , inj₂ tt) c →
  Bd (T hz) (inj₁ tt , inj₂ tt) c (world c)
admitted-next V c a = hself

module At (h : HB S⊥ → HB (Lv k)) where
  module K = IK.Keep k (inj₂ tt) h
  module F = FW.Relative k

  source-admitted : ∀ V c W → PS.Ad Q V (inj₁ tt , inj₂ tt) c →
    Bd K.S (inj₁ tt , inj₂ tt) c (F.ext (hΩ (inj₂ tt) h) (world c) W)
  source-admitted V c W a = K.target-bd (inj₂ tt) {v = world c} {W = W} hself

  source-legal-world : ∀ V c W → PS.Ad Q V (inj₁ tt , inj₂ tt) c → LgW K.S W →
    LgW K.S (F.ext (hΩ (inj₂ tt) h) (world c) W)
  source-legal-world V c W a lW = F.legal-ext (hΩ (inj₂ tt) h) (world-legal c (proj₂ a)) lW
```

桥不声称当前世界已经可入；只使用坐标进入后产生的合法世界。
仍需把真实折叠递归输出的 PH/支持证明接上，不能由本篇推出一般fold合法。
