# 在真实 Fold1 视图中去掉单槽更新

这是对现有代码的编译诊断，不是新 sup 折叠，不是值保持证明。
采用现有 `Vw`，直接替换 `liftL` 的坍缩分支。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.SupCollapseStay where

open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (Lv)
open import OCF.Lean.Fold1Base
open import OCF.Lean.Fold1Fold using (Vw; kp; co)
open import OCF.Lean.SupCollapseIf

stay : ∀ I F Legal → WeakUpdate I F Legal
stay I F Legal = record { update = λ i W v → W ; preserves = λ i W v lW lv → lW }

liftL-stay : ∀ {f : ℕ → Cd} {t}
  {Y : ∀ i → Wd (Lv t) → Wd (Lv (f i)) → Wd (Lv (f i))} {k κ} →
  Vw (f k) t (Y k) κ →
  Vw (hl f) t (λ v W i → Y i v (W i)) (k , κ)
liftL-stay {k = k} (kp κ′ fr a b c d) =
  kp κ′ fr (λ {v} {W} e → a {v} {W k} e)
    (λ {v} {W} e → b {v} {W k} e)
    (λ {v} {W} e → c {v} {W k} e) d
liftL-stay {k = k} (co y py to rd upd a b c d) =
  co y (hlim k py) to (λ W → rd (W k)) (λ W e → W)
    (λ {v} {W} e → a {v} {W k} e) b
    (λ lW → c (lW k)) (λ lW le → lW)
```

实际改变的是坍缩链中递归调用使用的世界，不能据此说原折叠值不变。
它也不修复不可数层号的 `Pos` 或 `extC`。若需要读回所请求的界，
必须额外证 `Readback.receives` 或一个与终点下界直接相关的替代律。
这条结果反驳“只要去掉 updAt 就能完成 sup”的推断：弱接口本来
就允许不写回，真正的值义务不在这个接口里。
