# 合法树层号的内部四形视图

每个子对象仍是 Level，原树投影逐构造子一致；只打包已有合法性，
不识别两份证明，也不比较两个函数。Ω 分支的低层对象还可读成合法层号，
这一步读的是树，不是有限记号。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiLevelView where

open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Align.LevelFixCore using (LF; Raw; Gd; Lgl)
import OCF.Align.LevelFixCore as F
open import OCF.Align.LevelFixVal using (CP)
import OCF.Align.LevelFixVal as V
open import OCF.Align.YiLevelBase

data View : LF → Set where
  vzero : View F.zero
  vsuc : (x : Level) → View (tree (suc x))
  vlim : (f : ℕ → Level)
    (step : ∀ n → CP (tree (f n)) (tree (f (Data.Nat.Base.suc n)))) →
    View (tree (lim f step))
  vnode : (k : Level) (c : Raw (tree k)) (t : Level)
    (g : (η : Raw (tree k)) → Gd (tree k) c η → Level)
    (first : ∀ η e → CP (tree t) (tree (g η e)))
    (mono : ∀ η e η′ e′ → Gd (tree k) η η′ → CP (tree (g η e)) (tree (g η′ e′)))
    (same : ∀ η e e′ → tree (g η e) ≡ tree (g η e′)) →
    View (tree (node k c t g first mono same))

view : (x : Level) → View (tree x)
view (level F.zero lawful) = vzero
view (level (F.suc x) lawful) = vsuc (level x lawful)
view (level (F.lim f) (step , lawful)) = vlim (λ n → level (f n) (lawful n)) step
view (level (F.lc k c t g) (lk , first , mono , same , lt , lg)) =
  vnode (level k lk) c (level t lt) (λ η e → level (g η e) (lg η e)) first mono same

read-low : (k : Level) (η : Raw (tree k)) → Lgl (tree k) η → Level
read-low k η lawful = level (V.up (tree k) η) (V.lgl→Legal (tree k) (legal k) η lawful)

coordinate : (k : Level) (c η : Raw (tree k)) → Gd (tree k) c η → Level
coordinate k c η e = read-low k η (proj₂ e)

omega-coordinate : (k : Level) (c η : Raw (tree k)) → Gd (tree k) c η → Level
omega-coordinate k c η e = Ω (coordinate k c η e)
```

这里的 View 是原树投影的精确形状陈述，不是记号 Lab，也没有新增阶段字段。
read-low／omega-coordinate 对全部层号一条；它们不把高层值送入固定的 HB 类型。
尚未定义成品的序数值解释，不能把本篇算作终点值证明或完整派发的位置生成。
