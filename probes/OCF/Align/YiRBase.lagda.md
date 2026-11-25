# 分支相对路径：每次进入合法分支另取上下文界

本篇重写不变量，不改变旧 Inv、LF、CP 或树。
在当前结点只检查当前派发字段；进入第η支时，分支证据改用该次选择的新合法界。
不同分支返回不同界，不把它们的字段收集到同一个旧界。
旧界到新界的CP用于沿当前路径运输环境，未加入裸层号比较律。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiRBase where

open import Data.List.Base using (List)
open import Data.Unit.Base using (⊤)
open import Data.Product.Base using (Σ; _×_)
open import OCF.Align.LevelFixCore using (LF)
import OCF.Align.LevelFixCore as F
open import OCF.Align.LevelFixVal using (CP)
import OCF.Align.YiLevelBase as Y
open import OCF.Align.YiCtxBase using (Ctx; bound)

Path : Y.Level → LF → Set
Path B F.zero = ⊤
Path B (F.suc t) = Path B t
Path B (F.lim f) = ∀ n → Path B (f n)
Path B (F.lc k c t g) = CP (F.suc k) (Y.tree B) × Path B t ×
  (∀ η e → Σ Y.Level (λ B′ → CP (Y.tree B) (Y.tree B′) × Path B′ (g η e)))

record InvR (Env : List Y.Level) (current : Y.Level) : Set where
  constructor relative
  field
    context : Ctx Env
    path : Path (bound context) (Y.tree current)
open InvR public
```

Ω处的函数是在选中一个合法输入时提供那一支的新界与后续路径证据；
它不返回该支与其它分支的公共界。所有界都带Legal。
本接口暂取原Gd域，不额外限制坐标；是否还能承受γ所需的证据运输要单独验证。
特别不将旧界CP扩展下的Path单调性作为已有定理或隐藏字段。
