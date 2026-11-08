# 两份真实反馈的异族模拟

分类证书明确保留same和above的原低层高度及路径；迭代对关系
递归而不是对高层Same递归。完整观察保持暂以Classification为参数，
实际全n验收须在后篇填入原分类器的实例。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableFiniteRun where
open import OCF.Lean.CRwBase
import OCF.Lean.GeneralOmegaCountableObserveIf as C
import OCF.Lean.GeneralOmegaCountableObserveRun as CR
import OCF.Lean.GeneralOmegaFiniteObserveIf as F
import OCF.Lean.GeneralOmegaFiniteObserveRun as FR
open import OCF.Lean.GeneralOmegaCountableObserveClass using (num; num-legal)
open import OCF.Align.GeneralOmegaCountableFiniteRel
open import OCF.Align.GeneralOmegaCountableFiniteIf

node-rel : ∀ {n m A A′} {p : F.Within n m} {pt : num m ⊲ num n}
  {Q : A → A′ → Set} {v w} → Match p pt Q v w →
  (rec : ∀ r → r ⊲ num n → A → HB (C.F r)) →
  (rec′ : ∀ k → F.Within n k → A′ → HB (F.F k)) →
  (∀ k (q : F.Within n k) (pk : num k ⊲ num n) {a b} → Q a b →
    Rel k (rec (num k) pk a) (rec′ k q b)) →
  Rel m (C.node pt v rec) (F.node p w rec′)
node-rel {m = m} {p = p} {pt} (kept k good) rec rec′ rel =
  ro k (λ q → rel m p pt (good q))
node-rel {m = m} {p = p} {pt} (same {q = q} good) rec rec′ rel =
  rl (λ i → rel m p pt (good
    (iterate-rel (λ r → rel m q pt (good r)) (floor-rel m) i)))
node-rel {m = m} {p = p} {pt} (above {k = k} {pr = pr} {q = q} good) rec rec′ rel =
  rl (λ i → rel m p pt (good
    (iterate-rel (λ r → rel k q (⊲ᴮ-tr (hsuc hself) pr) (good r)) (floor-rel k) i)))

module Bridge (classification : Classification) where
  open Classification classification
  observe-rel : ∀ {n m a b} (p : F.Within n m) (pt : num m ⊲ num n) → Rel n a b →
    Rel m (CR.observe (num n) (num-legal n) (num m) pt a) (FR.observe p b)
  observe-rel {m = m} p pt rz = floor-rel m
  observe-rel p pt (rs r) = rl (left-rel (observe-rel p pt r))
  observe-rel p pt (rl r) = rl (λ i → observe-rel p pt (r i))
  observe-rel {n} p pt (ro {f = f} {g} k r) = node-rel (matched p pt k)
    (λ t qt e → CR.observe (num n) (num-legal n) t qt (f e))
    (λ t qt e → FR.observe qt (g e))
    (λ t qt pr e → observe-rel qt pr (r e))
```

递归只用原源子树，保持Countable原above回灌路径；目标0时可以由
zero-same取可数结构对应。尚未在此独立声称classify/view全族已配对。
