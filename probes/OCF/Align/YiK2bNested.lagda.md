# K2′：含嵌套 lc 0 的闭项

本篇交合法闭项，与全 Source0 递归器的未完成义务分开。
输入是原块的 `Ω₁ +ᴸ Ω₁`：外层 lc 0 的每支是 `Ω₁ +ᴸ up 0 η`，
其中的 Ω₁ 本身仍是 lc 0。因此它确实在 Only0 中，分支并非都为 Raw 0 读回。
没有把它叫作全片段 ψ 的实例；这里独立定义这族前缀分支的折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiK2bNested where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.LevelFixCore as F
import OCF.Align.LevelFixVal as V
import OCF.Align.YiCarry as C
import OCF.Align.YiK2Base as A
open import OCF.Align.YiK2bBase
open import OCF.Align.YiRegBase using (Reg)
open import OCF.Align.YiDispBase using (one; more; e-first; e-suc)
open F using (module G)

-- 任意已认证的种子，沿可数尾部递归；证书不参与 raw 的计算。
tail : A.R → A.R → A.R
tail seed G.zero = seed
tail seed (G.suc a) = A.successor (tail seed a)
tail seed (G.lim f) = G.lim (λ n → tail seed (f n))
tail seed (G.lc () c t g)
tail seed (G.em () a)
tail seed G.top = A.successor seed

tail-positive : ∀ seed → F.Dn F.zero G.zero seed → ∀ a →
  F.Dn F.zero G.zero (tail seed a)
tail-positive seed pos G.zero = pos
tail-positive seed pos (G.suc a) = zero , inj₁ refl
tail-positive seed pos (G.lim f) = zero , inj₂ (tail-positive seed pos (f zero))
tail-positive seed pos (G.lc () c t g)
tail-positive seed pos (G.em () a)
tail-positive seed pos G.top = zero , inj₁ refl

tail-cp : ∀ seed {a b} → F.Cp F.zero a b →
  F.Cp F.zero (tail seed a) (tail seed b)
tail-dn : ∀ seed {a} b → F.Dn F.zero a b →
  F.Dn F.zero (tail seed a) (tail seed b)
tail-cp seed (inj₁ refl) = inj₁ refl
tail-cp seed {b = b} (inj₂ p) = inj₂ (tail-dn seed b p)
tail-dn seed (G.suc b) p = 1 , tail-cp seed p
tail-dn seed (G.lim f) (n , p) = n , tail-cp seed p
tail-dn seed (G.lc () c t g) p
tail-dn seed (G.em () a) p
tail-dn seed G.top ()

tail-legal : ∀ seed → F.Lgl F.zero seed → F.Dn F.zero G.zero seed →
  ∀ a → F.Lgl F.zero a → F.Lgl F.zero (tail seed a)
tail-legal seed ls pos G.zero la = ls
tail-legal seed ls pos (G.suc a) la =
  A.copies-step (tail seed a) (inj₂ (tail-positive seed pos a)) ,
  A.copies-legal (tail seed a) (tail-legal seed ls pos a la)
tail-legal seed ls pos (G.lim f) (st , lf) =
  (λ n → tail-cp seed (st n)) , (λ n → tail-legal seed ls pos (f n) (lf n))
tail-legal seed ls pos (G.lc () c t g) la
tail-legal seed ls pos (G.em () a) la
tail-legal seed ls pos G.top la =
  A.copies-step seed (inj₂ pos) , A.copies-legal seed ls

-- Ω₁ 的闭子折叠已有无条件合法性；本篇不修改它。
inner : Output
inner = output A.closed A.closed-legal (zero , inj₂ (A.positive A.one))

Ω₁-only : Only0 V.Ω₁
Ω₁-only = tt , (λ η e → read0-only η)

prefix : A.R → F.LF
prefix a = V.Ω₁ V.+ᴸ V.up F.zero a

prefix-reg : ∀ a → Reg (prefix a)
prefix-reg G.zero = C.forget C.tw2-carry
prefix-reg (G.suc a) = prefix-reg a
prefix-reg (G.lim f) = λ n → prefix-reg (f n)
prefix-reg (G.lc () c t g)
prefix-reg (G.em () a)
prefix-reg G.top = C.forget C.tw2-carry

prefix-carry : ∀ a → C.Carry (prefix a)
prefix-carry G.zero = C.tw2-carry
prefix-carry (G.suc a) = prefix-carry a
prefix-carry (G.lim f) = λ n → prefix-carry (f n)
prefix-carry (G.lc () c t g)
prefix-carry (G.em () a)
prefix-carry G.top = C.tw2-carry

prefix-legal : ∀ a → F.Lgl F.zero a → V.Legal (prefix a)
prefix-legal a la = V.Legal-add V.Ω₁ (V.up F.zero a)
  (V.Legal-tw 2) (V.lgl→Legal F.zero tt a la)

nested : F.LF
nested = V.Ω₁ V.+ᴸ V.Ω₁

nested-equation : nested ≡
  F.lc F.zero A.one (F.suc V.Ω₁) (λ η e → prefix η)
nested-equation = refl

nested-only : Only0 nested
nested-only = Ω₁-only , (λ η e → prefix-only V.Ω₁ Ω₁-only η)

nested-reg : Reg nested
nested-reg = more (more (one e-first) e-suc) e-first , tt ,
  C.forget C.tw2-carry , (λ η e → prefix-reg η)

nested-carry : C.Carry nested
nested-carry = nested-reg , tt , C.tw2-carry , (λ η e b → prefix-carry η)

nested-legal : V.Legal nested
nested-legal = V.Legal-add V.Ω₁ V.Ω₁ (V.Legal-tw 2) (V.Legal-tw 2)

nested-source : Source0
nested-source = source0 (C.source nested nested-carry nested-legal) nested-only

prefix-output : C.PointB F.zero A.one → Output
prefix-output p = output (tail (raw inner) (C.coordinate p))
  (tail-legal (raw inner) (legal inner) (positive inner)
    (C.coordinate p) (proj₁ (C.bounds p)))
  (tail-positive (raw inner) (positive inner) (C.coordinate p))

prefix-output-mono : ∀ p q → F.Gd F.zero (C.coordinate p) (C.coordinate q) →
  F.Cp F.zero (raw (prefix-output p)) (raw (prefix-output q))
prefix-output-mono p q d = tail-cp (raw inner) (proj₁ d)

module NestedChain = AddChain A.one prefix-output prefix-output-mono

initial : C.PointB F.zero A.one
initial = C.start0-B nested-carry

closed : Output
closed = NestedChain.collapse initial

closed-B : C.LglB F.zero (raw closed)
closed-B = output-B closed

closed-legal : V.Legal (V.up F.zero (raw closed))
closed-legal = output-legal closed

closed-positive : F.Dn F.zero G.zero (raw closed)
closed-positive = positive closed

closed-row : raw closed ≡ G.lim (λ n →
  tail A.closed (C.coordinate (NestedChain.chain initial n)))
closed-row = refl

closed-additive : ∀ p → C.coordinate (NestedChain.next p) ≡
  A._+ʳ_ (C.coordinate p) (tail A.closed (C.coordinate p))
closed-additive p = refl

closed-start : C.coordinate initial ≡ A.one
closed-start = refl
```

`tail-cp` 是全 Raw 0 的参数化定理，seed 不按阶段定制。
它在本例给真正的嵌套 LF 分支提供相邻输出位置；链点的 LglB 在 next 的
返回类型中由加法规则产生，增长由 `NestedChain.chain-grow` 给出。
这仍没有把任意 Only0 树都写成 prefix，不能把本例代替完整结构递归。
