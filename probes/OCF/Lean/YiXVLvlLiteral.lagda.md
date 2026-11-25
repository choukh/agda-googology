# YiXVLvlLiteral
> 验收文件。档位：编译定理。复用原 lvl：第 0 层合法源树的第一位置步给参照字面前驱与 Sim。
> 按 YiLSRead.St≺/st-dn/lt≺ 与 Level.sim/<ᴵ-dec 的现有计算证明；未交可数层折叠闭包或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVLvlLiteral where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
import OCF.Lean.YiLegBlock as S
import OCF.Align.Level as L

import OCF.Lean.YiLSTw1 as T
Stable : S.Tr S.zero → Set
Stable S.zero = ⊤
Stable (S.suc x) = Stable x
Stable (S.lim f a) = ((n : ℕ) → Stable (f n)) × ((n : ℕ) → T.lvl (f n) L.<ᴵ T.lvl (f (suc n)))
Stable (S.Ω () g)
Stable (S.up x () y e)

down : ∀ {x y} → Stable y → S.zero S.⊢ x ◃ y → Stable x
down h S.◃s = h
down h (S.◃l n) = proj₁ h n
down h (S.◃w {p = ()})
down h (S.◃u x () y e)
down h (S.◃c x () e)
down h (S.◃t d e) = down (down h e) d

literal : ∀ {x y} → Stable y → S.zero S.⊢ x ◃ y → T.lvl x L.<ᴵ T.lvl y
literal h S.◃s = L.zero
literal h (S.◃l n) = L.lim (suc n) (proj₂ h n)
literal h (S.◃w {p = ()})
literal h (S.◃u x () y e)
literal h (S.◃c x () e)
literal h (S.◃t d e) = L.<ᴵ-trans (literal (down h e) d) (literal h e)

all : ∀ x → Stable x
all S.zero = tt
all (S.suc x) = all x
all (S.lim f a) = (λ n → all (f n)) , (λ n → literal (all (f (suc n))) (a n))
all (S.Ω () g)
all (S.up x () y e)

step : ∀ {x y} → S.zero S.⊢ x ◃ y → T.lvl x L.<ᴵ T.lvl y
step {y = y} d = literal (all y) d

sim : ∀ {x y} → S.zero S.⊢ x ◃ y → L.Simᴵ (T.lvl x) (T.lvl y)
sim d p = L.<ᴵ-trans p (step d)
```
