# 原全参数纯读取进入新累计解释的值下界

已有异族关系允许保留整个高阶反馈后得到普通树。本篇对其全部零目标
输出证明新累计解释不低于原普通树；不是截取参数零或有限层样本。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TotalValuePureLower where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Ordˢ; toZ)
open import OCF.Align.OrdLabZPrefix using (_~_; z~; s~; l~; lᵢ~; upˡ; upʳ)
import OCF.Free.TotalOrbitBuild as A
import OCF.Free.TotalOrbitRun as R
open import OCF.Align.ValueJudgeBase

right-add : ∀ c a → A.read a ≼ A.read (R.add c a)
right-add c zero = z≼
right-add c (suc a) = s≼s (right-add c a)
right-add c (lim f st) = l≼ (λ n → ≼l n (right-add c (f n)))

part : ∀ (f : ℕ → Ordᴵ) n → A.read (f n) ≼ A.read (R.sum f n)
part f zero = ≼-refl _
part f (suc n) = right-add (R.sum f n) (f (suc n))

pure-lower : ∀ {ℓ} {x : Ordˢ zero} {y : Ordᶜ ℓ} → x ~ y → y ≼ A.read (R.run (toZ x))
pure-lower z~ = z≼
pure-lower (s~ p) = s≼s (pure-lower p)
pure-lower (l~ {f = f} p) = l≼ (λ n → ≼l n
  (≼-trans (pure-lower (p n)) (part (λ k → R.run (toZ (f k))) n)))
pure-lower (lᵢ~ {p = ()} e h)
pure-lower (upˡ {r = ()} p)
pure-lower (upʳ {r = zero} p) = u≼ (pure-lower p)
pure-lower (upʳ {r = self n} p) = u≼ (pure-lower p)
```
