# 直接把已内置合法性的树作为最终树

`Ordᴵ` 虽有历史名字“层号”，其定义就是零、后继、带 `⊑ᴵ` 步进的
ℕ-极限。新解释器已经生成它。本篇测试直接保留这一表示的 View
与 FGH；所有分支仍是同一类型。

重要限制：`⊑ᴵ` 是模同形的前驱包含，不是纲领所需的字面第一位置。
因此这里的 View 只按原类型的较弱步进口径，尚不构成成品内部 View
验收；不能以少做一次表示转换为由略过这项差别。

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Free.NativeBrouwer where

open import Data.Nat using (ℕ; zero; suc)
open import OCF.Free.Level using (Ordᴵ; zero; suc; lim; _⊑ᴵ_)

data View : Ordᴵ → Set where
  vz : View zero
  vs : (a : Ordᴵ) → View (suc a)
  vl : (f : ℕ → Ordᴵ) (st : ∀ n → f n ⊑ᴵ f (suc n)) → View (lim f st)

view : ∀ a → View a
view zero = vz
view (suc a) = vs a
view (lim f st) = vl f st

iterate : (ℕ → ℕ) → ℕ → ℕ → ℕ
iterate f a zero = a
iterate f a (suc n) = f (iterate f a n)

FGH : Ordᴵ → ℕ → ℕ
FGH zero n = suc n
FGH (suc a) n = iterate (FGH a) n n
FGH (lim f st) n = FGH (f n) n
```

View 的构造子索引与原构造子字面一致，值上的两向对应由自反性给出；
不增加规整性假设，不要求相邻项按值严格递增，也不要求全局三歧。
具体反差为 `lim (λ _ → zero) _ ⊑ᴵ zero` 可以成立，却不是其字面子位置。
