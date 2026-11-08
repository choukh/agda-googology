# 原生二元 max 的前驱包含边界

严格使用提出的递归方程。两个输入是同一棵合法的值 1 树；
合并增加了一层退化极限，故不能保证原树前驱包含于输出。
此处不否定输出合法性或序数值上的 max 性质，也不否定其他完成方法。

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.RadicalNegJoin where
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import OCF.Free.Level

join : Ordᶜ zero → Ordᶜ zero → Ordᶜ zero
join zero b = b
join (suc a) zero = suc a
join (suc a) (suc b) = suc (join a b)
join (suc a) (lim g) = lim (λ n → join (suc a) (g n))
join (suc a) (limᵢ () g)
join (suc a) (up () b)
join (lim f) b = lim (λ n → join (f n) b)
join (limᵢ () f) b
join (up () a) b

e : Ordᶜ zero
e = lim (λ _ → zero)
a : Ordᶜ zero
a = suc e

legal-e : HS e
legal-e = hl (λ _ → hz) (λ _ ())
legal-a : HS a
legal-a = hs legal-e

no-self : ¬ (e ≺ e)
no-self (≺l n ())

no-inclusion : ¬ (a ⊑⁰ join a a)
no-inclusion p with p (≺z (≅-refl⁰ e))
... | ≺z (l≅ h) with h 0
... | ()
no-inclusion p | ≺s (≺l n q) = no-self q

LeftIncludes : Set
LeftIncludes = ∀ x y → HS x → HS y → x ⊑⁰ join x y

RightIncludes : Set
RightIncludes = ∀ x y → HS x → HS y → y ⊑⁰ join x y

no-left : ¬ LeftIncludes
no-left f = no-inclusion (f a a legal-a legal-a)
no-right : ¬ RightIncludes
no-right f = no-inclusion (f a a legal-a legal-a)
```
