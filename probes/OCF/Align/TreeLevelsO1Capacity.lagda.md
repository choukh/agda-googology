# 路线乙 O1：对象类型容量与固定程序的值须分开

**第 4 层诊断；不交新树侧闭项。** `Cd` 是仅含零、后继、ℕ-极限的
布劳威尔树。两个已有候选的最终容器分别是 `Σ Cd LgB` 和 `A`。
下面证明：每棵 `Cd` 都可送进前者并保下界，送进后者并双向保值。
因此不能仅凭最终类型是 `Cd` 或 `A`，判定一个候选到不了 EBO。
这不否定高层读回有损的既有定理，也不提供实际折叠的 ι。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeLevelsO1Capacity where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁)
open import Relation.Nullary using (¬_)
open import OCF.Lean.CRwBase
  using (Cd; hz; hs; hl; hΩ; LgB; _⊞_)
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; s≤s; l≤; ≤l)
open import OCF.Lean.NegFold1Base using (≤ᵛ-refl; ≤ᵛ-trans)
open import OCF.Lean.NegFold1If using (¬s≤ᵛ)
import OCF.Free.LiteralCompletion as C
import OCF.Align.CumReadCF as A
open import OCF.Align.TerminalFoldAccept using (reference)

LegalObject : Set
LegalObject = Σ Cd LgB

complete : Cd → LegalObject
complete a = C.leg a , C.Lg-leg a

right-add : ∀ (a b : Cd) → b ≤ᵛ a ⊞ b
right-add a hz = z≤
right-add a (hs b) = s≤s (right-add a b)
right-add a (hl f) = l≤ (λ n → ≤l n (right-add a (f n)))
right-add a (hΩ () _)

item-sum : ∀ (f : ℕ → Cd) n → f n ≤ᵛ C.Σ₀ f n
item-sum f zero = ≤ᵛ-refl (f zero)
item-sum f (suc n) = right-add (C.Σ₀ f n) (f (suc n))

complete-lower : ∀ a → a ≤ᵛ proj₁ (complete a)
complete-lower hz = z≤
complete-lower (hs a) = s≤s (complete-lower a)
complete-lower (hl f) = l≤ (λ n → ≤l n
  (≤ᵛ-trans (complete-lower (f n)) (item-sum (λ k → C.leg (f k)) n)))
complete-lower (hΩ () _)

toA : Cd → A.A
toA hz = A.azero
toA (hs a) = A.asuc (toA a)
toA (hl f) = A.alim (λ n → toA (f n))
toA (hΩ () _)

fromA : A.A → Cd
fromA A.azero = hz
fromA (A.asuc a) = hs (fromA a)
fromA (A.alim f) = hl (λ n → fromA (f n))

round-lower : ∀ a → a ≤ᵛ fromA (toA a)
round-lower hz = z≤
round-lower (hs a) = s≤s (round-lower a)
round-lower (hl f) = l≤ (λ n → ≤l n (round-lower (f n)))
round-lower (hΩ () _)

round-upper : ∀ a → fromA (toA a) ≤ᵛ a
round-upper hz = z≤
round-upper (hs a) = s≤s (round-upper a)
round-upper (hl f) = l≤ (λ n → ≤l n (round-upper (f n)))
round-upper (hΩ () _)

legal-reference-room : Σ LegalObject (λ a → reference ≤ᵛ proj₁ a)
legal-reference-room = complete reference , complete-lower reference

A-reference-room : Σ A.A (λ a → reference ≤ᵛ fromA a)
A-reference-room = toA reference , round-lower reference

no-legal-cap : ∀ c → ¬ (∀ (a : LegalObject) → proj₁ a ≤ᵛ c)
no-legal-cap c cap = ¬s≤ᵛ c
  (≤ᵛ-trans (complete-lower (hs c)) (cap (complete (hs c))))

no-A-cap : ∀ c → ¬ (∀ (a : A.A) → fromA a ≤ᵛ c)
no-A-cap c cap = ¬s≤ᵛ c
  (≤ᵛ-trans (round-lower (hs c)) (cap (toA (hs c))))
```

以上均为全称构造/定理，不是有限样本。两个 `reference-room` 的见证
显式读 EBO 参照，只证明验收层的类型有此容量，不进入成品。
不能把见证换成 `RadicalValueNativeFinal.closed` 或 `HtFeedClosed.TΛ`
而仍使用同一证明；那个替换正是候选尚缺的值证明。
`no-legal-cap` 与 `no-A-cap` 更明确排除对容器全部元素的任意固定可数
值上界：反例由 `c + 1` 的上述像给出。实际折叠的像可能是容器的真子集，
本篇没有排除那个生成域有上界。
