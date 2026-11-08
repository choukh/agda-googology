# 事件返回的零层观察：全部实际输出格

本篇只研究原 `EvFoldTree.drp`。零层数据没有 Ω 节点，故删除事件
不改变 `sum` 的全部基本列；这一结论不推广到 `drp₁/drp₂`，也不
允许把任意高层分支函数作用在逐形相关的坐标上。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EventReturnValueZero where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥-elim)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim)
open import OCF.Align.EvFoldTree

data Same : A → A → Set where
  sz : Same azero azero
  ss : ∀ {a b} → Same a b → Same (asuc a) (asuc b)
  sl : ∀ {f g} → (∀ n → Same (f n) (g n)) → Same (alim f) (alim g)

self : ∀ a → Same a a
self azero = sz
self (asuc a) = ss (self a)
self (alim f) = sl (λ n → self (f n))

sum-drop : ∀ {W W′ a b} → Same a b → (d : D₀ W) →
  Same (sum a d) (sum b (drp {W′ = W′} d))
partial-drop : ∀ {W W′ a b} → Same a b → (f : ℕ → D₀ W) → ∀ n →
  Same (pt a f n) (pt b (λ k → drp {W′ = W′} (f k)) n)
sum-drop p n0 = p
sum-drop p n1 = ss p
sum-drop p (x ⨾ y) = sum-drop (sum-drop p x) y
sum-drop p (nl f) = sl (partial-drop p f)
sum-drop p (ni () u)
sum-drop p (nκ () u)
sum-drop p (nε κ zz u) = ⊥-elim (ze0 κ zz)
sum-drop p (nw q d) = sum-drop p d
partial-drop p f zero = p
partial-drop p f (suc n) = sum-drop (partial-drop p f n) (f n)
```

验收只在此处把逐形关系送入既有可数树值序；两向都成立，不假设外延。

```agda
import OCF.Align.CumReadBase as V

sound : ∀ {a b} → Same a b → V.toO a V.≼ V.toO b
sound sz = V.z≼
sound (ss p) = V.s≼ (sound p)
sound (sl p) = V.l≼ (λ n → V.l≼ʳ n (sound (p n)))

reverse : ∀ {a b} → Same a b → Same b a
reverse sz = sz
reverse (ss p) = ss (reverse p)
reverse (sl p) = sl (λ n → reverse (p n))

drop-lower : ∀ {W W′} b (d : D₀ W) →
  V.toO (sum b d) V.≼ V.toO (sum b (drp {W′ = W′} d))
drop-lower b d = sound (sum-drop (self b) d)

drop-upper : ∀ {W W′} b (d : D₀ W) →
  V.toO (sum b (drp {W′ = W′} d)) V.≼ V.toO (sum b d)
drop-upper b d = sound (reverse (sum-drop (self b) d))
```
