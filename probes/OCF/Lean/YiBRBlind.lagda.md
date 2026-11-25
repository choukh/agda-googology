# 新旧块的逐层关系: 推导不进关系时的反例

> 编译定理 (否定, 无前提): 有第 0 层的一对树 c₁ (精简块), c₂ (F2), 不看推导时相关 (`b0 : B0 c₁ c₂`), 但塔第 1 项在这两个孩子处的证据不相关 (`blind-E`), 因为两边 ℕ 极限层号的第 0 条相邻路径由不同的推导读出 (`blind-W`); 所以 `RelE` 的 Ω 形状一项若只对 `B0` 相关的孩子陈述, 对塔第 1 项不成立. `YiBRRel` 的 `RelT` 把这一对分开 (`sep`).
> 只否定 "推导不进关系" 的写法, 不否定什么别的.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBRBlind where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
import OCF.Lean.YiLegBlock as F
import OCF.Lean.YiLegOps as F
import OCF.Lean.YiLegPath as F
open import OCF.Lean.YiBRRel
```

## 两棵树: 同一列, 第 0 步的推导不同

列是 0, ω+1, ω+2, …; 精简块一侧第 0 步经 `◃l 0`, F2 一侧经 `◃s` 再 `◃l 1`.

```agda
ωR : Tr zero
ωR = lim (iter suc zero) (λ n → ◃s)

GR : ℕ → Tr zero
GR zero    = zero
GR (suc n) = iter suc (suc ωR) n

aR : (n : ℕ) → zero ⊢ GR n ◃ GR (suc n)
aR zero    = ◃t (◃l zero) ◃s
aR (suc n) = ◃s

c₁ : Tr zero
c₁ = lim GR aR

ωF : F.Tr F.zero
ωF = F.lim (F.iter F.suc F.zero) (λ n → F.◃s)

GF : ℕ → F.Tr F.zero
GF zero    = F.zero
GF (suc n) = F.iter F.suc (F.suc ωF) n

aF : (n : ℕ) → F._⊢_◃_ F.zero (GF n) (GF (suc n))
aF zero    = F.◃t (F.◃t F.◃s (F.◃l 1)) F.◃s
aF (suc n) = F.◃s

c₂ : F.Tr F.zero
c₂ = F.lim GF aF
```

## 不看推导的关系

```agda
B0 : Tr zero → F.Tr F.zero → Set
B0 zero      F.zero       = ⊤
B0 (suc x)   (F.suc x′)   = B0 x x′
B0 (lim f _) (F.lim f′ _) = (n : ℕ) → B0 (f n) (f′ n)
B0 _         _            = ⊥

b0-iter : (n : ℕ) {x : Tr zero} {x′ : F.Tr F.zero} → B0 x x′ → B0 (iter suc x n) (F.iter F.suc x′ n)
b0-iter zero    r = r
b0-iter (suc n) r = b0-iter n r

b0 : B0 c₁ c₂
b0 zero    = tt
b0 (suc n) = b0-iter n (b0-iter 0 {suc ωR} {F.suc ωF} (λ m → b0-iter m tt))
```

## 证据不相关

塔第 1 项的孩子 c 处的证据: 精简块是 `proj₂ (Ok-tw 1) c`, F2 是 `proj₂ (proj₂ (Ev-tw 1) c)` 与 `proj₂ (Rt-tw 1) c`. 第 0 条相邻路径, 精简块读成 `inc tt (inc 0 self)`, F2 读成 `ins (inl 1 (ins self))`.

```agda
blind-W : ¬ RelW (proj₁ (proj₂ (Ok-tw 1) c₁) 0) (proj₂ (proj₂ (F.Rt-tw 1) c₂) 0)
blind-W (wincS ())

blind-E : ¬ RelE (tw 0 ⊕ ↑ (tw 0) c₁) (F.tw 0 F.⊕ F.↑ (F.tw 0) c₂)
                 (proj₂ (Ok-tw 1) c₁) (proj₂ (proj₂ (F.Ev-tw 1) c₂)) (proj₂ (F.Rt-tw 1) c₂)
blind-E (eL rr _) = blind-W (rr 0)

sep : ¬ RelT zero F.zero c₁ c₂
sep (il (_ , ra)) = no (ra 0)
  where
  no : RelD zero F.zero (aR 0) (aF 0) → ⊥
  no (dt (() , _))
```
