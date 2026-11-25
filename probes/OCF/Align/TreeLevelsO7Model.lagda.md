# TreeLevels O7：三路接口的相对模型

本篇只检查 `ThreeEquations` 没有因等式选择而偷偷自相矛盾。
若提供每对 `Ordᴵ` 层号切口的判定，则可以逐树结构定义一个总函数，
使该接口的三条输出等式同时成立。不假定三歧性，也不假定不可比输入
具有某一条比较证据：不可比输入在“非保留”支按链处理。

`Cuts` 虽然显式接收 `Common`，但后者只是主篇 raw 扩张签名的共同
作用域证据，对任意 `i,j` 都有 `common i j`。它没有连接到实际合法
高层树的第一位置，不能称作某个现有候选的“合法公共界内切口判定”。
`Layer` 与 `TΩ+1.nodeΩ+1` 的分支域 `TΩ` 之间的桥也仍未证。

判定本身是强前提，本篇既不构造它，也不把这个相对模型算作乙线成品。
在经典的集合模型中可按排中选取这些判定，因此这是接口可满足性的
相对说明，不是从三个非空触发域推断完整接口非空。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeLevelsO7Model where

open import Data.Nat using (ℕ)
import Data.Nat as N
open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.Level as L
open import OCF.Align.TreeLevelsO7

Cuts : Set
Cuts = ∀ i j → Common i j → Dec (j L.≺ᴵ i)

fold : Cuts → Fold
fold d i z = L.Ω i
fold d i (s a) = L.lim (iter (fold d i a L.+_) L.zero)
fold d i (l f) = L.lim (λ n → fold d i (f n))
fold d i (node j b f) with d i j (common i j)
... | yes (L.via e p) = L.limᵢ p
  (λ y → fold d i (f (L.tr⁻ e (L.out (L.<→◃ p) y))))
... | no np = L.lim (λ n → fold d i
  (f (iter (λ x → fold d j (f x)) (L.Ω j) n)))
fold d i (nodeΩ+1 f) = L.Ω i

fold-keep : ∀ d i j → Common i j → (f : L.Ordᶜ j → TΩ+1) → j L.≺ᴵ i →
  Σ[ j′ ∈ L.Ordᴵ ] Σ[ e ∈ j L.≅ᴵ j′ ] Σ[ p ∈ j′ L.<ᴵ i ]
    fold d i (at j f) ≡ L.limᵢ p
      (λ y → fold d i (f (L.tr⁻ e (L.out (L.<→◃ p) y))))
fold-keep d i j b f p with d i j (common i j)
... | yes (L.via e q) = _ , e , q , refl
... | no np = ⊥-elim (np p)

fold-same : ∀ d i j → Common i j → (f : L.Ordᶜ j → TΩ+1) → j L.≅ᴵ i →
  fold d i (at j f) ≡ chain (fold d) i j f
fold-same d i j b f e with d i j (common i j)
... | yes p = ⊥-elim (L.≺ᴵ-irrefl (L.≺ᴵ-respˡ (L.≅ᴵ-sym e) p))
... | no np = chain-eq
  where
  chain-eq : L.lim (λ n → fold d i (f (iter (λ x → fold d j (f x)) (L.Ω j) n))) ≡ chain (fold d) i j f
  chain-eq = refl

fold-above : ∀ d i j → Common i j → (f : L.Ordᶜ j → TΩ+1) → i L.≺ᴵ j →
  fold d i (at j f) ≡ chain (fold d) i j f
fold-above d i j b f p with d i j (common i j)
... | yes q = ⊥-elim (L.≺ᴵ-irrefl (L.≺ᴵ-trans p q))
... | no np = refl

cuts→equations : Cuts → ThreeEquations
cuts→equations d = record
  { F = fold d
  ; keep = fold-keep d
  ; same = fold-same d
  ; above = fold-above d
  }
```

顶层 Ω 结点的分支在这里没有给 BTBO 方程，任取 `Ω i`；主篇的接口
也没有要求这一条。因此相对模型只认证主篇写出的三路接口。对完整的
更高层折叠，须先给出主篇列明的作用域、合法性、内部 View 及方程桥，
才能提取这里的接口；本篇没有实现这些桥，不声称任何候选已经实例化。
O7 仍是部分完成：raw 接口的条件定理与相对模型已编译，实际候选的
合法公共界连接未证。
