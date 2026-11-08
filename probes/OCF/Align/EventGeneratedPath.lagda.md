# 动态层的同世界节点运输

Shape 不被当作层的命题相等。每个原路径递归产生目标路径和低层 Shape；
Ω 步保留同一个 raw 坐标及同一个 Bd 证据。双方在同一实际世界，
不比较裸高度，不识别不同路径或不同 Shape 证明。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EventGeneratedPath where
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import OCF.Align.HtTowerTy
open import OCF.Align.EvFoldTree
open import OCF.Align.EventReturnCodeIf using (Shape; sz; ss; sl; so)

reverse : ∀ {S} {a b : HB S} → Shape a b → Shape b a
reverse sz = sz
reverse (ss p) = ss (reverse p)
reverse (sl p) = sl (λ n → reverse (p n))
reverse (so p) = so (λ c → reverse (p c))

move : ∀ {S W a b k} → Shape {S} a b → k ⊲[ W ] a →
       Σ (HB S) (λ k′ → Shape k k′ × (k′ ⊲[ W ] b))
move p hself = _ , p , hself
move (ss p) (hsuc q) with move p q
... | k , r , q′ = k , r , hsuc q′
move (sl p) (hlim n q) with move (p n) q
... | k , r , q′ = k , r , hlim n q′
move (so p) (hLim {c = c} e q) with move (p c) q
... | k , r , q′ = k , r , hLim e q′

node : ∀ {W L L′ k} → Shape L L′ → StH W k L →
       Σ Ht (λ k′ → Shape k k′ × StH W k′ L′)
node (ss p) (ss q) with move p q
... | k , r , q′ = k , r , ss q′
node (sl p) (sl n q) with move (p n) q
... | k , r , q′ = k , r , sl n q′
node (so p) (sL {c = c} e q) with move (p c) q
... | k , r , q′ = k , r , sL e q′

-- 运输给定的可达证明；不是依靠所有层另有 accL 而替换它。
accessible : ∀ {L L′} → Shape L L′ → AccY L → AccY L′
accessible p (acc f) = acc λ r → descend (node (reverse p) r)
  where
  descend : ∀ {W k} → Σ Ht (λ k′ → Shape k k′ × StH W k′ _) → AccY k
  descend (_ , q , r) = accessible (reverse q) (f r)
```

两个方向分别使用 `p` 和 `reverse p`，没有断言往返是字面恒等。
此处仍不构造 D L → D L′：高阶 ni 的低坐标需逆向运输、回调需显式
关系保持，不能从本节点路径定理自动获得数据或 Run 的自然性。
