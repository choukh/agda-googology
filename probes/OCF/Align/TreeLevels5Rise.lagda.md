# 第五轮：保留原内外状态的 riseΩ 方程

**编译过的运算方程；不是实际单点 Cp 的解。** 源层固定为原 toU Λ，
位置 r 固定为原 lim 2 (fst zero)，没有修改原 Fold。At 保留执行到这个
节点时的输入地板 π、输出地板 ρ、原状态 st 和原分支 h。

对每组这些原参数，rise-equation 逐字展开原 ψ / riseΩ：trim 的返回值
M 原样保留；内层的 tp r tt 与 stChain、外层的 tn 0 与 stBody 不相认。
这个等式没有未知的比较律或合法性前提；例如 π / ρ 取 tz、st 取空函数、
h 取常值原 o0 就给参数实例。这个实例只认证方程非空，不是实际种子。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeLevels5Rise where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.LevelNoKU using (module U; toU)
open import OCF.Align.LevelFixVal using (Λ)
import OCF.Align.LevelNoKFold as O
open import OCF.Align.TreeLevelsO1Native using (module Initial)
module P = Initial
C : U.LG
C = toU Λ
r : U.zero U.< C
r = U.lim 2 (U.fst U.zero)
module At {π ρ : U.Fl} (st : P.St U.∅ ρ π)
  (h : ∀ ξ → O.O U.zero ξ → O.O C (ξ U.∪ π)) where
  module _ (M : P.Tr π st) where
    ξ : U.Fl
    ξ = P.ξᵗ M
    inner-state : P.St U.∅ ξ (ξ U.∪ π)
    inner-state = P.stChain ξ (P.bkᵗ M) (P.wkᵗ M) st
    outer-state : P.St U.∅ ρ (ξ U.∪ π)
    outer-state = P.stBody ξ (P.wkᵗ M) st
    inner : O.O U.zero ξ → O.O U.zero ξ
    inner z = P.ψ U.∅ (P.tp r tt) inner-state (h ξ z)
    outer : O.O U.zero ξ → O.O U.zero ρ
    outer z = P.ψ U.∅ (P.tn 0) outer-state (h ξ z)
    chain : ℕ → O.O U.zero ξ
    chain = P.chainᵒ {k = U.zero} tt inner
    chain-zero : chain 0 ≡ O.TT.owk {π = U.tz} {ρ = ξ} (λ ()) (O.TT.os O.TT.o0)
    chain-zero = refl
    chain-one : chain 1 ≡ inner (chain 0)
    chain-one = refl
  recipe : P.Tr π st → O.O U.zero ρ
  recipe (P.mkTr ξ w bk) = O.TT.ol (λ n → outer (P.mkTr ξ w bk) (chain (P.mkTr ξ w bk) n))
  rise-equation : P.ψ U.∅ (P.tn 0) st (O.TT.oΩ r tt h) ≡ recipe (P.trim π st {r} tt)
  rise-equation with P.trim π st {r} tt
  ... | P.mkTr ξ w bk = refl
```

**精确公式。** 给定原节点的参数，令 M = trim π st {r} tt，ξ = ξᵗ M：

```text
I(z) = ψ ∅ (tp r tt) (stChain ξ (bkᵗ M) (wkᵗ M) st) (h ξ z)
O(z) = ψ ∅ (tn 0)    (stBody  ξ (wkᵗ M) st)         (h ξ z)
z₀   = owk {π = tz} {ρ = ξ} (λ ()) (os o0)
z₁   = I(z₀)
ψ ∅ (tn 0) st (oΩ r tt h) = ol (λ n → O(chain M n)).
```

因此此节点上所需的第 0→1 步要比较 O(z₀) 与 O(I(z₀)) 的原计值读回。
内层状态类型为 St ∅ ξ (ξ ∪ π)，外层为 St ∅ ρ (ξ ∪ π)。即使两次的
对象目标都是 U.zero，也不能由此删除 st / 地板参数或证明两个原函数
相同。本篇不采用这种相认，不使用 Funext，不改原定义。

**与实际路径的关系和限度。** r 是原 Λ 的第 2 支内第一支的零层节点
位置。上述方程对到达它的原参数逐字成立；尚未把整棵实际种子与某个
简化的纯树迭代相认，也没有宣称已在编译器里复原了该节点之前全部
包装所生成的 st / h 的闭表达式。实际单点目标始终以 TreeLevels5Point
中的原 actual-seed 定义为准；本篇的变量参数不得冒充该目标已解。
