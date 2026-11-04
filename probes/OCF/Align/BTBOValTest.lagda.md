# BTBOVal 的有限测试

> 接 [BTBOVal](BTBOVal.lagda.md). **本文件全是有限测试, 不是证明.** 比较两族对角线: src 的 $x_k=$ `ψⁿ k` (经 `tr₀`) 与 `NoCumsum` 的 $\gamma_k$.
>
> 翻译: 两族第 0 层不是同一类型, 但构造子一一对应, `tr₀` 逐构造子翻译, `FGH-tr₀` 说它不改 FGH (定理, `BTBOValBase`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BTBOValTest where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; _∨_; _∧_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.BTBO using (module Ord-Ord)
module S = Ord-Ord
open import OCF.Align.Level
import OCF.Align.NoCumsum as N
open import OCF.Align.BTBOValBase using (tr₀)
open import OCF.Align.BTBOValMain using (x; K)
```

## §1 FGH

比较器: `refl`. 盲区: 参数只到能算完的范围.

```agda
_ : S.FGH (x 1) 1 ≡ 2
_ = refl
_ : S.FGH (x 2) 1 ≡ 2
_ = refl
_ : S.FGH (x 3) 1 ≡ 2
_ = refl
_ : S.FGH S.BTBO 1 ≡ FGH N.BTBOᴵ 1
_ = refl
_ : S.FGH (x 1) 2 ≡ 8
_ = refl
_ : FGH (N.γ 0) 2 ≡ 4
_ = refl
_ : FGH (ψ⁰ (Ω Ordᴵ.zero)) 2 ≡ 8
_ = refl
```

参数 1 沿 $[1]$ 降到 0, 恒为 2, **不区分任何东西**. 参数 2 从 `S.FGH (x 2) 2`, `FGH (γ 1) 2` 起算不完 (`NoCumsum` §2 记录 60 秒超时, 一进制写不下). 所以 FGH 的小值比较给不出 $\gamma_k$ 与 $x_k$ 的关系. `S.FGH BTBO 2` 的第一步是 $x_2$, `FGH BTBOᴵ 2` 的第一步是 $\gamma_3$, 两边基本列不同: 逐点相等没有理由, 判断是不等, 未证.

## §2 累加的层号

`cum-K` 是定理; 这里列前几项: $K=0,2,5,9,14$, 与 `toLevel` 的 $0,1,2,3,4$ 对照.

```agda
_ : K 1 ≡ 2
_ = refl
_ : K 2 ≡ 5
_ = refl
_ : K 3 ≡ 9
_ = refl
_ : K 4 ≡ 14
_ = refl
```

## §3 树的形状

`pre d w t`: 深度 $d$, 宽度 $w$ 的前缀. `Q` 是截断, `Z`, `Sc`, `L` 是构造子. 比较器: `refl`. 盲区: 前缀外的一切.

```agda
data Co : Set where
  Z : Co
  Sc : Co → Co
  L : List Co → Co
  Q : Co

take : ℕ → (ℕ → Co) → List Co
take zero f    = []
take (suc n) f = f 0 ∷ take n (λ i → f (suc i))

pre : ℕ → ℕ → Ordᶜ Ordᴵ.zero → Co
pre zero w t = Q
pre (suc d) w zero    = Z
pre (suc d) w (suc a) = Sc (pre d w a)
pre (suc d) w (lim f) = L (take w (λ i → pre d w (f i)))
pre (suc d) w (limᵢ () f)
pre (suc d) w (up () x)
```

$x_1=\omega$ 与 $\psi^0(\Omega_0)$ 同形:

```agda
_ : pre 3 3 (tr₀ (x 1)) ≡ L (Z ∷ Sc Z ∷ Sc (Sc Q) ∷ [])
_ = refl
_ : pre 3 3 (ψ⁰ (Ω Ordᴵ.zero)) ≡ L (Z ∷ Sc Z ∷ Sc (Sc Q) ∷ [])
_ = refl
```

$x_2$ 与 $\psi^0(\Omega_\omega)$ 同值 (`x₂≈BO`), 形状从第 0 项就不同: 前者的第 0 项是 $\omega^\omega$ 的基本列 ($\omega,\omega^2,\dots$), 后者的第 0 项是 $\omega$ 本身.

```agda
Q³ : Co
Q³ = L (Q ∷ Q ∷ Q ∷ [])

_ : pre 4 3 (tr₀ (x 2)) ≡
    L (L (L (Z ∷ Sc Q ∷ Sc Q ∷ []) ∷ L (Z ∷ Q³ ∷ Q³ ∷ []) ∷ L (Z ∷ Q³ ∷ Q³ ∷ []) ∷ []) ∷
       L (L (Z ∷ Sc Q ∷ Sc Q ∷ []) ∷ L (Z ∷ Q³ ∷ Q³ ∷ []) ∷ L (Z ∷ Q³ ∷ Q³ ∷ []) ∷ []) ∷
       L (L (Z ∷ Sc Q ∷ Sc Q ∷ []) ∷ L (Q³ ∷ Q³ ∷ Q³ ∷ []) ∷ L (Q³ ∷ Q³ ∷ Q³ ∷ []) ∷ []) ∷ [])
_ = refl

_ : pre 4 3 (ψ⁰ (Ω ωᴵ)) ≡
    L (L (Z ∷ Sc Z ∷ Sc (Sc Q) ∷ []) ∷
       L (L (Z ∷ Sc Q ∷ Sc Q ∷ []) ∷ L (Sc Q ∷ Q³ ∷ Q³ ∷ []) ∷ L (Q³ ∷ Q³ ∷ Q³ ∷ []) ∷ []) ∷
       L (L (Q³ ∷ Q³ ∷ Q³ ∷ []) ∷ L (Q³ ∷ Q³ ∷ Q³ ∷ []) ∷ L (Q³ ∷ Q³ ∷ Q³ ∷ []) ∷ []) ∷ [])
_ = refl
```

## §4 有界比较器

`leq d w a b`: 深度 $d$ 内找 $a\preccurlyeq b$ 的推导, `lim` 只看前 $w$ 项. **盲区两头都有:** `true` 也只看了左边极限的前 $w$ 项; `false` 只说明预算内没找到, 什么都不说明.

```agda
anyB allB : ℕ → (ℕ → Bool) → Bool
anyB zero f    = false
anyB (suc n) f = f 0 ∨ anyB n (λ i → f (suc i))
allB zero f    = true
allB (suc n) f = f 0 ∧ allB n (λ i → f (suc i))

leq : ℕ → ℕ → Ordᶜ Ordᴵ.zero → Ordᶜ Ordᴵ.zero → Bool
leq zero w a b = false
leq (suc d) w zero b = true
leq (suc d) w (lim h) b = allB w (λ i → leq d w (h i) b)
leq (suc d) w (suc a) zero = false
leq (suc d) w (suc a) (suc b) = leq d w a b ∨ leq d w (suc a) b
leq (suc d) w (suc a) (lim g) = anyB w (λ i → leq d w (suc a) (g i))
leq (suc d) w (limᵢ () f) b
leq (suc d) w (up () x) b
leq (suc d) w a (limᵢ () f)
leq (suc d) w a (up () x)

_ : leq 6 2 (N.γ 0) (tr₀ (x 1)) ≡ true
_ = refl
_ : leq 6 2 (tr₀ (x 1)) (N.γ 1) ≡ true
_ = refl
```

**没有结论的测试 (只记录).** 想用 `leq` 测 $x_2$ 的 `St` 步进和 $\gamma_1$ 对 $x_2$ 的项: 预算 $(d,w)\le(9,3)$ 内都返回 `false`, 预算 $(8,3)$ 下比较 $x_k$ 与 $\gamma_k$ 的整棵树 500 秒内算不完. `false` 不说明任何事. 所以 **src 的 $x_k$ 是否 `St`, 目前连有说服力的有限证据都没有**, 只有纸面判断: `ψ<` 的每个 `lim` 都是倍数、链或逐项的严格递增序列.
