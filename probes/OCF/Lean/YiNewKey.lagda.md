# YiNew 验收: 最小见证树, 闭项, 与第一个障碍的形状

判决 (形状测试, 都是 `refl`; `key-diff` 是小定理): 见证树进孩子层 2 时, 朝第 0, 1 层的对角化用的是 x 朝第 1 层的折叠, 朝第 2 层保留的分支里是 x 朝第 2 层的折叠.
做了什么: 见证树 `W x`, 闭项 `ebo` (形状读作 ψ₀(Λ)) 与 `boW`, 非零.
不否定什么: `loc-blind` 表明非有限层的顶码的对角化不含底; 闭项的序数值与输出树的合法性都没有定理.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNewKey where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNewBlock
open import OCF.Lean.YiNewFold
```

## 最小见证树

塔第 1 项 `tw 1` 的孩子是第 0 层的树 c, 孩子层是 c 读回的层号加一: 孩子 `zr` 的层是有限层 1, 孩子 `sc zr` 的层是有限层 2.
`xΩ` 是 `tw 1` 层里的一棵 Ω 树 (码取自孩子 `zr`); `yΩ` 是孩子层 2 里的 Ω 树 (顶码, 按有限层 1 的树分支).

```agda
xΩ : T (tw 1)
xΩ = Lm (zr , inj₁ tt) (λ ζ → up zr zr (up zr tt ζ))

yΩ : F 2
yΩ = Lm (inj₁ tt) (λ ζ → up zr tt ζ)

W : T (tw 1) → T (tw 1)
W x = up x (sc zr) yΩ
```

嵌入一致在这棵树上的实例, 对一切 x 与一切底.

```agda
W-up : ∀ x B → Ψ (tw 1) (W x) B ≡ Ψ (fin 2) yΩ (Ψ (tw 1) x B)
W-up x B = refl
```

## 关键判据

朝第 0 层: 孩子层 2 的顶码没有槽位, 对角化; 迭代的每一步是 "朝第 1 层折叠", 底是 x 的整族折叠.

```agda
step₁ : T (tw 1) → Base → F 1 → F 1
step₁ x B ζ = Ψ (fin 1) ζ (Ψ (tw 1) x B) 1

key-0 : ∀ x B → Ψ (tw 1) (W x) B 0
              ≡ lm (λ n → Ψ (fin 1) (iter (step₁ x B) zr n) (Ψ (tw 1) x B) 0)
key-0 x B = refl
```

对角化的第 1 项就是 x 朝第 1 层的折叠 (底里出现 x 的朝第 1 层的折叠).

```agda
key-1 : ∀ x B → iter (step₁ x B) zr 1 ≡ Ψ (tw 1) x B 1
key-1 x B = refl
```

朝第 1 层同样对角化; 朝第 2 层保留成分支, 分支在零处的值是 x 朝第 2 层的折叠.

```agda
key-1′ : ∀ x B → Ψ (tw 1) (W x) B 1
               ≡ lm (λ n → Ψ (fin 1) (iter (step₁ x B) zr n) (Ψ (tw 1) x B) 1)
key-1′ x B = refl

key-2 : ∀ x B → Ψ (tw 1) (W x) B 2
              ≡ Lm (inj₁ tt) (λ ζ → Ψ (fin 1) ζ (Ψ (tw 1) x B) 2)
key-2 x B = refl

key-2z : ∀ x B → Ψ (fin 1) zr (Ψ (tw 1) x B) 2 ≡ Ψ (tw 1) x B 2
key-2z x B = refl
```

两个不同的 x 给出不同的第 1 层底分量: `xΩ` 的是分支结点, `sc xΩ` 的是 ℕ 极限.

```agda
xΩ-1 : Ψ (tw 1) xΩ B° 1 ≡ Lm (inj₁ tt) (λ ζ → Ψ ze ζ B° 1)
xΩ-1 = refl

key-diff : Ψ (tw 1) xΩ B° 1 ≡ Ψ (tw 1) (sc xΩ) B° 1 → ⊥
key-diff ()
```

## 闭项

`top ℓ` 是 `su ℓ` 层的顶码分支 (一加上 ℓ 层的每棵树). `ebo` 取塔各项之上的 `top` 朝第 0 层折叠, 再取 ℕ 极限; 形状读作 ψ₀(Λ), 值没有定理.
`boW` 是 `tw 1` 层里 "各有限孩子层的 `top` 的 ℕ 极限" 朝第 0 层的折叠.

```agda
top : (ℓ : Lv) → T (su ℓ)
top ℓ = Lm (inj₁ tt) (λ ζ → up one tt ζ)

ebo : F 0
ebo = lm (λ n → Ψ (su (tw n)) (top (tw n)) B° 0)

num : ℕ → F 0
num zero    = zr
num (suc k) = sc (num k)

wω : T (tw 1)
wω = lm (λ k → up zr (num k) (top (ze ⊕ inj ze (num k))))

boW : F 0
boW = Ψ (tw 1) wω B° 0

ebo-nz : Le (fin 0) one ebo
ebo-nz = Ord.≤l (nz (su (tw 0)) (top (tw 0)) 0)

boW-nz : Le (fin 0) one boW
boW-nz = nz (tw 1) wω 0
```

## 第一个障碍的形状

`su (tw 1)` 的顶码按 `tw 1` 层的树分支, `tw 1` 不是有限层, 码归 `loc`: 对角化的迭代用局部一步折叠 `D`, 起点与底都是常数, 不含 B.

```agda
loc-blind : ∀ B j → Ψ (su (tw 1)) (top (tw 1)) B j
                  ≡ lm (λ n → Ψ (su (tw 1))
                                (up one tt (iter (λ ζ → D (tw 1) (up one tt ζ) one) zr n)) B j)
loc-blind B j = refl
```
