# NoAcc: 有限测试 (逐点与累加的闭项对照)

> 不含记号. 入口 [NoAcc](NoAcc.lagda.md). 全文 `--safe --without-K --lossy-unification`. **有限测试, 不是证明**; 只有 `e1ᴾ`, `e1ᴬ` 两条是定理 (`refl`, 字面等式).
>
> - `t1`–`t3`: `TXᴾ` (逐点) 与 CRw 的 `TX` (累加) 的有界展开 (深度 4, 每个 ℕ-极限展开前 4 项) 结点数相同 (41), 沿下标串 `[2,2,2]`, `[0,1,2]` 走下去的子树结点数也相同. 这几个深度上**没有测出**差别; 差别在更深处 (判断: 逐点与部分和只在折叠遇到输入的 ℕ-极限时不同, 而 `topL` 的输入的 ℕ-极限要经回灌的坐标 `leg b′` 才出现).
> - `e1ᴾ`, `e1ᴬ` (定理): 第 1 层的 $\omega=\lim(1,2,3,\dots)$ 折到第 0 层, 输出的第 1 项: 逐点是 $\omega^2$ 本身 (`hl (mul ω)`), 累加是 $\omegaoxplus\omega^2$. 这是作者说的毛刺在一个最小输入上的字面形状. `t4`–`t7`: 对应的结点数 (第 1 项都是 19; 再沿第 0 项走两步, 逐点是 2 (就是 $1$), 累加是 11 ($\omegaoxplus1$)).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NoAccTest where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Unit using (tt)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (I₁; W₀; PH-topL; TX)
open import OCF.Lean.CRwFold I₁
open import OCF.Lean.NoAccFold I₁

TXᴾ : Cd
TXᴾ = Φᴾ bX hz (wf bX hz) tt b⊥ hz (cx W₀ tt (z⊲ᴮ W₀)) hz topL (PH-topL W₀ hself)

szN : ℕ → Cd → ℕ
szsN : ℕ → ℕ → (ℕ → Cd) → ℕ
szN zero x = 0
szN (suc k) hz = 1
szN (suc k) (hs x) = suc (szN (suc k) x)
szN (suc k) (hl f) = suc (szsN k (suc k) f)
szN (suc k) (hΩ () g)
szsN k zero f = 0
szsN k (suc i) f = szN k (f i) + szsN k i f

t1 : szN 4 TXᴾ ≡ szN 4 TX
t1 = refl

open import Data.List using (List; []; _∷_)

-- 沿一串下标走: ℕ-极限取第 i 项, 后继取前驱
go : List ℕ → Cd → Cd
go [] x = x
go (i ∷ is) hz = hz
go (i ∷ is) (hs x) = go is x
go (i ∷ is) (hl f) = go is (f i)
go (i ∷ is) (hΩ () g)

t2 : szN 3 (go (2 ∷ 2 ∷ 2 ∷ []) TXᴾ) ≡ szN 3 (go (2 ∷ 2 ∷ 2 ∷ []) TX)
t2 = refl

t3 : szN 4 (go (0 ∷ 1 ∷ 2 ∷ []) TXᴾ) ≡ szN 4 (go (0 ∷ 1 ∷ 2 ∷ []) TX)
t3 = refl

numL : ℕ → HB (Lev b⊥ (hs hz))
numL zero = hz
numL (suc n) = hs (numL n)

ωL : HB (Lev b⊥ (hs hz))
ωL = hl (λ n → numL (suc n))

P10 A10 : Cd
P10 = Φᴾ b⊥ (hs hz) (wf b⊥ (hs hz)) tt b⊥ hz (sm (hsuc hself)) hz ωL tt
A10 = Φ b⊥ (hs hz) (wf b⊥ (hs hz)) tt b⊥ hz (sm (hsuc hself)) hz ωL tt

t4 : szN 3 (go (1 ∷ []) P10) ≡ 19
t4 = refl

t5 : szN 3 (go (1 ∷ []) A10) ≡ 19
t5 = refl

t6 : szN 3 (go (1 ∷ 0 ∷ 0 ∷ []) P10) ≡ 2
t6 = refl

t7 : szN 3 (go (1 ∷ 0 ∷ 0 ∷ []) A10) ≡ 11
t7 = refl

-- 第 1 项, 字面 (定理, refl): 逐点是 ω², 累加是 ω ⊞ ω²
e1ᴾ : go (1 ∷ []) P10 ≡ hl (mul (hl (mul (hs hz))))
e1ᴾ = refl

e1ᴬ : go (1 ∷ []) A10 ≡ hl (mul (hs hz)) ⊞ hl (mul (hl (mul (hs hz))))
e1ᴬ = refl
```
