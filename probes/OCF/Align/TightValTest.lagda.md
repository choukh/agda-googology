# 紧界树比值 (八): 有限测试

> [TightVal](TightVal.lagda.md) 的第八篇. **本文全是有限测试, 不是定理.** 比较器 `shape d w x`: 第 0 层符号树展开到深度 $d$, 每个 `lim` 看前 $w$ 项, 每个节点记外形 (`s0`, `ss`, `sl`, `sc`); 闭包节点只记 `sc` 并只看第 0 点或第 0 个输出.
>
> **盲区.** (1) 不看闭包的界 `c` (这一点单独用 `kind` 测). (2) 不看闭包的分支 `g η e`: 链点要证书才有, 分支只在具体的 $\eta$ 上可算. (3) 宽度 $w$ 以外的项不看. (4) `lim` 的结构相同不等于值相同, 反之亦然. 这是结构比较, 不是值比较.
>
> 环境都是写明的具体环境. 全部 `refl`. 全文 `--safe --without-K --lossy-unification`. 不读记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TightValTest where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Align.Level
open import OCF.Align.Prefix using (Z; ĉᴸ; Ord₊ˢ; Ordˢ; toZ; Ωˢ; walkˢ; kind; kz; ks; kl; kĉ; kc)
open import OCF.Align.OmegaExpBase using (∅ˢ)
open import OCF.Align.OmegaSqBase using (ψᵉ′; lowˢ; ψ₂1ˢ; z3; three)
open import OCF.Align.OmegaSq using (TΩ₂ˢ)
open import OCF.Align.UniformS using (two)
open import OCF.Align.TightValNeg using (F₃; four; z4)
import OCF.Align.Uniform2Base as U2
import OCF.Align.Uniform3Base as U3

data Sh : Set where
  s0 : Sh
  ss : Sh → Sh
  sl : List Sh → Sh
  sc : Sh → Sh
  s· : Sh

upTo : ℕ → (ℕ → Sh) → List Sh
upTo zero    f = []
upTo (suc w) f = f zero ∷ upTo w (λ n → f (suc n))

shape : ℕ → ℕ → Ordˢ zero → Sh
shape zero    w x = s·
shape (suc d) w Ord₊ˢ.zero = s0
shape (suc d) w (Ord₊ˢ.suc x) = ss (shape d w x)
shape (suc d) w (Ord₊ˢ.lim f) = sl (upTo w (λ n → shape d w (f n)))
shape (suc d) w (Ord₊ˢ.limᵢ () f)
shape (suc d) w (Ord₊ˢ.up () x)
shape (suc d) w (Ord₊ˢ.ŝ c t₀ g) = sc (shape d w t₀)
shape (suc d) w (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) = sc (shape d w o₀)
```

## §1 紧界树对新树

新树在同一环境形状上的 $\psi_0(\psi_\Omega(\cdot))$. `Tn x` 第 $k$ 层指数 $x$, 地板 `flo k`.

```agda
σ₁₃ : Simᴵ (suc zero) three
σ₁₃ q = suc (suc q)

σ₂₃ : Simᴵ two three
σ₂₃ q = suc q

evn : U3.Ev three (U3.fz U3.⊔ (U3.fk zero U3.⊔ U3.fk (suc zero)))
evn = tt , (σ₁₃ , σ₂₃)

Tn : Ordˢ two → Ordˢ zero
Tn x = U3.fold 1 (U3.flo two) (U3.cvFlo two) (U3.Ω̂A 0) x U3.∅ᴿ evn z3
```

$\Omega_2$ 上两棵树在测到的范围内同形 (定理在 `OmegaSq.TΩ₂-label` 与 `Uniform3.TΩ₂-label′`, 这里只是比较器的正对照).

```agda
same-Ω₂ : shape 9 3 TΩ₂ˢ ≡ shape 9 3 (Tn (Ωˢ two))
same-Ω₂ = refl
```

$\psi_2(1)$ 上: 深度 2 以内同形, 第一个分岔在 `low-term` 的路径 $[2,0,0]$: 紧界树是占位 $0$, 新树是极限.

```agda
same-low₂ : shape 2 3 lowˢ ≡ shape 2 3 (Tn ψ₂1ˢ)
same-low₂ = refl

diff-low-a : kind (walkˢ lowˢ (2 ∷ 0 ∷ 0 ∷ [])) ≡ kz
diff-low-a = refl

diff-low-c : kind (walkˢ (Tn ψ₂1ˢ) (2 ∷ 0 ∷ 0 ∷ [])) ≡ kl
diff-low-c = refl
```

$\Omega_3$ 的同一路径上紧界树也是 $0$:

```agda
diff-Ω₃ : kind (walkˢ F₃ (1 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 2 ∷ 0 ∷ 0 ∷ [])) ≡ kz
diff-Ω₃ = refl
```

**新树在哪里第一次不紧.** `low-pop` 的位置 $\psi_0(\psi_\Omega(\Omega_2)+\Omega_\Omega)$: 目标 0, 紧界应是 $1$, 新树的界是 $2$, 由帧的地板 `fk 1` 抬上来. 紧界树走不到这里 (前一步就是 $0$).

```agda
new-not-tight : kind (walkˢ (Tn ψ₂1ˢ) (2 ∷ 0 ∷ 0 ∷ 2 ∷ 0 ∷ 0 ∷ 1 ∷ [])) ≡ kc two
new-not-tight = refl
```

## §2 旧地板树对新树

指数 $\Omega_\omega$, 环境第 $\omega+1$ 层. 这是 `up (self n)` 第一次出现的层号. 两棵树的第 0 层树在测到的范围内同形; 差别只在闭包的界: 路径 $[0,2]$ 处旧树是 $\omega+1$, 新树是 $1$. 这是 [TightValFloor](TightValFloor.lagda.md) 的 `no-cert` 的最小实例.

```agda
η : Ordᴵ
η = toLevel ωᶜ ωᶜ-HS

pos : zero <ᴵ η
pos = lim 1 zero

σ₁ : Simᴵ (suc zero) (suc η)
σ₁ zero = suc pos
σ₁ (suc ())

T2 : Ordˢ zero
T2 = U2.fold 1 (U2.fk η) (λ e q → e (suc q)) (U2.Ω̂A 0) (Ωˢ η) U2.∅ᴿ (tt , (σ₁ , (λ q → q))) (suc pos)

T3 : Ordˢ zero
T3 = U3.fold 1 (U3.fk η) (λ e q → e (suc q)) (U3.Ω̂A 0) (Ωˢ η) U3.∅ᴿ (tt , (σ₁ , (λ q → q))) (suc pos)

bound-old : kind (walkˢ T2 (0 ∷ 2 ∷ [])) ≡ kc (suc η)
bound-old = refl

bound-new : kind (walkˢ T3 (0 ∷ 2 ∷ [])) ≡ kc (suc zero)
bound-new = refl

same-floor : shape 10 3 T2 ≡ shape 10 3 T3
same-floor = refl
```
