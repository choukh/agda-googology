# 盲测: 预测 (写在比较之前, 不再改)

> **这个文件是预测, 写完就封存.** 结论写在 [TreeJudge](TreeJudge.lagda.md). 结果在 [TreeJudgeBlindResult](TreeJudgeBlindResult.lagda.md) (树自己算), [TreeJudgeAccept](TreeJudgeAccept.lagda.md) (与记号比). 本文件不含记号, 也没有运行过这些预测. **每一条 `p…` 是一个 `Bool`, "预测" 的意思是它算出 `true`; 这里不写 `≡ true`, 所以编译通过不代表任何一条对.**
>
> **目标.** $a=\psi_1(1)$ (层号 `La`). $A=\psi_0(\Omega_{a+1})$, $B=\psi_0(\Omega_{a+a})$, $C=\psi_0(\Omega_{\psi_1(2)})$, $D=\psi_0(\Omega_{a+a+1})$. 现有树都没有证书或标签: `GuardTightAccept` 对 $A$ 有种类测试, 对 $B,C,D$ 没有.
>
> **定义的来源.** 折叠是 [GuardTightTree](GuardTightTree.lagda.md) 的 `T₀`, 不新写. 层号的证书由 `Good→WF₁` 给. 读法由判据选 ([TreeJudgeRd](TreeJudgeRd.lagda.md)): 紧读法, 对前缀 $W$ 一般写. **这就是这次新写的全部定义.** 其余都是继承.
>
> **预测的来源.** 手算. 用四条行律, 都不看记号:
>
> 1. **极限行.** $T(\lim f)[n]$ 就是 $T(f\,n)$.
> 2. **闭包行.** $T(\mathrm{lc}\,c\,t\,g)$ 是闭包, 目标 0 且没有帧时界就是层号自己的 $c$ (这里是 1), 头和第一支是 $T(t)$, 分支 $\eta$ 是 $T(g\,\eta)$.
> 3. **后继行.** $T(L+1)[n]=\psi_0(y_n)$, $y_0=\dot\Omega_L$, $y_{n+1}=\psi_L(y_n)$.
> 4. **`HF`.** 闭包的界是头的函数. 紧读法下界不读穿过的分支.
>
> 手算示例 ($A$): $T(a+1)[0]=\psi_0(\dot\Omega_a)=T(a)$. $[1]=\psi_0(\psi_a(\dot\Omega_a))$, $\dot\Omega_a$ 是极限, 所以 $[1]$ 是极限. $[1][0]=\psi_0(\psi_a(\dot\Omega_0))=\psi_0(\psi_a(1))$, $\psi_a(1)$ 是 $\dot\Omega_a\cdot m$ 的极限, 所以 $[1][0]$ 是极限, $[1][0][0]=\psi_0(0)=1$ (后继), $[1][0][1]=\psi_0(\dot\Omega_a)=T(a)$. $[1][1]=\psi_0(\psi_a(\dot\Omega_\Omega))$: 闭包在目标 $a$ 里有位置, 保留, 再被 $\psi_0$ 计值, 界 1. $[2]=\psi_0(\psi_a(\psi_a(\dot\Omega_a)))$, $[2][0]=\psi_0(\psi_a(\psi_a(\dot\Omega_0)))$, 其中 $\psi_a(1)$ 是极限, 第 0 项是 $0$, 所以 $[2][0][0]=\psi_0(\psi_a(0))=\psi_0(\dot\Omega_a)=T(a)$.
>
> **指纹深度 7, 宽度 2.** `same` 的预测在这个指纹意义下; 不是 $\cong$.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeJudgeBlind where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; not)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
open import OCF.Free.Prefix using (Z)
open import OCF.Align.GuardTightCum using (Ordᶜ; _+_; add; Ω; Ω-refl; add-≅; zero; suc; lim; _≅_; s≅; z≅)
open import OCF.Align.GuardTightLv
open Lv Dom₀ using (LG; suc; Cfˢ; s≈)
import OCF.Align.GuardTightUni as Uni
private module U = Uni Dom₀
open U using (rb₁; rb-≈₁₁; ψ¹; ψ¹-≅; Good; Good-Ω; Good-add; Good-ψ¹; good-F; Good→WF₁; gs; gz)
open import OCF.Align.GuardTightBase using (Tc; Tc-id)
open import OCF.Align.GuardTightRd using (module RdIter)
open import OCF.Align.GuardTightTree using (T₀)
open import OCF.Align.TreeJudgeRd using (module Pre; module RdPre; Wr)
open import OCF.Align.TreeJudgeObs
open import OCF.Align.TreeJudgeRead using (rd)
```

## §1 新的定义: 层号, 证书, 读法

```agda
a c : Ordᶜ (suc zero)
a = ψ¹ (Ω zero)
c = Ω (suc zero)

e-a : a ≅ a
e-a = ψ¹-≅ {k₁ = zero} {k₂ = zero} (Ω-refl zero)

e-c : c ≅ c
e-c = Ω-refl (suc zero)

g-a : Good a
g-a = good-F zero

Cf-of : ∀ {x} → Good x → x ≅ x → Cfˢ (rb₁ x)
Cf-of g e = Good→WF₁ g , rb-≈₁₁ e

sucCf : ∀ {x : LG} → Cfˢ x → Cfˢ (suc x)
sucCf cf = proj₁ cf , s≈ (proj₂ cf)

Tc-a : Tc (rb₁ a)
Tc-a = λ n → RdIter.Tc-iter n

open Pre a using (Wm)
open Pre.At a refl Tc-a using (Rm; tcm; Tc-m)

b2 : Ordᶜ zero
b2 = suc (suc zero)

Lab LaΩ LaΩ2 Lψ2 : LG
Lab = rb₁ (a + a)
LaΩ = rb₁ (a + c)
LaΩ2 = rb₁ (a + (c + c))
Lψ2 = rb₁ (ψ¹ b2)

Cf-a : Cfˢ (rb₁ a)
Cf-a = Cf-of g-a e-a

Cf-ab : Cfˢ Lab
Cf-ab = Cf-of (Good-add {σ = λ q → q} g-a e-a g-a) (add-≅ {σ = λ q → q} {σ′ = λ q → q} e-a e-a)

Cf-aΩ : Cfˢ LaΩ
Cf-aΩ = Cf-of (Good-add {σ = λ q → q} g-a e-a (Good-Ω (suc zero))) (add-≅ {σ = λ q → q} {σ′ = λ q → q} e-a e-c)

Cf-aΩ2 : Cfˢ LaΩ2
Cf-aΩ2 = Cf-of (Good-add {σ = λ q → q} g-a e-a (Good-add {σ = λ q → q} (Good-Ω (suc zero)) e-c (Good-Ω (suc zero))))
               (add-≅ {σ = λ q → q} {σ′ = λ q → q} e-a (add-≅ {σ = λ q → q} {σ′ = λ q → q} e-c e-c))

Cf-ψ2 : Cfˢ Lψ2
Cf-ψ2 = Cf-of (Good-ψ¹ {x = b2} (gs (gs gz)) (s≅ (s≅ z≅))) (ψ¹-≅ {a = b2} {b = b2} (s≅ (s≅ z≅)))

Tc-ab : Tc Lab
Tc-ab = Tc-m 0

Tc-aΩ : Tc LaΩ
Tc-aΩ = RdPre.Tc-Wc (Rm 0)

Tc-aΩ2 : Tc LaΩ2
Tc-aΩ2 = RdPre.Tc-Y0 (Rm 0) 1

eq-iter : ∀ m → iter (a +_) zero (suc m) ≡ Wm m zero
eq-iter zero = refl
eq-iter (suc m) = cong′ (eq-iter m)
  where
  cong′ : ∀ {u v} → u ≡ v → (a + u) ≡ (a + v)
  cong′ refl = refl

Tc-ψ2 : Tc Lψ2
Tc-ψ2 zero = _
Tc-ψ2 (suc m) = tcS′ (eq-iter m) (tcm m)
  where
  tcS′ : ∀ {u v : Ordᶜ (suc zero)} → u ≡ v → Tc (rb₁ v) → Tc (rb₁ u)
  tcS′ refl t = t
```

## §2 这几棵树

```agda
Ta TA T2 TB TC TD TaΩ TaΩ1 TaΩ2 : Obs
Ta   = rd (T₀ (rb₁ a) Cf-a Tc-a)
TA   = rd (T₀ (suc (rb₁ a)) (sucCf Cf-a) Tc-a)
T2   = rd (T₀ (suc (suc (rb₁ a))) (sucCf (sucCf Cf-a)) Tc-a)
TB   = rd (T₀ Lab Cf-ab Tc-ab)
TC   = rd (T₀ Lψ2 Cf-ψ2 Tc-ψ2)
TD   = rd (T₀ (suc Lab) (sucCf Cf-ab) Tc-ab)
TaΩ  = rd (T₀ LaΩ Cf-aΩ Tc-aΩ)
TaΩ1 = rd (T₀ (suc LaΩ) (sucCf Cf-aΩ) Tc-aΩ)
TaΩ2 = rd (T₀ LaΩ2 Cf-aΩ2 Tc-aΩ2)

-- 对照: 同样的层号, 恒等读法
TBid : Obs
TBid = rd (T₀ Lab Cf-ab (Tc-id Lab))
```

## §3 预测的写法

```agda
isSh : Sh → Sh → Bool
isSh sh0 sh0 = true
isSh shs shs = true
isSh shl shl = true
isSh (shc m) (shc n) = m == n
isSh shN shN = true
isSh _ _ = false

at : List St → Obs → Maybe Obs
at p x = go p x

-- `is p x s`: x 沿 p 的形状是 s
is : List St → Obs → Sh → Bool
is p x s = isSh (shape (at p x)) s

-- `same p x y`: x 沿 p 的子树与 y 指纹相同 (深 7 宽 2)
same : List St → Obs → Obs → Bool
same p x y = sameM 7 2 (at p x) (just y)

-- `hsame p x y`: x 沿 p 的闭包的头与 y 指纹相同
hsame : List St → Obs → Obs → Bool
hsame p x y = sameM 7 2 (hdOf (at p x)) (just y)

noVio : Maybe Vio → Bool
noVio nothing = true
noVio (just _) = false

noBad : V → Bool
noBad (bad _ _) = false
noBad (okv _ _) = true
```

## §4 预测

**$A=\psi_0(\Omega_{a+1})$.**

```agda
pA1  = is [] TA shl
pA2  = same (lm 0 ∷ []) TA Ta
pA3  = is (lm 1 ∷ []) TA shl
pA4  = is (lm 1 ∷ lm 0 ∷ []) TA shl
pA5  = is (lm 1 ∷ lm 0 ∷ lm 0 ∷ []) TA shs
pA6  = same (lm 1 ∷ lm 0 ∷ lm 1 ∷ []) TA Ta
pA7  = is (lm 1 ∷ lm 1 ∷ []) TA (shc 1)
pA8  = is (lm 2 ∷ []) TA shl
pA9  = is (lm 2 ∷ lm 0 ∷ []) TA shl
pA10 = same (lm 2 ∷ lm 0 ∷ lm 0 ∷ []) TA Ta
pA11 = noVio (run 9 9 2 TA)
```

**$B=\psi_0(\Omega_{a+a})$.** 极限行: $[n]=T(a+\Omega\cdot n)$. 闭包行: $[1]$ 是 $a+\Omega$ 的闭包, 分支 $k$ 是 $\eta=1+k$ 的 $T(a+\eta)$.

```agda
pB1  = is [] TB shl
pB2  = same (lm 0 ∷ []) TB Ta
pB3  = is (lm 1 ∷ []) TB (shc 1)
pB4  = hsame (lm 1 ∷ []) TB TA
pB5  = same (lm 1 ∷ fs ∷ []) TB TA
pB6  = same (lm 1 ∷ br 0 ∷ []) TB TA
pB7  = same (lm 1 ∷ br 1 ∷ []) TB T2
pB8  = is (lm 2 ∷ []) TB (shc 1)
pB9  = hsame (lm 2 ∷ []) TB TaΩ1
pB10 = same (lm 2 ∷ br 0 ∷ []) TB TaΩ1
pB11 = same (lm 2 ∷ fs ∷ lm 0 ∷ []) TB TaΩ
pB12 = is (lm 3 ∷ []) TB (shc 1)
pB13 = noVio (run 9 9 2 TB)
pB14 = not (noVio (run 9 9 2 TBid))
pB15 = same (lm 1 ∷ []) TB TaΩ
pB16 = same (lm 2 ∷ []) TB TaΩ2
```

**$C=\psi_0(\Omega_{\psi_1(2)})$.** $\psi_1(2)=\lim a\cdot n$. $[0]=T(0)$ 是极限 ($\omega$). $[1]=T(a)$. $[2]=T(a+a)$. $[3]=T(a+(a+a))$, 还是极限, 第 0 项是 $T(a+a)$, 第 1 项是闭包.

```agda
pC1 = is [] TC shl
pC2 = is (lm 0 ∷ []) TC shl
pC3 = same (lm 1 ∷ []) TC Ta
pC4 = same (lm 2 ∷ []) TC TB
pC5 = is (lm 3 ∷ []) TC shl
pC6 = same (lm 3 ∷ lm 0 ∷ []) TC TB
pC7 = is (lm 3 ∷ lm 1 ∷ []) TC (shc 1)
pC8 = noVio (run 9 9 2 TC)
```

**$D=\psi_0(\Omega_{a+a+1})$.** 后继行. $[0]=T(a+a)$. $[1]=\psi_0(\psi_{a+a}(\dot\Omega_{a+a}))$ 是极限, 第 $n$ 项读 $\dot\Omega_{a+\Omega\cdot n}$: 第 0 项是 $\psi_0(\psi_{a+a}(\dot\Omega_a))$, 还是极限; 第 1 项是闭包, 界 1. 第 0 项的第 1 项读 $\dot\Omega_{\Omega}$: 闭包, 界 1.

```agda
pD1 = is [] TD shl
pD2 = same (lm 0 ∷ []) TD TB
pD3 = is (lm 1 ∷ []) TD shl
pD4 = is (lm 1 ∷ lm 0 ∷ []) TD shl
pD5 = is (lm 1 ∷ lm 1 ∷ []) TD (shc 1)
pD6 = is (lm 1 ∷ lm 0 ∷ lm 1 ∷ []) TD (shc 1)
pD7 = noVio (run 9 9 2 TD)
```

**Bachmann 取样不报反例** (力量弱).

```agda
pR1 = noBad (reg 6 20 3 2 [] TA)
pR2 = noBad (reg 6 20 3 2 [] TB)
```
