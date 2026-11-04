# 树侧判据 (二): 有限测试

> **这里全部是有限测试 (`refl`), 不是定理.** 不含记号: 导入闭包干净 (`importclosure.py`). 工具在 [TreeJudgeObs](TreeJudgeObs.lagda.md), [TreeJudgeRead](TreeJudgeRead.lagda.md). 结论写在 [TreeJudge2](TreeJudge2.lagda.md). 指纹相同不是 $\cong$.
>
> `Tk`, `tabk`: **同头的闭包的界随分支怎么走.** 走闭包 $X$ 的分支 $k$ 的第一路径 (深度 $d$, 宽度 $w$), 只看头的指纹等于 `r` 的闭包, 取最大的界. 这是新判据的取样形式: 界跟着分支走, 头不动, 就是 `Pinch` 的形状.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeJudge2Test where

open import Data.Nat using (ℕ; zero; suc; _⊔_)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Free.Prefix using (Z)
open import OCF.Align.GuardTightCum using (Ordᶜ; Ω; _+_; add-≅; Ω-refl; _≅_; Ordᴵ) renaming (suc to sucᴵ; zero to zeroᴵ)
open import OCF.Align.GuardTightLv
open Lv Dom₀ using (suc; s≈; LG; Cfˢ)
import OCF.Align.GuardTightUni as Uni
private module U = Uni Dom₀
open U using (rb₁; rb-≈₁₁; Good-Ω; Good-add; Good→WF₁; Good)
open import OCF.Align.GuardTightBase using (Tc; Tc-id)
open import OCF.Align.GuardTightRd using (module RdIter; module RdAdd)
open import OCF.Align.GuardTightCert using (c₁; wf₁; sf₁; tc₁)
import OCF.Align.GuardTightTree as G
import OCF.Align.TreeJudgeNoTrim as N
open import OCF.Align.GuardBridgeTree using (T₀′)
open import OCF.Align.TreeJudgeObs
open import OCF.Align.TreeJudgeRead using (rd)
open import OCF.Free.Prefix using (toZ)
open import OCF.Free.Tree using (TΩ·2)
open import OCF.Free.Closed using (ev₀)
import OCF.Free.Level as FL
```

## §1 工具与树

```agda
mhL : ℕ → ℕ → ℕ → ℕ → List ℕ → ℕ → (ℕ → Obs) → ℕ
mh : ℕ → ℕ → ℕ → List ℕ → Obs → ℕ
mh zero w fd r x = 0
mh (suc d) w fd r o0 = 0
mh (suc d) w fd r (os x) = mh d w fd r x
mh (suc d) w fd r (ol f) = mhL w d w fd r 0 f
mh (suc d) w fd r (oc b h o₀ o) with eqL r (fp fd w h)
... | true = b ⊔ mh d w fd r o₀
... | false = mh d w fd r o₀
mhL zero d w fd r s f = 0
mhL (suc n) d w fd r s f = mhL n d w fd r (suc s) f ⊔ mh d w fd r (f s)

-- 走到 p 的闭包, 分支 k, 同头 (头是 `hp` 处的头) 的最大界
Tk : List St → List St → ℕ → ℕ → ℕ → Obs → ℕ
Tk p hp k d w x with go (p ++ (br k ∷ [])) x
... | just y = mh d w 7 (fpM 7 w (hdOf (go hp x))) y
... | nothing = 99

tabk : List St → List St → ℕ → ℕ → ℕ → Obs → List ℕ
tabk p hp n d w x = go′ n
  where
  go′ : ℕ → List ℕ
  go′ zero = []
  go′ (suc m) = go′ m ++ (Tk p hp m d w x ∷ [])

Lc₁ : LG
Lc₁ = suc c₁

Cf-s : Cfˢ Lc₁
Cf-s = wf₁ , s≈ sf₁

Cf-ss : Cfˢ (suc Lc₁)
Cf-ss = wf₁ , s≈ (s≈ sf₁)

o-id o-t o-t′ o-n o-t₂ o-n₂ : Obs
o-id = rd (G.T₀ Lc₁ Cf-s (Tc-id c₁))
o-t = rd (G.T₀ Lc₁ Cf-s tc₁)
o-t′ = rd (T₀′ Lc₁ Cf-s tc₁)
o-n = rd (N.T₀ Lc₁ Cf-s tc₁)
o-t₂ = rd (G.T₀ (suc Lc₁) Cf-ss tc₁)
o-n₂ = rd (N.T₀ (suc Lc₁) Cf-ss tc₁)
```

## §2 同头的界跟着分支走

$\psi_0(\Omega_{\Omega+1})$ 的第 1 项 $X$, 分支 $k=0,\dots,4$ (分支值 $k+1$), 头是第 0 项 (`lm 0`) 的头. **恒等读法: 界就是分支值.** 紧的读法: 恒为 1.

```agda
b-id : tabk (lm 1 ∷ []) (lm 0 ∷ []) 5 8 2 o-id ≡ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []
b-id = refl

b-t : tabk (lm 1 ∷ []) (lm 0 ∷ []) 5 8 2 o-t ≡ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ []
b-t = refl

-- `ghost` 的前提要界 ≥ τ+1. 分支值 2 上的界是 2: 这一条前提在后继分支上是假的
b-ghost₂ : Tk (lm 1 ∷ []) (lm 0 ∷ []) 1 8 2 o-id ≡ 2
b-ghost₂ = refl
```

没有 `trim`: $\Omega+1$ 看不到 (`b-n`), $\Omega+2$ 看得到 (`b-n₂`), 同一个位置带 `trim` 恒为 1 (`b-t₂`).

```agda
b-n : tabk (lm 1 ∷ []) (lm 0 ∷ []) 3 8 2 o-n ≡ 1 ∷ 1 ∷ 1 ∷ []
b-n = refl

b-n₂ : tabk (lm 1 ∷ lm 1 ∷ []) (lm 1 ∷ lm 0 ∷ []) 3 7 2 o-n₂ ≡ 1 ∷ 2 ∷ 3 ∷ []
b-n₂ = refl

b-t₂ : tabk (lm 1 ∷ lm 1 ∷ []) (lm 1 ∷ lm 0 ∷ []) 3 7 2 o-t₂ ≡ 1 ∷ 1 ∷ 1 ∷ []
b-t₂ = refl

-- `HF` 的取样, 最小的目标
hf-id : run 9 7 2 o-id ≡ just (vio (0 ∷ []) 1 (1 ∷ 101 ∷ 0 ∷ 1 ∷ 1 ∷ []) 2)
hf-id = refl

hf-n₂ : run 8 7 2 o-n₂ ≡ just (vio (1 ∷ 0 ∷ []) 1 (1 ∷ 1 ∷ 101 ∷ 0 ∷ 0 ∷ 0 ∷ []) 2)
hf-n₂ = refl

hf-t₂ : run 8 7 2 o-t₂ ≡ nothing
hf-t₂ = refl
```

## §3 紧的 `T₀` 本身过不了 `HF`

上一轮 `T₀` 的接受测试都是宽度 2. **宽度 3 的取样有一对同头 (指纹深 9, 宽 3) 异界: `lm 1` 界 1, `pC` 界 2.** 这就是 [GuardBridgeNeg](GuardBridgeNeg.lagda.md) `T₀-too-high` 的那一类路径. `T₀′` 在同一条路径上界 1.

```agda
pC : List St
pC = lm 2 ∷ br 2 ∷ lm 1 ∷ lm 0 ∷ lm 0 ∷ lm 0 ∷ fs ∷ lm 0 ∷ lm 0 ∷ []

v-t₁ : shape (go (lm 1 ∷ []) o-t) ≡ shc 1
v-t₁ = refl

v-t₂ : shape (go pC o-t) ≡ shc 2
v-t₂ = refl

v-same : sameM 9 3 (hdOf (go (lm 1 ∷ []) o-t)) (hdOf (go pC o-t)) ≡ true
v-same = refl

v-t′ : shape (go pC o-t′) ≡ shc 1
v-t′ = refl
```

**这对路径不是孤立的: 第 2 项 `lm 2` 上, 同头的界跟着分支走.** 分支值 $k+1$ 上界是 $k$ ($k\ge1$; `b-t2`, 分支 4, 5 要更深, `b-t2₄`, `b-t2₅`). `T₀′` 恒为 1 (`b-t2′`). 所以上一节 `b-t` 只是没走到 (第 1 项只过一遍折叠).

```agda
b-t2 : tabk (lm 2 ∷ []) (lm 1 ∷ []) 4 9 2 o-t ≡ 1 ∷ 1 ∷ 2 ∷ 3 ∷ []
b-t2 = refl

b-t2₄ : Tk (lm 2 ∷ []) (lm 1 ∷ []) 4 11 2 o-t ≡ 4
b-t2₄ = refl

b-t2′ : tabk (lm 2 ∷ []) (lm 1 ∷ []) 6 9 2 o-t′ ≡ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ []
b-t2′ = refl
```

## §4 对的树

`T₀′` 与主线的 `TΩ·2` (有证书 `certᵀ`) 上, 这个取样里同头的界不跟着分支走.

```agda
o-free : Obs
o-free = rd (toZ (TΩ·2 ev₀ FL.zero))

b-t′ : tabk (lm 1 ∷ []) (lm 0 ∷ []) 5 8 2 o-t′ ≡ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ []
b-t′ = refl

b-free : tabk (fs ∷ lm 1 ∷ []) (fs ∷ lm 0 ∷ []) 5 8 2 o-free ≡ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ []
b-free = refl
```
