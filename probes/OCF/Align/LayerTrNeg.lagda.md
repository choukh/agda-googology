# 差树按层互译 (三): `ni` 的往返不保值

> 不含记号. 入口 [LayerTr](LayerTr.lagda.md). 编译过的反例: 一棵第 1 层的差树 $x$, 没有 `nκ` (所以 `difT` 有定义), 译成布劳威尔树 $t=\mathrm{toB}\,x$ 后再读回、再译 ($t'=\mathrm{toB}(\mathrm{difT}\,x)$), 值从 $\ge1$ 变成 $0$: `no-round : ¬ (t ≼ t′)`.
>
> 原因: `ni` 的分支 $u$ 读坐标的字面形状. $t$ 在坐标 $\omega$ 那一支走 `dif ω` 的各个位置, 位置的坐标是 `((n0 ⨾ _) ⨾ n0) ⨾ _` 这种形状, $u$ 在那里给 $1$. 读回时坐标 $z$ 上的差是 $t$ 的分支从 $\mathrm{toA}\,z$ 到 $\mathrm{toA}\,z+1$ 那一段, 而那一段只在坐标 `n0 ⨾ nw _ (dif (toA z))` 上调用 $u$, 形状不对, 给 $0$. 往返只经规范坐标 (`dif` 的像), 分支在非规范坐标上的值丢了.
>
> 这否定的是 **这一对翻译** (`toB`, `dif₁`) 在值上互逆, 不否定别的翻译. 见 [LayerTr](LayerTr.lagda.md) §3.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LayerTrNeg where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ss)
import OCF.Align.CumReadCF as C
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; ni; nκ; nw)
open import OCF.Align.BrwMidZero using (ωA; lgω)
open import OCF.Align.LayerTrBase
open import OCF.Align.LayerTrOne
```

## §1 读坐标形状的分支

```agda
hit : ∀ {W} → D azero W → Bool
hit (((x ⨾ y) ⨾ n0) ⨾ z) = true
hit _ = false

pk : ∀ {W} → Bool → D one W
pk true = n1
pk false = n0

xᶜ : D one azero
xᶜ = ni (ss C.self) (λ p l w → pk (hit w))

okᶜ : Ok no xᶜ
okᶜ p l w = kp (hit w)
  where
  kp : ∀ b → Ok no (pk {_} b)
  kp true = tt
  kp false = tt

tᶜ : B₁ azero
tᶜ = toB tt xᶜ

Lg-tᶜ : LgB no tᶜ
Lg-tᶜ = Lg-toB no tt xᶜ okᶜ

-- 往返: 差 → 树 → 差 → 树
t′ᶜ : B₁ azero
t′ᶜ = toB tt (difT tt xᶜ okᶜ)
```

## §2 $t\ge1$, $t'$ 值为零

坐标 $\omega$ 那一支 (`dif ω = n0 ⨾ nl (λ _ → n0 ⨾ n1)`), 第 1 个部分和的位置坐标是 `((n0 ⨾ nw _ n0) ⨾ n0) ⨾ nw _ n0`, `hit` 给 `true`.

```agda
big : bs (bz {azero}) ≼ tᶜ
big = ≼i C.self tt ωA lgω (≼l 1 (s≼s z≼))

Zv-I : ∀ {W₀ W} (e : D azero W → B₁ W → B₁ W) → (∀ w b → Zv b → Zv (e w b)) →
       (z : D azero W₀) (q : W₀ ⊲ W) → ∀ w b → Zv b → Zv (I e z q w b)
Zv-Ip : ∀ {W₀ W} (e : D azero W → B₁ W → B₁ W) → (∀ w b → Zv b → Zv (e w b)) →
        (d : ℕ → D azero W₀) (q : W₀ ⊲ W) → ∀ w b → Zv b → ∀ n → Zv (Ip e d q w b n)
Zv-I e ze n0 q w b zb = zb
Zv-I e ze n1 q w b zb = ze w b zb
Zv-I e ze (x ⨾ y) q w b zb = Zv-I e ze y q _ _ (Zv-I e ze x q w b zb)
Zv-I e ze (nl d) q w b zb = Zv-Ip e ze d q w b zb
Zv-I e ze (ni () u) q w b zb
Zv-I e ze (nκ () u) q w b zb
Zv-I e ze (nw p x) q w b zb = Zv-I e ze x (C.⊲-tr p q) w b zb
Zv-Ip e ze d q w b zb zero = zb
Zv-Ip e ze d q w b zb (suc n) = Zv-I e ze (d n) q _ _ (Zv-Ip e ze d q w b zb n)

-- 读回的每一格都是 n0, 所以 t′ 的每一支都只抬升底
small : Zv t′ᶜ
small p l y ly = Zv-I _ (λ w b z → z) _ C.self n0 (bw p bz) tt
```

## §3 否定

```agda
no-round : ¬ (tᶜ ≼ t′ᶜ)
no-round h = no-suc {b = t′ᶜ} small (≼-trans big h)
```
