# 世界内的构造有没有封顶 (二): 判据在哪里变空

> 入口 [TLEnd](TLEnd.lagda.md). **判决: 编译过, 无条件, 前提都可满足 (是全称陈述或构造, 没有假设).** 不读记号. 每条只否定写明的判据形状.
>
> | 定理 | 陈述 | 只否定什么 |
> | --- | --- | --- |
> | `gen-all` | 由 0, 后继, 任意 ℕ-极限生成的类是全部 `Ordᴵ` | 把任意 ℕ-极限算进 "世界内的构造": 这样的类没有上界, 判据空洞 |
> | `cofinal` | 一切 `HS` 树 $t$: 把它喂给高度, 闭包点严格高于 $t$ | "落在某个闭包点之下" 作判据: 一切树都满足 |
> | `no-stop` | 对一切 $\rho$, $M_0$: 有 $M_1$, `suc lvβ(M₀) ≼ lvβ(M₁)` | "世界内的操作在值上走到头". 闭包点没有最后一个 |
> | `diag` | 任何可数的带证书族都有带证书的严格上界 | "一个可数类有上界" 作判据: 永远成立, 不说明任何事 |
>
> 这些都不否定相对封顶 (`rel-cap`), 也不否定对参数无关的类的判据 ([TLEndWord](TLEndWord.lagda.md)).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLEndNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_)
open import OCF.Free.Level hiding (up)
open import OCF.Free.Prefix using (Z; toZ)
open import OCF.Free.Force using (Goodᴺ; gs; gl; forceᴺ; forceᴺ-HS)
open import OCF.Free.Class using (lvG)
open import OCF.Align.LadderOrdPos
open import OCF.Align.LadderOrdCode using (⌈_⌉; _≼_; s≼; l≼ʳ; ≼-trans; ≼-refl)
open import OCF.Align.CrossMNode using (≺→⊑)
open import OCF.Align.CrossNextSum using (addZ; addG; addG≅; lvG-≼; w≼-suc)
open import OCF.Align.LadderOrdStr using (≺→s≼)
open import OCF.Align.CrossMUpTree using (≺-≅ˡ)
open import OCF.Align.TLEndCap
```

## §1 任意 ℕ-极限: 类是全体

`Ordᴵ` 就是由 0, 后继, ℕ-极限生成的. 所以类里只要有后继和任意 ℕ-极限, 就什么都有. 可数的树没有 "ℕ-极限封闭的上界": 这和不可数层相反.

```agda
data Gen : Ordᴵ → Set where
  g0 : Gen zero
  gS : ∀ {x} → Gen x → Gen (suc x)
  gL : ∀ {f s} → (∀ n → Gen (f n)) → Gen (lim f s)

gen-all : ∀ x → Gen x
gen-all zero = g0
gen-all (suc x) = gS (gen-all x)
gen-all (lim f s) = gL (λ n → gen-all (f n))
```

## §2 回灌过任何树

```agda
module _ (rp : ∀ M → Pos (cs M)) (ra : Code → Ordᴵ) where
  open Req rp ra

  cofinal : (t : Ordᶜ zero) (h : HS t) → suc (toLevel t h) ≼ At.lvβ (cs ⌈ toLevel t h ⌉)
  cofinal t h = above (toLevel t h)

  no-stop : ∀ M₀ → Σ Code λ M₁ → suc (At.lvβ M₀) ≼ At.lvβ M₁
  no-stop M₀ = cs ⌈ At.lvβ M₀ ⌉ , above (At.lvβ M₀)
```

## §3 可数族都有上界

带前缀累加: 第 $n+1$ 项字面地以第 $n$ 项为前缀, 单调不看族. 这是 `CrossNextSum.Sum` 的同一个办法, 这里不回灌.

```agda
module Diag (z : ℕ → Z) (G : ∀ n → Goodᴺ (z n)) where
  zA : ℕ → Z
  zA zero = z 0
  zA (suc n) = addZ (Z.suc (zA n)) (z (suc n))

  GA : ∀ n → Goodᴺ (zA n)
  GA zero = G 0
  GA (suc n) = addG (gs (GA n)) (G (suc n))

  st : ∀ n → forceᴺ _ (GA n) ≺ forceᴺ _ (GA (suc n))
  st n = ≺-respʳ (w≼-suc (forceᴺ _ (GA n)) (forceᴺ _ (G (suc n)))) (≅-sym (addG≅ (gs (GA n)) (G (suc n))))

  Ĝ : Goodᴺ (Z.lim zA)
  Ĝ = gl GA (λ n → ≺→⊑ (st n))

  right : ∀ n → lvG (G n) ≼ lvG (GA n)
  right zero = ≼-refl _
  right (suc n) = lvG-≼ (gs (GA n)) (G (suc n))

  -- 严格上界
  diag : ∀ n → suc (lvG (G n)) ≼ lvG Ĝ
  diag n = ≼-trans (s≼ (right n)) (l≼ʳ (suc n) (≺→s≼ (≺lv (GA n) (GA (suc n)) (st n))))
```
