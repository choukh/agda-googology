# `KeepMono` 在主线 `Lw-tw 2` 的根见证上不成立 (对任意派发)

验收文件. 编译定理 (否定, 对任意派发 `D`, 无前提): `Neg.no-keep`, `Neg.no-MW2 : MW (Lw-tw 2) → ⊥`, `Neg.no-refl` (目标层 `tw 2`, 派发 `self` 时 `top` 的像在同层模拟 `Sim` 里不自相关). 反例的下标 `suc zero ⊑ suc top` 合法, 不含极限; 配置 (`tw 2`, `Lw-tw 2`, `self`) 是 `T⁺ʷ` 的内层折叠 (`T⁺ʷ-form`).
否定的是 [YiMono](YiMono.lagda.md) 的同层 `Sim` (结点要位置相同) 作主线的关系, 不否定跨位置的 `Simʰ`: 失败处是两支的保留结点落在 `tw 2` 的不同位置上.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCrossKeepNeg where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using (lev; Way; keep; fold; Ext; R; self; succ; chain; acc-ind)
open import OCF.Lean.YiLamFold using (Kfk; Lw; w0; ws; wl; wΩ; lgl→Lw; Lw-tw; witU)
import OCF.Lean.YiDlFold as W
open import OCF.Lean.YiMono
```

## 1 不变量

`HN P a`: 沿后继, ℕ 极限的某一项, 结点的 `top` 那一支走下去, 遇到位置满足 `P` 的结点. `Sim` 保持它 (`hn`): `bR` 走 `top` 支, `nN` 的两个结点位置相同.
`Cl P`: 没有嵌入, 沿同样的路没有这样的结点; 对 `tw 2` 层的加法与 `succ` 封闭 (`tw 2` 是 Ω 结点层号, `x + top = suc x`, 加法不造结点).

```agda
topP : ∀ K r → SimP K r (Lay.tp (Lo K r)) (Lay.tp (Lo K r))
topP (suc k) (inj₁ _) = tT
topP (suc k) (inj₂ r) = topP k r
topP (lim f) (n , r) = topP (f n) r
topP (lc k g) (η , _ , r) = topP (g η) r

module Inv (P : Pre (tw 2) → Set) where
  HN : Raw (tw 2) → Set
  HN G.zero = ⊥
  HN (G.suc a) = HN a
  HN (G.lim f) = Σ ℕ λ n → HN (f n)
  HN (G.lc r g) = P r ⊎ HN (g (Lay.tp (Lo (tw 2) r)))
  HN (G.em i a) = ⊥
  HN G.top = ⊥

  hn : ∀ {a b} → Sim (tw 2) a b → HN a → HN b
  hn zS ()
  hn (sS d) h = hn d h
  hn (wS d) h = hn d h
  hn (lR n d) h = n , hn d h
  hn (lL f) (n , h) = hn (f n) h
  hn (bR d) h = inj₂ (hn d h)
  hn (nN f) (inj₁ p) = inj₁ p
  hn (nN {r = r} f) (inj₂ h) = inj₂ (hn (f _ _ (topP (tw 2) r)) h)
  hn (eE d) ()
  hn tT ()

  Cl : Raw (tw 2) → Set
  Cl G.zero = ⊤
  Cl (G.suc a) = Cl a
  Cl (G.lim f) = ∀ n → Cl (f n)
  Cl (G.lc r g) = (P r → ⊥) × Cl (g (Lay.tp (Lo (tw 2) r)))
  Cl (G.em i a) = ⊥
  Cl G.top = ⊤

  cl-hn : ∀ a → Cl a → HN a → ⊥
  cl-hn (G.suc a) c h = cl-hn a c h
  cl-hn (G.lim f) c (n , h) = cl-hn (f n) (c n) h
  cl-hn (G.lc r g) (np , c) (inj₁ p) = np p
  cl-hn (G.lc r g) (np , c) (inj₂ h) = cl-hn (g _) c h

  cl-plus : ∀ z b → Cl z → Cl b → Cl (plus (tw 2) z b)
  cl-plus z G.zero cz cb = cz
  cl-plus z (G.suc b) cz cb = cl-plus z b cz cb
  cl-plus z (G.lim f) cz cb = λ n → cl-plus z (f n) cz (cb n)
  cl-plus z (G.lc r g) cz (np , cb) = np , cl-plus z (g _) cz cb
  cl-plus z G.top cz cb = cz

  cl-succ : ∀ y → Cl y → Cl (succ (tw 2) y)
  cl-succ y cy = acc-ind Cl (λ _ z → plus (tw 2) y z) (λ _ z cz → cl-plus y z cy cz) y cy
```

## 2 反例

目标层 `tw 2`, 外部派发 `self (tw 2)`. 第 `suc zero` 支的 `top` 的像是位置 `(suc zero , _ , inj₁ tt)` 上的结点 (`P1`);
第 `suc top` 支的累加里的结点都在 `(top , …)`, `(suc top , …)` 上.

```agda
P1 : Pre (tw 2) → Set
P1 (G.suc G.zero , _ , _) = ⊤
P1 _ = ⊥

module I1 = Inv P1
module I2 = Inv (λ _ → ⊤)

module Neg (D : ∀ k K → Ext k K) where
  open W.Fold D
  open M D

  T : R → Raw (tw 2)
  T = TK (tw 2) {zero} {up zero} (λ η l → lgl→Lw zero tt w0 η l) (self (tw 2))

  lhs : I1.HN (Kfk zero T (G.suc G.zero))
  lhs = 1 , inj₁ tt

  rhs : I1.Cl (Kfk zero T (G.suc G.top))
  rhs = acc-ind I1.Cl (λ _ z → plus (tw 2) z (T (G.suc G.top)))
    (λ _ z cz → I1.cl-plus z (T (G.suc G.top)) cz ((λ ()) , (λ ()) , I1.cl-succ G.top tt))
    (T G.top) ((λ ()) , I1.cl-succ G.top tt)

  no-keep : KeepMono (λ η l → lgl→Lw zero tt w0 η l) (witU zero) → ⊥
  no-keep kh = I1.cl-hn (Kfk zero T (G.suc G.top)) rhs
    (I1.hn (kh (tw 2) (self (tw 2)) {η = G.suc G.zero} {η′ = G.suc G.top} (sS zS)) lhs)

  no-MW2 : MW (Lw-tw 2) → ⊥
  no-MW2 (mΩ Q kh) = no-keep kh

  -- top 的像是位置 (top , tt , inj₁ tt) 上的结点, 分支族是 Kfk zero T; 它不自相关.
  no-refl : Sim (tw 2) (Ψ (tw 2) (Lw-tw 2) (self (tw 2)) G.top) (Ψ (tw 2) (Lw-tw 2) (self (tw 2)) G.top) → ⊥
  no-refl (nN h) = I1.cl-hn (Kfk zero T (G.suc G.top)) rhs (I1.hn (h (G.suc G.zero) (G.suc G.top) (sS zS)) lhs)
  no-refl (bR (nN h)) = I1.cl-hn (succ (tw 2) G.top) (I1.cl-succ G.top tt)
    (I1.hn (h (G.suc G.zero) (G.suc G.zero) (sS zS)) lhs)
  no-refl (bR (bR d)) = I2.cl-hn (succ (tw 2) G.top) (I2.cl-succ G.top tt) (I2.hn d (inj₁ tt))

  -- 这个配置是读法 ψ₀(Ω_{Ω+1}) 的闭项的内层折叠 (链的下一步).
  T⁺ʷ-form : Ψ zero (ws (Lw-tw 2)) (λ _ → fold) G.top ≡
    G.lim (λ n → Ψ zero (Lw-tw 2) (λ _ → fold) (chain (tw 2) (λ η → Ψ (tw 2) (Lw-tw 2) (self (tw 2)) η) n))
  T⁺ʷ-form = refl
```
