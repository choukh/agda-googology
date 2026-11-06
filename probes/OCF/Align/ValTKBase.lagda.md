# TK 的值 (一): 对照闭项 `TK₀`, $\kappa_1$ 结点的两种输出, 坐标的攀升

> 不含记号. 入口 [ValTK](ValTK.lagda.md). 第 4 层: 只新增定义 (对照闭项) 与定理, 不改树, 折叠, 合法性. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP 作前提.
>
> - **§1 对照闭项 `TK₀`.** 与 [KindLvTw](KindLvTw.lagda.md) 的 `TK` 同一个坍缩 `ColL`, 同一个塔 (同一个 $\Lambda$, `lΛ`, `one⊲`), 同一个 `GΛ`; 只把级回灌换成平凡的 `lv₀ = λ _ → inj₂ tt`. 于是 $\kappa_1$ 退回 `fbA GΛ κ₁ = inj₂ tt` (有损), 其余种类与 `TK` 相同 (`lv-off`: 除 $\kappa_1$ 外 `lvΛ` 与 `lv₀` 逐点相等). 这就是 "把 $\kappa_1$ 换成有损的同一折叠".
> - **§2 $\kappa_1$ 结点在第 0 层目标上的两种输出 [定理, `refl`].** `node₀`: 有损的一边是 "当前世界里分支的输出, 重复 $\omega$ 次" (`ω⋅ (drp c)`); `nodeK`: 按级回灌的一边是 $\omega$ 格的极限, 第 $n$ 格是分支在升高的世界 $w_{n+1}$ 里的输出 (`nl (λ n → drp Δₙ)`). 两边**用的是两份折叠** (模块参数 `lv` 不同), 结点以外逐行相同.
> - **§3 坐标的攀升 [定理].** 按级回灌一边第 $n$ 格的世界里 $\kappa_1$ 的顶坐标 $v_n$ 构成第一位置的链: $\mathrm{top}_W\lhd v_0$, $v_n\lhd v_{n+1}$ (`climb₀`, `climb`, 每步在当时的世界里), 世界逐格变大 (`qA`), 顶就是读回的值 (`top-rd₀`, `top-rd`, `refl`). 有损的一边分支只在当前世界的顶上取 (`node₀` 的 `u q₀ lW`). 只是形状与第一位置 (不严格), 不说大小 (手册 §3.3).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ValTKBase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; Lg)
import OCF.Free.Level as FLv
open import OCF.Align.HtTowerTy
open import OCF.Align.GenFoldIf using (AccY; tpK; top; fbA; module FoldTy; nl)
open import OCF.Align.GenFoldTree using (module Tree)
open import OCF.Align.LvKtIf using (KΛc)
open import OCF.Align.NewTwrColl using (GΛ; LdΛ; flΛ)
open import OCF.Align.KindLvIf using (LvFb; KLv; ℓ⊲; rd; rd-fst)
open import OCF.Align.KindLvTw using (module ColL; Λ; lΛ; one⊲; lvΛ; κ₁; K1; ordK)
open import OCF.Align.NegKindLvInst using (only-κ₁)
import OCF.Align.KindLvRun as KR
```

## §1 对照闭项

```agda
lv₀ : LvFb KΛc (tpK GΛ) Λ
lv₀ _ = inj₂ tt

module C0 = ColL GΛ LdΛ flΛ Λ lΛ one⊲ lv₀

TK₀ : A
TK₀ = C0.Tψ

Lg-TK₀ : Lg TK₀
Lg-TK₀ = C0.Lg-Tψ

fghK₀ : ℕ → ℕ
fghK₀ = FLv.FGH (ordK TK₀)

-- 两个级回灌只在 κ₁ 处不同
lv-off : ∀ κ → ¬ (κ ≡ κ₁) → lvΛ κ ≡ lv₀ κ
lv-off κ ne with lvΛ κ in eq
... | inj₁ L = ⊥-elim (ne (only-κ₁ κ L eq))
... | inj₂ tt = refl

lv-on₀ : lv₀ κ₁ ≡ inj₂ tt
lv-on₀ = refl

lv-onK : lvΛ κ₁ ≡ inj₁ K1
lv-onK = refl

-- 有损的一边退回的是 GΛ 的有损行
fb-κ₁ : fbA GΛ κ₁ ≡ inj₂ tt
fb-κ₁ = refl
```

## §2 $\kappa_1$ 结点的两种输出

两份折叠: `NK` (按级回灌, `TK` 用的) 与 `N0` (平凡级回灌, `TK₀` 用的). 结点是旧种类 `inj₁ κ₁` 的闭包结点, 目标层 $0$.

```agda
module NK = KR KΛc GΛ LdΛ flΛ Λ lΛ one⊲ lvΛ
module N0 = KR KΛc GΛ LdΛ flΛ Λ lΛ one⊲ lv₀

open Tree KΛc using (L₀; D; drp; ≤rf)
open FoldTy KΛc Λ using (LW; Tg; tg; Ig; St; Df; module Df)
open Df using (yc)

module Node {ly W₀ W} (ac : AccY ly) (u : NK.Bu ly W₀) (q₀ : _≤w_ L₀ W₀ W) (lW : LgW L₀ W)
            (ll : LW ly W) (A₀ : Ig ly W) (w : D ly W) (Y : St W) where

  -- 按级回灌一边第 n 格的记录 (世界 wA, 状态 SA, 前缀 coA)
  c : ℕ → NK.ClA W ly
  c n = NK.κcL ac K1 u q₀ lW ll A₀ w Y n

  node₀ : ∀ {m} (Tq : Tg W hz m) →
          N0.RKc ac (inj₁ κ₁) u q₀ lW ll A₀ w Y hz Tq
            ≡ N0.ω⋅ (drp (yc (N0.Run ac (u q₀ lW) ≤rf lW ll A₀ w Y) (N0.τ₀ lW)))
  node₀ Tq = refl

  nodeK : ∀ {m} (Tq : Tg W hz m) →
          NK.RKc ac (inj₁ κ₁) u q₀ lW ll A₀ w Y hz Tq
            ≡ nl (λ n → drp (yc (NK.κΔA ac u q₀ lW ll A₀ (c n)) (NK.τ₀ (NK.lwA (c n) , proj₂ lW))))
  nodeK Tq = refl
```

## §3 坐标的攀升

```agda
  -- 第 n 格分支所在的世界里 κ₁ 的顶就是读回的值
  top-rd₀ : top (tpK GΛ) κ₁ (NK.wA (c 0))
            ≡ rd K1 lW (top (tpK GΛ) κ₁ (proj₁ W)) (yc (NK.d Y) (tg ≤rf (ℓ⊲ K1) lW))
  top-rd₀ = refl

  top-rd : ∀ n → top (tpK GΛ) κ₁ (NK.wA (c (suc n)))
           ≡ rd K1 (NK.lwA (c n) , proj₂ lW) (top (tpK GΛ) κ₁ (NK.wA (c n)))
                (yc (NK.κΔA ac u q₀ lW ll A₀ (c n)) (tg ≤rf (ℓ⊲ K1) (NK.lwA (c n) , proj₂ lW)))
  top-rd n = refl

  climb₀ : Pr KΛc κ₁ (proj₁ W) (top (tpK GΛ) κ₁ (proj₁ W)) (top (tpK GΛ) κ₁ (NK.wA (c 0)))
  climb₀ = rd-fst K1 lW (top (tpK GΛ) κ₁ (proj₁ W)) (yc (NK.d Y) (tg ≤rf (ℓ⊲ K1) lW))

  climb : ∀ n → Pr KΛc κ₁ (NK.wA (c n)) (top (tpK GΛ) κ₁ (NK.wA (c n))) (top (tpK GΛ) κ₁ (NK.wA (c (suc n))))
  climb n = rd-fst K1 (NK.lwA (c n) , proj₂ lW) (top (tpK GΛ) κ₁ (NK.wA (c n)))
              (yc (NK.κΔA ac u q₀ lW ll A₀ (c n)) (tg ≤rf (ℓ⊲ K1) (NK.lwA (c n) , proj₂ lW)))

  -- 世界逐格变大 (相对结点所在的世界)
  up-w : ∀ n → _≤w_ KΛc (proj₁ W) (NK.wA (c n))
  up-w n = NK.qA (c n)
```
