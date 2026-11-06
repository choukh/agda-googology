# Ω-极限高度 (否定): "一切可数高度 $a$ 都有 $T_a < T_\Lambda$" 对任何 $\Lambda$ 都不成立

> 入口 [MonoPort9](MonoPort9.lagda.md). 不含记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`.
>
> 接手清单第 4 项想要 "对一切可数高度 $a$, $T_a < T_\Omega$, 无前提". 这里证明它是假的, 而且对**任何**合法高度 $\Lambda$ 都假:
>
> - `id≤T`: 一切合法的可数 $a$, $a \le T_{\mathrm{emb}\,a}$. 后继一步用 `MonoPort7Lim.Suc.growS`, 极限一步用 `MonoPort7Lim.Lim.growL` (对一切 `hl f` 成立, 不要求相邻项严格递增).
> - `no-all`: 取 $a = T_\Lambda$ 本身 (它是合法的, `At.Lg-Tψ`), 则 $T_a < T_\Lambda = a \le T_a$, 与 `irr` 矛盾.
>
> 只否定这一个陈述形状: 对**一切** $a$ 无条件的 $T_a<T_\Lambda$. 它不否定 "对一切走过的坐标 $c$ 之下的 $a$" (那是 [MonoPort9Cell](MonoPort9Cell.lagda.md) 的正面结果), 也不说 $T_a<T_\Omega$ 在哪个 $a$ 处开始失败 (判断: 在 $T_\Omega$ 附近或更低; 本文只用到 $a=T_\Omega$ 处失败).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.MonoPort9Neg where

open import Data.Product using (_,_; proj₂)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; Lg)
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; l≤; ≤-refl; ≤-trans; ≤-suc; irr)
open import OCF.Align.HtFeedTree using (H; LgH)
open import OCF.Align.HtFeedClosed using (module At; TΛ)
open import OCF.Align.HtFeedHt using (emb; Lg-emb; Ωᴴ; Lg-Ωᴴ)
open import OCF.Align.HtCrossVInst using (free-emb)
open import OCF.Align.MonoPort7Lim using (module Suc; module Lim; TE)
```

## 1 $a \le T_a$

```agda
id≤T : ∀ a (la : Lg a) → a ≤ TE a la
id≤T azero la = z≤
id≤T (asuc a) la = ≤-trans (s≤ (id≤T a la)) (Suc.growS (emb a) (free-emb a) (Lg-emb a la))
id≤T (alim f) (st , l) =
  l≤ (λ n → ≤-trans (id≤T (f n) (l n))
              (≤-trans (≤-suc (≤-refl (TE (f n) (l n)))) (Lim.growL (λ m → emb (f m)) (Lg-emb (alim f) (st , l)) (λ m → free-emb (f m)) n)))
```

## 2 否定

```agda
-- 任何合法高度 Λ: 不是一切可数高度都在 T_Λ 之下 (反例 a = T_Λ)
no-all : ∀ Λ (lΛ : LgH Λ) → ¬ (∀ a (la : Lg a) → asuc (TE a la) ≤ TΛ Λ lΛ)
no-all Λ lΛ h = irr a (≤-trans (s≤ (id≤T a la)) (h a la))
  where
  a = TΛ Λ lΛ
  la = At.Lg-Tψ Λ lΛ

-- 特例 Ω: "对一切可数 a, T_a < T_Ω" 是假的
no-allΩ : ¬ (∀ a (la : Lg a) → asuc (TE a la) ≤ TΛ Ωᴴ Lg-Ωᴴ)
no-allΩ = no-all Ωᴴ Lg-Ωᴴ
```
