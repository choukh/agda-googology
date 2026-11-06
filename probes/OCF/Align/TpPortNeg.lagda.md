# 两种种类的单调 (十五): 边界 (编译过的否定)

> 入口 [TpPort](TpPort.lagda.md). 不含记号. 手写. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.
>
> 1. **`no-κA`, `no-κH`** (照 `HtCrossVNeg.no-κ`): 本组跨实例用的互模拟 `TpPortSim.Rl` 没有 `nκ`, `nμ` 的构造子, 所以两种种类的 Ω-极限层的 $\Omega_L$ 与自己不相关. 只否定 "这个关系覆盖 Ω-极限层的 $\Omega_L$", 不否定别的关系 (例如带回灌的、异质世界的) 能做到.
> 2. **`id≤T`, `no-all`** (照 `MonoPort9Neg`): 一切可数 $a$, $a\le T^+(a)$; 所以对任何合法 $\Lambda$, "对一切可数 $a$, $T^+(a)<T^+(\Lambda)$" 是假的 (反例 $a=T^+(\Lambda)$). 只否定 "一切 $a$, 无界" 这一形状; 带界的陈述 (例如 `TpPortTab` 的 `grow≪`, 两边都给出) 不受影响.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TpPortNeg where

open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₂)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; Lg)
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; l≤; ≤-refl; ≤-trans; ≤-suc; irr)
open import OCF.Align.HtTowerTy using (hz; hs; hl; hΩ; hself; hsuc; hlim; LgB; E)
open import OCF.Align.HtTowerFTree using (Ht; S₁; Wd₂; Ωd)
open import OCF.Align.HtTowerFClosed using (T⁺; Lg-T⁺)
open import OCF.Align.TpMonoIf using (psuc; plim)
open import OCF.Align.TpPortSim using (Rl; s⨾)
open import OCF.Align.TpPortStep using (fst<F)
open import OCF.Align.TpPortTab using (embᵀ; Lg-emb; free-emb; TE)
```

## §1 不含回灌的互模拟装不下 Ω-极限层

```agda
no-κA : ∀ (g : E S₁ (inj₁ tt) → Ht) {W : Wd₂} → ¬ Rl (hΩ (inj₁ tt) g) (Ωd (hΩ (inj₁ tt) g) {W}) (Ωd (hΩ (inj₁ tt) g) {W})
no-κA g (s⨾ _ ())

no-κH : ∀ (g : E S₁ (inj₂ tt) → Ht) {W : Wd₂} → ¬ Rl (hΩ (inj₂ tt) g) (Ωd (hΩ (inj₂ tt) g) {W}) (Ωd (hΩ (inj₂ tt) g) {W})
no-κH g (s⨾ _ ())
```

## §2 无界的 "一切可数 $a$" 不成立

```agda
id≤T : ∀ a (la : Lg a) → a ≤ TE a la
id≤T azero la = z≤
id≤T (asuc a) la = ≤-trans (s≤ (id≤T a la)) (fst<F (embᵀ a) (Lg-emb a la) (embᵀ (asuc a)) (Lg-emb a la) (free-emb a) (psuc hself))
id≤T (alim f) (st , l) =
  l≤ (λ n → ≤-trans (id≤T (f n) (l n))
              (≤-trans (≤-suc (≤-refl (TE (f n) (l n))))
                 (fst<F (embᵀ (f n)) (Lg-emb (f n) (l n)) (embᵀ (alim f)) (Lg-emb (alim f) (st , l)) (λ m → free-emb (f m)) (plim n hself))))

-- 任何合法高度 Λ: 不是一切可数高度都在 T⁺ Λ 之下 (反例 a = T⁺ Λ)
no-all : ∀ Λ (lΛ : LgB Λ) → ¬ (∀ a (la : Lg a) → asuc (TE a la) ≤ T⁺ Λ lΛ)
no-all Λ lΛ h = irr a (≤-trans (s≤ (id≤T a la)) (h a la))
  where
  a = T⁺ Λ lΛ
  la = Lg-T⁺ Λ lΛ
```
