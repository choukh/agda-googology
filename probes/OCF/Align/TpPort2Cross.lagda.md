# 两种种类的 Ω-极限一步 (二): 换世界、换实例

> 入口 [TpPort2](TpPort2.lagda.md). 不含记号. 手写. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`, 不改树、折叠、合法性.
>
> 照 `MonoPort8Sim` §8: 用生成的两世界互模拟 [TpPort2Sim](TpPort2Sim.lagda.md) 证明 **`changeW`**: 不含 Ω-极限的层 $\Lambda$ (以第 1 层为第一位置), 闭项 $T_\Lambda$ (世界 $(1,0)$, 实例 $\Lambda$) 与 $\Omega_\Lambda$ 在**任意**实例 $\Lambda'$ 的**任意**合法世界 $W\ge(0,0)$ 里、任意位置 $e:\Lambda\lhd_{[W]}\Lambda'$ 上折叠到第 0 层的和在值上互相 $\le$. 这是回灌格里的节点 (世界 $V$, 实例 $1\boxplus\mathrm{h\Omega}\,\kappa\,g$) 与较小一边 $T^+(g\,c)$ (世界 $(1,0)$, 实例 $1\boxplus g\,c$) 之间唯一要跨世界的一步. 关系不含回灌, 所以不需要关于 `nκ`, `nμ` 的关系.
>
> 边界 (否定, 定理): `no-κAE`, `no-κHE`: 两世界互模拟没有 `nκ`, `nμ` 的构造子, 两种种类的 Ω-极限层的 $\Omega_L$ 与自己不相关 (一切 $g$, 一切两个世界). 只否定 "本关系覆盖 Ω-极限层", 不否定别的 (带回灌的) 关系.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TpPort2Cross where

open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; z⊲)
open import OCF.Align.TLRuleSpec using (_≤_; ≤-refl)
open import OCF.Align.HtTowerTy using (HB; hz; hs; hΩ; _⊲[_]_; hself; LgB; z⊲ᴮ; E)
open import OCF.Align.HtTowerFTree using (S₁; Ht; Wd₂; LgW₂; D; accᴸ; n0; n1; Ωd; sum; ≤rf) renaming (_≤_ to _≤ʷ_)
open import OCF.Align.HtTowerFClosed using (module At; TΛ; one)
open import OCF.Align.TpPortSim using (Free; free⊲)
open import OCF.Align.TpPort2Sim using (module Two; Re; sumE; symE0; ΩdE; e0; e⨾)
```

## §1 两个实例的闭项

```agda
module Cross (Λ₁ : Ht) (l₁ : LgB Λ₁) (o₁ : ∀ {w} → hs hz ⊲[ w ] Λ₁) (Λ₂ : Ht) (l₂ : LgB Λ₂) (o₂ : ∀ {w} → hs hz ⊲[ w ] Λ₂)
  (fr : ∀ {t m m′} → t ⊲[ m ] Λ₁ → t ⊲[ m′ ] Λ₂ → Free t) where
  open Two Λ₁ l₁ o₁ Λ₂ l₂ o₂ fr public
  module P₁ = At Λ₁ l₁ o₁
  module P₂ = At Λ₂ l₂ o₂

  Act-E : ∀ {ly W W′} → IgE (P₁.Act {ly} {W}) (P₂.Act {ly} {W′})
  Act-E = ige (λ p p′ lV lV′ hw hY → StepE hY)

  Y₀-E : ∀ {W W′} → StE (P₁.Y₀ {W}) (P₂.Y₀ {W′})
  Y₀-E = ste zeroE

-- 值上相等
infix 4 _≃_
_≃_ : A → A → Set
a ≃ b = (a ≤ b) × (b ≤ a)

w₀ : Wd₂
w₀ = azero , hz

-- Ω_Λ 在实例 Λ′、世界 W、位置 e 上折叠到第 0 层的和 (底 1)
TΛ-at : ∀ (Λ′ : Ht) → LgB Λ′ → (∀ {w} → hs hz ⊲[ w ] Λ′) → ∀ Λ {W} → LgW₂ W → w₀ ≤ʷ W → Λ ⊲[ W ] Λ′ → A
TΛ-at Λ′ l′ o′ Λ lW q e = sum one (P.yc (P.Run accᴸ (Ωd Λ {w₀}) q lW e P.Act n0 P.Y₀) (P.τ₀ lW))
  where module P = At Λ′ l′ o′

changeW : ∀ Λ (l : LgB Λ) (o : ∀ {w} → hs hz ⊲[ w ] Λ) → Free Λ →
          ∀ Λ′ (l′ : LgB Λ′) (o′ : ∀ {w} → hs hz ⊲[ w ] Λ′) {W} (lW : LgW₂ W) (q : w₀ ≤ʷ W) (e : Λ ⊲[ W ] Λ′) →
          TΛ Λ l o ≃ TΛ-at Λ′ l′ o′ Λ lW q e
changeW Λ l o fΛ Λ′ l′ o′ lW q e = sumE accᴸ r (≤-refl one) , sumE accᴸ (symE0 accᴸ r) (≤-refl one)
  where
  open Cross Λ l o Λ′ l′ o′ (λ tm _ → free⊲ tm fΛ)
  r = at (Run-E accᴸ accᴸ (ΩdE Λ fΛ accᴸ) (z⊲ one , hself) q (tt , tt) lW hself e Act-E e0 Y₀-E) ≤rf ≤rf (z⊲ᴮ Λ) (z⊲ᴮ Λ′) (tt , tt) lW
```

## §2 边界

```agda
no-κAE : ∀ (g : E S₁ (inj₁ tt) → Ht) {W W′ : Wd₂} → ¬ Re (hΩ (inj₁ tt) g) (Ωd (hΩ (inj₁ tt) g) {W}) (Ωd (hΩ (inj₁ tt) g) {W′})
no-κAE g (e⨾ _ ())

no-κHE : ∀ (g : E S₁ (inj₂ tt) → Ht) {W W′ : Wd₂} → ¬ Re (hΩ (inj₂ tt) g) (Ωd (hΩ (inj₂ tt) g) {W}) (Ωd (hΩ (inj₂ tt) g) {W′})
no-κHE g (e⨾ _ ())
```
