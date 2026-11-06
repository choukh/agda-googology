# 终点下界 (树侧): 高度的值序与 "高度没有顶"

> 不含记号, 不是验收文件. 入口 [EndLow](EndLow.lagda.md). 只导入 `HtFeedTree` (高度 `H`) 与 `CumReadCF` (坐标 `A`).
>
> 结论 (编译过的定理):
>
> 1. `_≤ᴴ_`: 高度 `H` 上的外延值前序, 与 `TLRuleSpec._≤_` 同形, 多一对 $\Omega$-极限的构造子 (`≤hΩ`, `hΩ≤`). 自反, 传递.
> 2. **`no-top : ¬ Σ H (λ Λ → ∀ h → hs h ≤ᴴ Λ)`**: 没有一棵高度严格高于一切高度. `H` 是第二数类的布劳威尔树, 读法下它的值都 $<\Omega_2$; 这条定理是 "$\Omega_2$ 不在 `H` 里" 的树侧形式, 不读记号.
> 3. 正对照 `emb<Ωᴴ`: 一切可数高度 (`emb c`) 都严格低于 `Ωᴴ`. 所以 `no-top` 否定的不是 "高度里没有不可数的元素", 只是 "没有高于一切高度的高度".
>
> 用处见 [EndLowAccept](EndLowAccept.lagda.md) §5: 终点下界在第 3 级 ($\psi_0(\Omega_{\Omega_\Omega})$) 要一棵高度不低于 $\Omega_\Omega$, 在 `H` 里那就是 "高于一切高度" (判断), 而 `no-top` 说这样的高度不存在 (定理).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EndLowH where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim)
open import OCF.Align.HtFeedTree using (H; hz; hs; hl; hΩ)
open import OCF.Align.HtFeedHt using (emb; Ωᴴ)
```

## §1 值序

`hΩ g` 的值是一切坐标上分支的上确界 (坐标取遍 `A`, 不限合法的; `A` 的树都是可数的, 所以这只是第二数类的上确界). 这是 `H` 作为布劳威尔树的值, 不看 `LgH`.

```agda
infix 4 _≤ᴴ_
data _≤ᴴ_ : H → H → Set where
  z≤ᴴ : ∀ {b} → hz ≤ᴴ b
  s≤ᴴ : ∀ {a b} → a ≤ᴴ b → hs a ≤ᴴ hs b
  ≤hl : ∀ {a f} n → a ≤ᴴ f n → a ≤ᴴ hl f
  hl≤ : ∀ {f b} → (∀ n → f n ≤ᴴ b) → hl f ≤ᴴ b
  ≤hΩ : ∀ {a g} c → a ≤ᴴ g c → a ≤ᴴ hΩ g
  hΩ≤ : ∀ {g b} → (∀ c → g c ≤ᴴ b) → hΩ g ≤ᴴ b

≤ᴴ-refl : ∀ a → a ≤ᴴ a
≤ᴴ-refl hz = z≤ᴴ
≤ᴴ-refl (hs a) = s≤ᴴ (≤ᴴ-refl a)
≤ᴴ-refl (hl f) = hl≤ (λ n → ≤hl n (≤ᴴ-refl (f n)))
≤ᴴ-refl (hΩ g) = hΩ≤ (λ c → ≤hΩ c (≤ᴴ-refl (g c)))

≤ᴴ-trans : ∀ {a b c} → a ≤ᴴ b → b ≤ᴴ c → a ≤ᴴ c
≤ᴴ-trans z≤ᴴ q = z≤ᴴ
≤ᴴ-trans p (≤hl n q) = ≤hl n (≤ᴴ-trans p q)
≤ᴴ-trans p (≤hΩ c q) = ≤hΩ c (≤ᴴ-trans p q)
≤ᴴ-trans (hl≤ p) q = hl≤ (λ n → ≤ᴴ-trans (p n) q)
≤ᴴ-trans (hΩ≤ p) q = hΩ≤ (λ c → ≤ᴴ-trans (p c) q)
≤ᴴ-trans (s≤ᴴ p) (s≤ᴴ q) = s≤ᴴ (≤ᴴ-trans p q)
≤ᴴ-trans (≤hl n p) (hl≤ q) = ≤ᴴ-trans p (q n)
≤ᴴ-trans (≤hΩ c p) (hΩ≤ q) = ≤ᴴ-trans p (q c)

≤ᴴ-suc : ∀ {a b} → a ≤ᴴ b → a ≤ᴴ hs b
≤ᴴ-suc z≤ᴴ = z≤ᴴ
≤ᴴ-suc (s≤ᴴ p) = s≤ᴴ (≤ᴴ-suc p)
≤ᴴ-suc (≤hl {f = f} n p) = ≤ᴴ-trans (≤ᴴ-suc p) (s≤ᴴ (≤hl n (≤ᴴ-refl (f n))))
≤ᴴ-suc (hl≤ p) = hl≤ (λ n → ≤ᴴ-suc (p n))
≤ᴴ-suc (≤hΩ {g = g} c p) = ≤ᴴ-trans (≤ᴴ-suc p) (s≤ᴴ (≤hΩ c (≤ᴴ-refl (g c))))
≤ᴴ-suc (hΩ≤ p) = hΩ≤ (λ c → ≤ᴴ-suc (p c))
```

## §2 没有顶

反演: 后继 $\le$ 极限只能经某一支. 非自反 `irrᴴ` 对高度结构递归 (同 `TLRuleSpec.irr`, 多一个 $\Omega$-极限的情形).

```agda
≤hl⁻ : ∀ {a f} → hs a ≤ᴴ hl f → Σ ℕ (λ n → hs a ≤ᴴ f n)
≤hl⁻ (≤hl n p) = n , p

≤hΩ⁻ : ∀ {a g} → hs a ≤ᴴ hΩ g → Σ A (λ c → hs a ≤ᴴ g c)
≤hΩ⁻ (≤hΩ c p) = c , p

irrᴴ : ∀ a → ¬ (hs a ≤ᴴ a)
irrᴴ hz ()
irrᴴ (hs a) (s≤ᴴ p) = irrᴴ a p
irrᴴ (hl f) p with ≤hl⁻ p
... | n , q = irrᴴ (f n) (≤ᴴ-trans (s≤ᴴ (≤hl n (≤ᴴ-refl (f n)))) q)
irrᴴ (hΩ g) p with ≤hΩ⁻ p
... | c , q = irrᴴ (g c) (≤ᴴ-trans (s≤ᴴ (≤hΩ c (≤ᴴ-refl (g c)))) q)

no-top : ¬ Σ H (λ Λ → ∀ h → hs h ≤ᴴ Λ)
no-top (Λ , dom) = irrᴴ Λ (dom Λ)
```

**正对照.** `Ωᴴ` 高于一切可数高度 (`emb c`), 而且严格 (`hs (emb c) ≤ᴴ Ωᴴ`); 所以 `no-top` 否定的不是 "高度里没有不可数的元素", 只是 "没有高于一切高度的高度".

```agda
emb<Ωᴴ : ∀ c → hs (emb c) ≤ᴴ Ωᴴ
emb<Ωᴴ c = ≤hΩ (asuc c) (≤ᴴ-refl (hs (emb c)))
```
