# `T⁺` 对输入单调 (二): 律的形状可满足

> 不含记号. 接口 [TpMonoIf](TpMonoIf.lagda.md). 给接口的四条律 (`Laws`) 一个实例 `F₀`, 说明律的**形状**本身不矛盾: 用接口推出的条件定理 ([TpMonoTab](TpMonoTab.lagda.md)) 不是空真的 (手册 §3.13). `F₀` 不是 `T⁺`, 这里**不**说 `T⁺` 满足这些律.
>
> `rk`: 高度的结构秩 ($0$, 后继, ℕ-极限取极限再加一, $\Omega$-极限取最小坐标的分支再加一). 它不看合法性. 四条律都对它成立 (`toy`), 一步律也成立 (`toySteps`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TpMonoToy where

open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim)
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (S₁; Ht)
open import OCF.Align.DiagK3Zero using (≈z; ≈s; ≈l; ≈Ω)
open import OCF.Align.TpMonoIf
open import OCF.Align.TpMonoStep using (laws)

rk : Ht → A
rk hz = azero
rk (hs h) = asuc (rk h)
rk (hl f) = asuc (alim (λ n → rk (f n)))
rk (hΩ κ g) = asuc (rk (g (bot S₁ κ)))

F₀ : Fn
F₀ h _ = rk h

rk-≈ : ∀ {a b : Ht} → a ≈ b → rk a ≤ rk b
rk-≈ ≈z = z≤
rk-≈ (≈s p) = s≤ (rk-≈ p)
rk-≈ (≈l p) = s≤ (l≤ (λ n → ≤l n (rk-≈ (p n))))
rk-≈ {hΩ κ f} (≈Ω p) = s≤ (rk-≈ (p (bot S₁ κ)))

rk-⊞ : ∀ (a b : Ht) → rk b ≤ rk (a ⊞ b)
rk-⊞ a hz = z≤
rk-⊞ a (hs b) = s≤ (rk-⊞ a b)
rk-⊞ a (hl f) = s≤ (l≤ (λ n → ≤l n (rk-⊞ a (f n))))
rk-⊞ a (hΩ κ g) = s≤ (rk-⊞ a (g (bot S₁ κ)))

toySteps : Steps F₀
toySteps = record
  { irr  = λ a la la′ → ≤-refl (rk a)
  ; s-hs = λ a la → ≤-refl (asuc (rk a))
  ; s-hl = λ f lf n → s≤ (≤l n (≤-refl (rk (f n))))
  ; s-hΩ = λ κ g lg lc → ≤-refl (asuc (rk (g (bot S₁ κ))))
  }

toy : Laws F₀
toy = laws (λ a la b lb e → rk-≈ e) toySteps (λ a la b lb → rk-⊞ a b)
```
