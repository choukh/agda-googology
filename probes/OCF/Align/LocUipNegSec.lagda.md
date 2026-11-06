# 局部 UIP 的否定一路 (三): 截面的值作增量时, 单个增量写法无条件相干

> 不含记号. 入口 [LocUipNeg](LocUipNeg.lagda.md), 接口 [LocUipIf](LocUipIf.lagda.md) (定稿 2026-11-05 10:45, 无变更). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> 构造一路的第一个障碍 (判断): 读回值只在 $c_0$ 处算出, 化成族 `Inc` 的三条路都没走通. 本篇把这个障碍说准: `IncIrr` 失败 (若失败) 只会发生在**不是截面之值**的增量上. 若读回值是某个对坐标一致定义的函数 $F : $ `Inc` 在 $c_0$ 处的值 $\delta = F\,c_0$, 则
>
> - `sec-subst`: 沿任一相等证明 $e : c_0\equiv c$ 搬运 $F\,c_0$ 得 $F\,c$ (对终点自由的 J, 不用 K);
> - `sec→irr`: `IncIrr` 对这样的 $\delta$ 无条件成立; `sec→coh`: `raise₀ᴮ` 对这样的 $\delta$ 无条件保 `Coh≡`;
> - `sec-agree`: 此时 `raise₀ᴮ` 与族增量的 `LocUipNegFeed.raiseFᵒ` (族取 $F$) 逐分量相等.
>
> 所以 "化成族" 与 "读回值是截面的值" 是同一件事, 与 UIP 无关: 要的不是相等证明唯一, 而是回灌对坐标一致 (同一个定义对一切 $c$ 都给出读回, $c_0$ 处的值是它的特例). 这是一个陈述的改写, 不是新的构造: 回灌能否写成对坐标一致的函数, 本篇不判断. 与 `LocUipNegLoop` 的关系: `LoopFix` 要求**一切** $\delta$ 被环固定; 截面的值总被固定 (`sec-subst` 在环上的特例), 那里的困难只对非截面的值.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LocUipNegSec where

open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)
open import OCF.Align.HtTowerTy
open import OCF.Align.AdmWIf
open import OCF.Align.AdmWCoh using (incD; dD; raise₀; raise₀ᴮ)
open import OCF.Align.LocUipIf
open import OCF.Align.LocUipNegFeed using (bD; raiseFᵒ)
open Slot
open RaiseIf

sec-subst : ∀ (F : Inc) {c₀ c : HB S₀} (e : c₀ ≡ c) → subst (λ z → HB (G₀ z)) e (F c₀) ≡ F c
sec-subst F refl = refl

sec-incD : ∀ (F : Inc) {c₀ c : HB S₀} (d : (c₀ ≡ c) ⊎ ¬ (c₀ ≡ c)) → incD d (F c₀) ≡ bD d F
sec-incD F (inj₁ e) = sec-subst F e
sec-incD F (inj₂ _) = refl

sec→irr : ∀ (F : Inc) w (lo : LgO w) {c₀ c : HB S₀} (p₀ : AdmE w c₀) (p p′ : AdmE w c) →
  incD (dD w lo p p₀) (F c₀) ≡ incD (dD w lo p′ p₀) (F c₀)
sec→irr F w lo p₀ p p′ = h (dD w lo p p₀) (dD w lo p′ p₀)
  where
  h : ∀ {c₀ c : HB S₀} (d d′ : (c₀ ≡ c) ⊎ ¬ (c₀ ≡ c)) → incD d (F c₀) ≡ incD d′ (F c₀)
  h (inj₁ e) (inj₁ e′) = trans (sec-subst F e) (sym (sec-subst F e′))
  h (inj₁ e) (inj₂ ne) = ⊥-elim (ne e)
  h (inj₂ ne) (inj₁ e) = ⊥-elim (ne e)
  h (inj₂ _) (inj₂ _) = refl

sec→coh : ∀ (F : Inc) w lo v c₀ p₀ → Coh≡ (w , v) → Coh≡ (w , raise₀ w lo v c₀ p₀ (F c₀))
sec→coh F w lo v c₀ p₀ coh c p p′ =
  cong₂ (λ X t → proj₁ X , (proj₂ X ⊞ t)) (coh c p p′) (sec→irr F w lo p₀ p p′)

sec-agree : ∀ (F : Inc) w lo v c₀ p₀ c (p : AdmE w c) →
  raise₀ w lo v c₀ p₀ (F c₀) c p ≡ RaiseF.raiseF raiseFᵒ w lo v c₀ p₀ F c p
sec-agree F w lo v c₀ p₀ c p = cong (λ t → proj₁ (v c p) , (proj₂ (v c p) ⊞ t)) (sec-incD F (dD w lo p p₀))
```

**前提实例.** 任一 `F : Inc`, 例如 `λ c → hz`; 截面的值不必合法 (`sec→coh` 不要求).

**档.** `sec-subst`, `sec-incD`, `sec→irr`, `sec→coh`, `sec-agree`: 定理. "回灌能否写成对坐标一致的函数": 未判断.
