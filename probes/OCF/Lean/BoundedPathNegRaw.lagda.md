# 配对审计：真实 Ω 高度的原始反馈坐标可入

这是一项正面范围检验。对 B=Ω₁ 中第 1 分量的秩 0 新种类，任意合法
原始坐标 c（可含前缀 Ω）都有完整合法源世界使其可入；不使用 ClP 或 PS。
世界在每个可数坐标分量递归复制同一前缀信息，不进行坐标判等。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.BoundedPathNegRaw where
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecLeg using (w₀L; lw₀L)
open import OCF.Lean.LHRecFl using (Lg-up; Lg-ι; flL; Lg-flL)
open import OCF.Lean.BoundedFoldIf

B : HB U
B = flL k
β : Cd
β = hs hz
S = Safe β B

lift : ∀ e → HB (T hz) → HB (T (up e))
lift hz c = c
lift (hs e) c = up (lift e c)
lift (hl f) c = ι 0 (lift (f 0) c)

lift-legal : ∀ e c → LgB c → LgB (lift e c)
lift-legal hz c l = l
lift-legal (hs e) c l = Lg-up _ (lift-legal e c l)
lift-legal (hl f) c l = Lg-ι 0 _ (lift-legal (f 0) c l)

module At (c : HB (T hz)) where
  worlds : ∀ e → Wd (T (up e))
  worlds hz = w₀L P
  worlds (hs e) = worlds e , lift e c
  worlds (hl f) = λ n → worlds (f n)

  worlds-legal : LgB c → ∀ e → LgW (T (up e)) (worlds e)
  worlds-legal l hz = lw₀L P
  worlds-legal l (hs e) = worlds-legal l e , lift-legal e c l
  worlds-legal l (hl f) = λ n → worlds-legal l (f n)

  whole : Wd S
  whole (inj₁ _) = tt , hz
  whole (inj₂ e) = worlds e

  whole-legal : LgB c → LgW S whole
  whole-legal l (inj₁ _) = tt , tt
  whole-legal l (inj₂ e) = worlds-legal l e

κ : K S
κ = (inj₂ (hs hz) , inj₂ tt) , (hself , tt)

admitted : ∀ c → Bd S κ c (At.whole c)
admitted c = hself

raw-world : ∀ c → LgB c → Σ (Wd S) (λ W → LgW S W × Bd S κ c W)
raw-world c l = At.whole c , At.whole-legal c l , admitted c

raw-branch-legal : ∀ (g : E S κ → HB S) → LgB (hΩ κ g) →
  ∀ c → LgB c → LgB (g c)
raw-branch-legal g lg c lc = proj₂ lg (At.whole-legal c lc) (admitted c)

legal-B : LgB B
legal-B = Lg-flL k
legal-β : LgB β
legal-β = tt
```

字面公共高度为 B，内分量坐标 1 在合法 β=1 下，目标秩为 0。
这不是任意 rank、任意 B 或任意 Ctx 的世界截面；它说明上轮缺口在真实
Ω 源中的这一反馈族可直接由原始 LgB 补齐，不能把 ClP 当作必需条件。
翻译账：复制世界由实际层族的递归结构导出，没有新增记号规则或标签。

```agda
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.BoundedFoldClass using (classify; Class; rank)

classified : classify β B (inj₂ (hs hz) , inj₂ tt) (hself , tt) ≡
  rank hz (hLim hself hself) (λ c → c)
classified = refl

constant-input : HB S
constant-input = hΩ κ (λ _ → hz)
constant-legal : LgB constant-input
constant-legal = (λ lw e e′ p → hself) , (λ lw e → tt)
```
