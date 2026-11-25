# 规范 Ω 的第三步失败：Raw Ω 分支仍可常值

本篇只检验已冻结的 Legalˢˢ，不改 Core 的 Raw、Lgl 或原 Ω 算法。
输入2有 Legalˢˢ，但 Ω̂2 的一个合法 Raw1 分支读回后不满足新增的严格单调性。
所选坐标的外层守卫、Raw 第一支到各分支都有真路径；内层所测两个坐标也
严格高于守卫下界。因此失败不靠下界等号或第一支停顿，而来自 Raw 的
Lgl.lc 仍允许用 Cp.self 证明常分支单调。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiLglAllStop where

open import Data.Nat.Base using (ℕ; suc)
open import Data.Unit.Base using (tt)
open import Data.Empty using (⊥)
open import Data.Product.Base using (_,_; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.YiLglCore as F
open F using (module G)
import OCF.Align.YiLglVal as V
import OCF.Align.YiLglStrict as S
import OCF.Align.YiLglFoldPause as P
open import OCF.Align.YiLglAllBase using (Legalˢˢ)
import OCF.Align.YiLglAllBase as B

One Two OmegaOne : F.LF
One = F.suc F.zero
Two = F.suc One
OmegaOne = V.Ω̂ One

two-legal : Legalˢˢ Two
two-legal = tt

omega-one-legal : Legalˢˢ OmegaOne
omega-one-legal = B.omega-one-legal

raw1 raw2 raw3 : F.Raw F.zero
raw1 = G.suc G.zero
raw2 = G.suc raw1
raw3 = G.suc raw2

raw2-guard : F.Gd F.zero raw1 raw2
raw2-guard = inj₂ (inj₁ refl) , tt

raw3-guard : F.Gd F.zero raw1 raw3
raw3-guard = inj₂ (inj₂ (inj₁ refl)) , tt

raw1-below-raw2 : F.Dn F.zero raw1 raw2
raw1-below-raw2 = inj₁ refl

raw1-below-raw3 : F.Dn F.zero raw1 raw3
raw1-below-raw3 = inj₂ (inj₁ refl)

raw2-below-raw3 : F.Dn F.zero raw2 raw3
raw2-below-raw3 = inj₁ refl

-- Raw1 的首个 Ω 槽；其低层域仍是原 Raw0。
eta : F.Raw One
eta = G.lc (inj₁ tt) raw1 G.top (λ _ _ → G.suc G.top)

eta-first-step : F.Dn One G.top (G.suc G.top)
eta-first-step = inj₁ refl

eta-lawful : F.Lgl One eta
eta-lawful =
  (λ _ _ → inj₂ eta-first-step) ,
  (λ _ _ _ _ _ → inj₁ refl) ,
  (λ _ _ _ → refl) , tt , (λ _ _ → tt)

-- 外层守卫走 lc 的第一支，是 Dn 真路径而非下界相等。
eta-above-top : F.Dn One G.top eta
eta-above-top = inj₁ refl

eta-guard : F.Gd One (V.cO One) eta
eta-guard = inj₂ eta-above-top , eta-lawful

bad : F.LF
bad = F.lc F.zero raw1 OmegaOne (λ _ _ → F.suc OmegaOne)

eta-read : V.up One eta ≡ bad
eta-read = refl

bad-first-strict : (η : F.Raw F.zero) → F.Gd F.zero raw1 η →
  S.Properˢ OmegaOne (F.suc OmegaOne)
bad-first-strict η e = S.under-suc V.self
```

bad 的第一支到每个分支也有 Properˢ 真路径；不能把它的失败归因于
新增定义保留第一支弱 CP。真正冲突发生在严格坐标 raw2 到 raw3：
两个分支都为 suc Ω̂1。下面沿 Ω̂1 的有限第一支1排除该树到自身的真路径。

```agda
no-finite-suc-omega-one : P.Finite (F.suc OmegaOne) → ⊥
no-finite-suc-omega-one (P.finite-suc ())

no-proper-suc-omega-one : S.Properˢ (F.suc OmegaOne) (F.suc OmegaOne) → ⊥
no-proper-suc-omega-one (S.under-suc (V.fst p)) =
  no-finite-suc-omega-one
    (P.finite-position p (P.finite-suc P.finite-zero))

no-bad : Legalˢˢ bad → ⊥
no-bad (lk , first , strict , same , lt , lg) =
  no-proper-suc-omega-one
    (strict raw2 raw2-guard raw3 raw3-guard raw2-below-raw3)

no-omega-two : Legalˢˢ (V.Ω̂ Two) → ⊥
no-omega-two (lk , first , strict , same , lt , lg) =
  no-bad (lg eta eta-guard)

no-omega-preservation :
  (∀ x → Legalˢˢ x → Legalˢˢ (V.Ω̂ x)) → ⊥
no-omega-preservation preserve = no-omega-two (preserve Two two-legal)
```

因此规范 Ω 的全层闭包已经失败；不继续尝试 ψ。
还能直接指出既有塔的失败位置：第三项 Ω̂(Ω̂1) 的根合法坐标 raw2
读回分支正是 Ω̂2。这里用的是该塔自己的根分支，不把 Raw(Ω̂1)
中的另一个坐标误说成它的根分支。

```agda
tower3 : F.LF
tower3 = V.Ω̂ OmegaOne

tower3-form : V.tw 3 ≡ tower3
tower3-form = refl

tower3-raw2 :
  V.Ω̂ (V.up F.zero raw2) ≡ V.Ω̂ Two
tower3-raw2 = refl

no-tower3 : Legalˢˢ tower3 → ⊥
no-tower3 (lk , first , strict , same , lt , lg) =
  no-omega-two (lg raw2 raw2-guard)

no-all-towers : (∀ n → Legalˢˢ (V.tw n)) → ⊥
no-all-towers lawful = no-tower3 (lawful 3)

no-Lambda : Legalˢˢ V.Λ → ⊥
no-Lambda lawful = no-tower3 (proj₂ lawful 3)
```

以上否定只针对本轮冻结的 Legalˢˢ 与未改的规范 Ω／塔／Λ。
two-legal、omega-one-legal、eta-guard 以及严格坐标证据都已实填，
没有假定完整折叠存在。常 Ω 分支在旧 Raw 的 Lgl 中仍合法，
本篇既不加强它，也不补新的正则形状。没有给这些坐标的 EBO Reach
选择证据，不称实际记号基本列或实际 ψ／γ 输出反例。
