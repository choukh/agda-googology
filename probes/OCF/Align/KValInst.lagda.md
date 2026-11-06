# `nκ` 的值语义 (六): 实例, `Step` 满足前提

> 不含记号. 入口 [KVal](KVal.lagda.md). `Step` (闭项里每个 `n1` 的动作) 跨世界、对一切路径满足 `KValSound.HA⁺`, 并且路径一致 (`CohA`). 所以 `lo` 档的折叠单调 `snd-lo` 在 `Step` 的上下文里无前提 (`mono-lo`). 另: `DValNeg` 的 `uκ` 不满足 `κ⊑` 的判据 (`uκ-not-KMono`), 所以 `¬κ-refl` 的反例不在新关系里.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.KValInst where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; Tg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans)
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; nκ; sum; pt; cnt; Ωd)
import OCF.Align.SumOneClosed as F
open import OCF.Align.LayerTrOne using (one)
open import OCF.Align.KValTree
open import OCF.Align.KValSem
open import OCF.Align.KValSound
import OCF.Align.DValNeg as N
```

## §1 `Step`

```agda
StepA : ∀ {W} → F.Ig (cnt one) W
StepA _ _ _ Y = F.Step Y

-- 一步之后: ω 份 (1 ⨾ 0) ⨾ 差; 对差的值单调
step≤ : ∀ {V V′} (s : D azero V) (s′ : D azero V′) c c′ → c ≤ c′ → val s ≤ val s′ →
        sum c (nl (λ _ → Ωd azero C.self tt ⨾ s)) ≤ sum c′ (nl (λ _ → Ωd azero C.self tt ⨾ s′))
step≤ s s′ c c′ cb r = l≤ (λ n → ≤l n (go n))
  where
  go : ∀ n → pt c (λ _ → Ωd azero C.self tt ⨾ s) n ≤ pt c′ (λ _ → Ωd azero C.self tt ⨾ s′) n
  go zero = cb
  go (suc n) = svmono s s′ (s≤ (go n)) r

HA-Step : ∀ {W W′} {lW : Lg W} {lW′ : Lg W′} {ll : one ⊲ W} {ll′ : one ⊲ W′} → HA⁺ (sd W lW ll StepA) (sd W′ lW′ ll′ StepA)
HA-Step p p′ lV lV′ w w′ Y Y′ k k′ cY cY′ r c c′ cb =
  step≤ (F.yc (F.d Y) (inj₁ k) tt) (F.yc (F.d Y′) (inj₁ k′) tt) c c′ cb r

Coh-Step : ∀ {W} → CohA (StepA {W})
Coh-Step p lV w Y cY = cd (λ τ τ′ c → step≤ (F.yc (F.d Y) τ tt) (F.yc (F.d Y) τ′ tt) c c (≤-refl c) (cyA cY τ τ′))

ok-Step : ∀ {W W′} (lW : Lg W) (lW′ : Lg W′) (ll : one ⊲ W) (ll′ : one ⊲ W′) → Ok (sd W lW ll StepA) (sd W′ lW′ ll′ StepA)
ok-Step lW lW′ ll ll′ = ok (HA-Step {lW = lW} {lW′} {ll} {ll′}) (HA-Step {lW = lW} {lW} {ll} {ll}) (HA-Step {lW = lW′} {lW′} {ll′} {ll′}) Coh-Step Coh-Step
```

## §2 `lo` 档在 `Step` 的上下文里无前提

两边世界任取, 状态路径一致且值可比 ⇒ 输出可比.

```agda
mono-lo : ∀ {V V′} {x : D one V} {x′ : D one V′} → x ⊑[ lo ] x′ →
          ∀ {W W′} (lW : Lg W) (lW′ : Lg W′) (ll : one ⊲ W) (ll′ : one ⊲ W′) (q : V ⊲ W) (q′ : V′ ⊲ W′) w w′ Y Y′ →
          CohY Y → CohY Y′ → vYk (κ₀ ll) Y ≤ vYk (κ₀ ll′) Y′ → ∀ c c′ → c ≤ c′ →
          Ob (sd W lW ll StepA) c x q w Y ≤ Ob (sd W′ lW′ ll′ StepA) c′ x′ q′ w′ Y′
mono-lo h lW lW′ ll ll′ q q′ w w′ Y Y′ cY cY′ r =
  snd-lo h (sd _ lW ll StepA) (sd _ lW′ ll′ StepA) (ok-Step lW lW′ ll ll′) q q′ w w′ Y Y′ (cx cY cY′ r tt)
```

## §3 `¬κ-refl` 的分支不满足判据

`uκ` 在字面的层 $1$ 上给 `n1`, 在值也是 $1$ 的层 $\lim_n 1$ 上给 `n0`. 判据要求 $1\le\lim_n1$ 时 $u(1)\sqsubseteq_{\mathsf{lo}}u(\lim_n 1)$, 由 `mono-lo` 推出 $c+\omega\le c$ 一类的矛盾.

```agda
lim1 : A
lim1 = alim (λ _ → one)

lg1 : Lg lim1
lg1 = (λ _ → C.self) , (λ _ → tt)

one⊲lim1 : one ⊲ lim1
one⊲lim1 = C.lim 0 C.self

1≤lim1 : one ≤ lim1
1≤lim1 = ≤l 0 (≤-refl one)

-- n1 ⊑ n0 在 lo 档不成立: Step 的输出非零
no-10 : ¬ (n1 {W = one} ⊑[ lo ] n0 {W = lim1})
no-10 h = bad (mono-lo h tt lg1 C.self one⊲lim1 C.self C.self n0 n0 (F.st F.zeroD n0) (F.st F.zeroD n0) cohY0 cohY0 z≤ azero azero z≤)
  where
  noS : ¬ (asuc azero ≤ azero)
  noS ()
  bad : ¬ (sum azero (nl (λ _ → Ωd azero C.self tt ⨾ n0)) ≤ azero)
  bad (l≤ h) = noS (h 1)

uκ-not-KMono : ¬ KMono N.uκ
uκ-not-KMono m = no-10 (m C.self one⊲lim1 tt lg1 1≤lim1)
```
