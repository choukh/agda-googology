# 单层 `nκ` (四): 实例

> 不含记号. 入口 [KValK](KValK.lagda.md).
>
> 1. `mono-hi`: `hi` 档在 `Step` 的上下文里单调, 前提只剩状态的路径一致、值可比、回灌层可比.
> 2. `rf-κΩ`: $\sum_{c\ge V}\sum_{z:0}1$ (`nκ` 的分支是第 0 层节点, 即 $\Omega_\Omega$ 的形状搬到第 1 层) 满足判据, `hi` 档自比. 所以 `κ⊑` 不是空规则.
> 3. `¬rel-κκ`: `DValNeg` 的 `¬κ-refl` 那一对 ($1⨾\mathrm{n\kappa}\,u_\kappa$ 对 $(\lim_n0⨾1)⨾\mathrm{n\kappa}\,u_\kappa$) **不**在 `hi` 档的关系里. 由 `snd-hi` 与 `DValNeg.sepκ` (动作 `A⁺`, 每个 `n1` 输出 $1$) 推出, 不必看推导.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.KValKInst where

open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg; ss)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤-refl)
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; ni; nκ; sum)
import OCF.Align.SumOneClosed as F
open import OCF.Align.LayerTrOne using (one)
open import OCF.Align.KValTree
open import OCF.Align.KValSem
open import OCF.Align.KValSound
open import OCF.Align.KValInst using (StepA; ok-Step)
open import OCF.Align.KValKHi using (snd-hi)
import OCF.Align.DValNeg as N
```

## §1 `Step` 的上下文

```agda
mono-hi : ∀ {V V′} {x : D one V} {x′ : D one V′} → x ⊑[ hi ] x′ →
          ∀ {W W′} (lW : Lg W) (lW′ : Lg W′) (ll : one ⊲ W) (ll′ : one ⊲ W′) (q : V ⊲ W) (q′ : V′ ⊲ W′) w w′ Y Y′ →
          CohY Y → CohY Y′ → vYk (κ₀ ll) Y ≤ vYk (κ₀ ll′) Y′ → sum W (F.z Y) ≤ sum W′ (F.z Y′) → ∀ c c′ → c ≤ c′ →
          Ob (sd W lW ll StepA) c x q w Y ≤ Ob (sd W′ lW′ ll′ StepA) c′ x′ q′ w′ Y′
mono-hi h lW lW′ ll ll′ q q′ w w′ Y Y′ cY cY′ r hl =
  snd-hi h (sd _ lW ll StepA) (sd _ lW′ ll′ StepA) (ok-Step lW lW′ ll ll′) q q′ w w′ Y Y′ (cx cY cY′ r hl)
```

## §2 判据不空

```agda
uΩ : ∀ {V} → Bk V
uΩ _ _ = ni (ss C.self) (λ _ _ _ → n1)

mono-uΩ : ∀ {V} → KMono (uΩ {V})
mono-uΩ p p′ l l′ le = ni⊑ (λ _ _ _ _ _ _ _ → n1⊑) (λ _ _ _ _ _ _ _ → n1⊑) (λ _ _ _ _ _ _ _ → n1⊑)

rf-κΩ : ∀ {V} → Rfᵏ hi (nκ {W = V} tt uΩ)
rf-κΩ {V} = rf-κ (≤-refl V) mono-uΩ

rf-1κΩ : ∀ {V} → Rfᵏ hi (n1 ⨾ nκ {W = V} tt uΩ)
rf-1κΩ = ⨾⊑ n1⊑ rf-κΩ
```

## §3 `¬κ-refl` 的那一对不在关系里

```agda
A⁺s : Sd
A⁺s = sd one tt C.self N.A⁺

ok⁺ : Ok A⁺s A⁺s
ok⁺ = ok ha ha ha cA cA
  where
  ha : HA⁺ A⁺s A⁺s
  ha p p′ lV lV′ w w′ Y Y′ k k′ cY cY′ r c c′ cb = s≤ cb
  cA : CohA (act A⁺s)
  cA p lV w Y cY = cd (λ τ τ′ c → ≤-refl _)

¬rel-κκ : ¬ (N.Xκ ⊑[ hi ] N.X′κ)
¬rel-κκ h = N.sepκ (snd-hi h A⁺s A⁺s ok⁺ C.self C.self n0 n0 F.Y₀ F.Y₀ (cx cohY0 cohY0 z≤ (≤-refl _)) azero azero z≤)
```
