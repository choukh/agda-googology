# 相对塔的内层指标采用前缀路径

这里限定已经运行的 k=ls lz。源 Ω 指标槽从前缀 Q 拉回路径，
并保留它的真正 next；不是用 triv 冻结该槽。KS 世界由 ext 重设，
路径世界由 Q 提供，两层结构分开。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.BoundedPathRun where
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.BoundedFoldIf using (U; P; T)
open import OCF.Lean.BoundedIndexContext using (first-index)
open import OCF.Lean.LHRecLeg using (ek)
open import OCF.Lean.ThirdPS
open import OCF.Lean.BoundedPathIf

module Relative {O : Po} (Q : PS O (T hz)) where
  project : PS O U
  project = record
    { Ev = λ V κ → PS.Ev Q V (ek first-index κ)
    ; Ad = λ V κ e → PS.Ad Q V (ek first-index κ) e
    ; nx = λ V κ e a → PS.nx Q V (ek first-index κ) e a
    ; ev↑ = λ q {κ} → PS.ev↑ Q q {ek first-index κ}
    ; ad↓ = λ q {κ} {e} → PS.ad↓ Q q {ek first-index κ} {e}
    ; nx↑ = λ {V} {κ} {e} → PS.nx↑ Q {V} {ek first-index κ} {e} }

  paths : ∀ B → PS O (T B)
  components : ∀ f → (i : _ ) → PS O _
  paths hz = Q
  paths (hs B) = psStep (paths B)
  paths (hl f) = psSup (λ n → paths (f n))
  paths (hΩ (inj₁ ()) f)
  paths (hΩ (inj₂ _) f) = psSup (components f)
  components f (inj₁ _) = project
  components f (inj₂ e) = paths (f e)

  keep-index : Keep first-index project Q
  keep-index = record
    { event = λ p → p
    ; admission = λ V κ e a → a
    ; next = λ V κ e a → Po.rf O }

  -- 实际 Ω 高度内的指标，源路径按上面递归定义，不是额外假设。
  index-ad : ∀ f V κ e → PS.Ad Q V (ek first-index κ) e →
    PS.Ad (paths (hΩ (inj₂ tt) f)) V (inj₁ tt , κ) e
  index-ad f V κ e a = a

  index-next : ∀ f V κ e (a : PS.Ad Q V (ek first-index κ) e) →
    Po._≤_ O (PS.nx (paths (hΩ (inj₂ tt) f)) V (inj₁ tt , κ) e (index-ad f V κ e a))
      (PS.nx Q V (ek first-index κ) e a)
  index-next f V κ e a = Po.rf O
```

这证明了 source 指标copy与 target 前缀copy的进入与 next 同步。
尚未证明消去后继种类时反馈坐标带 PH，故不把此同步称整个fold保路径。
