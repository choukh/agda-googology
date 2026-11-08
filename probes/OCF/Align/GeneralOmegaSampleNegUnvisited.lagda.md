# 可编码且可入不等于已被完整输出覆盖

共用冻结SampleWorld的实际世界。取真实最低Ω地板，反馈d明确为其原
输出的后继。对应code仍合法、可入，源子树也是合法第一位置前驱，
但子树的run严格超过完整地板的run。此坐标未声称是实际chain中的点。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaSampleNegUnvisited where
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg)
open import OCF.Lean.Fold1If using (_≤ᵛ_; s≤s; z≤; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-trans)
open import OCF.Lean.NegFold1If using (¬s≤ᵛ)
open import OCF.Lean.CountableCompletionRun using (inflation)
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; same-value; same-sym)
open import OCF.Lean.LHRecTy using (ls; lz)
open import OCF.Lean.LHRecFl using (flL; Lg-flL; Lg-up)
open import OCF.Lean.HigherIndexConsumeCode using (pure)
open import OCF.Lean.GeneralOmegaConsumeIf using (code)
open import OCF.Lean.GeneralOmegaConsumeRun using (run)
open import OCF.Align.GeneralOmegaConsumeValuePure using (positive)
open import OCF.Align.FrozenValueFirst using (add-mono)
import OCF.Lean.GeneralOmegaSampleWorld as W

pure-inflate : ∀ a → a ≤ᵛ run (ls lz) (up a)
pure-inflate hz = z≤
pure-inflate (hs a) = ≤l 1 (add-mono (pure-inflate a) (positive (ls lz) (up a)))
pure-inflate (hl f) = l≤ (λ n → ≤l n (pure-inflate (f n)))
pure-inflate (hΩ () f)
code-shape : ∀ a → Same (hz ⊞ pure S⊥ a) a
code-shape hz = zz
code-shape (hs a) = ss (code-shape a)
code-shape (hl f) = ll (λ n → code-shape (f n))
code-shape (hΩ () f)

source = flL (ls lz)
output : Cd
output = run (ls lz) source
feedback : Cd
feedback = hs output
coordinate : Cd
coordinate = code (ls lz) (inj₂ tt) feedback
world = W.World (ls lz) feedback
legal-world : LgW (step S⊥) world
legal-world = W.legal (ls lz) feedback
admitted : Bd (step S⊥) (inj₂ tt) coordinate world
admitted = W.admitted (ls lz) (inj₂ tt) feedback
zero-admitted : Bd (step S⊥) (inj₂ tt) (code (ls lz) (inj₂ tt) hz) world
zero-admitted = Bd↑ (step S⊥) {κ = inj₂ tt} {c = code (ls lz) (inj₂ tt) hz}
  {w = W.World (ls lz) hz} {w′ = world} (W.growth (ls lz) {d = hz} {e = feedback} (z⊲ᴮ (leg feedback)))
  (W.admitted (ls lz) (inj₂ tt) hz)
zero-before : Pr (step S⊥) (inj₂ tt) world (code (ls lz) (inj₂ tt) hz) coordinate
zero-before = W.position (ls lz) (inj₂ tt) {d = hz} {e = feedback} (z⊲ᴮ (leg feedback))
legal-coordinate : LgB coordinate
legal-coordinate = lgB⊲ admitted (proj₁ legal-world) (proj₂ legal-world)
legal-source : LgB source
legal-source = Lg-flL (ls lz)
legal-branch : LgB (up {S⊥} coordinate)
legal-branch = Lg-up coordinate legal-coordinate
source-position : up coordinate ⊲[ world ] source
source-position = hLim admitted hself

strict-branch : hs output ≤ᵛ run (ls lz) (up coordinate)
strict-branch = ≤-trans (inflation feedback)
  (≤-trans (same-value (same-sym (code-shape (leg feedback)))) (pure-inflate coordinate))
not-covered : run (ls lz) (up coordinate) ≤ᵛ output → ⊥
not-covered p = ¬s≤ᵛ output (≤-trans strict-branch p)
```

全部前提给了真实合法实例，坐标确是实际code而非任意外加值。否定
仅排除把“所有可编码/可入分支”当作“所有已访问样本”的推理；不
否定SampleWorlds.pair、实际相邻采样递增或实际输出部分和包含定理。
它也不否定当前算法、完整Λ闭项或其EBO潜力。
