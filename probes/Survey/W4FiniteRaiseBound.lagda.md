# 正层折叠只接收零层提升时，反馈的精确上确界

第四层，无条件。种子取 bₙ 的合法零层表示再加一。任取正层、基表和以前的系数与输入，有限次零层提升折叠的值严格小于 ε⁺(bₙ)。逐次使用终端所取的塔表、单位系数，任意选塔序列均达到这个上确界，且 ε⁺(bₙ) < ψ₀(Ωₙ₊₁) < bₙ₊₁。
测试中的种子由外部指定。结论覆盖实际折叠算子的这一类输入，闭项自身的反馈地址另需见证。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4FiniteRaiseBound where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Empty using (⊥)
open import OCF.Align.EboLeanBase using (c∷; c[])
open import OCF.Lean.YiRefTw2 using (Rt)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼-trans; ≼-refl; ≼-suc; z≼; s≼s; l≼; ≼l)
open import OCF.Align.TightValBase using (s≼-irrefl)
open import WVOne using (read; T₀; 𝟏)
import W4Block as W
import W4Ops as O
import W4Fold as F
import W4Path as Path
import B12Terminal as T
import B12BtboCut as C
import B18Product as M
import B19IdealArithmetic as Ar
import B19IdealPowers as Pow
import B22MovingIndex as E
import B26CScalar as Fold
import B27UArbitrary as Embed
import B27UEpsilon as Hull
import Survey.EboPTOFinite as Code
import Survey.W4FixedDepth as Fixed
import Survey.W4FiniteOmegaCut as Cut
import Survey.W4FiniteRaiseBoundSeed as Seed

module Tower (k : ℕ) where
  r = T.limRun W.tw T.terminal (suc k)
  module Unit = Fold.Positive (W.sΩ (W.tw k)) (λ j → W.tw k W.⊕ W.↑ (W.tw k) j)
    (T.Run.ok r) (T.Run.bs r) (O.Ωt W.zero)

  step : W.Tr W.zero → W.Tr W.zero
  step x = proj₁ (Unit.run x)

  lower : ∀ x → Ar.norm (read x) ≼ read (step x)
  lower x = ≼-trans {b = 𝟏 M.· Ar.norm (read x)} (M.one-left (Ar.norm (read x))) (proj₂ (Unit.exact x))

module At (i : ℕ) where
  b = Fixed.sample i
  module H = Hull.At b
  module B = Cut.Branch i 1

  start = W.suc (proj₁ (Embed.zrep b))
  small-start : H.In (read start)
  small-start = H.sucC {read (proj₁ (Embed.zrep b))} (H.down {x = read (proj₁ (Embed.zrep b))} {y = Ar.norm (L.suc b)}
    (Seed.upper (Code.nf-collapsed (suc i) 2) (c∷ c[]) (Code.tower-h (suc i) 2)) (H.expC {L.suc b} (H.sucC {b} H.seed)))

  data Built : W.Tr W.zero → Set where
    start-here : Built start
    unit : Built (proj₁ (O.Ωt W.zero))
    fold : ∀ (s : W.Sh) (g : W.Ch s → W.L) (o : Path.Ok (W.nd s g)) (table : F.Base (W.nd s g))
      (β : O.Tr⁺ W.zero) (x : W.Tr W.zero) → Built (proj₁ β) → Built x → Built (proj₁ (Fold.Positive.run s g o table β x))

  small : ∀ {x} → Built x → H.In (read x)
  small start-here = small-start
  small unit = H.sucC {L.zero} (H.down {x = L.zero} {y = b} z≼ H.seed)
  small (fold s g o table β x coeff arg) = H.down {x = read (proj₁ (Row.run x))} {y = read (proj₁ β) M.· Ar.norm (read x)}
    (proj₁ (Row.exact x)) (H.mulC {read (proj₁ β)} {Ar.norm (read x)} (small coeff) (H.expC {read x} (small arg)))
    where module Row = Fold.Positive s g o table β

  finite : ∀ {x} → Built x → L.suc (read x) ≼ E.above b
  finite {x} h = H.finite {read x} (small h)

  limit : (f : ℕ → W.Tr W.zero) → (∀ j → Built (f j)) → L.lim (λ j → read (f j)) ≼ E.above b
  limit f h = l≼ λ j → ≼-trans {b = L.suc (read (f j))} (≼-suc (≼-refl _)) (finite (h j))

  module Schedule (height : ℕ → ℕ) where
    stage : ℕ → W.Tr W.zero
    stage zero = start
    stage (suc j) = Tower.step (height j) (stage j)

    witness : ∀ j → Built (stage j)
    witness zero = start-here
    witness (suc j) = fold _ _ (T.Run.ok r) (T.Run.bs r) (O.Ωt W.zero) (stage j) unit (witness j)
      where r = Tower.r (height j)

    lower : ∀ j → E.steps b j ≼ read (stage j)
    lower zero = s≼s (Embed.dominates b)
    lower (suc j) = ≼-trans {b = Ar.norm (read (stage j))} (Pow.expo Pow.omega-pos (lower j)) (Tower.lower (height j) (stage j))

    exact : L.lim (λ j → read (stage j)) ≈ᵛ E.above b
    exact = limit stage witness , l≼ (λ j → ≼l {f = λ k → read (stage k)} j (lower j))

  below-next-cut : L.suc (E.above b) ≼ C.finite (suc (suc i))
  below-next-cut = ≼-trans {b = L.suc (Rt B.ceiling)} (s≼s (≼-trans {b = L.lim (W.iter E.above b)}
    (≼l {f = W.iter E.above b} 1 (≼-refl _)) (B.all b (≼-refl _)))) B.proper

  insufficient : (f : ℕ → W.Tr W.zero) → (∀ j → Built (f j)) → Fixed.sample (suc i) ≼ L.lim (λ j → read (f j)) → ⊥
  insufficient f h reach = s≼-irrefl (E.above b) (≼-trans {b = C.finite (suc (suc i))} below-next-cut
    (≼-trans {b = Fixed.sample (suc i)} (≼-trans {b = L.suc (C.finite (suc (suc i)))} (≼-suc (≼-refl _)) (Fixed.lower (suc i)))
      (≼-trans {b = L.lim (λ j → read (f j))} reach (limit f h))))
```
