# 一步对一切有限高度 (六): 外层链与严格增长

> 入口 [MonoPort6](MonoPort6.lagda.md). 不含记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`.
>
> 对一切有限的 $\Lambda_0$ (`Fin`): 实例 `hs Λ₀` 里外层链 (点在层 $\Lambda_0$, 动作 `StepA`) 两边的极限可比, 即 `MonoPortStep.Ch.ChainLe Λ₀ l` (`chainLe`). 链用 `chainV` (第 0 层: `MonoPort6Zero`; 第 $\ge1$ 层: `MonoPort5Chn.chainG` 加 `sndS`). `StepA` 的动作前提 (`HA-Step`) 与两个起点 (`sLR`, `hb`) 对 $\Lambda_0$ 写一次 (逐字照 `MonoPort5Chain`, 观测换成一切目标). 于是 `MonoStep (hs Λ₀)` (`monoS`), 加上 `HtCrossVInst.HsS.hs-reduce<′`, 对一切 $n$: `TΛ n < TΛ (n+1)` (`grow`), 与 `TΛ 0 + n ≤ TΛ n` (`grow₀`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.MonoPort6Chain where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import OCF.Align.CumReadCF using (A; azero; asuc)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤-refl; ≤-trans; ⊲→≤)
open import OCF.Align.HtFeedTree using (H; LgH; hz; hs; hl; hΩ; _⊲[_]_; hself; hsuc; z⊲ᴴ; D; AccY; accL; Ωd; n0; n1; _⨾_; nl; sum; sum-fst)
open import OCF.Align.HtFeedClosed using (one; TΛ)
open import OCF.Align.HtCrossInst using (module Hs; b₀)
open import OCF.Align.StrRelDef {one} tt using (val₀)
import OCF.Align.MonoPortStep as St
import OCF.Align.HtCrossVInst as CV
import OCF.Align.HtCrossVSim as VS
import OCF.Align.MonoPort6Rel as Rl
import OCF.Align.MonoPort6Snd as Sd
import OCF.Align.MonoPort6Lay as Ly
```

## 1 有限高度

```agda
FinH : H → Set
FinH hz = ⊤
FinH (hs b) = FinH b
FinH (hl _) = ⊥
FinH (hΩ _) = ⊥

toFin : ∀ {Λ : H} {lΛ : LgH Λ} {W : A} {lW : C.Lg W} {t₀ : hz ⊲[ W ] Λ} k → FinH k → Rl.Fin Λ lΛ {W} lW t₀ k
toFin hz f = tt
toFin {Λ} {lΛ} {W} {lW} {t₀} (hs b) f = toFin {Λ} {lΛ} {W} {lW} {t₀} b f
toFin (hl _) ()
toFin (hΩ _) ()
```

## 2 实例 `hs Λ₀` 里的外层链

```agda
module Top (Λ₀ : H) (fΛ : FinH Λ₀) (l : LgH Λ₀) where
  Λ : H
  Λ = hs Λ₀
  t₀ : hz ⊲[ one ] Λ
  t₀ = z⊲ᴴ Λ
  open Rl Λ l {one} tt t₀
  open Sd Λ l {one} tt t₀
  open import OCF.Align.MonoPort6Int Λ l {one} tt t₀ using (cx00)
  module Kc = St.Ch Λ₀ l

  hk : Λ₀ ⊲[ one ] Λ
  hk = hsuc hself

  StepA : P.Ig Λ₀ one
  StepA = Kc.StepA

  -- 链的读数极限 (对层分两种)
  chainV : ∀ k → Fin k → (ac : AccY k) (pos : k ⊲[ one ] Λ) → SndArg k ac → (i j : P.Ig k one) → HAK k i i → HAK k j j → HAK k i j →
           ∀ Y Y′ b b′ → Good Y → Good Y′ → SRel Y Y′ → b ≤ b′ →
           sum b (nl (λ n → o₀ (OutsK ac pos i Y n))) ≤ sum b′ (nl (λ n → o₀ (OutsK ac pos j Y′ n)))
  chainV hz fk ac pos sk i j hi hj hij Y Y′ b b′ g g′ s cb =
    proj₁ (B₀.Chain.chain₀ ac pos i j (toHA₀ ac pos i i hi) (toHA₀ ac pos j j hj) (toHA₀ ac pos i j hij) Y Y′ b b′ g g′ s cb)
  chainV (hs b₁) fk ac pos sk i j hi hj hij Y Y′ b b′ g g′ s cb =
    proj₁ (Ly.L.Ch.chainG Λ l {one} tt t₀ b₁ ac pos (sk pos) i j hi hj hij Y Y′ b b′ g g′ s cb)

  HA-Step : HAK Λ₀ StepA StepA
  HA-Step w w′ c c′ Y Y′ _ g g′ s cb =
    obs cb (λ {t} tm → rnl t (λ _ → r⨾ t (rΩ t) (rΩ t) (rΩ t) (g tm)) (λ _ → r⨾ t (rΩ t) (rΩ t) (rΩ t) (g′ tm))
                             (λ _ → r⨾ t (rΩ t) (rΩ t) (rΩ t) (proj₂ s tm)))

  z≼ : ∀ Δ → P.zeroD ≼ Δ
  z≼ Δ {t} tm = r0 t

  g0 : Good P.Y₀
  g0 = z≼ P.zeroD

  rS : ∀ Y → Good Y → P.Step Y ≼ P.Step Y
  rS Y gY = proj₂ (HA-Step n0 n0 azero azero Y Y (cx00 Λ₀) gY gY (≤-refl _ , gY) z≤)

  gL : Good Kc.Yᴸ
  gL = ⨾≼ {P.d P.Y₀} {P.Step P.Y₀} {P.d P.Y₀} {P.Step P.Y₀} g0 g0 g0 (rS P.Y₀ g0)

  gR₀ : Good Kc.Yʳ₀
  gR₀ = ⨾≼ {P.d Kc.Yᴸ} {P.zeroD} {P.d Kc.Yᴸ} {P.zeroD} gL gL gL (z≼ P.zeroD)

  gR : Good Kc.Yʳ
  gR = ⨾≼ {P.d Kc.Yʳ₀} {P.Step Kc.Yʳ₀} {P.d Kc.Yʳ₀} {P.Step Kc.Yʳ₀} gR₀ gR₀ gR₀ (rS Kc.Yʳ₀ gR₀)

  -- 两个起点: x ≼ (x ⨾ 0) ⨾ y, 只用单位律与 0 ≼ y
  sLR : SRel Kc.Yᴸ Kc.Yʳ
  sLR = val₀ (r t₀) (≤-refl azero) , r
    where
    r : P.d Kc.Yᴸ ≼ P.d Kc.Yʳ
    r = tr≼ {P.d Kc.Yᴸ} {P.d Kc.Yʳ₀ P.⨾ᴰ P.zeroD} {P.d Kc.Yʳ}
            (u1≼ʳ {P.d Kc.Yᴸ} {P.d Kc.Yᴸ P.⨾ᴰ P.zeroD} (u1≼ʳ {P.d Kc.Yᴸ} {P.d Kc.Yᴸ} gL))
            (⨾≼ {P.d Kc.Yʳ₀} {P.zeroD} {P.d Kc.Yʳ₀} {P.Step Kc.Yʳ₀} gR₀ gR₀ gR₀ (z≼ (P.Step Kc.Yʳ₀)))

  hb : Kc.bᴸ ≤ Kc.bʳ
  hb = val₀ (proj₂ (HA-Step n0 n0 azero azero P.Y₀ Kc.Yʳ₀ (cx00 Λ₀) g0 gR₀ (z≤ , z≼ (P.d Kc.Yʳ₀)) z≤) t₀) (⊲→≤ (sum-fst one (nl (λ _ → n1 ⨾ n0))))

  chainLe : Kc.ChainLe
  chainLe = chainV Λ₀ (toFin {Λ} {l} {one} {tt} {t₀} Λ₀ fΛ) (accL Λ₀) hk (sndArg Λ₀ (toFin {Λ} {l} {one} {tt} {t₀} Λ₀ fΛ) (accL Λ₀)) StepA StepA HA-Step HA-Step HA-Step
              Kc.Yᴸ Kc.Yʳ Kc.bᴸ Kc.bʳ gL gR sLR hb

  monoS : Hs.MonoStep (hs Λ₀) l
  monoS = subst (λ X → X) (sym Kc.step≡) chainLe
```

## 3 一切有限高度上严格增长

```agda
N : ℕ → H
N zero = hz
N (suc n) = hs (N n)

lgN : ∀ n → LgH (N n)
lgN zero = tt
lgN (suc n) = lgN n

finN : ∀ n → FinH (N n)
finN zero = tt
finN (suc n) = finN n

freeN : ∀ n → VS.Free (N n)
freeN zero = tt
freeN (suc n) = freeN n

-- 高度 n 到 n+1, 一切 n
grow : ∀ n → asuc (TΛ (N n) (lgN n)) ≤ TΛ (N (suc n)) (lgN (suc n))
grow zero = CV.hz<1′
grow (suc n) = CV.HsS.hs-reduce<′ (N (suc n)) (lgN n) (freeN (suc n)) (Top.monoS (N n) (finN n) (lgN n))

_+ᴬ_ : A → ℕ → A
a +ᴬ zero = a
a +ᴬ suc n = asuc (a +ᴬ n)

grow₀ : ∀ n → TΛ hz tt +ᴬ n ≤ TΛ (N n) (lgN n)
grow₀ zero = ≤-refl _
grow₀ (suc n) = ≤-trans (s≤ (grow₀ n)) (grow n)
```

前几站作为特例 (同一个陈述, 不再按站写): 高度 3 到 4 与 `MonoPort5Chain.grow₃₄` 同型, 再往上一站 4 到 5 是上一组没有的.

```agda
mono₃′ : Hs.MonoStep (hs (hs (hs hz))) tt
mono₃′ = Top.monoS (N 2) tt tt

grow₄₅ : asuc (TΛ (N 4) tt) ≤ TΛ (N 5) tt
grow₄₅ = grow 4

grow₁₀ : TΛ hz tt +ᴬ 10 ≤ TΛ (N 10) tt
grow₁₀ = grow₀ 10
```
