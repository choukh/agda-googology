# 可数原标准项进入 W4 零层时的值界

第四层。将原可数标准项的参照树变成合法 W4 零树。其值介于原值 α 与 ω^(α+1) 之间。这个界允许在真实折叠中投入任一 bₙ，同时把起点保持在 bₙ 上方首个 ε 数以下。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4FiniteRaiseBoundSeed where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (proj₁)
open import OCF.Align.EboLeanDef using (T; HC; h0; h1; hω)
open import OCF.Align.EboLeanBase using (NF; Ctbl; nf-pred; Ctbl-pred)
open import OCF.Align.EboLeanClosure using (cl-fsn-NF; Ctbl-fsn; trian-fsn)
open import OCF.Align.EboLeanTrian using (t<)
open import OCF.Lean.YiRefTw2 using (Rt)
open import OCF.Lean.YiCFMono using (mono<ⁿ)
open import WVOne using (T₀; read)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≼-refl; s≼s; ≼l; l≼; +-mono)
import W4Block as W
import W4Ops as O
import B8FreezeMain as Upper
import B18Product as M
import B19IdealPowers as Pow
import B19IdealArithmetic as Ar
import B27UEpsilon as Hull
import B27UArbitrary as Embed

module Sum (f : ℕ → W.Tr W.zero) (a : T₀) (cap : ∀ j → read (f j) ≼ a) where
  bound : ∀ n → read (O.cum f n) ≼ a M.· L.natᶜ (suc n)
  bound zero = ≼-trans {b = a} (cap 0) (M.one-right a)
  bound (suc n) = ≼-trans {b = read (O.cum f n) L.+ read (f (suc n))}
    (Upper.read-+′ (O.cum f n) (f (suc n))) (+-mono (bound n) (cap (suc n)))

upper : ∀ {t} → NF t → Ctbl t → (h : HC t) → read (proj₁ (Embed.zrep (Rt h))) ≼ Ar.norm (L.suc (Rt h))
upper nt ct (h0 _) = Pow.positive Pow.omega-pos (L.suc L.zero)
upper nt ct (h1 _ c) = ≼-trans {b = L.suc (Ar.norm (L.suc (Rt c)))} (s≼s (upper (nf-pred nt) (Ctbl-pred ct) c))
  (Hull.norm-strict (L.suc (Rt c)))
upper nt ct h@(hω w c) = l≼ (λ n → ≼l (suc n) (Sum.bound f (Ar.norm (Rt h)) slots n))
  where
  f = λ n → proj₁ (Embed.zrep (Rt (c n)))
  slots : ∀ n → read (f n) ≼ Ar.norm (Rt h)
  slots n = ≼-trans {b = Ar.norm (L.suc (Rt (c n)))} (upper (cl-fsn-NF nt w n) (Ctbl-fsn ct w n) (c n))
    (Pow.expo Pow.omega-pos (mono<ⁿ (cl-fsn-NF nt w n) nt ct (c n) h (t< (trian-fsn nt w n))))
```
