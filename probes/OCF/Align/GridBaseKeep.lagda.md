# 原 component 0 的完整保留片段：全部输入的值不缩

这不是原 ΦX 的全域单调性。只取原 `ι₀(up a)` 片段：全部种类来自底
`V`，实际分类走 `bas keep`，不经 Er。比较仍在同一合法 `B` 内。
定理覆盖含任意底 Ω 的整个 `a`，没有要求它合法或分支值单调。
此片段尚未自动成为完整高地板输出的前驱，也不能穿过下一底下降。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GridBaseKeep where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₂)
open import Data.Product using (_,_; proj₁)
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdTw using (Ix; FX; Sb; fl)
import OCF.Lean.ThirdRichLegBuild as Rich
import OCF.Lean.OutputDrivenTop as Top
import OCF.Lean.ThirdSan as San
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; s≤s; l≤; ≤l; ≤Ω; Ω≤Ω)
open import OCF.Lean.NegFold1Base using (≤ᵛ-refl; ≤ᵛ-trans; ⊞≤ʳ)
import OCF.Lean.ThirdFold as Fold
import OCF.Lean.OutputDrivenBuild as Build

module Kept (V : KS) (w : Wd V) (lw : LgW V w)
  (fb : HB V) (normal : HB V → HB V) (normal-legal : ∀ a → LgB (normal a))
  (pk : (κ : K V) → E V κ) (pk-bd : ∀ κ → Bd V κ (pk κ) w)
  (B : HB V) (lB : LgB B) (p : hs hz ⊲[ w ] B)
  (b : Fold.GT V w lw hz) where
  module K = Build.Whole V w lw fb normal normal-legal pk pk-bd
  module F = Fold V w lw

  run : HB V → HB V
  run a = proj₁ (K.X.ΦX hz B lB (⊲ᴮ-tr (hsuc hself) p) b
    (ι {Ix V} {FX V} (inj₂ hz) (up a))
    (K.component hz B p (up a) (K.S.Gd-up hz a (K.S.gd-z a))))

  right : ∀ (a c : HB V) → c ≤ᵛ (a ⊞ c)
  right a hz = z≤
  right a (hs c) = s≤s (right a c)
  right a (hl f) = l≤ (λ n → ≤l n (right a (f n)))
  right a (hΩ κ g) = Ω≤Ω (λ e → right a (g e))

  in-sum : ∀ (f : ℕ → F.GT hz) n → proj₁ (f n) ≤ᵛ proj₁ (F.ΣG f n)
  in-sum f zero = ≤ᵛ-refl (proj₁ (f zero))
  in-sum f (suc n) = right (proj₁ (F.ΣG f n)) (proj₁ (f (suc n)))

  positive : ∀ a → hs hz ≤ᵛ run a
  positive hz = s≤s z≤
  positive (hs a) = ≤l zero (positive a)
  positive (hl f) = ≤l zero (positive (f zero))
  positive (hΩ κ g) = ≤Ω (bot V κ) (positive (g (bot V κ)))

  inflation : ∀ a → a ≤ᵛ run a
  inflation hz = z≤
  inflation (hs a) = ≤l (suc zero)
    (≤ᵛ-trans (s≤s (inflation a)) (⊞≤ʳ (run a) (positive a)))
  inflation (hl f) = l≤ (λ n → ≤l n
    (≤ᵛ-trans (inflation (f n)) (in-sum _ n)))
  inflation (hΩ κ g) = Ω≤Ω (λ e → inflation (g e))
```

这是保留原底种类的一整类真实运行，而非把输出读法指定成原输入。
与已验 BTBO 标尺之间仍缺完整高根反馈的控制比较。

原全底地板实例（包括所有非零底），当前世界任意但必须合法：

```agda
module Actual (n : ℕ) (w : Wd (Sb n)) (lw : LgW (Sb n) w) where
  module S = San (Sb n) w lw (fl n)
  module K = Kept (Sb n) w lw (fl n) (Rich.legS n) (Rich.Lg-legS n)
    (Top.topS n w) (Top.topS-bd n w) (hs hz) tt hself (fl n , S.gd-z (fl n))

  floor-kept : fl n ≤ᵛ K.run (fl n)
  floor-kept = K.inflation (fl n)
```
