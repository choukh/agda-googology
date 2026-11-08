# 实际整源输出可以在未来底世界正规化并再次运行

本篇不使用已被否定的通用 LegalTransport。实际原 Φ 输出有 Full，
故其所有裸分支均已覆盖；先在新世界取得该输出的 Gd，再在新世界应用
同一个 Rich.legT 的保持定理。最后确实调用新世界中的原 Φ。

未来底世界 v 及其增长证据必须实际给出。本篇不把局部
Wd(step(Tw U t)) 世界偷换成 Wd U，也没有从运行输出生成 v。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.CircuitGeneratedFuture where

open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁)
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdIf using (Tw)
open import OCF.Lean.ThirdTw using (Sb)
import OCF.Lean.ThirdFold as TF
import OCF.Lean.ThirdSan as San
import OCF.Lean.ThirdRunFamilyBuild as Family
import OCF.Lean.CircuitKernelStableBuild as S
import OCF.Lean.CircuitGeneratedIf as I
import OCF.Lean.CircuitGeneratedBuild as G
open import OCF.Lean.CircuitLegalBuildNormal using (normal-gd)

module Bridge (U : KS) (w : Wd U) (lw : LgW U w) where
  open I.At U w lw using (Full)
  module P = S.For U

  future-gd : ∀ {v} (lv : LgW U v) → P.Future w v →
    ∀ m h → Full m h → TF.Gd U v lv m h
  future-gd lv q m hz p = tt
  future-gd lv q m (hs h) p = future-gd lv q m h p
  future-gd lv q m (hl f) p = λ n → future-gd lv q m (f n) (p n)
  future-gd lv q m (hΩ κ g) (pos , branches) =
    P.pos-up m κ q pos , λ e _ → future-gd lv q m (g e) (branches e)

module Run (n : ℕ) (w : Wd (Sb n)) (lw : LgW (Sb n) w)
  (fb : HB (Sb n)) (M : HB (Sb n)) (lm : LgB M)
  (h : HB (Tw (Sb n) M)) (nd : TF.Gd (Sb n) w lw M h) where
  U = Sb n
  module A = Family.Run n w lw fb M lm h nd
  module F = G.At U w lw A.E.Er
  module B = Bridge U w lw

  output-full : ∀ t (pt : t ⊲[ w ] M) b → I.At.Full U w lw t (A.output t pt b)
  output-full t pt b = F.outputs M (A.R.wfC M) lm t pt b h nd

  module Enter (v : Wd U) (lv : LgW U v) (q : _≤w_ U w v) where
    module New = TF U v lv
    module E = San U v lv fb
    module Col = New.F E.Er

    output-certificate : ∀ t (pt : t ⊲[ w ] M) b → New.Gd t (A.output t pt b)
    output-certificate t pt b = B.future-gd lv (B.P.grow q) t _ (output-full t pt b)

    normal-certificate : ∀ t (pt : t ⊲[ w ] M) b → New.Gd t (A.normal t pt b)
    normal-certificate t pt b = normal-gd n v lv t (lgB⊲ pt lw lm)
      (A.output t pt b) (output-certificate t pt b)

    again : ∀ t (pt : t ⊲[ w ] M) (b : A.F.GT t)
      s → s ⊲[ v ] t → New.GT s → New.GT s
    again t pt b s ps seed = Col.Φ t (Col.wfC t) (lgB⊲ pt lw lm)
      s ps seed (A.normal t pt b) (normal-certificate t pt b)

    again-full : ∀ t pt b s ps seed →
      I.At.Full U v lv s (proj₁ (again t pt b s ps seed))
    again-full t pt b s ps seed = G.At.outputs U v lv E.Er
      t (Col.wfC t) (lgB⊲ pt lw lm) s ps seed
      (A.normal t pt b) (normal-certificate t pt b)
```

整源与种子是原程序的全部允许参数，不局限 Run n1、首格或有限高度。
again-full 使再次运行的原输出还能应用同一未来证书定理。原高度比较均
有合法公共上界；新目标路径由调用者在 v 中给出。

此处消去的是“实际输出在给定未来底世界还能否作为输入”的缺项。
由输出生成这样的底世界、原 QL 全族 PH 的保持、整条值覆盖与 EBO
下界仍未交付；原 San 可能正是全裸分支可处理的原因。
