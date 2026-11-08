# 保留完整旧世界的后继扩界闭项

先给任意旧合法世界的真实扩张，继而把上一轮全部自然数分量混合树
搬过 Ω→Ω+1，并加入新界分量的地板。旧世界没有被规范零世界替换。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.BoundedGrowthClosed where
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecLay
open import OCF.Lean.LHRecLeg using (rfL; w₀L; lw₀L)
open import OCF.Lean.LHRecFl using (flL; Lg-flL)
open import OCF.Lean.BoundedGrowthIf
open import OCF.Lean.BoundedGrowthRun
import OCF.Lean.BoundedContextClosed as C

successor : ∀ P k w B (W : Wd (Lv (P ⊕L upL k B))) →
  LgW (Lv (P ⊕L upL k B)) W → WorldGrowth P k w B (hs B) (hsuc hself) W
successor P k w B W lW = record
  { future = W , hz
  ; legal-future = lW , tt
  ; extends = rfL (P ⊕L upL k B) W }

module G = Grow (ΩL C.k) C.k C.w C.B (hs C.B) (hsuc hself)

W : Wd G.Old.T
W = w₀L (ΩL C.k ⊕L upL C.k C.B)

growth : WorldGrowth (ΩL C.k) C.k C.w C.B (hs C.B) (hsuc hself) W
growth = successor _ _ _ _ W (lw₀L _)

moved : HB G.New.S
moved = G.move C.input
legal-moved : LgB moved
legal-moved = G.move-legal C.input C.legal-input

output : HB G.Fresh.T
output = G.result C.input ⊞ flL (ΩL C.k ⊕L upL C.k (hs C.B))
legal-output : LgB output
legal-output = Lg-⊞ (G.result C.input) (flL (ΩL C.k ⊕L upL C.k (hs C.B)))
  (G.result-legal C.input C.legal-input) (Lg-flL (ΩL C.k ⊕L upL C.k (hs C.B)))

-- 原输入的每个部分和仍在未来世界处位于搬运后的整体。
preserved : ∀ {a} → a ⊲[ W ] C.input →
  G.move a ⊲[ WorldGrowth.future growth ] moved
preserved = G.witnessed-position growth
```

这是动态支持与合法性的实例，不是指标种类的完整消去：新界是后继，
未由可数折叠输出产生，且没有证明 output 的序数值大小。累加扩界
B⊞R 的世界扩张由配对路线另证；一般 Ω-sup 的任意世界逆投影不在此处。
