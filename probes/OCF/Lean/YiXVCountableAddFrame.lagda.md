# YiXVCountableAddFrame
> 验收文件。档位：编译定理。加法对两变量及不同嵌入的混合比较；节点部分复用公共映射比较。
> 按 YiXVFiniteFold*/FiniteChain/FiniteGamma 推广，搬运与节点比较复用 Countable 接口；未交外层源链上界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVCountableAddFrame where
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableAdd as Add
import OCF.Lean.YiXVCountableMapCompare as Compare

left : ∀ {κ X Y} → A.Le {κ} X Y → A.Gd X
left {κ} = A.Layer.left κ A.Gd< A.Le<
right : ∀ {κ X Y} → A.Le {κ} X Y → A.Gd Y
right {κ} = A.Layer.right κ A.Gd< A.Le<

mutual
  frame : ∀ {κ ν} {Z W : L.Ordᶜ ν} {σ τ : L.Simᴵ κ ν} {X} →
    A.Le Z W → A.Gd X → A.Le (L.add Z σ X) (L.add W τ X)
  frame p A.Layer.gz = p
  frame {ν = ν} p (A.Layer.gs gx) = A.Basics.s≤ ν (frame p gx)
  frame {ν = ν} {Z} {W} {σ} {τ} p (A.Layer.gl {f} gf) =
    A.Layer.pack (Add.good (left p) (A.Layer.gl gf)) (Add.good (right p) (A.Layer.gl gf))
      (A.Layer.ll (λ n → A.Layer.pack (Add.good (left p) (gf n))
        (Add.good (right p) (A.Layer.gl gf)) (A.Layer.lr n (frame p (gf n)))))
  frame {κ} {ν} {Z} {W} {σ} {τ} p h@(A.Layer.gn {q = q} {f = f} ex (A.Layer.sc mo db po) gb) =
    A.Layer.pack (Add.good (left p) h) (Add.good (right p) h)
      (Compare.Map.result (L.add Z σ) (L.add W τ)
        (Add.view Z σ (left p)) (Add.view W τ (right p)) q q f f
        (λ X Y gx gy o t → mixed p (mo X Y gx gy o t)))
  frame {σ = σ} {τ = τ} p (A.Layer.gu L.zero gx) =
    frame {σ = λ q → σ (L.suc q)} {τ = λ q → τ (L.suc q)} p gx
  frame {σ = σ} {τ = τ} p (A.Layer.gu (L.self n) gx) =
    frame {σ = λ q → σ (L.lim n q)} {τ = λ q → τ (L.lim n q)} p gx

  mixed : ∀ {κ ν} {Z W : L.Ordᶜ ν} {σ τ : L.Simᴵ κ ν} {X Y} →
    A.Le Z W → A.Le X Y → A.Le (L.add Z σ X) (L.add W τ Y)
  mixed {ν = ν} {σ = σ} p t@(A.Layer.pack gx gy q) =
    A.Layer.trans ν A.Gd< A.Le< (Add.mono {σ = σ} (left p) t) (frame p gy)

actual : A.Le (L.Ω L.ωᴵ L.+ L.Ω L.ωᴵ) (L.Ω L.ωᴵ L.+ L.Ω L.ωᴵ)
actual = mixed (A.Layer.rfl L.ωᴵ A.Gd< A.Le< A.omegaΩ) (A.Layer.rfl L.ωᴵ A.Gd< A.Le< A.omegaΩ)
```
