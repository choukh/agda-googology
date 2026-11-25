# 多标签窗口：指定成员的结点保持与覆盖全部标签后的保持
验收文件，读记号；窗口逐槽位取集合，不要求标签唯一，非空、标签覆盖、框架分别陈述。
编译条件定理：`Rows.member-row` 保持窗口中指定成员；`Rows.pres` 还要求覆盖所有原标签、`Kit` 与原路径证据。
证明复用 `YiXPRows.Core.node-at`、`YiXPFold.pres`，不新建关系族；这些前提在有限层的实填见 `YiLWChecks.exact-example`。
Ω 形状的颈槽位与 p* 检查见 `YiLWChecks`；不改树、折叠、合法性，不给新序数界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLWWindow where
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps using (Tr⁺)
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; kp)
open import OCF.Lean.YiTBRow using (Rb; ψ)
open import OCF.Lean.YiLKIface using (OK)
import OCF.Align.EboLeanDef as E
import OCF.Lean.YiXPRel as XP
import OCF.Lean.YiXPRows as XR
import OCF.Lean.YiXPFold as XF
import OCF.Lean.YiGTNode as GN
import OCF.Lean.YiGIRel as GR

record Window {ℓ : L} (Label : Pos ℓ → E.T → Set) : Set₁ where
  field
    Member : Pos ℓ → E.T → Set
    sound : ∀ p κ → Member p κ → Label p κ
open Window public

NonemptyAt : ∀ {ℓ Label} → Window {ℓ} Label → Pos ℓ → Set
NonemptyAt W p = Σ E.T (Member W p)

Covers : ∀ {ℓ Label} → Window {ℓ} Label → Set
Covers {Label = Label} W = ∀ p κ → Label p κ → Member W p κ

full : ∀ {ℓ} (Label : Pos ℓ → E.T → Set) → Window Label
full Label = record { Member = Label ; sound = λ p κ l → l }

full-covers : ∀ {ℓ} (Label : Pos ℓ → E.T → Set) → Covers (full Label)
full-covers Label p κ l = l

WindowFrame : ∀ {ℓ Label} → Window {ℓ} Label → (Pos ℓ → E.T → Set) → Set
WindowFrame W Spec = ∀ p κ → Member W p κ → Spec p κ

cover-frame : ∀ {ℓ Label} (W : Window {ℓ} Label) (Spec : Pos ℓ → E.T → Set)
  → Covers W → WindowFrame W Spec → ∀ p κ → Label p κ → Spec p κ
cover-frame W Spec cv fr p κ l = fr p κ (cv p κ l)

WeakFrame : ∀ ℓ → Window (GR.Nu ℓ) → Ok ℓ → ∀ j → j ≤ ℓ → E.T → Set
WeakFrame ℓ W o j w ν = WindowFrame W (λ p κ → GN.KeepSpec ℓ j ν p κ (kp ℓ o p w))
```

`Member p κ` 不允许把当前结点的余尾标签 κ 换成另一个成员；`cof a ≡ cΩ κ` 仍是原保持定理的前提。
`Covers` 的量化域是原关系中所有可用标签；仅有每个窗口非空不能调用 `pres`。

```agda
module Rows (Lab : L → E.T → Set) where
  module X = XP Lab
  module Y = XR Lab
  module F = XF Lab

  Frame : ∀ ℓ → Window (λ p κ → Lab (at ℓ p) κ) → Ok ℓ → ∀ j → j ≤ ℓ → E.T → Set
  Frame ℓ W o j w ν = WindowFrame W (λ p κ → Y.KeepSpec ℓ j ν p κ (kp ℓ o p w))

  covered-frame : ∀ ℓ (W : Window (λ p κ → Lab (at ℓ p) κ)) o j w ν
    → Covers W → Frame ℓ W o j w ν → Y.NodeFrame ℓ o j w ν
  covered-frame ℓ W o j w ν cv fr = cover-frame W _ cv fr

  module Node (ℓ j : L) (W : Window (λ p κ → Lab (at ℓ p) κ))
    (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) (w : j ≤ ℓ) (ν t : E.T) (β : Tr⁺ j) where
    private module C = Y.Core ℓ j o r B w ν t β

    member-row : Frame ℓ W o j w ν
      → ∀ (p : Pos ℓ) {a κ} (g : Br ℓ p → Tr ℓ) → E.cof a ≡ E.cΩ κ → Member W p κ
      → (∀ η c → X.Low ℓ p η c → X.R ℓ (E.fsT a η) (g c))
      → (∀ η c → X.Low ℓ p η c → X.R j (E.ψ ν (t ++ E.fsT a η) ∷ []) (proj₁ (C.F (g c))))
      → Y.ChainAt ℓ o r B t a p κ g
      → X.R j (E.ψ ν (t ++ a) ∷ []) (proj₁ (C.F (Ω p g)))
    member-row fr p {κ = κ} g e m hg bh hc =
      C.node-at p g e (sound W p κ m) hg bh hc (kp ℓ o p w) (fr p κ m)

  pres : ∀ ℓ (W : Window (λ p κ → Lab (at ℓ p) κ)) → Covers W → Y.Kit ℓ
    → (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) → OK B
    → (t : E.T) → X.PrefixU B t → (j : L) (w : j ≤ ℓ) (ν : E.T)
    → Frame ℓ W o j w ν → Y.RouteOK ℓ o r j w ν
    → (β : Tr⁺ j) → X.R j (E.ψ ν t ∷ []) (proj₁ β)
    → ∀ {a x} → X.R ℓ a x
    → X.R j (E.ψ ν (t ++ a) ∷ []) (proj₁ (ψ ℓ o r B j w β x))
  pres ℓ W cv kt o r B gb t pref j w ν fr rt =
    F.pres ℓ kt o r B gb t pref j w ν (covered-frame ℓ W o j w ν cv fr , rt)
```
