# Ω 形状的窗口检查：非空不能消除颈链与 p* 的证据阻点
验收文件，读记号；编译定理：颈结点层号有非空且不唯一的完整自身窗框架；颈槽位朝零层的局部框架、自身的精确窗框架有居民。
首个阻点：p* 的任意合法标签皆为 0，目标 ν = 1 时窗口中没有满足原规格或 `KeepSpec′` 的成员（`no-star-window`、`no-star-window′`）。
颈槽位同样只能取 0，保留原精确链要求时窗口不能消除 `no-chain-neck`（`no-neck-window-chain`）；仅否定这些证据，不否定 LowKeep 或值。
复用 `YiCXWindow`、`YiCNTw1.rd-zero`、`YiMGNeck.no-chain-neck`、`YiKTSlot.no-spec*`；参数化保持及有限层实填见 `YiLWWindow.Rows.pres`、`exact-example`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLWChecks where
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (B₀; kp)
open import OCF.Lean.YiGTNode using (KeepSpec)
open import OCF.Lean.YiGLFrame using (nu0; Lbl; lbl-fin; ≤→pen)
open import OCF.Lean.YiCNTw1 using (rd-zero)
open import OCF.Lean.YiSYReduce using (a₁; h₁; oᴱ)
open import OCF.Lean.YiCLFam using (fn; okf)
open import OCF.Lean.YiLWWindow
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiBVSmall as S
import OCF.Lean.YiMGNeck as N
import OCF.Lean.YiMGRel as MR
import OCF.Lean.YiKTSlot as K
import OCF.Lean.YiCXWindow as CX
import OCF.Lean.YiELOmega as EL
open import OCF.Lean.YiELZero using (Ω₁)
import OCF.Align.EboLeanDef as E
open import OCF.Align.EboLeanBase using (_≤ᵀ_; ≤-<)
open import OCF.Align.EboLean3Base using (sucT≤)

weak-window : ∀ ℓ → Window (GR.Nu ℓ)
weak-window ℓ = full (GR.Nu ℓ)

weak-nonempty : ∀ ℓ p → NonemptyAt (weak-window ℓ) p
weak-nonempty ℓ p = [] , nu0 ℓ p

neck-nonempty : NonemptyAt (weak-window S.layer) N.neck
neck-nonempty = [] , GR.c0 refl

star-nonempty : NonemptyAt (weak-window (a₁ (suc K.one))) K.p*
star-nonempty = [] , K.nu*

neck-zero-frame : KeepSpec S.layer zero [] N.neck [] (kp S.layer S.okay N.neck (z≤ S.layer))
neck-zero-frame = refl

exact-neck-window : Window (λ p κ → EL.Lblᵒ (at S.layer p) κ)
exact-neck-window = full (λ p κ → EL.Lblᵒ (at S.layer p) κ)

exact-neck-nonempty : NonemptyAt exact-neck-window N.neck
exact-neck-nonempty = [] , refl

exact-self-frame : WindowFrame exact-neck-window
  (λ p κ → N.KeepGᵐ S.layer Ω₁ (MR.Lowᵐ S.layer p) κ (kp S.layer S.okay p self))
exact-self-frame = N.frame-selfᵐ
```

这个自身窗口取全部不高于 1 的合法标签；每个槽位都有 0，孩子 0 的顶槽位同时有 0 和 1。

```agda
bounded-window : Window (GR.Nu S.layer)
bounded-window = record
  { Member = λ p κ → GR.Nu S.layer p κ × (κ ≤ᵀ E.natT 1)
  ; sound = λ p κ m → proj₁ m }

bounded-nonempty : ∀ p → NonemptyAt bounded-window p
bounded-nonempty p = [] , nu0 S.layer p , inj₁ E.[]<

bounded-self-frame : WeakFrame S.layer bounded-window S.okay S.layer self Ω₁
bounded-self-frame p κ (nu , le) =
  ≤→pen (sucT≤ (≤-< le (E.hd< (E.lv< E.[]<)))) , nu , λ η c r → r

double-slot : Pos S.layer
double-slot = inj₂ (zero , inj₁ tt)

bounded-one : Member bounded-window double-slot (E.natT 1)
bounded-one = GR.ca (inj₂ (refl , GR.c0 refl)) , inj₂ refl

bounded-nonunique : ((p : Pos S.layer) {κ ν : E.T} → Member bounded-window p κ
  → Member bounded-window p ν → κ ≡ ν) → ⊥
bounded-nonunique un with un double-slot (proj₂ (bounded-nonempty double-slot)) bounded-one
... | ()
```

这里的窗口成员有原标签证据。p* 处零层的读法只能是 0，不是由全域标签唯一性反例推出。
比较式 `cmpᵀ 1 1 ≡ gt` 无居民；`KeepSpec′` 的额外 `Above` 一支由原 `no-spec*` 排除。

```agda
private
  zero-cut : ∀ κ → κ ≡ [] → E.cmpᵀ (E.sucT κ) (E.natT 1) ≡ E.gt → ⊥
  zero-cut .[] refl ()

star-label-zero : ∀ κ → GR.Nu (a₁ (suc K.one)) K.p* κ → κ ≡ []
star-label-zero κ nu = rd-zero nu

no-star-member : ∀ κ → GR.Nu (a₁ (suc K.one)) K.p* κ
  → KeepSpec (a₁ (suc K.one)) (h₁ K.one) (E.natT 1) K.p* κ
      (kp (a₁ (suc K.one)) (proj₂ oᴱ (suc K.one)) K.p* (ink self)) → ⊥
no-star-member κ nu sp = zero-cut κ (star-label-zero κ nu) sp

no-star-window : (W : Window (GR.Nu (a₁ (suc K.one)))) → NonemptyAt W K.p*
  → WeakFrame (a₁ (suc K.one)) W (proj₂ oᴱ (suc K.one)) (h₁ K.one) (ink self) (E.natT 1) → ⊥
no-star-window W (κ , m) fr = no-star-member κ (sound W K.p* κ m) (fr K.p* κ m)

no-star-member′ : ∀ κ → GR.Nu (a₁ (suc K.one)) K.p* κ
  → K.KeepSpec′ (a₁ (suc K.one)) (h₁ K.one) (E.natT 1) K.p* κ
      (kp (a₁ (suc K.one)) (proj₂ oᴱ (suc K.one)) K.p* (ink self)) → ⊥
no-star-member′ κ nu sp = K.no-spec* (subst
  (λ μ → K.KeepSpec′ (a₁ (suc K.one)) (h₁ K.one) (E.natT 1) K.p* μ
    (kp (a₁ (suc K.one)) (proj₂ oᴱ (suc K.one)) K.p* (ink self)))
  (star-label-zero κ nu) sp)

no-star-window′ : (W : Window (GR.Nu (a₁ (suc K.one)))) → NonemptyAt W K.p*
  → WindowFrame W (λ p κ → K.KeepSpec′ (a₁ (suc K.one)) (h₁ K.one) (E.natT 1) p κ
      (kp (a₁ (suc K.one)) (proj₂ oᴱ (suc K.one)) p (ink self))) → ⊥
no-star-window′ W (κ , m) fr = no-star-member′ κ (sound W K.p* κ m) (fr K.p* κ m)

neck-label-zero : ∀ κ → GR.Nu S.layer N.neck κ → κ ≡ []
neck-label-zero κ nu = rd-zero nu

no-neck-label-chain : ∀ r B t a κ → GR.Nu S.layer N.neck κ
  → N.ChainAtᵐ S.layer S.okay r B t a N.neck κ N.gL → ⊥
no-neck-label-chain r B t a κ nu ch = N.no-chain-neck r B t a (subst
  (λ μ → N.ChainAtᵐ S.layer S.okay r B t a N.neck μ N.gL) (neck-label-zero κ nu) ch)

no-neck-window-chain : ∀ r B t a (W : Window (GR.Nu S.layer)) κ → Member W N.neck κ
  → N.ChainAtᵐ S.layer S.okay r B t a N.neck κ N.gL → ⊥
no-neck-window-chain r B t a W κ m = no-neck-label-chain r B t a κ (sound W N.neck κ m)
```

有限层的旧多标签窗口仍有居民；它漏掉顶槽位的合法零标签，故非空与成员框架不推出 `Covers`。

```agda
finite-window : Window (GR.Nu (fn 3))
finite-window = record { Member = CX.Window ; sound = λ p κ m → CX.window-rd m }

finite-nonempty : ∀ p → NonemptyAt finite-window p
finite-nonempty = CX.window-covers

finite-frame : WeakFrame (fn 3) finite-window (okf 3) (fn 2) (inc tt self) (E.natT 2)
finite-frame = CX.window-frame

finite-nonunique : ((p : Pos (fn 3)) {κ ν : E.T} → Member finite-window p κ
  → Member finite-window p ν → κ ≡ ν) → ⊥
finite-nonunique = CX.window-nonunique

finite-not-cover : Covers finite-window → ⊥
finite-not-cover cv with cv CX.p₂ [] (nu0 (fn 3) CX.p₂)
... | ()
```

下例实填 `Rows.pres` 的覆盖、框架、路径、`Kit`、底前缀及输入关系；只复用已知有限层结论。

```agda
import OCF.Lean.YiXPRel as XP
import OCF.Lean.YiXPRows as XR
import OCF.Lean.YiXPFold as XF
import OCF.Lean.YiXPFrame as PF
import OCF.Lean.YiXPExact as PE
import OCF.Lean.YiGLExact as GX
import OCF.Lean.YiRWOps as O
open import OCF.Lean.YiTBRow using (ψ; rb-no)
open import OCF.Lean.YiKVRel using (⊴r)
module Exact = Rows Lbl
module X = XP Lbl
module Y = XR Lbl
module F = XF Lbl

exact-window : Window (λ p κ → Lbl (at (fn 3) p) κ)
exact-window = full (λ p κ → Lbl (at (fn 3) p) κ)

exact-index : Y.IndexOK (fn 3) (okf 3) (rb-no (fn 3)) (fn 2) (inc tt self) (E.natT 2)
exact-index = PF.index-all (fn 3) tt (okf 3) (rb-no (fn 3)) (inc tt self) (lbl-fin 2)

exact-example : X.R (fn 2) (E.ψ (E.natT 2) (E.Ωt (E.natT 3)) ∷ [])
  (proj₁ (ψ (fn 3) (okf 3) (rb-no (fn 3)) (B₀ (fn 3)) (fn 2) (inc tt self)
    (O.Ωt (fn 2)) (proj₁ (O.Ωt (fn 3)))))
exact-example = Exact.pres (fn 3) exact-window (full-covers _) (F.kit (fn 3) (PF.index-tree (fn 3) tt))
  (okf 3) (rb-no (fn 3)) (B₀ (fn 3)) (λ i u → ⊴r) []
  (λ p κ l → PE.to (at (fn 3) p) (GX.topˣ (at (fn 3) p) l))
  (fn 2) (inc tt self) (E.natT 2) (proj₁ exact-index) (proj₂ exact-index)
  (O.Ωt (fn 2)) (PE.to (fn 2) (GX.topˣ (fn 2) (lbl-fin 2)))
  (PE.to (fn 3) (GX.topˣ (fn 3) (lbl-fin 3)))
```
