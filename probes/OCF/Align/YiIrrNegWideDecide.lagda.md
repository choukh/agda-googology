# YiIrrNeg 第 3 项（续）：同一个大定义域推出 "无关证据的判定"

[YiIrrNegWide](YiIrrNegWide.lagda.md) 从 "定义域含整个 `Only0 × Legal` 片段" 推出 `IrrSearch`。
`IrrSearch` 可以由不看证据的搜索实现，它在 Agda 里写不出，只因为语言没有这种递归。
本篇把同一处写得更硬：同样的前提推出 `IrrDecide`——对单调的布尔列 `γ`，
凭一份只能无关使用的 "`γ` 字面全假，或 `γ` 有真值" 的证明，判定是哪一种。

**读法（判断，不是定理）。** `IrrDecide` 不能由只读 `γ` 的可计算过程实现：
单调的布尔列在经典意义上总是两种之一，判定它等于判定停机。所以这条不依赖 Agda
对无关参数的具体限制。它仍然**不是乙线的数学障碍**：反例对象不在规范塔的读回域内，
并且缺的东西很具体——定义域里没有相关的下界合法证据。给定义域补上它
（`YiIrrNegWide.Low0`），证据本身就含判定结果（`low0-node₂→decide`）。

这是同形反例的第二条，也是最后一条；这个方向到此为止。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiIrrNegWideDecide where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim; ⊥-elim-irr)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck
open import OCF.Align.YiIrrIf
open import OCF.Align.YiIrrNegWide using (Found; lgl-cp; body; suc≢lim; Low0)
```

## 1 被推出的原则

`Flat γ` 是字面的函数相等，不是逐点全假；这样前提不借函数外延。
两种证据各有闭实例（`quiet`、`loud`）。

```agda
Mono : (ℕ → Bool) → Set
Mono γ = ∀ n → γ n ≡ true → γ (suc n) ≡ true

AllFalse : (ℕ → Bool) → Set
AllFalse γ = ∀ n → γ n ≡ false

Flat : (ℕ → Bool) → Set
Flat γ = γ ≡ (λ n → false)

Evidence : (ℕ → Bool) → Set
Evidence γ = Flat γ ⊎ Found γ

IrrDecide : Set
IrrDecide = ∀ γ → Mono γ → .(Evidence γ) → AllFalse γ ⊎ Found γ

quiet loud : ℕ → Bool
quiet n = false
loud n = true

quiet-mono : Mono quiet
quiet-mono n ()

loud-mono : Mono loud
loud-mono n p = refl

quiet-evidence : Evidence quiet
quiet-evidence = inj₁ refl

loud-evidence : Evidence loud
loud-evidence = inj₂ (zero , refl)
```

## 2 下界：它合法，当且仅当有证据

`trace γ = lim (tick (γ n))`，`tick` 把假送到 0，把真送到 `flat + 1`，`flat = lim (0, 0, …)`。
`γ` 字面全假时 `trace γ` 字面就是 `flat`。`roof γ = lim (slot γ (γ m))`，
`slot` 把假送到 `flat`，把真送到 `trace γ + 1`。下界是 `lim (trace γ, roof γ, roof γ, …)`；
它的第 0 步 `trace γ ⊲ roof γ` 要么在某个真值处走 "加一"，要么在某个假值处要求 `trace γ ≡ flat`。

```agda
flat : R
flat = G.lim (λ n → G.zero)

flat-legal : Lgl zero flat
flat-legal = (λ n → inj₁ refl) , (λ n → tt)

tick : Bool → R
tick false = G.zero
tick true = G.suc flat

tick-step : ∀ x y → (x ≡ true → y ≡ true) → Cp zero (tick x) (tick y)
tick-step false false h = inj₁ refl
tick-step false true h = inj₂ (inj₂ (zero , inj₁ refl))
tick-step true false h with h refl
... | ()
tick-step true true h = inj₁ refl

tick-legal : ∀ x → Lgl zero (tick x)
tick-legal false = tt
tick-legal true = flat-legal

tick-zero : ∀ x → tick x ≡ G.zero → x ≡ false
tick-zero false e = refl
tick-zero true ()

trace : (ℕ → Bool) → R
trace γ = G.lim (λ n → tick (γ n))

trace-legal : ∀ γ → Mono γ → Lgl zero (trace γ)
trace-legal γ mono =
  (λ n → tick-step (γ n) (γ (suc n)) (mono n)) , (λ n → tick-legal (γ n))

flat-below-trace : ∀ γ n → γ n ≡ true → Cp zero flat (trace γ)
flat-below-trace γ n p = inj₂ (n ,
  subst (λ z → Cp zero flat (tick z)) (sym p) (inj₂ (inj₁ refl)))

slot : (ℕ → Bool) → Bool → R
slot γ false = flat
slot γ true = G.suc (trace γ)

slot-step : ∀ γ x y → (x ≡ true → y ≡ true) →
  (y ≡ true → Cp zero flat (trace γ)) → Cp zero (slot γ x) (slot γ y)
slot-step γ false false h b = inj₁ refl
slot-step γ false true h b = inj₂ (b refl)
slot-step γ true false h b with h refl
... | ()
slot-step γ true true h b = inj₁ refl

slot-legal : ∀ γ → Mono γ → ∀ x → Lgl zero (slot γ x)
slot-legal γ mono false = flat-legal
slot-legal γ mono true = trace-legal γ mono

roof : (ℕ → Bool) → R
roof γ = G.lim (λ m → slot γ (γ m))

roof-legal : ∀ γ → Mono γ → Lgl zero (roof γ)
roof-legal γ mono =
  (λ m → slot-step γ (γ m) (γ (suc m)) (mono m) (flat-below-trace γ (suc m))) ,
  (λ m → slot-legal γ mono (γ m))

column₂ : (ℕ → Bool) → ℕ → R
column₂ γ zero = trace γ
column₂ γ (suc n) = roof γ

bound₂ : (ℕ → Bool) → R
bound₂ γ = G.lim (column₂ γ)

trace-below-roof : ∀ γ → Evidence γ → Cp zero (trace γ) (roof γ)
trace-below-roof .(λ n → false) (inj₁ refl) = inj₂ (zero , inj₁ refl)
trace-below-roof γ (inj₂ (n , p)) = inj₂ (n ,
  subst (λ z → Cp zero (trace γ) (slot γ z)) (sym p) (inj₂ (inj₁ refl)))

evidence→legal : ∀ γ → Mono γ → Evidence γ → Lgl zero (bound₂ γ)
evidence→legal γ mono ev = step , lawful
  where
  step : ∀ k → Cp zero (column₂ γ k) (column₂ γ (suc k))
  step zero = trace-below-roof γ ev
  step (suc k) = inj₁ refl
  lawful : ∀ k → Lgl zero (column₂ γ k)
  lawful zero = trace-legal γ mono
  lawful (suc k) = roof-legal γ mono

unsuc : R → R
unsuc (G.suc a) = a
unsuc _ = G.zero

zero≢suc : ∀ {a : R} → G.zero ≡ G.suc a → ⊥
zero≢suc ()

head-clash : ∀ γ (x : Bool) → γ zero ≡ x → tick x ≡ slot γ x → ⊥
head-clash γ false q ()
head-clash γ true q e = zero≢suc
  (trans (cong (λ z → body z zero) (cong unsuc e)) (cong tick q))

slot-case : ∀ γ m (x : Bool) → γ m ≡ x → Cp zero (trace γ) (slot γ x) →
  Found γ ⊎ (trace γ ≡ flat)
slot-case γ m true q p = inj₁ (m , q)
slot-case γ m false q (inj₁ e) = inj₂ e
slot-case γ m false q (inj₂ (n , inj₁ ()))
slot-case γ m false q (inj₂ (n , inj₂ ()))

legal→case : ∀ γ → Lgl zero (bound₂ γ) → Found γ ⊎ (trace γ ≡ flat)
legal→case γ (st , lf) with st zero
... | inj₁ e = ⊥-elim (head-clash γ (γ zero) refl (cong (λ z → body z zero) e))
... | inj₂ (m , p) = slot-case γ m (γ m) refl p

flat→all-false : ∀ γ → trace γ ≡ flat → AllFalse γ
flat→all-false γ q n = tick-zero (γ n) (cong (λ z → body z n) q)
```

## 3 结点

第一支是 `lower γ`（`trace γ` 的读回），分支恒为 `upper γ = lim (slotᴸ γ (γ m))`。
`Legal` 的第一位置字段 `CP (lower γ) (upper γ)` 在两种情形各有证明，都从相关的守卫取得。

```agda
base : LF
base = lim (λ n → zero)

base-legal : Legal base
base-legal = (λ n → self) , (λ n → tt)

lower : (ℕ → Bool) → LF
lower γ = read0 (trace γ)

lower-legal : ∀ γ → Mono γ → Legal (lower γ)
lower-legal γ mono = read0-legal (trace γ) (trace-legal γ mono)

lower-only : ∀ γ → Only0 (lower γ)
lower-only γ = read0-only (trace γ)

base-below-lower : ∀ γ n → γ n ≡ true → CP base (lower γ)
base-below-lower γ n p = lim n
  (subst (λ z → CP base (read0 (tick z))) (sym p) (suc self))

slotᴸ : (ℕ → Bool) → Bool → LF
slotᴸ γ false = base
slotᴸ γ true = suc (lower γ)

slotᴸ-step : ∀ γ x y → (x ≡ true → y ≡ true) →
  (y ≡ true → CP base (lower γ)) → CP (slotᴸ γ x) (slotᴸ γ y)
slotᴸ-step γ false false h b = self
slotᴸ-step γ false true h b = suc (b refl)
slotᴸ-step γ true false h b with h refl
... | ()
slotᴸ-step γ true true h b = self

slotᴸ-legal : ∀ γ → Mono γ → ∀ x → Legal (slotᴸ γ x)
slotᴸ-legal γ mono false = base-legal
slotᴸ-legal γ mono true = lower-legal γ mono

slotᴸ-only : ∀ γ x → Only0 (slotᴸ γ x)
slotᴸ-only γ false = λ n → tt
slotᴸ-only γ true = lower-only γ

upper : (ℕ → Bool) → LF
upper γ = lim (λ m → slotᴸ γ (γ m))

upper-legal : ∀ γ → Mono γ → Legal (upper γ)
upper-legal γ mono =
  (λ m → slotᴸ-step γ (γ m) (γ (suc m)) (mono m) (base-below-lower γ (suc m))) ,
  (λ m → slotᴸ-legal γ mono (γ m))

upper-only : ∀ γ → Only0 (upper γ)
upper-only γ m = slotᴸ-only γ (γ m)

node₂ : ∀ γ → Mono γ → .(Evidence γ) → LF
node₂ γ mono s = lc zero (bound₂ γ) (evidence→legal γ mono s)
  (raw0-Nested (bound₂ γ)) (lower γ) (λ η e → upper γ)

found-first : ∀ γ n → γ n ≡ true → CP (lower γ) (upper γ)
found-first γ n p = lim n
  (subst (λ z → CP (lower γ) (slotᴸ γ z)) (sym p) (suc self))

flat-first : ∀ γ → trace γ ≡ flat → CP (lower γ) (upper γ)
flat-first γ q = lim zero (aux (γ zero) (flat→all-false γ q zero))
  where
  aux : ∀ x → x ≡ false → CP (lower γ) (slotᴸ γ x)
  aux .false refl = subst (λ z → CP z base) (sym (cong read0 q)) self

lower-below-upper : ∀ γ η → Gd zero (bound₂ γ) η → CP (lower γ) (upper γ)
lower-below-upper γ η e with legal→case γ (lgl-cp η (proj₁ e) (proj₁ (proj₂ e)))
... | inj₁ (n , p) = found-first γ n p
... | inj₂ q = flat-first γ q

node₂-only : ∀ γ (mono : Mono γ) .(s : Evidence γ) → Only0 (node₂ γ mono s)
node₂-only γ mono s = lower-only γ , (λ η e → upper-only γ)

node₂-legal : ∀ γ (mono : Mono γ) .(s : Evidence γ) → Legal (node₂ γ mono s)
node₂-legal γ mono s =
  tt ,
  (λ η e → lower-below-upper γ η e) ,
  (λ η e η′ e′ d → self) ,
  (λ η e e′ → refl) ,
  lower-legal γ mono ,
  (λ η e → upper-legal γ mono)

-- 前提可满足: 两种证据各有一棵闭的合法结点.
quiet-node-legal : Legal (node₂ quiet quiet-mono quiet-evidence)
quiet-node-legal = node₂-legal quiet quiet-mono quiet-evidence

loud-node-legal : Legal (node₂ loud loud-mono loud-evidence)
loud-node-legal = node₂-legal loud loud-mono loud-evidence
```

## 4 从接口取出判定

相关的数据仍只有一处：`Cp zero (ψ (lower γ)) (ψ (node₂ …))` 的证明。它在两层极限里各选一个下标。
第二层的下标 `m` 处若 `γ m` 为真，得到见证；若为假，则对每个 `n`，`γ n` 为真会与这条相关的路径矛盾，
而 `γ n` 可判定，于是逐点得到 `γ n ≡ false`。关于输出形状的等式都只在无关位置使用。

```agda
flatω : R
flatω = G.lim (λ n → one)

val : Bool → R
val false = one
val true = successor flatω

one≢lim : ∀ {f : ℕ → R} → one ≡ G.lim f → ⊥
one≢lim ()

val-not-lim : ∀ x (f : ℕ → R) → Dn zero G.zero (f zero) → val x ≡ G.lim f → ⊥
val-not-lim false f pos ()
val-not-lim true f pos e =
  subst (Dn zero G.zero) (sym (cong (λ z → body z zero) e)) pos

val-one : ∀ x → x ≡ true → val x ≡ one → ⊥
val-one .true refl ()

below-flat : ∀ (L : ℕ → R) → Cp zero (G.lim L) flatω → L ≡ (λ n → one)
below-flat L (inj₁ e) = cong body e
below-flat L (inj₂ (k , inj₁ ()))
below-flat L (inj₂ (k , inj₂ (inj₁ ())))
below-flat L (inj₂ (k , inj₂ (inj₂ ())))

recover-false : ∀ (y : Bool) → .(y ≡ true → ⊥) → y ≡ false
recover-false false no = refl
recover-false true no = ⊥-elim-irr (no refl)

settle : ∀ γ m (x : Bool) → γ m ≡ x →
  .(x ≡ false → ∀ n → γ n ≡ true → ⊥) → AllFalse γ ⊎ Found γ
settle γ m true eq no = inj₂ (m , eq)
settle γ m false eq no =
  inj₁ (λ n → recover-false (γ n) (λ ist → no refl n ist))

module Decide (F : FoldRows)
  (wide : ∀ x → Only0 x → Legal x → FoldRows.Dom F x) where
  open FoldRows F

  dom-zero : Dom zero
  dom-zero = wide zero tt tt

  dom-base : Dom base
  dom-base = wide base (λ n → tt) base-legal

  dom-tick : ∀ x → Dom (read0 (tick x))
  dom-tick x = wide (read0 (tick x)) (read0-only (tick x))
    (read0-legal (tick x) (tick-legal x))

  dom-lower : ∀ γ → Mono γ → Dom (lower γ)
  dom-lower γ mono = wide (lower γ) (lower-only γ) (lower-legal γ mono)

  dom-slot : ∀ γ → Mono γ → ∀ x → Dom (slotᴸ γ x)
  dom-slot γ mono x = wide (slotᴸ γ x) (slotᴸ-only γ x) (slotᴸ-legal γ mono x)

  dom-upper : ∀ γ → Mono γ → Dom (upper γ)
  dom-upper γ mono = wide (upper γ) (upper-only γ) (upper-legal γ mono)

  dom-node : ∀ γ (mono : Mono γ) .(s : Evidence γ) → Dom (node₂ γ mono s)
  dom-node γ mono s = wide (node₂ γ mono s)
    (node₂-only γ mono s) (node₂-legal γ mono s)

  ψ-base : ψ base dom-base ≡ flatω
  ψ-base = trans (lim-row (λ n → zero) dom-base)
    (cong (λ z → G.lim (λ n → z)) (zero-row dom-zero))

  ψ-tick : ∀ x → ψ (read0 (tick x)) (dom-tick x) ≡ val x
  ψ-tick false = zero-row dom-zero
  ψ-tick true = trans (suc-row base (dom-tick true)) (cong successor ψ-base)

  ψ-lower : ∀ γ mono → ψ (lower γ) (dom-lower γ mono) ≡
    G.lim (λ n → ψ (read0 (tick (γ n))) (dom-tick (γ n)))
  ψ-lower γ mono = lim-row (λ n → read0 (tick (γ n))) (dom-lower γ mono)

  ψ-slot-false : ∀ γ mono x → x ≡ false →
    ψ (slotᴸ γ x) (dom-slot γ mono x) ≡ flatω
  ψ-slot-false γ mono .false refl = ψ-base

  ψ-slot-true : ∀ γ mono → ψ (slotᴸ γ true) (dom-slot γ mono true) ≡
    successor (ψ (lower γ) (dom-lower γ mono))
  ψ-slot-true γ mono = suc-row (lower γ) (dom-slot γ mono true)

  ψ-upper : ∀ γ mono → ψ (upper γ) (dom-upper γ mono) ≡
    G.lim (λ m → ψ (slotᴸ γ (γ m)) (dom-slot γ mono (γ m)))
  ψ-upper γ mono = lim-row (λ m → slotᴸ γ (γ m)) (dom-upper γ mono)

  -- gt 行; s 在这里是相关参数, 下面只在无关位置调用.
  ψ-node : ∀ γ mono (s : Evidence γ) →
    ψ (node₂ γ mono s) (dom-node γ mono s) ≡
    G.lim (λ n → ψ (upper γ) (dom-upper γ mono))
  ψ-node γ mono s = gt-row (bound₂ γ) (evidence→legal γ mono s)
    (raw0-Nested (bound₂ γ)) (lower γ) (λ η e → upper γ) (dom-node γ mono s)

  no-eq₁ : ∀ γ mono → ψ (lower γ) (dom-lower γ mono) ≡
    G.lim (λ n → ψ (upper γ) (dom-upper γ mono)) → ⊥
  no-eq₁ γ mono eq = val-not-lim (γ zero)
    (λ m → ψ (slotᴸ γ (γ m)) (dom-slot γ mono (γ m)))
    (fold-positive (slotᴸ γ (γ zero)) (dom-slot γ mono (γ zero)))
    (trans (sym (ψ-tick (γ zero)))
      (trans (cong (λ z → body z zero) (trans (sym (ψ-lower γ mono)) eq))
        (ψ-upper γ mono)))

  clash : ∀ γ mono (x : Bool) → γ zero ≡ x →
    ψ (read0 (tick x)) (dom-tick x) ≡ ψ (slotᴸ γ x) (dom-slot γ mono x) → ⊥
  clash γ mono false q e =
    one≢lim (trans (sym (ψ-tick false)) (trans e ψ-base))
  clash γ mono true q e = one≢lim
    (trans
      (cong (λ z → body z zero)
        (trans
          (cong (λ z → body z (suc zero))
            (trans (sym (ψ-tick true)) (trans e (ψ-slot-true γ mono))))
          (ψ-lower γ mono)))
      (trans (ψ-tick (γ zero)) (cong val q)))

  no-eq₂ : ∀ γ mono → ψ (lower γ) (dom-lower γ mono) ≡
    G.lim (λ m → ψ (slotᴸ γ (γ m)) (dom-slot γ mono (γ m))) → ⊥
  no-eq₂ γ mono eq = clash γ mono (γ zero) refl
    (cong (λ z → body z zero) (trans (sym (ψ-lower γ mono)) eq))

  no-true : ∀ γ mono m n (w : R) → γ m ≡ false → γ n ≡ true →
    Cp zero (ψ (lower γ) (dom-lower γ mono)) w →
    w ≡ ψ (slotᴸ γ (γ m)) (dom-slot γ mono (γ m)) → ⊥
  no-true γ mono m n w isf ist q eq = val-one (γ n) ist
    (trans (sym (ψ-tick (γ n)))
      (cong (λ f → f n)
        (below-flat (λ k → ψ (read0 (tick (γ k))) (dom-tick (γ k)))
          (subst (λ z → Cp zero z flatω) (ψ-lower γ mono)
            (subst (Cp zero (ψ (lower γ) (dom-lower γ mono)))
              (trans eq (ψ-slot-false γ mono (γ m) isf)) q)))))

  stage₂ : ∀ γ mono (w : R) → Cp zero (ψ (lower γ) (dom-lower γ mono)) w →
    .(w ≡ G.lim (λ m → ψ (slotᴸ γ (γ m)) (dom-slot γ mono (γ m)))) →
    AllFalse γ ⊎ Found γ
  stage₂ γ mono w (inj₁ e) E = ⊥-elim-irr (no-eq₂ γ mono (trans e E))
  stage₂ γ mono G.zero (inj₂ ()) E
  stage₂ γ mono (G.suc v) (inj₂ p) E = ⊥-elim-irr (suc≢lim E)
  stage₂ γ mono (G.lim r) (inj₂ (m , q)) E = settle γ m (γ m) refl
    (λ isf n ist →
      no-true γ mono m n (r m) isf ist q (cong (λ z → body z m) E))
  stage₂ γ mono (G.lc () c t g) (inj₂ p) E
  stage₂ γ mono (G.em () a) (inj₂ p) E
  stage₂ γ mono G.top (inj₂ ()) E

  stage₁ : ∀ γ mono (v : R) → Cp zero (ψ (lower γ) (dom-lower γ mono)) v →
    .(v ≡ G.lim (λ n → ψ (upper γ) (dom-upper γ mono))) →
    AllFalse γ ⊎ Found γ
  stage₁ γ mono v (inj₁ e) E = ⊥-elim-irr (no-eq₁ γ mono (trans e E))
  stage₁ γ mono G.zero (inj₂ ()) E
  stage₁ γ mono (G.suc v) (inj₂ p) E = ⊥-elim-irr (suc≢lim E)
  stage₁ γ mono (G.lim r) (inj₂ (n , q)) E = stage₂ γ mono (r n) q
    (trans (cong (λ z → body z n) E) (ψ-upper γ mono))
  stage₁ γ mono (G.lc () c t g) (inj₂ p) E
  stage₁ γ mono (G.em () a) (inj₂ p) E
  stage₁ γ mono G.top (inj₂ ()) E

  by-position : IrrDecide
  by-position γ mono s = stage₁ γ mono (ψ (node₂ γ mono s) (dom-node γ mono s))
    (position (lower γ) (node₂ γ mono s) (dom-lower γ mono)
      (dom-node γ mono s) (fst self))
    (ψ-node γ mono s)

wide→irr-decide : (F : FoldRows) →
  (∀ x → Only0 x → Legal x → FoldRows.Dom F x) → IrrDecide
wide→irr-decide F wide = Decide.by-position F wide
```

## 5 与搜索的关系，与补上的字段

`IrrDecide` 给出单调列上的搜索。反过来不成立的理由在读法里（搜索可由不看证据的程序实现，判定不能）。
补上相关的下界证据后，判定结果就在成员资格里。

```agda
irr-decide→search : IrrDecide → ∀ γ → Mono γ → .(Found γ) → Found γ
irr-decide→search dec γ mono s with dec γ mono (inj₂ s)
... | inj₂ f = f
... | inj₁ af = ⊥-elim-irr (clash-with af s)
  where
  true≢false : ∀ {x : Bool} → x ≡ true → x ≡ false → ⊥
  true≢false refl ()
  clash-with : AllFalse γ → Found γ → ⊥
  clash-with af (n , p) = true≢false p (af n)

low0-node₂→decide : ∀ γ (mono : Mono γ) .(s : Evidence γ) →
  Low0 (node₂ γ mono s) → AllFalse γ ⊎ Found γ
low0-node₂→decide γ mono s (l , _) with legal→case γ l
... | inj₁ f = inj₂ f
... | inj₂ q = inj₁ (flat→all-false γ q)
```

## 结论与范围

| 档 | 结果 |
|---|---|
| 编译定理 | `wide→irr-decide`：`FoldRows` 的实例若定义域含整个 `Only0 × Legal` 片段，则 `IrrDecide`。用到 `position`、`gt-row`、`lim-row`、`suc-row`、`zero-row`、`fold-positive` |
| 编译定理 | `node₂-legal`、`node₂-only`：反例结点只凭无关的证据就在片段里；`quiet-node-legal`、`loud-node-legal` 是两种证据下的闭实例 |
| 编译定理 | `irr-decide→search`：`IrrDecide` 给出单调列上的无关搜索 |
| 编译定理 | `low0-node₂→decide`：带相关下界证据时，判定结果由证据直接读出 |
| 判断 | `IrrDecide` 没有 Agda 的闭证明。纸面理由（连续性）：这样的项只能读 `γ` 的有限多项；在 `quiet` 上它必须答 "全假"，读过的项数为 N；把第 N 项以后改成真，输入的前 N 项不变，它仍答 "全假"，与给出的 `AllFalse` 矛盾。这一步用到 "Agda 可定义的泛函连续"，是元层的事实，本篇没有形式化 |
| 判断 | 所以 `Dom x = Only0 x × Legal x` 这一取法不只是在 Agda 里写不出，也不能由不带证据的可计算过程实现 |

**这条否定的范围。** 否定的是 "定义域取整个 `Only0 × Legal`，不另带相关的下界证据" 这一种取法。
不否定 `FoldRows`（它只要求定义域含规范 Ω₁ 并遗传），不否定带 `Low0` 的整个合法片段，
不否定乙线。反例对象 `node₂ γ mono s` 不在规范塔的读回域内。

**否定的依据属于哪一档。** `wide→irr-decide` 是编译定理；"`IrrDecide` 不可证" 是判断。
按 AGENTS "否定路线要有依据"，在这个判断经独立审核之前，对该取法只能写 "未走通"，
不能写成已否定。

没有 Funext，没有公设，没有洞。没有序数值，强度没有变化。
