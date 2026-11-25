# YiRawNeg 第 1 项：记录 `RawFold` 可满足，槽位可以读 `L`，无前提的 `legal` 逼出什么

**判决：编译定理。** `RawFold` 有不带任何原则的模型 (`canonical`)，四条律同时可满足；它不是折叠 (分支取常值，没有链)。
把派发里的 `ccompare` 换成 `compare` 仍是模型 (`by-compare`)，它的保留槽位随 `L` 变 (`by-compare-reads-L`)：`position` 加 `keep-law` 推不出槽位与 `L` 无关。
加上 `top` 在极限层号处逐项的一行之后，无前提的 `legal` 逼出 `Φ` 在 (`base`, `top`) 处换 `Plain` 的证明与 `L` 都字面相等，以及两族任意证书下的函数相等 (`Forced`)。
不否定 `RawFold`，不否定带一致性前提的 `legal`。接口 [YiRawIf](YiRawIf.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiRawNegModel where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim; ⊥-elim-irr)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck
open import OCF.Align.YiIrrIf
open import OCF.Align.YiLvIf
open import OCF.Align.YiLvNegCompare using (At)
open import OCF.Align.YiLvNegCert using (Kᶜ; Kᶜ-plain; Kᶜ-legal; hiᶜ; loᶜ; zero≢one; antisym)
open import OCF.Align.YiLvNegCanon using (ccompare; Shape; shape; belowˢ; aboveˢ; sameˢ; ccompare-slot)
open import OCF.Align.YiLvNegKeep using (low-zero; slot-or)
open import OCF.Align.YiLvNegRestrict using (restrictL)
open import OCF.Align.YiLvFoldBase using (Way; keep; fold)
open import OCF.Align.YiLvFoldFin using (IsKeep)
open import OCF.Align.YiRawIf
```

## 1 便宜的模型，以派发为参数

保留时输出槽位 `s` 上的结点，下界取零，各支都取第一支的像；折叠时输出常值极限。
目标 `base` 处，`em` 进到低一层，`top` 按层号递归 (极限层号逐项)，使 §4 与 [YiRawNegChain](YiRawNegChain.lagda.md) 的前提有实例；其余目标把两者送到零。

```agda
Dispatch : Set
Dispatch = ∀ K → Plain K → Legal K → (τ : Tgt K) (r : Pre K) → Way (tlev K τ) (lev K r)

Complete : Dispatch → Set
Complete way = ∀ K pl L τ r → At (tlev K τ) (lev K r) → IsKeep (way K pl L τ r)

out : ∀ {m k} → Way m k → Raw m → Raw m
out {m} (keep s e) y = G.lc s (low-zero m s) y (λ _ _ → y)
out fold y = G.lim (λ _ → y)

out-dn : ∀ {m k} (w : Way m k) {a y : Raw m} → Cp m a y → Dn m a (out w y)
out-dn (keep s e) p = p
out-dn fold p = zero , p

out-lgl : ∀ {m k} (w : Way m k) {y : Raw m} → Lgl m y → Lgl m (out w y)
out-lgl (keep s e) ly =
  (λ η e′ → inj₁ refl) , (λ η e′ η′ e″ d → inj₁ refl) , (λ η e′ e″ → refl) , ly , (λ η e′ → ly)
out-lgl fold ly = (λ n → inj₁ refl) , (λ n → ly)

out-kept : ∀ {m k} (w : Way m k) (y : Raw m) → IsKeep w → Kept m k (out w y)
out-kept {m} (keep s e) y h = s , e , low-zero m s , y , (λ _ _ → y) , refl

out-lim : ∀ {m k} (w : Way m k) (y : Raw m) → (At m k → ⊥) → IsLim (out w y)
out-lim (keep s e) y no = ⊥-elim (no (s , e))
out-lim fold y no = tt

topv : ∀ K (τ : Tgt K) → Raw (tlev K τ)
topv K self = G.zero
topv K (at q) = G.zero
topv zero base = G.zero
topv (suc k) base = G.suc (topv k base)
topv (lim f) base = G.lim (λ n → topv (f n) base)
topv (lc k c w b t g) base = G.zero

topv-mono : ∀ {a} b → Plain b → CP a b → Cp zero (topv a base) (topv b base)
topv-mono b pl self = inj₁ refl
topv-mono (suc b) pl (suc p) = inj₂ (topv-mono b pl p)
topv-mono (lim f) pl (lim n p) = inj₂ (n , topv-mono (f n) (pl n) p)
topv-mono (lc k c w b t g) () (fst p)

topv-lgl : ∀ K → Plain K → Legal K → (τ : Tgt K) → Lgl (tlev K τ) (topv K τ)
topv-lgl K pl L self = tt
topv-lgl K pl L (at q) = tt
topv-lgl zero pl L base = tt
topv-lgl (suc k) pl L base = topv-lgl k pl L base
topv-lgl (lim f) pl (st , lg) base =
  (λ n → topv-mono (f (suc n)) (pl (suc n)) (st n)) , (λ n → topv-lgl (f n) (pl n) (lg n) base)
topv-lgl (lc k c w b t g) () L base

module Cheap (way : Dispatch) (complete : Complete way) where

  Φ : ∀ K → Plain K → Legal K → (τ : Tgt K) → Raw K → Raw (tlev K τ)
  emv : ∀ K → Plain K → Legal K → (τ : Tgt K) (i : Kid K) → KidR K i → Raw (tlev K τ)
  Φ K pl L τ G.zero = G.zero
  Φ K pl L τ (G.suc a) = G.suc (Φ K pl L τ a)
  Φ K pl L τ (G.lim f) = G.lim (λ n → Φ K pl L τ (f n))
  Φ K pl L τ (G.lc r c t g) = out (way K pl L τ r) (Φ K pl L τ t)
  Φ K pl L τ (G.em i T) = emv K pl L τ i T
  Φ K pl L τ G.top = topv K τ
  emv K pl L self i T = G.zero
  emv K pl L (at q) i T = G.zero
  emv zero pl L base () T
  emv (suc k) pl L base i T = Φ k pl L base T
  emv (lim f) pl (st , lg) base n T = Φ (f n) (pl n) (lg n) base T
  emv (lc k c w b t g) () L base i T

  pos : ∀ K pl L τ ξ ξ′ → Cp K ξ ξ′ → Cp (tlev K τ) (Φ K pl L τ ξ) (Φ K pl L τ ξ′)
  dn : ∀ K pl L τ ξ ξ′ → Dn K ξ ξ′ → Cp (tlev K τ) (Φ K pl L τ ξ) (Φ K pl L τ ξ′)
  dn-em : ∀ K pl L τ i′ i a T → DnK K i′ i a T →
    Cp (tlev K τ) (emv K pl L τ i′ a) (emv K pl L τ i T)
  em-top : ∀ k pl L (τ : Tgt (suc k)) a → Cp k a G.top →
    Cp (tlev (suc k) τ) (emv (suc k) pl L τ tt a) (topv (suc k) τ)
  pos K pl L τ ξ .ξ (inj₁ refl) = inj₁ refl
  pos K pl L τ ξ ξ′ (inj₂ p) = dn K pl L τ ξ ξ′ p
  dn-em K pl L self i′ i a T p = inj₁ refl
  dn-em K pl L (at q) i′ i a T p = inj₁ refl
  dn-em zero pl L base () i a T p
  dn-em (suc k) pl L base i′ i a T p = dn k pl L base a T p
  dn-em (lim f) pl (st , lg) base n .n a T (refl , p) = dn (f n) (pl n) (lg n) base a T p
  dn-em (lc k c w b t g) () L base i′ i a T p
  em-top k pl L self a p = inj₁ refl
  em-top k pl L (at q) a p = inj₁ refl
  em-top k pl L base a p = inj₂ (pos k pl L base a G.top p)
  dn K pl L τ ξ G.zero ()
  dn K pl L τ ξ (G.suc d) p = inj₂ (pos K pl L τ ξ d p)
  dn K pl L τ ξ (G.lim f) (n , p) = inj₂ (n , pos K pl L τ ξ (f n) p)
  dn K pl L τ ξ (G.lc r c t g) p = inj₂ (out-dn (way K pl L τ r) (pos K pl L τ ξ t p))
  dn K pl L τ (G.em i′ a) (G.em i T) p = dn-em K pl L τ i′ i a T p
  dn K pl L τ G.zero (G.em i T) ()
  dn K pl L τ (G.suc _) (G.em i T) ()
  dn K pl L τ (G.lim _) (G.em i T) ()
  dn K pl L τ (G.lc _ _ _ _) (G.em i T) ()
  dn K pl L τ G.top (G.em i T) ()
  dn zero pl L τ ξ G.top ()
  dn (suc k) pl L τ (G.em _ a) G.top p = em-top k pl L τ a p
  dn (suc k) pl L τ G.zero G.top ()
  dn (suc k) pl L τ (G.suc _) G.top ()
  dn (suc k) pl L τ (G.lim _) G.top ()
  dn (suc k) pl L τ (G.lc _ _ _ _) G.top ()
  dn (suc k) pl L τ G.top G.top ()
  dn (lim f) pl L τ ξ G.top ()
  dn (lc k c w b t g) () L τ ξ G.top p

  lgl : ∀ K pl L τ ξ → Lgl K ξ → Lgl (tlev K τ) (Φ K pl L τ ξ)
  lgl-em : ∀ K pl L τ i T → LglK K i T → Lgl (tlev K τ) (emv K pl L τ i T)
  lgl-em K pl L self i T l = tt
  lgl-em K pl L (at q) i T l = tt
  lgl-em zero pl L base () T l
  lgl-em (suc k) pl L base i T l = lgl k pl L base T l
  lgl-em (lim f) pl (st , lg) base n T l = lgl (f n) (pl n) (lg n) base T l
  lgl-em (lc k c w b t g) () L base i T l
  lgl K pl L τ G.zero l = tt
  lgl K pl L τ (G.suc a) l = lgl K pl L τ a l
  lgl K pl L τ (G.lim f) (st , lf) =
    (λ n → pos K pl L τ (f n) (f (suc n)) (st n)) , (λ n → lgl K pl L τ (f n) (lf n))
  lgl K pl L τ (G.lc r c t g) (tg , dir , irr , lt , lg) =
    out-lgl (way K pl L τ r) (lgl K pl L τ t lt)
  lgl K pl L τ (G.em i T) l = lgl-em K pl L τ i T l
  lgl K pl L τ G.top l = topv-lgl K pl L τ

  model : RawFold
  model = record
    { Φ = λ K pl L τ ξ l nb → Φ K pl L τ ξ
    ; keep-law = λ K pl L τ r c t g l nb a →
        out-kept (way K pl L τ r) (Φ K pl L τ t) (complete K pl L τ r a)
    ; fold-law = λ K pl L τ r c t g l nb no → out-lim (way K pl L τ r) (Φ K pl L τ t) no
    ; position = λ K pl L τ ξ ξ′ l nb l′ nb′ p → pos K pl L τ ξ ξ′ p
    ; legal = λ K pl L τ ξ l nb → lgl K pl L τ ξ l
    }
```

## 2 两个实例

`canonical` 用接口的 `dispatch`。`by-compare` 把目标在位置上的那一支换成原始的 `compare`；它同样完全。

```agda
canonical : RawFold
canonical = Cheap.model dispatch dispatch-complete

dispatchᶜ : Dispatch
dispatchᶜ K pl L base r = fold
dispatchᶜ K pl L self r = keep r refl
dispatchᶜ K pl L (at q) r = tri→way (compare K pl L q r)

completeᶜ : Complete dispatchᶜ
completeᶜ K pl L base r (() , e)
completeᶜ K pl L self r a = tt
completeᶜ K pl L (at q) r a = tri-complete (compare K pl L q r) a

by-compare : RawFold
by-compare = Cheap.model dispatchᶜ completeᶜ
```

## 3 槽位与 `L`

`SlotFree`：保留结点的槽位换 `L` 不变。`canonical` 满足 (由 `ccompare-slot`)；`by-compare` 在 `Kᶜ` 的两份证书上交出槽位 0 与 1。
探针结点在 `Kᶜ` 第 0 支的根上 (层号 0)，目标在第 1 支的根上，两份证书都是闭的。

```agda
SlotFree : RawFold → Set
SlotFree F = ∀ K pl (L L′ : Legal K) τ r c t g
  (l : Lgl K (G.lc r c t g)) (nb : Nested K (G.lc r c t g)) (d : Pre (tlev K τ)) →
  slot-or d (RawFold.Φ F K pl L τ (G.lc r c t g) l nb) ≡
  slot-or d (RawFold.Φ F K pl L′ τ (G.lc r c t g) l nb)

wslot : ∀ {m k} → Pre m → Way m k → Pre m
wslot d (keep s e) = s
wslot d fold = d

sslot : ∀ {i j} → Pre i → Shape i j → Pre i
sslot d (belowˢ s) = s
sslot d (aboveˢ s) = d
sslot d sameˢ = d

slot-out : ∀ {m k} (d : Pre m) (w : Way m k) (y : Raw m) → slot-or d (out w y) ≡ wslot d w
slot-out d (keep s e) y = refl
slot-out d fold y = refl

wslot-tri : ∀ {i j} (d : Pre i) (t : Tri i j) → wslot d (tri→way t) ≡ sslot d (shape t)
wslot-tri d (below s e) = refl
wslot-tri d (above s e) = refl
wslot-tri d (same e) = refl

dispatch-slot : ∀ K pl (L L′ : Legal K) τ r (d : Pre (tlev K τ)) →
  wslot d (dispatch K pl L τ r) ≡ wslot d (dispatch K pl L′ τ r)
dispatch-slot K pl L L′ base r d = refl
dispatch-slot K pl L L′ self r d = refl
dispatch-slot K pl L L′ (at q) r d =
  trans (wslot-tri d (ccompare K pl L q r))
    (trans (cong (sslot d) (ccompare-slot K pl L L′ q r))
      (sym (wslot-tri d (ccompare K pl L′ q r))))

canonical-slot-free : SlotFree canonical
canonical-slot-free K pl L L′ τ r c t g l nb d =
  trans (slot-out d (dispatch K pl L τ r) _)
    (trans (dispatch-slot K pl L L′ τ r d) (sym (slot-out d (dispatch K pl L′ τ r) _)))

ξᶜ : Raw Kᶜ
ξᶜ = G.lc loᶜ G.zero G.zero (λ _ _ → G.zero)

ξᶜ-lgl : Lgl Kᶜ ξᶜ
ξᶜ-lgl = (λ η e → inj₁ refl) , (λ η e η′ e′ d → inj₁ refl) , (λ η e e′ → refl) , tt , (λ η e → tt)

ξᶜ-nested : Nested Kᶜ ξᶜ
ξᶜ-nested = tt , tt , tt , (λ η e → tt)

by-compare-slot₀ : slot-or (5 , inj₁ tt)
  (RawFold.Φ by-compare Kᶜ Kᶜ-plain (Kᶜ-legal 0) (at hiᶜ) ξᶜ ξᶜ-lgl ξᶜ-nested) ≡ (0 , inj₁ tt)
by-compare-slot₀ = refl

by-compare-slot₁ : slot-or (5 , inj₁ tt)
  (RawFold.Φ by-compare Kᶜ Kᶜ-plain (Kᶜ-legal 1) (at hiᶜ) ξᶜ ξᶜ-lgl ξᶜ-nested) ≡ (1 , inj₁ tt)
by-compare-slot₁ = refl

by-compare-reads-L : SlotFree by-compare → ⊥
by-compare-reads-L sf = zero≢one (cong proj₁
  (sf Kᶜ Kᶜ-plain (Kᶜ-legal 0) (Kᶜ-legal 1) (at hiᶜ) loᶜ G.zero G.zero (λ _ _ → G.zero)
    ξᶜ-lgl ξᶜ-nested (5 , inj₁ tt)))
```

## 4 无前提的 `legal` 加上 `top` 的极限行

`TopLim`：极限层号处 `top` 折到第 0 层是各支的 `top` 逐项。读回一侧 `upT (lim f) = lim (λ n → upT (f n))`；极限逐项的折叠有这一行，在极限处改取部分和的折叠没有。
取层号 `lim (λ _ → K)`，各支的路径都是 `self`，第 0 支的证书取 `L`，其余取 `L′` (`Plain` 的证明同样取两份)：它是 `Plain` 且合法的，证书不一致。
`legal` 在这里给出 `Φ K pl L ⊲ Φ K pl′ L′`，对换后反对称。

```agda
two : ∀ {A : Set} → A → A → ℕ → A
two a b zero = a
two a b (suc n) = b

lim-body : R → ℕ → R
lim-body (G.lim f) = f
lim-body _ = λ n → G.zero

mixed : ∀ K → Legal K → Legal K → Legal (lim (λ _ → K))
mixed K L L′ = (λ n → self) , two L L′

module Forced (F : RawFold) where
  open RawFold F

  TopLim : Set
  TopLim = ∀ f (pl : Plain (lim f)) (L : Legal (lim f)) →
    Φ (lim f) pl L base G.top tt tt ≡
    G.lim (λ n → Φ (f n) (pl n) (proj₂ L n) base G.top tt tt)

  module _ (top-lim : TopLim) where

    step : ∀ K (pl pl′ : Plain K) (L L′ : Legal K) →
      Cp zero (Φ K pl L base G.top tt tt) (Φ K pl′ L′ base G.top tt tt)
    step K pl pl′ L L′ = proj₁
      (subst (Lgl zero) (top-lim (λ _ → K) (two pl pl′) (mixed K L L′))
        (legal (lim (λ _ → K)) (two pl pl′) (mixed K L L′) base G.top tt tt)) zero

    -- 换 Plain 的证明与 L, (base, top) 处的输出字面相等.
    forced-coherence : ∀ K (pl pl′ : Plain K) (L L′ : Legal K) →
      Φ K pl L base G.top tt tt ≡ Φ K pl′ L′ base G.top tt tt
    forced-coherence K pl pl′ L L′ =
      antisym zero tt (step K pl pl′ L L′) (step K pl′ pl L′ L)

    -- 极限层号处, 两族各自任意的证书给出的两个输出函数字面相等.
    function-equality-required : ∀ f (pl pl′ : Plain (lim f)) (L L′ : Legal (lim f)) →
      (λ n → Φ (f n) (pl n) (proj₂ L n) base G.top tt tt) ≡
      (λ n → Φ (f n) (pl′ n) (proj₂ L′ n) base G.top tt tt)
    function-equality-required f pl pl′ L L′ = cong lim-body
      (trans (sym (top-lim f pl L))
        (trans (forced-coherence (lim f) pl pl′ L L′) (top-lim f pl′ L′)))

-- 前提的实例: 便宜的模型满足 TopLim; 它在 (base, top) 处不读 Plain 的证明, 也不读 L.
canonical-top-lim : Forced.TopLim canonical
canonical-top-lim f pl L = refl

by-compare-top-lim : Forced.TopLim by-compare
by-compare-top-lim f pl L = refl

-- 不一致的证书的闭实例: 层号 lim (λ _ → Kᶜ), 第 0 支用 Kᶜ-legal 0, 其余用 Kᶜ-legal 1.
mixedᶜ : Legal (lim (λ _ → Kᶜ))
mixedᶜ = mixed Kᶜ (Kᶜ-legal 0) (Kᶜ-legal 1)
```

## 5 一致性前提

`CohLg`：极限层号处，后一支的证书沿这一步的路径限制回来等于前一支的证书，逐支遗传。带上这个前提，§4 用的 `mixed K L L′` 只在两份证书相等时合格。
`Plain` 的证明不携带信息，可以由无关的证明按层号重新算出 (`plain-fix`)；`Φ` 若相关地读它，跨公共上界的陈述里它也要取限制，或先过 `plain-fix`。

```agda
CohLg : ∀ K → Legal K → Set
CohLg zero L = ⊤
CohLg (suc k) L = CohLg k L
CohLg (lim f) (st , lg) =
  (∀ n → restrictL (f (suc n)) (st n) (lg (suc n)) ≡ lg n) × (∀ n → CohLg (f n) (lg n))
CohLg (lc k c w b t g) L = ⊤

mixed-coherent→same : ∀ K (L L′ : Legal K) → CohLg (lim (λ _ → K)) (mixed K L L′) → L′ ≡ L
mixed-coherent→same K L L′ (cs , cf) = cs zero

plain-fix : ∀ K → .(Plain K) → Plain K
plain-fix zero pl = tt
plain-fix (suc k) pl = plain-fix k pl
plain-fix (lim f) pl = λ n → plain-fix (f n) (pl n)
plain-fix (lc k c w b t g) pl = ⊥-elim-irr pl

plain-fix-free : ∀ K (pl pl′ : Plain K) → plain-fix K pl ≡ plain-fix K pl′
plain-fix-free K pl pl′ = refl
```

范围。§1 的模型说明四条律本身不逼出对 `legal` 的违反，对任何 `L` (含 `mixedᶜ`)。§4 说的是：再加 `TopLim` 一行，
`legal` 不带一致性前提时，`Φ` 在 (`base`, `top`) 处必须与 `Plain` 的证明、与 `L` 都字面无关，并且极限处要两个函数字面相等。
便宜的模型满足它，因为它在这一处根本不接触这两个参数。读 `L` 或只是把 `L` 逐支传下去的折叠要证这条函数相等；本文件没有证它不可得 (判断：不用函数外延证不出)。
带一致性前提时这一处的合法性可以由各支的合法性得到，见 [YiRawNegChain](YiRawNegChain.lagda.md) 的 `Bridge.top-legal`。
