# YiRawNeg 第 3 项 (i)：根上的链带相关证书时，极限合法等价于什么

**判决：编译定理与一条条件定理，不用函数外延。** 链点带相关的 `Lgl zero η`，证书由分支值的合法性引理生产时：根的极限对一切起点合法，当且仅当分支值沿链的一步单调 (`StepMono`)。
"沿限制单调" (`RestrMono`) 推出它，并且穿过极限行不要函数相等 (`restr-lim`)；"两份独立证书下单调" (`FreeMono`) 也推出它，但逼出分支值与证书无关，在极限行上要函数相等。两者都不是必要的 (`reading`)。
条件定理 `Bridge.root-legal`：任何 `RawFold` 加上 `em` 与 `top` 在目标 `base` 处的两行，`top` 处的折叠作分支值时根合法；前提的实例是 [YiRawNegModel](YiRawNegModel.lagda.md) 的 `canonical`，它不是折叠。
不否定任何写法；没有值。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiRawNegChain where

open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck
open import OCF.Align.YiIrrIf
open import OCF.Align.YiLvIf
open import OCF.Align.YiIrrFoldBase using (add-legal)
open import OCF.Align.YiIrrFbRaw using (Cp-tr)
open import OCF.Align.YiLvNegCert using (κ; κ-lgl; antisym; Kᶜ; Kᶜ-plain; Kᶜ-legal)
open import OCF.Align.YiLvNegRestrict
  using (restrict; add-weak; restrict-add-weak; Coh; add-coh; restrictL; restrictL-read0)
open import OCF.Align.YiRawIf
open import OCF.Align.YiRawNegModel using (canonical; lim-body; module Forced; canonical-top-lim)
```

## 1 最小记录与三种单调

`E η l` 是坐标 `η` 那一支的折叠值，读相关的证书 `l`。链点是坐标连同证书；下一点的证书由 `add-legal` 与 `E-legal` 造出。
根是各链点处分支值的极限 (目标层 0，推进与观察是同一个值)。

```agda
record Branch : Set where
  field
    E : (η : R) → Lgl zero η → R
    E-legal : ∀ η l → Lgl zero (E η l)

module Root (B : Branch) where
  open Branch B

  Pt : Set
  Pt = Σ R (Lgl zero)

  next : Pt → Pt
  next (η , l) = (η +ʳ E η l) , add-legal η (E η l) l (E-legal η l)

  see : Pt → R
  see (η , l) = E η l

  root : Pt → R
  root p = G.lim (λ n → see (iterate next p n))

  StepMono : Set
  StepMono = ∀ η l →
    Cp zero (E η l) (E (η +ʳ E η l) (add-legal η (E η l) l (E-legal η l)))

  RestrAt : R → Set
  RestrAt η′ = ∀ η (p : Cp zero η η′) (l′ : Lgl zero η′) →
    Cp zero (E η (restrict p l′)) (E η′ l′)

  RestrMono : Set
  RestrMono = ∀ η′ → RestrAt η′

  FreeMono : Set
  FreeMono = ∀ η η′ (l : Lgl zero η) (l′ : Lgl zero η′) →
    Cp zero η η′ → Cp zero (E η l) (E η′ l′)

  see-step : StepMono → ∀ q → Cp zero (see q) (see (next q))
  see-step sm (η , l) = sm η l

  see-legal : ∀ q → Lgl zero (see q)
  see-legal (η , l) = E-legal η l

  -- 根对一切起点合法, 当且仅当 StepMono.
  step→root : StepMono → ∀ p → Lgl zero (root p)
  step→root sm p =
    (λ n → see-step sm (iterate next p n)) , (λ n → see-legal (iterate next p n))

  root→step : (∀ p → Lgl zero (root p)) → StepMono
  root→step h η l = proj₁ (h (η , l)) zero

  -- 限制形式推出它: 下一点的证书沿 add-weak 限制回来就是这一点的证书.
  restr→step : RestrMono → StepMono
  restr→step rm η l =
    subst (λ z → Cp zero (E η z)
        (E (η +ʳ E η l) (add-legal η (E η l) l (E-legal η l))))
      (restrict-add-weak η (E η l) l (E-legal η l))
      (rm (η +ʳ E η l) η (add-weak η (E η l)) (add-legal η (E η l) l (E-legal η l)))

  free→restr : FreeMono → RestrMono
  free→restr fm η′ η p l′ = fm η η′ (restrict p l′) l′ p

  -- 两份独立证书的形式逼出分支值与证书无关.
  free→const : FreeMono → ∀ η (l l′ : Lgl zero η) → E η l ≡ E η l′
  free→const fm η l l′ =
    antisym zero tt (fm η η l l′ (inj₁ refl)) (fm η η l′ l (inj₁ refl))
```

极限行：极限坐标的分支值是各项分支值的极限 (读回与 Ω 都逐项，真的折叠会有这一行)。
限制形式在这一行上由各项的限制形式得到；独立证书的形式在这一行上要两个函数字面相等。

```agda
  LimRow : Set
  LimRow = ∀ f (st : ∀ n → Cp zero (f n) (f (suc n))) (lf : ∀ n → Lgl zero (f n)) →
    E (G.lim f) (st , lf) ≡ G.lim (λ n → E (f n) (lf n))

  restr-lim : LimRow → ∀ f → (∀ n → RestrAt (f n)) → RestrAt (G.lim f)
  restr-lim row f ih .(G.lim f) (inj₁ refl) l′ = inj₁ refl
  restr-lim row f ih η (inj₂ (n , p)) (st , lf) =
    subst (Cp zero (E η (restrict p (lf n)))) (sym (row f st lf))
      (inj₂ (n , ih n η p (lf n)))

  free-needs-function-equality : FreeMono → LimRow →
    ∀ f (st st′ : ∀ n → Cp zero (f n) (f (suc n))) (lf lf′ : ∀ n → Lgl zero (f n)) →
    (λ n → E (f n) (lf n)) ≡ (λ n → E (f n) (lf′ n))
  free-needs-function-equality fm row f st st′ lf lf′ = cong lim-body
    (trans (sym (row f st lf))
      (trans (free→const fm (G.lim f) (st , lf) (st′ , lf′)) (row f st′ lf′)))
```

## 2 实例

`plain`：分支值就是坐标，不读证书，三种单调与极限行都成立。
`reading`：分支值读证书里的路径 (极限处第 0 步走过的分支编号之和是否为零)。它的根对一切起点合法，但不满足独立证书的形式：
`κ` 的两份证书给出不同的分支值。所以 "分支值不依赖证书" 不是根合法的必要条件。

```agda
plain : Branch
plain = record { E = λ η l → η ; E-legal = λ η l → l }

plain-free : Root.FreeMono plain
plain-free η η′ l l′ p = p

plain-lim : Root.LimRow plain
plain-lim f st lf = refl

weight : ∀ {a} b → Cp zero a b → ℕ
weightᵈ : ∀ {a} b → Dn zero a b → ℕ
weight b (inj₁ e) = 0
weight b (inj₂ p) = weightᵈ b p
weightᵈ (G.suc b) p = weight b p
weightᵈ (G.lim f) (n , p) = n + weight (f n) p
weightᵈ (G.lc () c t g) p
weightᵈ (G.em () T) p
weightᵈ G.top ()

bit : ℕ → R
bit zero = G.zero
bit (suc n) = one

bit-legal : ∀ n → Lgl zero (bit n)
bit-legal zero = tt
bit-legal (suc n) = tt

zero-bit : ∀ n → Cp zero G.zero (bit n)
zero-bit zero = inj₁ refl
zero-bit (suc n) = inj₂ (inj₁ refl)

Eʳ : (η : R) → Lgl zero η → R
Eʳ (G.lim f) (st , lf) = bit (weight (f 1) (st 0))
Eʳ G.zero l = one
Eʳ (G.suc a) l = one
Eʳ G.top l = one
Eʳ (G.lc () c t g) l
Eʳ (G.em () T) l

Eʳ-legal : ∀ η l → Lgl zero (Eʳ η l)
Eʳ-legal (G.lim f) (st , lf) = bit-legal (weight (f 1) (st 0))
Eʳ-legal G.zero l = tt
Eʳ-legal (G.suc a) l = tt
Eʳ-legal G.top l = tt
Eʳ-legal (G.lc () c t g) l
Eʳ-legal (G.em () T) l

reading : Branch
reading = record { E = Eʳ ; E-legal = Eʳ-legal }

reading-lim-step : ∀ f (l : Lgl zero (G.lim f)) w →
  Cp zero (bit w) (Eʳ (G.lim f +ʳ bit w) (add-legal (G.lim f) (bit w) l (bit-legal w)))
reading-lim-step f (st , lf) zero = zero-bit (weight (f 1) (st 0))
reading-lim-step f l (suc w) = inj₁ refl

reading-step : Root.StepMono reading
reading-step (G.lim f) (st , lf) = reading-lim-step f (st , lf) (weight (f 1) (st 0))
reading-step G.zero l = inj₁ refl
reading-step (G.suc a) l = inj₁ refl
reading-step G.top l = inj₁ refl
reading-step (G.lc () c t g) l
reading-step (G.em () T) l

reading-root-legal : ∀ p → Lgl zero (Root.root reading p)
reading-root-legal = Root.step→root reading reading-step

IsZero : R → Set
IsZero G.zero = ⊤
IsZero _ = ⊥

reading₀ : Eʳ κ (κ-lgl 0) ≡ G.zero
reading₀ = refl

reading₁ : Eʳ κ (κ-lgl 1) ≡ one
reading₁ = refl

reading-not-free : Root.FreeMono reading → ⊥
reading-not-free fm = subst IsZero (Root.free→const reading fm κ (κ-lgl 0) (κ-lgl 1)) tt

-- 它也不满足限制形式: κ 的第 0 项是 1, 那里的分支值是 1, 而 κ 在证书 0 下的分支值是 0.
reading-not-restr : Root.RestrMono reading → ⊥
reading-not-restr rm with rm κ one (inj₂ (zero , inj₁ refl)) (κ-lgl 0)
... | inj₁ ()
... | inj₂ ()
```

## 3 合法性引理带一致性前提时

若 `E-legal` 只对一致的证书 (`YiLvNegRestrict.Coh`) 给出，链点还要带一致性，下一点的一致性要 "输出证书一致" (`E-coh`)。
根合法仍由一步单调得到。这里只写到一步单调；它由限制形式得到的推导与 §1 相同。

```agda
record CohBranch : Set where
  field
    E : (η : R) → Lgl zero η → R
    E-legal : ∀ η l → Coh η l → Lgl zero (E η l)
    E-coh : ∀ η l (ch : Coh η l) → Coh (E η l) (E-legal η l ch)

module CohRoot (B : CohBranch) where
  open CohBranch B

  Pt : Set
  Pt = Σ R λ η → Σ (Lgl zero η) (Coh η)

  next : Pt → Pt
  next (η , l , ch) =
    (η +ʳ E η l) , add-legal η (E η l) l (E-legal η l ch) ,
    add-coh η (E η l) l (E-legal η l ch) ch (E-coh η l ch)

  see : Pt → R
  see (η , l , ch) = E η l

  root : Pt → R
  root p = G.lim (λ n → see (iterate next p n))

  StepMono : Set
  StepMono = ∀ η l (ch : Coh η l) →
    Cp zero (E η l) (E (η +ʳ E η l) (add-legal η (E η l) l (E-legal η l ch)))

  RestrMono : Set
  RestrMono = ∀ η η′ (p : Cp zero η η′) (l′ : Lgl zero η′) → Coh η′ l′ →
    Cp zero (E η (restrict p l′)) (E η′ l′)

  restr→step : RestrMono → StepMono
  restr→step rm η l ch =
    subst (λ z → Cp zero (E η z)
        (E (η +ʳ E η l) (add-legal η (E η l) l (E-legal η l ch))))
      (restrict-add-weak η (E η l) l (E-legal η l ch))
      (rm η (η +ʳ E η l) (add-weak η (E η l)) (add-legal η (E η l) l (E-legal η l ch))
        (add-coh η (E η l) l (E-legal η l ch) ch (E-coh η l ch)))

  see-step : StepMono → ∀ q → Cp zero (see q) (see (next q))
  see-step sm (η , l , ch) = sm η l ch

  see-legal : ∀ q → Lgl zero (see q)
  see-legal (η , l , ch) = E-legal η l ch

  step→root : StepMono → ∀ p → Lgl zero (root p)
  step→root sm p =
    (λ n → see-step sm (iterate next p n)) , (λ n → see-legal (iterate next p n))

-- 前提的实例: 分支值就是坐标.
plain-coh : CohBranch
plain-coh = record { E = λ η l → η ; E-legal = λ η l ch → l ; E-coh = λ η l ch → ch }

plain-coh-root : ∀ p → Lgl zero (CohRoot.root plain-coh p)
plain-coh-root =
  CohRoot.step→root plain-coh (CohRoot.restr→step plain-coh (λ η η′ p l′ ch → p))
```

## 4 接到 `RawFold`：跨公共上界的一条

`RawFold.position` 只在同一个公共上界 `K` 里陈述。根上相邻两个链点的公共上界不同 (`read0 ηₙ` 与 `read0 ηₙ₊₁`)，要的是跨 `K` 的一条 `cross`。
它由 `position` 加两行得到：`em tt top` 在目标 `base` 处进到低一层；`top` 在极限层号处逐项 (`Forced.TopLim`)。
极限层号里 `top` 没有前驱 (`DnT (lim f) a = ⊥`)，所以这一处 `position` 帮不上，只能靠极限行。小的一边用大的一边的证书沿路径的限制。

```agda
restrictP : ∀ {a} b → CP a b → Plain b → Plain a
restrictP b self pl = pl
restrictP (suc b) (suc p) pl = restrictP b p pl
restrictP (lim f) (lim n p) pl = restrictP (f n) p (pl n)
restrictP (lc k c w b t g) (fst p) ()

restrictP-read0 : ∀ {a} b (p : Cp zero a b) →
  restrictP (read0 b) (read0-cp b p) (up0-plain b (raw0-Nested b)) ≡ up0-plain a (raw0-Nested a)
restrictP-read0-dn : ∀ {a} b (p : Dn zero a b) →
  restrictP (read0 b) (read0-dn b p) (up0-plain b (raw0-Nested b)) ≡ up0-plain a (raw0-Nested a)
restrictP-read0 b (inj₁ refl) = refl
restrictP-read0 b (inj₂ p) = restrictP-read0-dn b p
restrictP-read0-dn (G.suc b) p = restrictP-read0 b p
restrictP-read0-dn (G.lim f) (n , p) = restrictP-read0 (f n) p
restrictP-read0-dn (G.lc () c t g) p
restrictP-read0-dn (G.em () T) p
restrictP-read0-dn G.top ()

module Bridge (F : RawFold) where
  open RawFold F

  EmSucTop : Set
  EmSucTop = ∀ k (pl : Plain k) (L : Legal k) →
    Φ (suc k) pl L base (G.em tt G.top) tt tt ≡ Φ k pl L base G.top tt tt

  module _ (em-suc : EmSucTop) (top-lim : Forced.TopLim F) where

    cross : ∀ {a} b (p : CP a b) (pb : Plain b) (Lb : Legal b) →
      Cp zero (Φ a (restrictP b p pb) (restrictL b p Lb) base G.top tt tt)
              (Φ b pb Lb base G.top tt tt)
    cross b self pb Lb = inj₁ refl
    cross (suc b) (suc p) pb Lb =
      Cp-tr zero (cross b p pb Lb)
        (subst (λ z → Cp zero z (Φ (suc b) pb Lb base G.top tt tt)) (em-suc b pb Lb)
          (position (suc b) pb Lb base (G.em tt G.top) G.top tt tt tt tt (inj₂ (inj₁ refl))))
    cross (lim f) (lim n p) pb (st , lg) =
      subst (Cp zero (Φ _ (restrictP (f n) p (pb n)) (restrictL (f n) p (lg n)) base G.top tt tt))
        (sym (top-lim f pb (st , lg)))
        (inj₂ (n , cross (f n) p (pb n) (lg n)))
    cross (lc k c w b t g) (fst p) () Lb

    -- 极限层号处 top 折到第 0 层的合法性: 由各支的合法性加上相邻两支的证书一致得到, 不用无前提的 legal.
    top-legal : ∀ f (pl : Plain (lim f)) (st : ∀ n → CP (f n) (f (suc n)))
      (lg : ∀ n → Legal (f n)) →
      (∀ n → restrictP (f (suc n)) (st n) (pl (suc n)) ≡ pl n) →
      (∀ n → restrictL (f (suc n)) (st n) (lg (suc n)) ≡ lg n) →
      (∀ n → Lgl zero (Φ (f n) (pl n) (lg n) base G.top tt tt)) →
      Lgl zero (Φ (lim f) pl (st , lg) base G.top tt tt)
    top-legal f pl st lg cp cl h = subst (Lgl zero) (sym (top-lim f pl (st , lg)))
      ((λ n → subst₂
          (λ P L → Cp zero (Φ (f n) P L base G.top tt tt)
            (Φ (f (suc n)) (pl (suc n)) (lg (suc n)) base G.top tt tt))
          (cp n) (cl n) (cross (f (suc n)) (st n) (pl (suc n)) (lg (suc n)))) ,
       h)

    Eᶠ : (η : R) → Lgl zero η → R
    Eᶠ η l = Φ (read0 η) (up0-plain η (raw0-Nested η)) (read0-legal η l) base G.top tt tt

    branch : Branch
    branch = record
      { E = Eᶠ
      ; E-legal = λ η l →
          legal (read0 η) (up0-plain η (raw0-Nested η)) (read0-legal η l) base G.top tt tt }

    restr-mono : Root.RestrMono branch
    restr-mono η′ η p l′ =
      subst₂ (λ P L → Cp zero (Φ (read0 η) P L base G.top tt tt) (Eᶠ η′ l′))
        (restrictP-read0 η′ p) (restrictL-read0 η′ p l′)
        (cross (read0 η′) (read0-cp η′ p) (up0-plain η′ (raw0-Nested η′)) (read0-legal η′ l′))

    -- 塔的第 3 项的根: 起点 (raw1 , tt), 分支值是第 η 支的 top 折到第 0 层.
    root-legal : ∀ p → Lgl zero (Root.root branch p)
    root-legal = Root.step→root branch (Root.restr→step branch restr-mono)

-- 前提的实例 (便宜的模型, 不是折叠).
canonical-em-suc : Bridge.EmSucTop canonical
canonical-em-suc k pl L = refl

canonical-root-legal : Lgl zero
  (Root.root (Bridge.branch canonical canonical-em-suc canonical-top-lim) (raw1 , tt))
canonical-root-legal = Bridge.root-legal canonical canonical-em-suc canonical-top-lim (raw1 , tt)

-- top-legal 的前提的实例: 各支相同, 证书相同.
canonical-top-legal : Lgl zero (RawFold.Φ canonical (lim (λ _ → Kᶜ)) (λ _ → Kᶜ-plain)
  ((λ _ → self) , (λ _ → Kᶜ-legal 0)) base G.top tt tt)
canonical-top-legal =
  Bridge.top-legal canonical canonical-em-suc canonical-top-lim
    (λ _ → Kᶜ) (λ _ → Kᶜ-plain) (λ _ → self) (λ _ → Kᶜ-legal 0) (λ n → refl) (λ n → refl)
    (λ n → RawFold.legal canonical Kᶜ Kᶜ-plain (Kᶜ-legal 0) base G.top tt tt)
```

范围。§1 的等价对任何 `Branch` 成立，不假设折叠。§4 的 `cross`、`restr-mono`、`top-legal` 不用 `legal`；`root-legal` 用的是无前提的 `legal`，
而 [YiRawNegModel](YiRawNegModel.lagda.md) 的 `Forced` 说这样的 `F` 在 (`base`, `top`) 处必须与 `L` 字面无关。`legal` 改成带一致性前提时，
根合法走 §3：除限制形式外还要 `E-coh` (输出证书一致)，这一条对真的折叠没有证；或者走 [YiRawNegNorm](YiRawNegNorm.lagda.md) §4 的归一的链，那里不要它。
`cross` 里 `Plain` 的证明也取了限制 (`restrictP`)：接口的 `Φ` 相关地读它，两份 `Plain K` 的证明不用函数外延证不出相等。
