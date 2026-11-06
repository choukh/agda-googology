# Remark 4.15：弱封闭 ⟹ 封闭

> **EboLean 删节拷贝 (记号侧验收工作, 读 Setzer 的记号 OT_I).** 归档 `Mahlo.Inacc.WO.Closed2` 的拷贝, 只改了模块名, 并删去了 EBO 路线 ([EboLean](../../../EboLean.lagda.md)) 用不到的定义 (由定义级切片判定, 删后从头编译核对). 讲解文字照旧, 可能提到已删的定义; 归档原文未动.

Setzer [Se98] Definition 4.14 (b)(d) 与 Remark 4.15（原文"easy"）。「向下封闭」在弱向下封闭之上加：任意拆分 `x =NF y + z`、`x̃`、`x^{−Fi}`、`x^{−I}`、`κ⁻`（κ ∈ R ∩ A）；「向上封闭、以 P 为界」加：正规化的 `x + y`、`φ x y`、`Ω x`、`x⁺`。Remark 4.15：若 A 弱向下封闭、弱向上封闭以 P 为界、P 向下单调、且 A 的元素都满足 P，则 A 向下封闭、向上封闭以 P 为界。

证明全是沿 Def 2.10／2.13 各函数的定义展开：`x + y` 是 x 的一个前缀接上 y 的分量；`x̃`、`x^{−Fi}`、`x⁺` 沿首分量／max 下降。递归用 `size` 上的良基归纳（`Ω z`、`z + 1` 这类不是子项，结构递归不便）。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

open import OCF.Align.EboLean.OT.WO.Facts

module OCF.Align.EboLean.OT.WO.Closed2 (F : OTFacts) where

open OTFacts F

open import OCF.Align.EboLean.OT.Syntax
open import OCF.Align.EboLean.OT.Order
open import OCF.Align.EboLean.OT.Closure
open import OCF.Align.EboLean.OT.Arith
open import OCF.Align.EboLean.OT.BoolLemmas
open import OCF.Align.EboLean.OT.OTLemmas
open import OCF.Align.EboLean.OT.WO.K
open import OCF.Align.EboLean.OT.WO.Base
open import OCF.Align.EboLean.OT.WO.OrderLemmas F
open import OCF.Align.EboLean.OT.WO.Closed F

open import Level using (Level; _⊔_)
open import Data.Bool.Base using (Bool; true; false; _∧_; if_then_else_)
open import Data.Nat.Base using (ℕ; suc; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-trans; m≤m+n; m≤n+m; n≤1+n; m<m+n; +-monoʳ-≤)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

private variable
  ℓ ℓ′ : Level
  A B : Pred ℓ
```

## 0. 工具

size 归纳、`if` 的消去、「p 是 t 的分量」、和的前缀／后缀。

```agda
sizeRec : ∀ {ℓ} (Q : Tm → Set ℓ) → (∀ x → (∀ y → size y < size x → Q y) → Q x) → ∀ x → Q x
sizeRec Q step x = go x (<-wellFounded (size x))
  where
    go : ∀ x → Acc _<_ (size x) → Q x
    go x (acc rs) = step x (λ y y<x → go y (rs y<x))

A-if : (A : Pred ℓ) (b : Bool) {x y : Tm} → (b ≡ true → A x) → (b ≡ false → A y) → A (if b then x else y)
A-if A true  f g = f refl
A-if A false f g = g refl

data Comp (p : PTm) : Tm → Set where
  here  : ∀ {a} → Comp p (a ▹ p)
  there : ∀ {a q} → Comp p a → Comp p (a ▹ q)

Comp-app : ∀ {p} y z → Comp p (app y z) → Comp p y ⊎ Comp p z
Comp-app y zer     c         = inj₁ c
Comp-app y (z ▹ q) here      = inj₂ here
Comp-app y (z ▹ q) (there c) with Comp-app y z c
... | inj₁ d = inj₁ d
... | inj₂ d = inj₂ (there d)

Comp-app⁺ : ∀ {p} y z → Comp p z → Comp p (app y z)
Comp-app⁺ y (a ▹ q) here      = here
Comp-app⁺ y (a ▹ q) (there c) = there (Comp-app⁺ y a c)



OT-▹⁻ᵃ : ∀ {a q} → OT (a ▹ q) → OT a × OT ⟨ q ⟩          -- a 可为 0
OT-▹⁻ᵃ {a = zer}   o = OT-0 , o
OT-▹⁻ᵃ {a = _ ▹ _} o = OT-▹⁻ tt o

OT-prefixes : ∀ {y} z → OT (app y z) → OT y
OT-prefixes zer     o = o
OT-prefixes (z ▹ q) o = OT-prefixes z (proj₁ (OT-▹⁻ᵃ o))

OT-suffix : ∀ {y} z → NZ y → OT (app y z) → OT z
OT-suffix zer            nz o = OT-0
OT-suffix (zer ▹ q)      nz o = proj₂ (OT-▹⁻ nz o)
OT-suffix {y} (z ▹ r ▹ q) nz o =
  OT-▹⁺ tt (OT-suffix (z ▹ r) nz (proj₁ (OT-+⁻ o))) (proj₁ (proj₂ (OT-+⁻ o)))
           (le≡ (proj₂ (proj₂ (OT-+⁻ o))))

app-zer : ∀ z → app zer z ≡ z
app-zer zer     = refl
app-zer (z ▹ q) = cong (_▹ q) (app-zer z)

OT-suffixᵃ : ∀ y z → OT (app y z) → OT z               -- y 可为 0
OT-suffixᵃ zer     z o = subst OT (app-zer z) o
OT-suffixᵃ (_ ▹ _) z o = OT-suffix z tt o

OT-one : OT one
OT-one = ot! refl

Ω-OT : ∀ {z} → OT z → OT (Ω z)
Ω-OT {z} oz with Ω-view z
... | Ω-0 _ e        = subst OT (sym e) OT-0
... | Ω-Fi _ e       = subst OT (sym e) oz
... | Ω-Om e₀ e₁ e   = subst OT (sym e) (OT-Ω⁺ oz e₁ e₀)

-- x + 1 = x ▹ φ′_0 0（x ≠ 0）：1 是最小的非零项，dropLt 不去掉任何分量
lt-one-false : ∀ {p} → OT ⟨ p ⟩ → lt ⟨ p ⟩ one ≡ false
lt-one-false {p} o with lt ⟨ p ⟩ one in e
... | false = refl
... | true  = ⊥-elim (≺⇒¬⪯ (lt! e) (one⪯P o))

+one : ∀ x → NZ x → OT x → x + one ≡ x ▹ phi zer zer
+one (a ▹ p) _ o = cong (λ d → app d one) (if-false (lt-one-false (proj₂ (OT-▹⁻ᵃ o))))

isFiT-▹1 : ∀ b → NZ b → isFiT (b ▹ phi zer zer) ≡ false
isFiT-▹1 (_ ▹ _) _ = refl

```

size 的几条不等式（sizeRec 用）：

```agda
size-ψΩz : ∀ z p c → size z < size ⟨ psi (ΩR (z ▹ p)) c ⟩
size-ψΩz z p c = s≤s (≤-trans (m≤m+n (size z) (sizeP p))
                       (≤-trans (n≤1+n _) (≤-trans (n≤1+n _) (m≤m+n _ (size c)))))
```

## 1. 记录（Def 4.14 (b)(d)）

```agda
record DC (A : Pred ℓ) : Set ℓ where             -- 向下封闭
  field
    wdc      : WDC A
    dc-split : ∀ {y z} → NZ y → NZ z → OT (app y z) → A (app y z) → A y × A z
    dc-tilde : ∀ {x} → OT x → A x → A (tilde x)
    dc-mFi   : ∀ {x} → OT x → A x → A (mFi x)
    dc-mI    : ∀ {x} → OT x → A x → A (mI x)
    dc-κ⁻    : ∀ {κ} → isRR κ ≡ true → OT (regTm κ) → A (regTm κ) → A (κ⁻ κ)
open DC public

record UC (A : Pred ℓ) (P : Pred ℓ′) : Set (ℓ ⊔ ℓ′) where   -- 向上封闭，以 P 为界
  field
    wuc     : WUC A P
    uc-app  : ∀ {y z} → NZ z → OT (app y z) → P (app y z) → A y → A z → A (app y z)
    uc-+    : ∀ {x y} → OT x → OT y → OT (x + y) → P (x + y) → A x → A y → A (x + y)
    uc-φ    : ∀ {x y} → OT x → OT y → OT (φ x y) → P (φ x y) → A x → A y → A (φ x y)
    uc-Ω    : ∀ {x} → OT x → OT (Ω x) → P (Ω x) → A x → A (Ω x)
    uc-plus : ∀ {x} → OT x → OT (plus x) → P (plus x) → A x → A (plus x)
open UC public
```

## 2. Remark 4.15

```agda
module Rem4-15 {A : Pred ℓ} {P : Pred ℓ′} (w : WDC A) (u : WUC A P)
               (mono : Mono P) (bd : ∀ {x} → A x → P x) where

  -- 前缀、末分量、任一分量
  prefixA : ∀ {a p} → OT (a ▹ p) → A (a ▹ p) → A a
  prefixA {a = zer}   o ax = wuc-0 u (mono (0⪯ _) (bd ax))
  prefixA {a = _ ▹ _} o ax = proj₁ (wdc-+ w tt o ax)

  lastA : ∀ {a p} → OT (a ▹ p) → A (a ▹ p) → A ⟨ p ⟩
  lastA {a = zer}   o ax = ax
  lastA {a = _ ▹ _} o ax = proj₂ (wdc-+ w tt o ax)

  compA : ∀ {t p} → OT t → A t → Comp p t → A ⟨ p ⟩
  compA o at here      = lastA o at
  compA o at (there c) = compA (proj₁ (OT-▹⁻ᵃ o)) (prefixA o at) c

  -- 由全部分量搭回 t
  buildA : ∀ t → OT t → P t → (∀ {p} → Comp p t → A ⟨ p ⟩) → A t
  buildA zer         o pt f = wuc-0 u pt
  buildA (zer ▹ p)   o pt f = f here
  buildA (a ▹ q ▹ p) o pt f =
    wuc-+ u tt o pt (buildA (a ▹ q) (proj₁ (OT-▹⁻ tt o)) (mono (⪯-+ˡ o) pt) (λ c → f (there c)))
                    (f here)

  prefixesA : ∀ {y} z → OT (app y z) → A (app y z) → A y
  prefixesA zer     o ay = ay
  prefixesA (z ▹ q) o ax = prefixesA z (proj₁ (OT-▹⁻ᵃ o)) (prefixA o ax)

  A-one : ∀ {t} → P t → one ⪯ t → A one
  A-one pt p = wuc-φ u OT-one (mono p pt) a0 a0
    where a0 = wuc-0 u (mono (⪯-trans (0⪯ one) p) pt)

  -- (1) 任意拆分
  dc-split′ : ∀ {y z} → NZ y → NZ z → OT (app y z) → A (app y z) → A y × A z
  dc-split′ {y} {z} nzy nzz o ax =
    prefixesA z o ax
    , buildA z (OT-suffix z nzy o) (mono (⪯-app nzy nzz o) (bd ax))
              (λ c → compA o ax (Comp-app⁺ y z c))

  -- (6′) =NF y + z
  uc-app′ : ∀ {y z} → NZ z → OT (app y z) → P (app y z) → A y → A z → A (app y z)
  uc-app′ {y} {z} nzz o pt ay az =
    buildA (app y z) o pt (λ c → sel (Comp-app y z c))
    where
      sel : ∀ {p} → Comp p y ⊎ Comp p z → A ⟨ p ⟩
      sel (inj₁ c) = compA (OT-prefixes z o) ay c
      sel (inj₂ c) = compA (OT-suffixᵃ y z o) az c
```

`x + y`：`x + zer = x`，否则 `app (dropLt x (hd y)) y`，而 `dropLt x q` 是 x 的前缀。

```agda
  dropLt-prefix : ∀ x q → OT x → A x → A (dropLt x q) × OT (dropLt x q)
  dropLt-prefix zer     q o ax = ax , o
  dropLt-prefix (a ▹ p) q o ax = go (lt ⟨ p ⟩ ⟨ q ⟩)
    where
      go : ∀ b → A (if b then dropLt a q else a ▹ p) × OT (if b then dropLt a q else a ▹ p)
      go true  = dropLt-prefix a q (proj₁ (OT-▹⁻ᵃ o)) (prefixA o ax)
      go false = ax , o

  uc-+′ : ∀ {x y} → OT x → OT y → OT (x + y) → P (x + y) → A x → A y → A (x + y)
  uc-+′ {x} {y = zer}   ox oy o pt ax ay = ax
  uc-+′ {x} {y = y ▹ q} ox oy o pt ax ay =
    uc-app′ tt o pt (proj₁ (dropLt-prefix x (hd (y ▹ q)) ox ax)) ay
```

`φ x y`、`Ω x`：

```agda
  uc-φ′ : ∀ {x y} → OT x → OT y → OT (φ x y) → P (φ x y) → A x → A y → A (φ x y)
  uc-φ′ {x} {y} ox oy o pt ax ay =
    A-if A (inCr x y) (λ _ → ay) (λ e₁ → A-if A (isZero y ∧ isGT x) (λ _ → ax) (λ e₂ →
      let eq : φ x y ≡ ⟨ phi x y ⟩
          eq = trans (if-false e₁) (if-false e₂)
      in wuc-φ u (subst OT eq o) (subst P eq pt) ax ay))

  uc-Ω′ : ∀ {x} → OT x → OT (Ω x) → P (Ω x) → A x → A (Ω x)
  uc-Ω′ {x} ox o pt ax with Ω-view x
  ... | Ω-0 _ e      = subst A (sym e) (wuc-0 u (subst P e pt))
  ... | Ω-Fi _ e     = subst A (sym e) ax
  ... | Ω-Om e₀ e₁ e = subst A (sym e) (wuc-Ω u (subst OT e o) (subst P e pt) ax)
```

`x̃`、`x^{−Fi}`、`x^{−I}`、`κ⁻`：

```agda
  dc-tilde′ : ∀ x → OT x → A x → A (tilde x)
  dc-tilde′ = sizeRec (λ x → OT x → A x → A (tilde x)) step
    where
      step : ∀ x → (∀ y → size y < size x → OT y → A y → A (tilde y)) → OT x → A x → A (tilde x)
      step zer                    ih o ax = ax
      step (zer ▹ phi b c)        ih o ax =
        let (ob , oc , _) = OT-φ⁻ o
            (ab , ac)     = wdc-φ w o ax
        in A-if A (lt b c) (λ _ → ih c (size-φʳ b c) oc ac) (λ _ → ih b (size-φˡ b c) ob ab)
      step (zer ▹ psi (ΩR b) c)   ih o ax = wdc-ψ w o ax
      step (zer ▹ psi IR c)       ih o ax = ax
      step (zer ▹ Om b)           ih o ax = ax
      step (zer ▹ I)              ih o ax = ax
      step (a ▹ q ▹ p)            ih o ax =
        ih (a ▹ q) (size-▹ˡ (a ▹ q) p) (proj₁ (OT-+⁻ o)) (proj₁ (wdc-+ w tt o ax))

  -- 由 A (Ω z) 得 A z（z ≠ 0）
  A-Ω⁻ : ∀ {z} → NZ z → OT z → A (Ω z) → A z
  A-Ω⁻ {z} nz oz aΩ with Ω-view z
  ... | Ω-0 e₀ _     = ⊥-elim (nz-zero nz e₀)
    where
      nz-zero : ∀ {z} → NZ z → isZero z ≡ true → ⊥
      nz-zero {z = _ ▹ _} _ ()
  ... | Ω-Fi _ e     = subst A e aΩ
  ... | Ω-Om e₀ e₁ e = wdc-Ω w (OT-Ω⁺ oz e₁ e₀) (subst A e aΩ)

  dc-mFi′ : ∀ x → OT x → A x → A (mFi x)
  dc-mFi′ = sizeRec (λ x → OT x → A x → A (mFi x)) step
    where
      step : ∀ x → (∀ y → size y < size x → OT y → A y → A (mFi y)) → OT x → A x → A (mFi x)
      step zer                    ih o ax = ax
      step (zer ▹ phi b c)        ih o ax =
        let (ob , oc , _) = OT-φ⁻ o
            (ab , ac)     = wdc-φ w o ax
        in A-if A (lt b c) (λ _ → ih c (size-φʳ b c) oc ac) (λ _ → ih b (size-φˡ b c) ob ab)
      step (zer ▹ psi (ΩR b) c)   ih o ax with regView (ΩR b) (proj₁ (proj₂ (proj₂ (OT-ψ⁻ o))))
      ... | succ zer       = wuc-0 u (mono (0⪯ _) (bd ax))
      ... | succ (z ▹ r)   =
        let oz = proj₁ (OT-▹⁻ tt (proj₁ (OT-Ω⁻ (proj₁ (proj₂ (OT-ψ⁻ o))))))
        in ih (z ▹ r) (size-ψΩz (z ▹ r) (phi zer zer) c) oz (A-Ω⁻ tt oz (wdc-ψ w o ax))
      step (zer ▹ psi IR c)       ih o ax = ax
      step (zer ▹ Om b)           ih o ax =
        ih b (size-Ω b) (proj₁ (OT-Ω⁻ o)) (wdc-Ω w o ax)
      step (zer ▹ I)              ih o ax = ax
      step (a ▹ q ▹ p)            ih o ax =
        ih (a ▹ q) (size-▹ˡ (a ▹ q) p) (proj₁ (OT-+⁻ o)) (proj₁ (wdc-+ w tt o ax))

  dc-mI′ : ∀ {x} → OT x → A x → A (mI x)
  dc-mI′ {x} ox ax =
    A-if A (lt x I′) {x = zer} {y = I′}
         (λ _ → wuc-0 u (mono (0⪯ x) (bd ax)))
         (λ e → wuc-I u (mono (¬≺⇒⪰ (λ (lt! q) → true≢false (trans (sym q) e))) (bd ax)))

  dc-κ⁻′ : ∀ {κ} → isRR κ ≡ true → OT (regTm κ) → A (regTm κ) → A (κ⁻ κ)
  dc-κ⁻′ {κ} rκ o ax with regView κ rκ
  ... | inacc          = wuc-0 u (mono (0⪯ _) (bd ax))
  ... | succ zer       = wuc-0 u (mono (0⪯ _) (bd ax))
  ... | succ (z ▹ r)   = goΩ (Ω-view (z ▹ r))
    where
      oz1 : OT (z ▹ r ▹ phi zer zer)
      oz1 = proj₁ (OT-Ω⁻ o)
      az : A (z ▹ r)
      az = proj₁ (wdc-+ w tt oz1 (wdc-Ω w o ax))
      Ωz≺κ : Ω (z ▹ r) ≺ ⟨ Om (z ▹ r ▹ phi zer zer) ⟩
      Ωz≺κ = κ⁻≺κ rκ o
      goΩ : ΩView (z ▹ r) → A (Ω (z ▹ r))
      goΩ (Ω-0 () _)
      goΩ (Ω-Fi _ e)     = subst A (sym e) az
      goΩ (Ω-Om e₀ e₁ e) =
        subst A (sym e)
          (wuc-Ω u (OT-Ω⁺ (proj₁ (OT-▹⁻ tt oz1)) e₁ e₀)
                   (mono (≺⇒⪯ (subst (λ t → t ≺ ⟨ Om (z ▹ r ▹ phi zer zer) ⟩) e Ωz≺κ)) (bd ax)) az)
```

`x⁺`：沿 `plus` 的定义；ψ_{Ω_{z+1}} c 处 `x⁺ = Ω_{z+1}`，由 `κ⁻ = Ω_z ∈ A` 得 z ∈ A，z + 1 ∈ A，Ω_{z+1} ∈ A。

```agda
  -- A (x ▹ 1) 与 A (Ω (x ▹ 1))，x ≠ 0
  A-▹1 : ∀ {x} → NZ x → OT (x ▹ phi zer zer) → P (x ▹ phi zer zer) → A x → A (x ▹ phi zer zer)
  A-▹1 nz o pt ax = wuc-+ u nz o pt ax (A-one pt (⪯-+ʳ′ nz o))
    where
      ⪯-+ʳ′ : ∀ {x} → NZ x → OT (x ▹ phi zer zer) → one ⪯ (x ▹ phi zer zer)
      ⪯-+ʳ′ {x = a ▹ q} _ o′ = ⪯-+ʳ o′

  A-Ω▹1 : ∀ {x} → NZ x → OT (Ω (x ▹ phi zer zer)) → P (Ω (x ▹ phi zer zer)) → A x
        → A (Ω (x ▹ phi zer zer))
  A-Ω▹1 {x} nz o pt ax with Ω-view (x ▹ phi zer zer)
  ... | Ω-0 () _
  ... | Ω-Fi e₁ _  = ⊥-elim (true≢false (trans (sym e₁) (isFiT-▹1 x nz)))
  ... | Ω-Om e₀ e₁ e =
    subst A (sym e)
      (wuc-Ω u (subst OT e o) (subst P e pt)
        (A-▹1 nz (proj₁ (OT-Ω⁻ (subst OT e o))) (mono (≺⇒⪯ (≺-Ω (subst OT e o))) (subst P e pt)) ax))

  uc-plus′ : ∀ x → OT x → OT (plus x) → P (plus x) → A x → A (plus x)
  uc-plus′ = sizeRec (λ x → OT x → OT (plus x) → P (plus x) → A x → A (plus x)) step
    where
      step : ∀ x → (∀ y → size y < size x → OT y → OT (plus y) → P (plus y) → A y → A (plus y))
           → OT x → OT (plus x) → P (plus x) → A x → A (plus x)
      step zer ih o o′ pt ax = wuc-Ω u o′ pt (A-one pt (≺⇒⪯ (≺-Ω o′)))
      step (zer ▹ phi b c) ih o o′ pt ax =
        let (ob , oc , _) = OT-φ⁻ o
            (ab , ac)     = wdc-φ w o ax
        in A-if A (lt b c) {x = plus c} {y = plus b}
                (λ e → ih c (size-φʳ b c) oc (subst OT (if-true e) o′) (subst P (if-true e) pt) ac)
                (λ e → ih b (size-φˡ b c) ob (subst OT (if-false e) o′) (subst P (if-false e) pt) ab)
      step (zer ▹ psi (ΩR b) c) ih o o′ pt ax with regView (ΩR b) (proj₁ (proj₂ (proj₂ (OT-ψ⁻ o))))
      ... | succ zer     = wuc-Ω u o′ pt (A-one pt (≺⇒⪯ (≺-Ω o′)))
      ... | succ (z ▹ r) =
        let oz1 = proj₁ (OT-Ω⁻ o′)
            oz  = proj₁ (OT-▹⁻ tt oz1)
            az  = A-Ω⁻ tt oz (wdc-ψ w o ax)
        in wuc-Ω u o′ pt (A-▹1 tt oz1 (mono (≺⇒⪯ (≺-Ω o′)) pt) az)
      step (zer ▹ psi IR c) ih o o′ pt ax =
        subst (λ t → A (Ω t)) (sym eq) (A-Ω▹1 tt (subst (λ t → OT (Ω t)) eq o′) (subst (λ t → P (Ω t)) eq pt) ax)
        where
          eq : ⟨ psi IR c ⟩ + one ≡ ⟨ psi IR c ⟩ ▹ phi zer zer
          eq = +one _ tt o
      step (zer ▹ Om b) ih o o′ pt ax =
        subst (λ t → A (Ω t)) (sym eq) (A-Ω▹1 nzb (subst (λ t → OT (Ω t)) eq o′) (subst (λ t → P (Ω t)) eq pt) (wdc-Ω w o ax))
        where
          nzb : NZ b
          nzb = nz-of (proj₂ (proj₂ (OT-Ω⁻ o)))
            where
              nz-of : ∀ {b} → isZero b ≡ false → NZ b
              nz-of {b = _ ▹ _} _ = tt
          eq : b + one ≡ b ▹ phi zer zer
          eq = +one b nzb (proj₁ (OT-Ω⁻ o))
      step (zer ▹ I) ih o o′ pt ax =
        subst (λ t → A (Ω t)) (sym eq) (A-Ω▹1 tt (subst (λ t → OT (Ω t)) eq o′) (subst (λ t → P (Ω t)) eq pt) ax)
        where
          eq : I′ + one ≡ I′ ▹ phi zer zer
          eq = +one I′ tt OT-I
      step (a ▹ q ▹ p) ih o o′ pt ax =
        ih (a ▹ q) (size-▹ˡ (a ▹ q) p) (proj₁ (OT-+⁻ o)) o′ pt (proj₁ (wdc-+ w tt o ax))

  DC′ : DC A
  DC′ = record { wdc = w ; dc-split = dc-split′ ; dc-tilde = λ {x} → dc-tilde′ x
               ; dc-mFi = λ {x} → dc-mFi′ x ; dc-mI = dc-mI′ ; dc-κ⁻ = dc-κ⁻′ }

  UC′ : UC A P
  UC′ = record { wuc = u ; uc-app = uc-app′ ; uc-+ = uc-+′ ; uc-φ = uc-φ′ ; uc-Ω = uc-Ω′
               ; uc-plus = λ {x} → uc-plus′ x }
```

## 3. 推论：C^c(A) 向下、向上封闭（Lemma 4.16 (a) 的完整形式）

```agda
C-DC : ∀ {c} → WDC (A ∩ ↓ c) → DC (C c A)
C-DC w = Rem4-15.DC′ (C-WDC w) C-WUC (λ _ _ → tt) (λ _ → tt)

C-UC : ∀ {c} → WDC (A ∩ ↓ c) → UC (C c A) Unb
C-UC w = Rem4-15.UC′ (C-WDC w) C-WUC (λ _ _ → tt) (λ _ → tt)
```
