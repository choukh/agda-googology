# YiLvNeg 第 3 项：合法性作数据时，输出依赖证书

**判决：编译定理。** 同一个层号的两份合法性证书让 `YiLvIf.compare` 交出不同的槽位 (`compare-reads-certificate`)；
位置保持若按 "两份独立证书" 陈述，就推出换证书输出相等 (`coherence`)、极限行的两个输出函数字面相等
(`lim-function-equality-required`)、保留结点的槽位与证书无关 (`slot-coherence`)，因而槽位取自 `compare` 的写法不可满足 (`no-by-compare`)。
不否定：证书相关的折叠本身；槽位取规范位置的写法 ([YiLvNegCanon](YiLvNegCanon.lagda.md))；按限制形式陈述的位置保持 ([YiLvNegRestrict](YiLvNegRestrict.lagda.md))。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiLvNegCert where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck
open import OCF.Align.YiIrrIf
open import OCF.Align.YiLvIf
```

## 1 两份证书，两个槽位

坐标 `κ = lim (1, suc ω′, suc ω′, …)`，`ω′ = lim (1, 1, …)`。第 0 步 `1 ⊲ suc ω′` 可以在 `ω′` 里选任何一项，
所以 `κ` 有两份合法性证明，读回后是层号 `read0 κ` 的两份 `Legal`。`κ` 带着其中任一份都是 `tw 3` 的带守卫坐标，
两份证书都是闭的，对象在读回域内。

```agda
ω′ : R
ω′ = G.lim (λ _ → one)

colᶜ : ℕ → R
colᶜ zero = one
colᶜ (suc n) = G.suc ω′

κ : R
κ = G.lim colᶜ

κ-lgl : ℕ → Lgl zero κ
κ-lgl j = step , lawful
  where
  step : ∀ n → Cp zero (colᶜ n) (colᶜ (suc n))
  step zero = inj₂ (inj₂ (j , inj₁ refl))
  step (suc n) = inj₁ refl
  lawful : ∀ n → Lgl zero (colᶜ n)
  lawful zero = tt
  lawful (suc n) = (λ _ → inj₁ refl) , (λ _ → tt)

κ-guard : ℕ → Gd zero raw1 κ
κ-guard j = inj₂ (zero , inj₁ refl) , κ-lgl j , raw0-Nested κ

Kᶜ : LF
Kᶜ = read0 κ

Kᶜ-plain : Plain Kᶜ
Kᶜ-plain = up0-plain κ (raw0-Nested κ)

Kᶜ-legal : ℕ → Legal Kᶜ
Kᶜ-legal j = read0-legal κ (κ-lgl j)

-- 第 1 支的根 (层号 read0 ω′) 与第 0 支的根 (层号 zero).
hiᶜ loᶜ : Pre Kᶜ
hiᶜ = 1 , inj₁ tt
loᶜ = 0 , inj₁ tt

Bᶜ : LF
Bᶜ = lev Kᶜ hiᶜ

index : Tri Bᶜ zero → ℕ
index (below (m , r) e) = m
index (above s e) = zero
index (same e) = zero

compare₀ : compare Kᶜ Kᶜ-plain (Kᶜ-legal 0) hiᶜ loᶜ ≡ below (0 , inj₁ tt) refl
compare₀ = refl

compare₁ : compare Kᶜ Kᶜ-plain (Kᶜ-legal 1) hiᶜ loᶜ ≡ below (1 , inj₁ tt) refl
compare₁ = refl

zero≢one : _≡_ {A = ℕ} 0 1 → ⊥
zero≢one ()

compare-reads-certificate :
  compare Kᶜ Kᶜ-plain (Kᶜ-legal 0) hiᶜ loᶜ ≡ compare Kᶜ Kᶜ-plain (Kᶜ-legal 1) hiᶜ loᶜ → ⊥
compare-reads-certificate e = zero≢one (cong index e)
```

## 2 `Raw m` 的第一位置无环 (`m` 是 `Plain` 的)

对层号与值的字典序递归；`em`、`top` 之下的位置落在更低的层号里。不比较两个值，不用传递性。

```agda
data DAcc (y : LF) (d : Raw y) : Set where
  dacc : (∀ a → Dn y a d → DAcc y a) → DAcc y d

cp-dacc : ∀ {y a d} → DAcc y d → Cp y a d → DAcc y a
cp-dacc w (inj₁ refl) = w
cp-dacc (dacc h) (inj₂ p) = h _ p

em-suc : ∀ k T → DAcc k T → DAcc (suc k) (G.em tt T)
em-suc k T (dacc h) = dacc λ
  { G.zero () ; (G.suc _) () ; (G.lim _) () ; (G.lc _ _ _ _) () ; G.top ()
  ; (G.em _ a) p → em-suc k a (h a p) }

em-lim : ∀ (f : ℕ → LF) n T → DAcc (f n) T → DAcc (lim f) (G.em n T)
em-lim f n T (dacc h) = dacc λ
  { G.zero () ; (G.suc _) () ; (G.lim _) () ; (G.lc _ _ _ _) () ; G.top ()
  ; (G.em _ a) (refl , p) → em-lim f n a (h a p) }

dn-acc : ∀ y → Plain y → (d : Raw y) → DAcc y d
dn-acc y pl G.zero = dacc (λ a ())
dn-acc y pl (G.suc d) = dacc (λ a p → cp-dacc (dn-acc y pl d) p)
dn-acc y pl (G.lim f) = dacc (λ { a (n , p) → cp-dacc (dn-acc y pl (f n)) p })
dn-acc y pl (G.lc r c t g) = dacc (λ a p → cp-dacc (dn-acc y pl t) p)
dn-acc (suc k) pl (G.em _ T) = em-suc k T (dn-acc k pl T)
dn-acc (lim f) pl (G.em n T) = em-lim f n T (dn-acc (f n) (pl n) T)
dn-acc zero pl G.top = dacc (λ a ())
dn-acc (suc k) pl G.top = dacc λ
  { G.zero () ; (G.suc _) () ; (G.lim _) () ; (G.lc _ _ _ _) () ; G.top ()
  ; (G.em _ a) p → em-suc k a (dn-acc k pl a) }
dn-acc (lim f) pl G.top = dacc (λ a ())

dn-asym : ∀ {y a d} → DAcc y d → Dn y a d → Dn y d a → ⊥
dn-asym (dacc h) p q = dn-asym (h _ p) q p

antisym : ∀ y → Plain y → ∀ {a d : Raw y} → Cp y a d → Cp y d a → a ≡ d
antisym y pl (inj₁ e) q = e
antisym y pl (inj₂ p) (inj₁ e) = sym e
antisym y pl {d = d} (inj₂ p) (inj₂ q) = ⊥-elim (dn-asym (dn-acc y pl d) p q)
```

## 3 位置保持带两份独立证书：最小记录

`Cert m x` 是相关的证书。`position` 照 `FoldRows.position` 的写法，`dx`、`dy` 各自任意。
记录有平凡的实例 (`trivial`)，所以下面的推论不是空真。

```agda
record CertRows : Set₁ where
  field
    Cert : (m x : LF) → Set
    ψ : (m x : LF) → Cert m x → Raw m
    position : ∀ m x y (dx : Cert m x) (dy : Cert m y) → CP x y →
      Cp m (ψ m x dx) (ψ m y dy)

trivial : CertRows
trivial = record
  { Cert = λ m x → ⊤ ; ψ = λ m x d → G.zero ; position = λ m x y dx dy p → inj₁ refl }

module Forced (F : CertRows) where
  open CertRows F

  -- 换证书, 输出相等.
  coherence : ∀ m → Plain m → ∀ x (d d′ : Cert m x) → ψ m x d ≡ ψ m x d′
  coherence m pl x d d′ =
    antisym m pl (position m x x d d′ self) (position m x x d′ d self)

  slot-or : ∀ {m} → Pre m → Raw m → Pre m
  slot-or r (G.lc s c t g) = s
  slot-or r _ = r

  -- 保留结点的槽位与证书无关.
  slot-coherence : ∀ m → Plain m → ∀ x (d d′ : Cert m x) s c t g s′ c′ t′ g′ →
    ψ m x d ≡ G.lc s c t g → ψ m x d′ ≡ G.lc s′ c′ t′ g′ → s ≡ s′
  slot-coherence m pl x d d′ s c t g s′ c′ t′ g′ e e′ =
    cong (slot-or s) (trans (sym e) (trans (coherence m pl x d d′) e′))

  -- 极限逐项的折叠: 两族各自任意的证书给出的两个输出函数字面相等.
  module LimRow
    (cert-at : ∀ m f → Cert m (lim f) → ∀ n → Cert m (f n))
    (lim-row : ∀ m f (d : Cert m (lim f)) →
      ψ m (lim f) d ≡ G.lim (λ n → ψ m (f n) (cert-at m f d n))) where

    lim-body : ∀ {m} → Raw m → ℕ → Raw m
    lim-body (G.lim f) = f
    lim-body _ = λ n → G.zero

    lim-function-equality-required : ∀ m → Plain m → ∀ f (d d′ : Cert m (lim f)) →
      (λ n → ψ m (f n) (cert-at m f d n)) ≡ (λ n → ψ m (f n) (cert-at m f d′ n))
    lim-function-equality-required m pl f d d′ = cong lim-body
      (trans (sym (lim-row m f d)) (trans (coherence m pl (lim f) d d′) (lim-row m f d′)))
```

`lim-function-equality-required` 是函数相等。证书无关时它是 `refl` (`RR5IrrCheck.CertIrr`)；证书相关并且真的被读时，
逐点相等拼不成它，要函数外延。本篇没有证明它不可得。

## 4 槽位取自 `compare` 的写法

`ByCompare`：层号 `Kᶜ` 的每份合法性给出把 `tw 2` (层号 0 的结点) 折到目标层 `Bᶜ` 的证书，
输出的槽位就是 `compare` 交出的那个。只对这一个实例要求 (比对一切层号要求弱)。

```agda
record ByCompare (F : CertRows) : Set where
  open CertRows F
  field
    cert : Legal Kᶜ → Cert Bᶜ (tw 2)
    keep : ∀ (L : Legal Kᶜ) (s : Pre Bᶜ) (e : lev Bᶜ s ≡ zero) →
      compare Kᶜ Kᶜ-plain L hiᶜ loᶜ ≡ below s e →
      Σ (Low Bᶜ s) λ c → Σ (Raw Bᶜ) λ t →
      Σ ((η : Low Bᶜ s) → .(GdL Bᶜ s c η) → Raw Bᶜ) λ g →
      ψ Bᶜ (tw 2) (cert L) ≡ G.lc s c t g

Bᶜ-plain : Plain Bᶜ
Bᶜ-plain = lev-plain Kᶜ Kᶜ-plain hiᶜ

no-by-compare : (F : CertRows) → ByCompare F → ⊥
no-by-compare F B with keep (Kᶜ-legal 0) (0 , inj₁ tt) refl compare₀
                     | keep (Kᶜ-legal 1) (1 , inj₁ tt) refl compare₁
  where open ByCompare B
... | c , t , g , e | c′ , t′ , g′ , e′ =
  zero≢one (cong proj₁ (Forced.slot-coherence F Bᶜ Bᶜ-plain (tw 2)
    (ByCompare.cert B (Kᶜ-legal 0)) (ByCompare.cert B (Kᶜ-legal 1))
    (0 , inj₁ tt) c t g (1 , inj₁ tt) c′ t′ g′ e e′))
```
