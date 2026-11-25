# YiBtVal 层号类：一个合法层号的字面子项

**验收文件，档位：编译定理 (实例)。** 给定 `Plain` 且 `Legal` 的 `K₀`，层号类取 `K₀` 的字面子项 (`CP x K₀`)。`adm-sep` 不要函数外延：
合法层号的子项两两可比 (`chainCP`)，真子项与自身不结构对应 (`strict`，归结为 `Ordᴵ` 上的 `noSelf`)。另给有限层号与 ω+n 的对应 (`natC`, `ωC`) 与一般的参照层号 `toIL`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiBtValAdm where

open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans)
import OCF.Align.RR5IrrCore as B
open B using (LF)
open import OCF.Align.YiIrrIf using (CP; self; fst; Legal; CP-tr) renaming (suc to cpS; lim to cpL)
open import OCF.Align.YiLvIf using (Plain; lev)
open import OCF.Align.YiLvFoldFin using (fin)
open import OCF.Align.YiRawFoldBase using (plainR)
open import OCF.Align.YiRawFoldInst using (ω+)
open import OCF.Align.YiLvNegCompare using (At)
open import OCF.Align.YiBtValRel using (Corr; cz; cs; cl; Corr-uniq; posCorr)
open import OCF.Align.YiBtValFold using (AdmI; module FoldA)
import OCF.Align.Level as L
open L using (_≅ᴵ_; _<ᴵ_; _⊑ᴵ_)
```

## 1 `Ordᴵ` 上的真子项不与自身结构对应

```agda
data SubI : L.Ordᴵ → L.Ordᴵ → Set where
  si-refl : ∀ {a} → SubI a a
  si-suc : ∀ {a b} → SubI a b → SubI a (L.suc b)
  si-lim : ∀ {a g s} n → SubI a (g n) → SubI a (L.lim g s)

data SubP : L.Ordᴵ → L.Ordᴵ → Set where
  ps : ∀ {a b} → SubI a b → SubP a (L.suc b)
  pl : ∀ {a g s} n → SubI a (g n) → SubP a (L.lim g s)

P→I : ∀ {a b} → SubP a b → SubI a b
P→I (ps p) = si-suc p
P→I (pl n p) = si-lim n p

subSuc : ∀ {a b} → SubI (L.suc a) b → SubP a b
subSuc si-refl = ps si-refl
subSuc (si-suc p) = ps (P→I (subSuc p))
subSuc (si-lim n p) = pl n (P→I (subSuc p))

subLim : ∀ {h t b} → SubI (L.lim h t) b → ∀ n → SubP (h n) b
subLim si-refl n = pl n si-refl
subLim (si-suc p) n = ps (P→I (subLim p n))
subLim (si-lim m p) n = pl m (P→I (subLim p n))

noSelf : ∀ b {a} → SubP a b → a ≅ᴵ b → ⊥
noSelf L.zero () e
noSelf (L.suc b) (ps p) (L.s≅ e) = noSelf b (subSuc p) e
noSelf (L.lim g s) (pl n p) (L.l≅ h) = noSelf (g n) (subLim p n) (h n)
```

## 2 `LF` 上的严格子项

```agda
data Up : LF → LF → Set where
  us : ∀ {k} → Up k (B.suc k)
  ul : ∀ {f} n → Up (f n) (B.lim f)

CP⁺ : LF → LF → Set
CP⁺ x y = Σ LF λ z → CP x z × Up z y

CP→Sub : ∀ {x y a b} → CP x y → Corr a x → Corr b y → Σ L.Ordᴵ λ a′ → SubI a′ b × a ≅ᴵ a′
CP→Sub self ca cb = _ , si-refl , Corr-uniq ca cb
CP→Sub (cpS p) ca (cs cb) with CP→Sub p ca cb
... | a′ , q , e = a′ , si-suc q , e
CP→Sub (cpL n p) ca (cl cb) with CP→Sub p ca (cb n)
... | a′ , q , e = a′ , si-lim n q , e
CP→Sub (fst p) ca ()

strict : ∀ {x y a b} → CP⁺ x y → Corr a x → Corr b y → a ≅ᴵ b → ⊥
strict (z , p , us) ca (cs cb) e with CP→Sub p ca cb
... | a′ , q , e′ = noSelf _ (ps q) (L.≅ᴵ-trans (L.≅ᴵ-sym e′) e)
strict (z , p , ul n) ca (cl cb) e with CP→Sub p ca (cb n)
... | a′ , q , e′ = noSelf _ (pl n q) (L.≅ᴵ-trans (L.≅ᴵ-sym e′) e)
```

## 3 合法层号的子项两两可比

```agda
stepsCP : ∀ {f : ℕ → LF} → (∀ n → CP (f n) (f (suc n))) → ∀ d n → CP (f n) (f (d + n))
stepsCP st zero n = self
stepsCP st (suc d) n = CP-tr (stepsCP st d n) (st (d + n))

diff : ∀ n m → (Σ ℕ λ d → m ≡ d + n) ⊎ (Σ ℕ λ d → n ≡ d + m)
diff zero m = inj₁ (m , sym (+-identityʳ m))
diff (suc n) zero = inj₂ (suc n , sym (+-identityʳ (suc n)))
diff (suc n) (suc m) with diff n m
... | inj₁ (d , e) = inj₁ (d , trans (cong suc e) (sym (+-suc d n)))
... | inj₂ (d , e) = inj₂ (d , trans (cong suc e) (sym (+-suc d m)))

chainCP : ∀ K → Plain K → Legal K → ∀ {x y} → CP x K → CP y K → (x ≡ y) ⊎ (CP⁺ x y ⊎ CP⁺ y x)
chainCP K pK lK self self = inj₁ refl
chainCP (B.suc k) pK lK self (cpS q) = inj₂ (inj₂ (k , q , us))
chainCP (B.suc k) pK lK (cpS p) self = inj₂ (inj₁ (k , p , us))
chainCP (B.suc k) pK lK (cpS p) (cpS q) = chainCP k pK lK p q
chainCP (B.lim f) pK lK self (cpL m q) = inj₂ (inj₂ (f m , q , ul m))
chainCP (B.lim f) pK lK (cpL n p) self = inj₂ (inj₁ (f n , p , ul n))
chainCP (B.lim f) pK (st , lg) (cpL n p) (cpL m q) with diff n m
... | inj₁ (d , refl) = chainCP (f (d + n)) (pK (d + n)) (lg (d + n)) (CP-tr p (stepsCP st d n)) q
... | inj₂ (d , refl) = chainCP (f (d + m)) (pK (d + m)) (lg (d + m)) p (CP-tr q (stepsCP st d m))
chainCP (B.lc k c w b t g) () lK p q
```

## 4 层号类

```agda
lev-cp : ∀ K → Plain K → ∀ r → CP (lev K r) K
lev-cp B.zero pK ()
lev-cp (B.suc k) pK (inj₁ _) = cpS self
lev-cp (B.suc k) pK (inj₂ r) = cpS (lev-cp k pK r)
lev-cp (B.lim f) pK (n , r) = cpL n (lev-cp (f n) (pK n) r)
lev-cp (B.lc k c w b t g) () r

zero-cp : ∀ K → Plain K → CP B.zero K
zero-cp B.zero pK = self
zero-cp (B.suc k) pK = cpS (zero-cp k pK)
zero-cp (B.lim f) pK = cpL 0 (zero-cp (f 0) (pK 0))
zero-cp (B.lc k c w b t g) ()

module CPClass (K₀ : LF) (pK₀ : Plain K₀) (lK₀ : Legal K₀) where

  Adm : LF → Set
  Adm x = CP x K₀

  adm-plain : ∀ {K} → Adm K → Plain K
  adm-plain p = plainR K₀ p pK₀

  adm-S : ∀ {k} → Adm (B.suc k) → Adm k
  adm-S p = CP-tr (cpS self) p

  adm-L : ∀ {f} → Adm (B.lim f) → ∀ n → Adm (f n)
  adm-L p n = CP-tr (cpL n self) p

  adm-lev : ∀ {K} → Adm K → ∀ r → Adm (lev K r)
  adm-lev {K} p r = CP-tr (lev-cp K (adm-plain p) r) p

  adm-sep : ∀ {k m j a i} → Adm k → Adm m → Corr j k → j ≅ᴵ a → a <ᴵ i → Corr i m → At m k
  adm-sep {m = m} ak am cj e r ci with posCorr m ci r
  ... | s , ca with chainCP K₀ pK₀ lK₀ ak (adm-lev am s)
  ...   | inj₁ eq = s , sym eq
  ...   | inj₂ (inj₁ sp) = ⊥-elim (strict sp cj ca e)
  ...   | inj₂ (inj₂ sp) = ⊥-elim (strict sp ca cj (L.≅ᴵ-sym e))

  adm0 : Adm B.zero
  adm0 = zero-cp K₀ pK₀

  admI : AdmI
  admI = record
    { Adm = Adm; adm-S = adm-S; adm-L = adm-L; adm-lev = adm-lev
    ; adm-plain = adm-plain; adm-sep = adm-sep }

  open FoldA admI public using (FOLD)
```

## 5 参照层号

`toIL`：一般的 `Plain`, `Legal` 层号上的参照层号，极限的步进由 `CP⊑` 给出。

```agda
natC : ∀ n → Corr (L.natᴵ n) (fin n)
natC zero = cz
natC (suc n) = cs (natC n)

ωp : ℕ → L.Ordᴵ
ωp zero = L.ωᴵ
ωp (suc n) = L.suc (ωp n)

ωC : ∀ n → Corr (ωp n) (ω+ n)
ωC zero = cl natC
ωC (suc n) = cs (ωC n)

≅⊑ : ∀ {a b} → a ≅ᴵ b → a ⊑ᴵ b
≅⊑ L.z≅ = L.z⊑
≅⊑ (L.s≅ e) = L.s⊑ e L.zero
≅⊑ (L.l≅ h) = L.l⊑ (λ n → L.⊑ᴵ-trans (≅⊑ (h n)) (L.Sim→⊑ᴵ (L.lim n)))

CP⊑ : ∀ {x y a b} → CP x y → Corr a x → Corr b y → a ⊑ᴵ b
CP⊑ self ca cb = ≅⊑ (Corr-uniq ca cb)
CP⊑ (cpS p) ca (cs cb) = L.⊑ᴵ-trans (CP⊑ p ca cb) (L.Sim→⊑ᴵ L.suc)
CP⊑ (cpL n p) ca (cl cb) = L.⊑ᴵ-trans (CP⊑ p ca (cb n)) (L.Sim→⊑ᴵ (L.lim n))
CP⊑ (fst p) ca ()

toIL : ∀ K → Plain K → Legal K → L.Ordᴵ
toIL-c : ∀ K (pK : Plain K) (lK : Legal K) → Corr (toIL K pK lK) K
toIL B.zero pK lK = L.zero
toIL (B.suc k) pK lK = L.suc (toIL k pK lK)
toIL (B.lim f) pK (st , lg) = L.lim (λ n → toIL (f n) (pK n) (lg n)) (λ n →
  CP⊑ (st n) (toIL-c (f n) (pK n) (lg n)) (toIL-c (f (suc n)) (pK (suc n)) (lg (suc n))))
toIL (B.lc k c w b t g) () lK
toIL-c B.zero pK lK = cz
toIL-c (B.suc k) pK lK = cs (toIL-c k pK lK)
toIL-c (B.lim f) pK (st , lg) = cl (λ n → toIL-c (f n) (pK n) (lg n))
toIL-c (B.lc k c w b t g) () lK
```
