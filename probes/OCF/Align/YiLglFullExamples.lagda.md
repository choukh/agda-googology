# 四处严格后的旧反例排除与规范实例

以下对象在新的 FullCore 类型中按旧形状重写，不混用旧 Raw／LF 证据。
只排除已经出现的反例；规范 Ω／塔／Λ／cO／top／up 的全层闭包在 FullVal 中。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiLglFullExamples where

open import Data.Nat.Base using (ℕ)
open import Data.Unit.Base using (tt)
open import Data.Empty using (⊥)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl)
import OCF.Align.YiLglFullCore as F
open F using (module G)
open import OCF.Align.YiLglFullVal using (Legal; Properˢ; CP)
import OCF.Align.YiLglFullVal as V

One : F.LF
One = F.suc F.zero

raw1 raw2 raw3 : F.Raw F.zero
raw1 = G.suc G.zero
raw2 = G.suc raw1
raw3 = G.suc raw2

e1 : F.Gd F.zero raw1 raw1
e1 = inj₁ refl , tt
e2 : F.Gd F.zero raw1 raw2
e2 = inj₂ (inj₁ refl) , tt
e3 : F.Gd F.zero raw1 raw3
e3 = inj₂ (inj₂ (inj₁ refl)) , tt

no-raw-one-self : F.Dn F.zero raw1 raw1 → ⊥
no-raw-one-self (inj₁ ())
no-raw-one-self (inj₂ ())

no-round11-coordinate : F.Lgl F.zero (G.lim (λ _ → raw1)) → ⊥
no-round11-coordinate (step , lawful) = no-raw-one-self (step 0)

no-proper-one : Properˢ One One → ⊥
no-proper-one (V.under-suc ())

fold-source : F.LF
fold-source = F.lc F.zero raw1 One (λ _ _ → One)

no-fold-source : Legal fold-source → ⊥
no-fold-source (lk , first , strict , same , lt , lg) =
  no-proper-one (strict raw1 e1 raw2 e2 (inj₁ refl))

eta : F.Raw One
eta = G.lc (inj₁ tt) raw1 G.top (λ _ _ → G.suc G.top)

no-raw-bump-self : F.Dn One (G.suc G.top) (G.suc G.top) → ⊥
no-raw-bump-self (inj₁ ())
no-raw-bump-self (inj₂ ())

no-old-eta : F.Lgl One eta → ⊥
no-old-eta (first , strict , same , lt , lg) =
  no-raw-bump-self (strict raw2 e2 raw3 e3 (inj₁ refl))

data Finite : F.LF → Set where
  fzero : Finite F.zero
  fsuc : ∀ {x} → Finite x → Finite (F.suc x)

finite-position : ∀ {a b} → CP a b → Finite b → Finite a
finite-position V.self lawful = lawful
finite-position (V.suc p) (fsuc lawful) = finite-position p lawful
finite-position (V.lim n p) ()
finite-position (V.fst p) ()

OmegaOne : F.LF
OmegaOne = V.Ω̂ One

no-finite-bump : Finite (F.suc OmegaOne) → ⊥
no-finite-bump (fsuc ())

no-proper-bump : Properˢ (F.suc OmegaOne) (F.suc OmegaOne) → ⊥
no-proper-bump (V.under-suc (V.fst p)) = no-finite-bump (finite-position p (fsuc fzero))

bad : F.LF
bad = F.lc F.zero raw1 OmegaOne (λ _ _ → F.suc OmegaOne)

no-old-bad : Legal bad → ⊥
no-old-bad (lk , first , strict , same , lt , lg) =
  no-proper-bump (strict raw2 e2 raw3 e3 (inj₁ refl))

all-towers : ∀ n → Legal (V.tw n)
all-towers = V.Legal-tw

Lambda-legal : Legal V.Λ
Lambda-legal = V.Legal-Λ

top-lawful : ∀ k → F.Lgl k G.top
top-lawful k = tt

cO-lawful : ∀ k → F.Lgl k (V.cO k)
cO-lawful = V.Lgl-cO

lower-equality : ∀ k → F.Gd k (V.cO k) (V.cO k)
lower-equality k = inj₁ refl , cO-lawful k
```

两种常 Ω 分支的反例分别在 LF／Raw 的严格行被排除。
守卫下界本身仍可入，lower-equality 对一切层成立；第一支仍允许弱关系。
上轮失败的 Ω̂2 及塔第3项现由同一全层闭包给合法性，不补单站证明。
