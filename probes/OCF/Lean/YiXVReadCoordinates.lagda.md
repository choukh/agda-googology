# YiXVReadCoordinates
> 验收文件。档位：编译定理。同一实际上界内的层号等式反射与带证据坐标读回；不提供全域反射。
> 从 YiXVSource*、YiCeilRead 与原 Level 的递归推广；未交节点行、外层 n≥2 读回界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadCoordinates where
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Data.Product using (Σ; _×_; _,_)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegPath as Path
import OCF.Lean.YiLSRead as Read
import OCF.Lean.YiLSTw1 as T
import OCF.Align.Level as L
open import OCF.Align.Value using (≅→≼)
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadPaths as P
import OCF.Lean.YiXVReadThin as Thin

source-erase : S.L → L.Ordᶜ L.zero
source-erase S.zero = L.zero
source-erase (S.suc j) = L.suc (source-erase j)
source-erase (S.lim f) = L.lim (λ n → source-erase (f n))
source-erase (S.Ωₗ j f) = L.zero
source-read : ∀ r → source-erase (J.ℓ r) L.≅ Read.read r
source-read S.zero = L.z≅
source-read (S.suc r) = L.s≅ (source-read r)
source-read (S.lim f d) = L.l≅ (λ n → source-read (f n))
source-read (S.Ω () f)
source-read (S.up r () b nb)

native-erase : L.Ordᴵ → L.Ordᶜ L.zero
native-erase L.zero = L.zero
native-erase (L.suc j) = L.suc (native-erase j)
native-erase (L.lim f d) = L.lim (λ n → native-erase (f n))
native-read : ∀ r → native-erase (T.lvl r) L.≅ Read.read r
native-read S.zero = L.z≅
native-read (S.suc r) = L.s≅ (native-read r)
native-read (S.lim f d) = L.l≅ (λ n → native-read (f n))
native-read (S.Ω () f)
native-read (S.up r () b nb)

source-equal : ∀ {root x y} → x P.≤ᵀ root → y P.≤ᵀ root → J.ℓ x ≡ J.ℓ y → x ≡ y
source-equal {root} {x} {y} p q e = Thin.thin root p q (≅→≼ eq) (≅→≼ (L.≅-sym eq))
  where
  eq : Read.read x L.≅ Read.read y
  eq = L.≅-trans (L.≅-sym (source-read x))
    (subst (λ j → source-erase j L.≅ Read.read y) (sym e) (source-read y))
native-equal : ∀ {root x y} → x P.≤ᵀ root → y P.≤ᵀ root → T.lvl x ≡ T.lvl y → x ≡ y
native-equal {root} {x} {y} p q e = Thin.thin root p q (≅→≼ eq) (≅→≼ (L.≅-sym eq))
  where
  eq : Read.read x L.≅ Read.read y
  eq = L.≅-trans (L.≅-sym (native-read x))
    (subst (λ j → native-erase j L.≅ Read.read y) (sym e) (native-read y))

actual : S.zero ≡ S.zero
actual = source-equal Thin.first Thin.second refl

inside : ∀ {a b root} → a P.≺ᵀ b → b P.≤ᵀ root → a P.≤ᵀ root
inside p P.here = P.below p
inside p (P.below q) = P.below (P.trans p q)
find : ∀ {root} (r : S.Tr S.zero) (within : r P.≤ᵀ root) {j} → j Path.≤ J.ℓ r →
  Σ (S.Tr S.zero) (λ y → (y P.≤ᵀ root) × (j ≡ J.ℓ y))
find S.zero within Path.self = S.zero , within , refl
find r@(S.suc _) within Path.self = r , within , refl
find (S.suc r) within (Path.ins v) = find r (inside P.root within) v
find r@(S.lim _ _) within Path.self = r , within , refl
find (S.lim f d) within (Path.inl n v) = find (f n) (inside (P.branch n) within) v
find (S.lim f d) within (Path.inlu v) = find (f 0) (inside (P.branch 0) within) (v 0)
find (S.Ω () f) within v
find (S.up r () b nb) within v
strict-level-path : ∀ {x y} → x P.≺ᵀ y → J.ℓ x Path.≤ J.ℓ y
strict-level-path P.root = Path.ins Path.self
strict-level-path (P.under-suc p) = Path.ins (strict-level-path p)
strict-level-path (P.branch n) = Path.inl n Path.self
strict-level-path (P.under-lim n p) = Path.inl n (strict-level-path p)
level-path : ∀ {x y} → x P.≤ᵀ y → J.ℓ x Path.≤ J.ℓ y
level-path P.here = Path.self
level-path (P.below p) = strict-level-path p
```
