# 换一步: 层的严格性

> 不含记号, 不含旧树. 入口 [AddClo](AddClo.lagda.md). 跨层比较 (`Bump`) 要层严格: 相邻项之间有字面前驱. `Lg` 不给这个 ($f_n=f_{n+1}$ 也合法). 这里证: 只要 `S` 把正的严格的和送到正的严格的和 (`SSt`), `Gen S` 的每个 `cell` 都严格 (`SA-cell`). 所有 $S$ 这条都是字面的, 不要证书: $+1$, $\cdot2$, $\cdot\omega$ 都是一行 (`SSt-+1`, `SSt-·2`, `SSt-ω`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.AddCloStr where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; Lg; ⊲-tr; lg⊲; z⊲; ≪∘; ≪S; ≪⊲; Rk; keep; rise; cmpN)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSum using (D; n0; n1; _⨾_; nl; ni; Dif; Ωd; inS; outS; out-inS; sum; pt; sum-fst; AccL; acc; accL; ≪≪; Int; Ipt; module Fold; module Gen; ω⋅)
open import OCF.Align.TLRuleSpec using (_≤_; s≤; ≤l; ≤-refl; ≤-suc; ≤-trans; irr)
```

## §1 正, 严格

`Pz x`: $x$ 不空. `Str k x`: $x$ 的每个 $\omega$-极限的每一段都不空, 每个节点在严格的坐标上的被积函数也是.

```agda
Pz : ∀ {k} → D k → Set
Pz n0 = ⊥
Pz n1 = ⊤
Pz (x ⨾ y) = Pz x ⊎ Pz y
Pz (nl d) = Σ ℕ (λ n → Pz (d n))
Pz (ni r u) = ⊤

module _ (k : A) (lw : ∀ {j} → j ≪ k → D j → Set) where
  data T₊ : D k → Set where
    t0 : T₊ n0
    t1 : T₊ n1
    t⨾ : ∀ {x y} → T₊ x → T₊ y → T₊ (x ⨾ y)
    tl : ∀ {d} → (∀ n → T₊ (d n)) → (∀ n → Pz (d n)) → T₊ (nl d)
    ti : ∀ {j} {r : j ≪ k} {u} → (∀ z → lw r z → T₊ (u (inS (≪S r) z))) → (∀ z → lw r z → Pz (u (inS (≪S r) z))) → T₊ (ni r u)

Str : ∀ k → D k → Set
LowT : ∀ k {j} → j ≪ k → D j → Set
Str k = T₊ k (LowT k)
LowT (asuc a) C.zero = Str a
LowT (asuc a) (C.suc r) = LowT a r
LowT (alim f) (C.lim n r) = LowT (f n) r

toT : ∀ {k j} (r : j ≪ k) {x} → LowT k r x → Str j x
toT C.zero p = p
toT (C.suc r) p = toT r p
toT (C.lim n r) p = toT r p

ofT : ∀ {k j} (r : j ≪ k) {x} → Str j x → LowT k r x
ofT C.zero p = p
ofT (C.suc r) p = ofT r p
ofT (C.lim n r) p = ofT r p

ti-out : ∀ {t j} (s : j ≪ t) {G : D j → D t} → (∀ z → Str j z → Str t (G z)) → (∀ z → Str j z → Pz (G z)) → Str t (ni s (λ y → G (outS (≪S s) y)))
ti-out {t} s {G} h g = ti (λ z e → subst (λ a → Str t (G a)) (sym (out-inS (≪S s) z)) (h z (toT s e)))
                         (λ z e → subst (λ a → Pz (G a)) (sym (out-inS (≪S s) z)) (g z (toT s e)))
```

## §2 严格的层

```agda
SA : A → Set
SA azero = ⊤
SA (asuc a) = SA a
SA (alim f) = (∀ n → f n ≪ f (suc n)) × (∀ n → SA (f n))

sa⊲ : ∀ {a b} → a ⊲ b → SA b → SA a
sa⊲ C.self s = s
sa⊲ (C.suc p) s = sa⊲ p s
sa⊲ (C.lim n p) s = sa⊲ p (proj₂ s n)

≪→s≤ : ∀ {a b} → a ≪ b → asuc a ≤ b
≪→s≤ C.zero = ≤-refl _
≪→s≤ (C.suc r) = ≤-suc (≪→s≤ r)
≪→s≤ (C.lim n r) = ≤l n (≪→s≤ r)

≪-irr : ∀ {a} → a ≪ a → ⊥
≪-irr {a} r = irr a (≪→s≤ r)

difP : ∀ b {a L} (p : a ⊲ b) (q : b ⊲ L) (w : Lg b) → SA b → a ≪ b → Pz (Dif b p q w)
difP b C.self q w s r = ⊥-elim (≪-irr r)
difP (asuc c) (C.suc p) q w s r = inj₂ tt
difP (alim f) (C.lim n p) q (st , w) s r =
  inj₂ (0 , difP (f (suc n)) (st n) (⊲-tr (C.lim (suc n) C.self) q) (w (suc n)) (proj₂ s (suc n)) (proj₁ s n))

strDif : ∀ b {a L} (p : a ⊲ b) (q : b ⊲ L) (w : Lg b) → SA b → Str L (Dif b p q w)
strDif b C.self q w s = t0
strDif (asuc c) (C.suc p) q w s = t⨾ (strDif c p (⊲-tr (C.suc C.self) q) w s) (ti (λ _ _ → t1) (λ _ _ → tt))
strDif (alim f) (C.lim n p) q (st , w) s =
  t⨾ (strDif (f n) p (⊲-tr (C.lim n C.self) q) (w n) (proj₂ s n))
     (tl (λ m → strDif (f (suc (m + n))) (st (m + n)) (⊲-tr (C.lim (suc (m + n)) C.self) q) (w (suc (m + n))) (proj₂ s (suc (m + n))))
         (λ m → difP (f (suc (m + n))) (st (m + n)) (⊲-tr (C.lim (suc (m + n)) C.self) q) (w (suc (m + n))) (proj₂ s (suc (m + n))) (proj₁ s (m + n))))

strΩ : ∀ a {L} (q : a ⊲ L) (w : Lg a) → SA a → Str L (Ωd a q w)
strΩ a q w s = t⨾ t1 (strDif a (z⊲ a) q w s)
```

## §3 坐标

```agda
iptS : ∀ {j k} (ac : AccL j) (r : j ≪ k) (u : D j → D k) {w d} → Str j w → (∀ n → Str j (d n)) → ∀ n → Str j (Ipt ac r u w d n)
iptS ac r u h q zero = h
iptS ac r u h q (suc n) = t⨾ (iptS ac r u h q n) (q n)

intS : ∀ {j k} (ac : AccL j) (r : j ≪ k) {u : D j → D k} → (∀ z → Str j z → Str k (u z)) → (∀ z → Str j z → Pz (u z)) → ∀ {w x} → Str j w → Str j x → Str k (Int ac r u w x)
intP : ∀ {j k} (ac : AccL j) (r : j ≪ k) {u : D j → D k} → (∀ z → Str j z → Str k (u z)) → (∀ z → Str j z → Pz (u z)) → ∀ {w x} → Str j w → Str j x → Pz x → Pz (Int ac r u w x)

intS ac r hu pu h t0 = t0
intS ac r hu pu h t1 = hu _ h
intS ac r hu pu h (t⨾ d e) = t⨾ (intS ac r hu pu h d) (intS ac r hu pu (t⨾ h d) e)
intS ac r {u} hu pu h (tl q pq) = tl (λ n → intS ac r hu pu (iptS ac r u h q n) (q n)) (λ n → intP ac r hu pu (iptS ac r u h q n) (q n) (pq n))
intS (acc f) r {u} hu pu h (ti {r = r′} q pq) = ti-out (≪≪ r′ r)
  (λ z e → intS (acc f) r hu pu (t⨾ h (intS (f r′) r′ (λ a b → q a (ofT r′ b)) (λ a b → pq a (ofT r′ b)) t0 e)) (q z (ofT r′ e)))
  (λ z e → intP (acc f) r hu pu (t⨾ h (intS (f r′) r′ (λ a b → q a (ofT r′ b)) (λ a b → pq a (ofT r′ b)) t0 e)) (q z (ofT r′ e)) (pq z (ofT r′ e)))

intP ac r hu pu h t0 ()
intP ac r hu pu h t1 p = pu _ h
intP ac r hu pu h (t⨾ d e) (inj₁ p) = inj₁ (intP ac r hu pu h d p)
intP ac r hu pu h (t⨾ d e) (inj₂ p) = inj₂ (intP ac r hu pu (t⨾ h d) e p)
intP ac r {u} hu pu h (tl q pq) (n , p) = n , intP ac r hu pu (iptS ac r u h q n) (q n) p
intP (acc f) r hu pu h (ti q pq) p = tt
```

## §4 折叠保持严格

`HS`, `HP`: 原子在严格正的状态上给严格正的差. 状态要正, 否则链的第一段是空的: 这就是为什么输入 $\Omega_y$ 要以 $1$ 开头.

```agda
module Run (W : A) (lW : Lg W) (S : ∀ {t} → D t → D t) where
  open Fold W lW S

  StS PzS : St → Set
  StS Y = ∀ {t} (τ : t ⊲ W) → Str t (Y τ)
  PzS Y = ∀ {t} (τ : t ⊲ W) → Pz (Y τ)

  HS HP : ∀ {k} → (D k → St → St) → Set
  HS {k} A₀ = ∀ {w} {Y : St} → Str k w → StS Y → PzS Y → StS (A₀ w Y)
  HP {k} A₀ = ∀ {w} {Y : St} → Str k w → StS Y → PzS Y → PzS (A₀ w Y)

  runS : ∀ {k} (ac : AccL k) (kp : k ⊲ W) (A₀ : D k → St → St) → HS A₀ → HP A₀ → ∀ {w x} {Y : St} → Str k w → Str k x → StS Y → PzS Y → StS (Run ac kp A₀ w x Y)
  runP : ∀ {k} (ac : AccL k) (kp : k ⊲ W) (A₀ : D k → St → St) → HS A₀ → HP A₀ → ∀ {w x} {Y : St} → Str k w → Str k x → StS Y → PzS Y → Pz x → PzS (Run ac kp A₀ w x Y)
  rptW : ∀ {k} (ac : AccL k) (kp : k ⊲ W) (A₀ : D k → St → St) {w d} {Y : St} → Str k w → (∀ n → Str k (d n)) → ∀ n → Str k (proj₁ (Rpt ac kp A₀ w d Y n))
  rptY : ∀ {k} (ac : AccL k) (kp : k ⊲ W) (A₀ : D k → St → St) → HS A₀ → HP A₀ → ∀ {w d} {Y : St} → Str k w → (∀ n → Str k (d n)) → StS Y → PzS Y → ∀ n → StS (proj₂ (Rpt ac kp A₀ w d Y n))
  rptP : ∀ {k} (ac : AccL k) (kp : k ⊲ W) (A₀ : D k → St → St) {w d} {Y : St} → PzS Y → ∀ n → PzS (proj₂ (Rpt ac kp A₀ w d Y n))
  chnW : ∀ {j} (ac : AccL j) (ρ : j ⊲ W) (A₀ : D j → St → St) → HS A₀ → HP A₀ → ∀ {Y : St} → StS Y → PzS Y → ∀ n → Str j (proj₁ (Chn ac ρ A₀ Y n))
  chnD : ∀ {j} (ac : AccL j) (ρ : j ⊲ W) (A₀ : D j → St → St) → HS A₀ → HP A₀ → ∀ {Y : St} → StS Y → PzS Y → ∀ n → Str j (proj₁ (proj₂ (Chn ac ρ A₀ Y n)))
  chnQ : ∀ {j} (ac : AccL j) (ρ : j ⊲ W) (A₀ : D j → St → St) → HS A₀ → HP A₀ → ∀ {Y : St} → StS Y → PzS Y → ∀ n → Pz (proj₁ (proj₂ (Chn ac ρ A₀ Y n)))
  chnY : ∀ {j} (ac : AccL j) (ρ : j ⊲ W) (A₀ : D j → St → St) → HS A₀ → HP A₀ → ∀ {Y : St} → StS Y → PzS Y → ∀ n → StS (proj₂ (proj₂ (Chn ac ρ A₀ Y n)))
  chnP : ∀ {j} (ac : AccL j) (ρ : j ⊲ W) (A₀ : D j → St → St) {Y : St} → PzS Y → ∀ n → PzS (proj₂ (proj₂ (Chn ac ρ A₀ Y n)))
  runKS : ∀ {j k t} (ac : AccL k) (ac′ : AccL j) (r : j ≪ k) (kp : k ⊲ W) (A₀ : D k → St → St) → HS A₀ → HP A₀ →
          ∀ {u} → (∀ z → LowT k r z → Str k (u (inS (≪S r) z))) → (∀ z → LowT k r z → Pz (u (inS (≪S r) z))) →
          ∀ {w} {Y : St} → Str k w → StS Y → PzS Y → (τ : t ⊲ W) (c : Rk j t) → Str t (RunK ac ac′ kp A₀ w r u Y τ c)
  runKP : ∀ {j k t} (ac : AccL k) (ac′ : AccL j) (r : j ≪ k) (kp : k ⊲ W) (A₀ : D k → St → St) → HS A₀ → HP A₀ →
          ∀ {u} → (∀ z → LowT k r z → Str k (u (inS (≪S r) z))) → (∀ z → LowT k r z → Pz (u (inS (≪S r) z))) →
          ∀ {w} {Y : St} → Str k w → StS Y → PzS Y → (τ : t ⊲ W) (c : Rk j t) → Pz (RunK ac ac′ kp A₀ w r u Y τ c)
  aiS : ∀ {j k} (ac : AccL k) (ac′ : AccL j) (r : j ≪ k) (kp : k ⊲ W) (A₀ : D k → St → St) → HS A₀ → HP A₀ →
        ∀ {u} → (∀ z → LowT k r z → Str k (u (inS (≪S r) z))) → (∀ z → LowT k r z → Pz (u (inS (≪S r) z))) →
        ∀ {w} → Str k w → ∀ {z} {Y′ : St} → Str j z → StS Y′ → PzS Y′ → StS (Ai ac r kp ac′ A₀ w u z Y′)
  aiP : ∀ {j k} (ac : AccL k) (ac′ : AccL j) (r : j ≪ k) (kp : k ⊲ W) (A₀ : D k → St → St) → HS A₀ → HP A₀ →
        ∀ {u} → (∀ z → LowT k r z → Str k (u (inS (≪S r) z))) → (∀ z → LowT k r z → Pz (u (inS (≪S r) z))) →
        ∀ {w} → Str k w → ∀ {z} {Y′ : St} → Str j z → StS Y′ → PzS Y′ → PzS (Ai ac r kp ac′ A₀ w u z Y′)

  runS ac kp A₀ hS hP h t0 hY pY τ = t0
  runS ac kp A₀ hS hP h t1 hY pY τ = hS h hY pY τ
  runS ac kp A₀ hS hP h (t⨾ d e) hY pY τ =
    t⨾ (runS ac kp A₀ hS hP h d hY pY τ)
       (runS ac kp A₀ hS hP (t⨾ h d) e (λ τ′ → t⨾ (hY τ′) (runS ac kp A₀ hS hP h d hY pY τ′)) (λ τ′ → inj₁ (pY τ′)) τ)
  runS ac kp A₀ hS hP h (tl q pq) hY pY τ = tl
    (λ n → runS ac kp A₀ hS hP (rptW ac kp A₀ h q n) (q n) (rptY ac kp A₀ hS hP h q hY pY n) (rptP ac kp A₀ pY n) τ)
    (λ n → runP ac kp A₀ hS hP (rptW ac kp A₀ h q n) (q n) (rptY ac kp A₀ hS hP h q hY pY n) (rptP ac kp A₀ pY n) (pq n) τ)
  runS (acc f) kp A₀ hS hP h (ti {r = r} q pq) hY pY τ = runKS (acc f) (f r) r kp A₀ hS hP q pq h hY pY τ (cmpN (≪∘ r kp) τ lW)

  runP ac kp A₀ hS hP h t0 hY pY ()
  runP ac kp A₀ hS hP h t1 hY pY p τ = hP h hY pY τ
  runP ac kp A₀ hS hP h (t⨾ d e) hY pY (inj₁ p) τ = inj₁ (runP ac kp A₀ hS hP h d hY pY p τ)
  runP ac kp A₀ hS hP h (t⨾ d e) hY pY (inj₂ p) τ =
    inj₂ (runP ac kp A₀ hS hP (t⨾ h d) e (λ τ′ → t⨾ (hY τ′) (runS ac kp A₀ hS hP h d hY pY τ′)) (λ τ′ → inj₁ (pY τ′)) p τ)
  runP ac kp A₀ hS hP h (tl q pq) hY pY (n , p) τ =
    n , runP ac kp A₀ hS hP (rptW ac kp A₀ h q n) (q n) (rptY ac kp A₀ hS hP h q hY pY n) (rptP ac kp A₀ pY n) p τ
  runP (acc f) kp A₀ hS hP h (ti {r = r} q pq) hY pY p τ = runKP (acc f) (f r) r kp A₀ hS hP q pq h hY pY τ (cmpN (≪∘ r kp) τ lW)

  rptW ac kp A₀ h q zero = h
  rptW ac kp A₀ h q (suc n) = t⨾ (rptW ac kp A₀ h q n) (q n)

  rptY ac kp A₀ hS hP h q hY pY zero = hY
  rptY ac kp A₀ hS hP h q hY pY (suc n) τ =
    t⨾ (rptY ac kp A₀ hS hP h q hY pY n τ)
       (runS ac kp A₀ hS hP (rptW ac kp A₀ h q n) (q n) (rptY ac kp A₀ hS hP h q hY pY n) (rptP ac kp A₀ pY n) τ)

  rptP ac kp A₀ pY zero = pY
  rptP ac kp A₀ pY (suc n) τ = inj₁ (rptP ac kp A₀ pY n τ)

  chnP ac ρ A₀ pY zero = pY
  chnP ac ρ A₀ pY (suc n) τ = inj₁ (chnP ac ρ A₀ pY n τ)

  chnW ac ρ A₀ hS hP hY pY zero = t0
  chnW ac ρ A₀ hS hP hY pY (suc n) = t⨾ (chnW ac ρ A₀ hS hP hY pY n) (chnD ac ρ A₀ hS hP hY pY n)

  chnD ac ρ A₀ hS hP hY pY zero = hY ρ
  chnD ac ρ A₀ hS hP hY pY (suc n) =
    runS ac ρ A₀ hS hP (chnW ac ρ A₀ hS hP hY pY n) (chnD ac ρ A₀ hS hP hY pY n) (chnY ac ρ A₀ hS hP hY pY n) (chnP ac ρ A₀ pY n) ρ

  chnQ ac ρ A₀ hS hP hY pY zero = pY ρ
  chnQ ac ρ A₀ hS hP hY pY (suc n) =
    runP ac ρ A₀ hS hP (chnW ac ρ A₀ hS hP hY pY n) (chnD ac ρ A₀ hS hP hY pY n) (chnY ac ρ A₀ hS hP hY pY n) (chnP ac ρ A₀ pY n) (chnQ ac ρ A₀ hS hP hY pY n) ρ

  chnY ac ρ A₀ hS hP hY pY zero = hY
  chnY ac ρ A₀ hS hP hY pY (suc n) τ =
    t⨾ (chnY ac ρ A₀ hS hP hY pY n τ)
       (runS ac ρ A₀ hS hP (chnW ac ρ A₀ hS hP hY pY n) (chnD ac ρ A₀ hS hP hY pY n) (chnY ac ρ A₀ hS hP hY pY n) (chnP ac ρ A₀ pY n) τ)

  aiS ac ac′ r kp A₀ hS hP q pq h {z} {Y′} e hY′ pY′ τ =
    runS ac kp A₀ hS hP (t⨾ h (intS ac′ r (λ a b → q a (ofT r b)) (λ a b → pq a (ofT r b)) t0 e)) (q z (ofT r e)) hY′ pY′ τ
  aiP ac ac′ r kp A₀ hS hP q pq h {z} {Y′} e hY′ pY′ τ =
    runP ac kp A₀ hS hP (t⨾ h (intS ac′ r (λ a b → q a (ofT r b)) (λ a b → pq a (ofT r b)) t0 e)) (q z (ofT r e)) hY′ pY′ (pq z (ofT r e)) τ

  runKS {j} ac ac′ r kp A₀ hS hP {u} q pq {w} {Y} h hY pY τ (keep s) = ti-out s
    (λ z e → runS ac kp A₀ hS hP (t⨾ h (intS ac′ r (λ a b → q a (ofT r b)) (λ a b → pq a (ofT r b)) t0 e)) (q z (ofT r e))
       (λ τ′ → t⨾ (hY τ′) (runS ac′ (⊲-tr (≪⊲ r) kp) (Ai ac r kp ac′ A₀ w u) (aiS ac ac′ r kp A₀ hS hP {u} q pq h) (aiP ac ac′ r kp A₀ hS hP {u} q pq h) t0 e hY pY τ′))
       (λ τ′ → inj₁ (pY τ′)) τ)
    (λ z e → runP ac kp A₀ hS hP (t⨾ h (intS ac′ r (λ a b → q a (ofT r b)) (λ a b → pq a (ofT r b)) t0 e)) (q z (ofT r e))
       (λ τ′ → t⨾ (hY τ′) (runS ac′ (⊲-tr (≪⊲ r) kp) (Ai ac r kp ac′ A₀ w u) (aiS ac ac′ r kp A₀ hS hP {u} q pq h) (aiP ac ac′ r kp A₀ hS hP {u} q pq h) t0 e hY pY τ′))
       (λ τ′ → inj₁ (pY τ′)) (pq z (ofT r e)) τ)
  runKS {j} ac ac′ r kp A₀ hS hP {u} q pq {w} {Y} h hY pY τ (rise _) = tl
    (λ n → runS ac′ ρ A′ hS′ hP′ (chnW ac′ ρ A′ hS′ hP′ hY pY n) (chnD ac′ ρ A′ hS′ hP′ hY pY n) (chnY ac′ ρ A′ hS′ hP′ hY pY n) (chnP ac′ ρ A′ pY n) τ)
    (λ n → runP ac′ ρ A′ hS′ hP′ (chnW ac′ ρ A′ hS′ hP′ hY pY n) (chnD ac′ ρ A′ hS′ hP′ hY pY n) (chnY ac′ ρ A′ hS′ hP′ hY pY n) (chnP ac′ ρ A′ pY n) (chnQ ac′ ρ A′ hS′ hP′ hY pY n) τ)
    where
    ρ = ⊲-tr (≪⊲ r) kp
    A′ = Ai ac r kp ac′ A₀ w u
    hS′ = aiS ac ac′ r kp A₀ hS hP {u} q pq h
    hP′ = aiP ac ac′ r kp A₀ hS hP {u} q pq h

  runKP ac ac′ r kp A₀ hS hP q pq h hY pY τ (keep s) = tt
  runKP {j} ac ac′ r kp A₀ hS hP {u} q pq {w} {Y} h hY pY τ (rise _) =
    0 , runP ac′ ρ A′ hS′ hP′ t0 (hY ρ) hY pY (pY ρ) τ
    where
    ρ = ⊲-tr (≪⊲ r) kp
    A′ = Ai ac r kp ac′ A₀ w u
    hS′ = aiS ac ac′ r kp A₀ hS hP {u} q pq h
    hP′ = aiP ac ac′ r kp A₀ hS hP {u} q pq h
```

## §5 第 0 层: 正的和给严格的步

```agda
dichot : ∀ {x} → Str azero x → Pz x ⊎ (∀ b → sum b x ≡ b)
dichot t0 = inj₂ (λ b → refl)
dichot t1 = inj₁ tt
dichot {x ⨾ y} (t⨾ d e) with dichot d | dichot e
... | inj₁ p | _ = inj₁ (inj₁ p)
... | inj₂ q | inj₁ p = inj₁ (inj₂ p)
... | inj₂ q | inj₂ q′ = inj₂ (λ b → subst (λ a → sum a y ≡ b) (sym (q b)) (q′ b))
dichot (tl q pq) = inj₁ (0 , pq 0)
dichot (ti {r = ()} q pq)

pos≪ : ∀ {x} (b : A) → Str azero x → Pz x → b ≪ sum b x
pos≪ b t0 ()
pos≪ b t1 p = C.zero
pos≪ {x ⨾ y} b (t⨾ d e) (inj₁ p) = ≪∘ (pos≪ b d p) (sum-fst (sum b x) y)
pos≪ {x ⨾ y} b (t⨾ d e) (inj₂ p) with dichot d
... | inj₁ p′ = ≪∘ (pos≪ b d p′) (sum-fst (sum b x) y)
... | inj₂ q = subst (λ a → b ≪ sum a y) (sym (q b)) (pos≪ b e p)
pos≪ b (tl q pq) (n , p) = C.lim 1 (pos≪ b (q 0) (pq 0))
pos≪ b (ti {r = ()} q pq) p

saSum : ∀ {x} (b : A) → SA b → Str azero x → SA (sum b x)
saPt  : ∀ {d} (b : A) → SA b → (∀ n → Str azero (d n)) → ∀ n → SA (pt b d n)
saSum b s t0 = s
saSum b s t1 = s
saSum {x ⨾ y} b s (t⨾ d e) = saSum (sum b x) (saSum b s d) e
saSum {nl d} b s (tl q pq) = (λ n → pos≪ (pt b d n) (q n) (pq n)) , saPt b s q
saSum b s (ti {r = ()} q pq)
saPt b s q zero = s
saPt {d} b s q (suc n) = saSum (pt b d n) (saPt b s q n) (q n)
```

## §6 闭项严格

```agda
SSt : (∀ {t} → D t → D t) → Set
SSt S = ∀ {t} {c : D t} → Str t c → Pz c → Str t (S c) × Pz (S c)

SSt-ω : SSt ω⋅
SSt-ω h p = tl (λ _ → h) (λ _ → p) , (0 , p)

SSt-·2 : SSt (λ c → c)
SSt-·2 h p = h , p

SSt-+1 : SSt (λ _ → n1)
SSt-+1 h p = t1 , tt

module Cell (S : ∀ {t} → D t → D t) (hS : SSt S) where
  open Gen S

  module _ (y : A) (w : Lg y) (s : SA y) where
    open Fold y w S
    open Run y w S

    stepS : ∀ {Y : St} → StS Y → StS (Step Y)
    stepS hY {t} τ = proj₁ (hS (t⨾ (strΩ t C.self (lg⊲ τ w) (sa⊲ τ s)) (hY τ)) (inj₁ (inj₁ tt)))

    stepP : ∀ {Y : St} → StS Y → PzS (Step Y)
    stepP hY {t} τ = proj₂ (hS (t⨾ (strΩ t C.self (lg⊲ τ w) (sa⊲ τ s)) (hY τ)) (inj₁ (inj₁ tt)))

    Y₀ : St
    Y₀ _ = n0

    hY₀ : StS Y₀
    hY₀ τ = t0

    strΨd : Str azero (Ψd y w)
    strΨd = t⨾ (stepS hY₀ (z⊲ y))
      (runS (accL y) C.self (λ _ Y → Step Y) (λ _ hY _ → stepS hY) (λ _ hY _ → stepP hY) (t⨾ t0 t1) (strDif y (z⊲ y) C.self w s)
        (λ τ → t⨾ t0 (stepS hY₀ τ)) (λ τ → inj₂ (stepP hY₀ τ)) (z⊲ y))

  SA-cell : ∀ n → SA (proj₁ (cell n))
  SA-cell zero = tt
  SA-cell (suc n) = saSum azero tt (t⨾ t1 (strΨd (proj₁ (cell n)) (proj₂ (cell n)) (SA-cell n)))

  z≪cell : ∀ n → azero ≪ proj₁ (cell n)
  z≪cell zero = C.zero
  z≪cell (suc n) = pos≪ azero (t⨾ t1 (strΨd (proj₁ (cell n)) (proj₂ (cell n)) (SA-cell n))) (inj₁ tt)
```
