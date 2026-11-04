# 不带高度的树接上带高度的树 (三): 规范位置, 对一切 $\theta$

> 不含记号. 结论写在 [WeakBridge](WeakBridge.lagda.md). 由 [GuardCertNf](GuardCertNf.lagda.md) 与 [GuardWeakNorm](GuardWeakNorm.lagda.md) 推广到层号族 `c⁺ θ`:
>
> - `hp⁺ θ`: `R-ι` 要的读法性质 `HPf`, 对一切 $\theta$. 那里写死在 $c_1$, $c_1+1$.
> - `nfP θ`: 低层节点 ($k\approx\lceil j\rceil$) 的规范位置: 穿过后继与极限, 落在 `fst self` ($j\cong0$) 或 `bra (b+1) e self` ($b\cong j$). 这是 `nv` 的 $\theta$ 版, 极限层也一样.
> - `NT`: 规范路径. `pnt`: `⊴⁺` 把规范路径搬成规范路径, 所以比较里沿极限层的搬运不破坏 "分支值是后继".

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.WeakBridgeNf where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.BTBO using (module Trich)
open Trich renaming (_<_ to _<ᴺ_) using (zero; suc)
open import OCF.Free.Level
open import OCF.Align.GuardTightLv
open Lv Dom₀ hiding (zero; suc; lim)
open import OCF.Align.GuardTightTab Dom₀ using (Strict; st-suc; st-lim; st-fst; st-bra; stCp; st⊙; _⊙_)
open import OCF.Align.GuardTightBase
open import OCF.Align.GuardWeakRel using (⌜_⌝; ⌜≈⌝; ⌜≈⁻⌝; FrL; FrG; Fr≈; ZB)
open import OCF.Align.GuardWeakRd using (Tc-Ω₁; RdV; rvF; rvN)
open import OCF.Align.GuardWeakNorm using (viewR; no-below)
open import OCF.Align.GuardCertRel using (FlrLe; InvS; iE; iL; EndS; es0; es-s; es-l; es-f; es-b; HPf; EndT; le-emp)
open import OCF.Align.GuardCertNf using (FB; le-nfC; le-nfS; fb-end; fb-zero; fb-le; lc-absurd)
open import OCF.Align.GuardTightCert using (c₁; wf₁; sf₁)
open import OCF.Align.WeakBridgeBase
```

## §1 `HPf`

```agda
lo-c : ∀ {θ j} → c⁺ θ ≈ ⌜ j ⌝ → ⊥
lo-c {θ} {j} e = NF-c θ (Fr≈ (FrG j) (≈-sym e))

FB⁺ : ∀ θ {k₁} → Cp k₁ (c⁺ θ) → Ordᴵ → Set
FB⁺ zero Q k = FB Q k
FB⁺ (suc a) Lv.self k = ⊥
FB⁺ (suc a) (Lv.suc Q) k = FB⁺ a Q k
FB⁺ (lim f s) Lv.self k = ⊥
FB⁺ (lim f s) (Lv.lim n Q) k = FB⁺ (f n) Q k

le⁺ : ∀ θ {k₁ k} (Q₀ : Cp k₁ (c⁺ θ)) → FB⁺ θ Q₀ k → FlrLe (pF (posN (nfC (c⁺ θ) (tc⁺ θ) Q₀))) k
le⁺ zero Q₀ h = le-nfC Q₀ h
le⁺ (suc a) (Lv.suc Q) h with nfC (c⁺ a) (tc⁺ a) Q | le⁺ a Q h
... | nfc d Q′ t r | h′ = h′
le⁺ (lim f s) (Lv.lim n Q) h with nfC (c⁺ (f n)) (tc⁺ (f n)) Q | le⁺ (f n) Q h
... | nfc d Q′ t r | h′ = h′

leS⁺ : ∀ θ {k₁ k} (R : Strict k₁ (c⁺ θ)) → FB⁺ θ (stCp R) k → FlrLe (pF (stCp (posS (nfS (c⁺ θ) (tc⁺ θ) R)))) k
leS⁺ zero R h = le-nfS R h
leS⁺ (suc a) (st-suc Q) h with nfC (c⁺ a) (tc⁺ a) Q | le⁺ a Q h
... | nfc d Q′ t r | h′ = h′
leS⁺ (lim f s) (st-lim n Q) h with nfC (c⁺ (f n)) (tc⁺ (f n)) Q | le⁺ (f n) Q h
... | nfc d Q′ t r | h′ = h′

fb⁺-end : ∀ θ {k₁ k} (Q₀ : Cp k₁ (c⁺ θ)) → EndS Q₀ → k₁ ≈ ⌜ k ⌝ → FB⁺ θ Q₀ k
fb⁺-end zero Q₀ h dk = fb-end Q₀ h dk
fb⁺-end (suc a) (Lv.suc Lv.self) es0 dk = ⊥-elim (lo-c dk)
fb⁺-end (suc a) (Lv.suc Q) (es-s h) dk = fb⁺-end a Q h dk
fb⁺-end (lim f s) (Lv.lim n Q) (es-l h) dk = fb⁺-end (f n) Q h dk

fb⁺-zero : ∀ θ {k₁ k} (Q₀ : Cp k₁ (c⁺ θ)) → k₁ ≈ ⌜ k ⌝ → ZB k → FB⁺ θ Q₀ k
fb⁺-zero zero Q₀ dk z = fb-zero Q₀ dk z
fb⁺-zero (suc a) Lv.self dk z = lo-c dk
fb⁺-zero (suc a) (Lv.suc Q) dk z = fb⁺-zero a Q dk z
fb⁺-zero (lim f s) Lv.self dk z = lo-c dk
fb⁺-zero (lim f s) (Lv.lim n Q) dk z = fb⁺-zero (f n) Q dk z

fb⁺-le : ∀ θ {k₁ k} (Q₀ : Cp k₁ (c⁺ θ)) → k₁ ≈ ⌜ k ⌝ → FlrLe (pF Q₀) k → FB⁺ θ Q₀ k
fb⁺-le zero Q₀ dk c = fb-le Q₀ dk c
fb⁺-le (suc a) Lv.self dk c = lo-c dk
fb⁺-le (suc a) (Lv.suc Q) dk c = fb⁺-le a Q dk c
fb⁺-le (lim f s) Lv.self dk c = lo-c dk
fb⁺-le (lim f s) (Lv.lim n Q) dk c = fb⁺-le (f n) Q dk c

-- 无分支的位置不贡献帧
pF-⊙ : ∀ {k a b} {P : Cp a b} → Nb P → (Q : Cp k a) → ∀ {f} → Mem (pF (P ⊙ Q)) f → Mem (pF Q) f
pF-⊙ nself Q m = m
pF-⊙ (nsuc h) Q m = pF-⊙ h Q m
pF-⊙ (nlim h) Q m = pF-⊙ h Q m
pF-⊙ (nfst h) Q m = pF-⊙ h Q m

le-st⊙ : ∀ {k₁ a′ b k} (P : Cp a′ b) (R′ : Strict k₁ a′) → Nb P → FlrLe (pF (stCp R′)) k → FlrLe (pF (stCp (st⊙ P R′))) k
le-st⊙ Lv.self R′ h c = c
le-st⊙ (Lv.suc P) R′ (nsuc h) c f m = c f (pF-⊙ h (stCp R′) m)
le-st⊙ (Lv.lim n P) R′ (nlim h) c f m = c f (pF-⊙ h (stCp R′) m)
le-st⊙ (Lv.fst P) R′ (nfst h) c f m = c f (pF-⊙ h (stCp R′) m)

fbI : ∀ θ {k₁ a′ k} (P : Cp a′ (c⁺ θ)) (R′ : Strict k₁ a′) → k₁ ≈ ⌜ k ⌝ → InvS R′ k → FB⁺ θ (stCp (st⊙ P R′)) k
fbI θ P R′ dk (iE h) = fb⁺-end θ (stCp (st⊙ P R′)) (EndT R′ h P) dk
fbI θ P R′ dk (iL n c) = fb⁺-le θ (stCp (st⊙ P R′)) dk (le-st⊙ P R′ (nb⁺ θ P n) c)

hp⁺ : ∀ θ → HPf (c⁺ θ) (tc⁺ θ)
hp⁺ θ P R′ dk =
  (λ z → leS⁺ θ (st⊙ P R′) (fb⁺-zero θ (stCp (st⊙ P R′)) dk z)) ,
  (λ iv → leS⁺ θ (st⊙ P R′) (fbI θ P R′ dk iv) , iL (NF-c θ) (leS⁺ θ (st⊙ P R′) (fbI θ P R′ dk iv)))
```

## §2 低层节点的规范位置

```agda
one : Ordᴵ
one = suc zero

data NP : ∀ θ {rp} → Cp (Lv.suc rp) (c⁺ θ) → Ordᴵ → Set where
  npF : ∀ {j} → j ≅ᴵ zero → NP zero {Lv.zero} (Lv.fst Lv.self) j
  npB : ∀ {b j} {e : one ⊑ᴵ suc b} → b ≅ᴵ j → NP zero {⌜ b ⌝} (Lv.bra (suc b) e Lv.self) j
  nps : ∀ {a rp j} {Q : Cp (Lv.suc rp) (c⁺ a)} → NP a Q j → NP (suc a) (Lv.suc Q) j
  npl : ∀ {f s rp j} n {Q : Cp (Lv.suc rp) (c⁺ (f n))} → NP (f n) Q j → NP (lim f s) (Lv.lim n Q) j

data NPV (θ j : Ordᴵ) {k} {P : Cp (Lv.suc k) (c⁺ θ)} : NfC P → Set where
  npv : ∀ {rp d} {Q : Cp (Lv.suc rp) (c⁺ θ)} {t r} → NP θ Q j → NPV θ j (nfc {repN = Lv.suc rp} d Q t r)

nfP₀ : ∀ {k j} (P : Cp (Lv.suc k) c₁) → k ≈ ⌜ j ⌝ → NPV zero j (nfC c₁ Tc-Ω₁ P)
nfP₀ (Lv.fst Lv.self) dk = npv (npF (≅ᴵ-sym (⌜≈⁻⌝ {a = zero} dk)))
nfP₀ (Lv.fst (Lv.suc ())) dk
nfP₀ {j = j} (Lv.bra η e P) dk with viewR η e P
nfP₀ {j = j} (Lv.bra η e P) dk | rdF (inj₂ refl) Lv.self tr , eq , rvF rewrite eq = npv (npF (≅ᴵ-sym (⌜≈⁻⌝ {a = zero} dk)))
nfP₀ {j = j} (Lv.bra η e P) dk | rdF (inj₁ (Lv.s≈ d)) Lv.self tr , eq , rvF rewrite eq = npv (npF (≅ᴵ-sym (⌜≈⁻⌝ {a = zero} (≈-trans (≈-sym d) dk))))
nfP₀ {j = j} (Lv.bra η e P) dk | rdB (suc b) ea l (inj₂ refl) Lv.self tr , eq , rvN .b w rewrite eq = npv (npB (⌜≈⁻⌝ dk))
nfP₀ {j = j} (Lv.bra η e P) dk | rdB (suc b) ea l (inj₁ (Lv.s≈ d)) Lv.self tr , eq , rvN .b w rewrite eq = npv (npB (⌜≈⁻⌝ (≈-trans (≈-sym d) dk)))
nfP₀ (Lv.bra η e P) dk | rdB (suc b) ea l (inj₂ refl) (Lv.suc Q) tr , eq , rvN .b (inj₁ h) = ⊥-elim (no-below Q h)
nfP₀ (Lv.bra η e P) dk | rdB (suc b) ea l (inj₂ refl) (Lv.suc Q) tr , eq , rvN .b (inj₂ ())
nfP₀ (Lv.bra η e P) dk | rdB (suc b) ea l (inj₁ (Lv.s≈ d)) (Lv.suc Q) tr , eq , rvN .b (inj₁ h) = ⊥-elim (no-below Q h)
nfP₀ (Lv.bra η e P) dk | rdB (suc b) ea l (inj₁ (Lv.s≈ d)) (Lv.suc Q) tr , eq , rvN .b (inj₂ ())

nfP : ∀ θ {k j} (P : Cp (Lv.suc k) (c⁺ θ)) → k ≈ ⌜ j ⌝ → NPV θ j (nfC (c⁺ θ) (tc⁺ θ) P)
nfP zero P dk = nfP₀ P dk
nfP (suc a) Lv.self dk = ⊥-elim (lo-c dk)
nfP (suc a) (Lv.suc P) dk with nfC (c⁺ a) (tc⁺ a) P | nfP a P dk
... | nfc d Q t r | npv n = npv (nps n)
nfP (lim f s) (Lv.lim m P) dk with nfC (c⁺ (f m)) (tc⁺ (f m)) P | nfP (f m) P dk
... | nfc d Q t r | npv n = npv (npl m n)
```

## §3 规范路径

```agda
data NT : ∀ θ {t} → t < c⁺ θ → Ordᴵ → Set where
  ntF : ∀ {j} → j ≅ᴵ zero → NT zero {Lv.zero} (Lv.fst Lv.zero) j
  ntB : ∀ {b j} {e : one ⊑ᴵ suc b} → b ≅ᴵ j → NT zero {⌜ b ⌝} (Lv.bra (suc b) e Lv.zero) j
  nts : ∀ {a t j} {q : t < c⁺ a} → NT a q j → NT (suc a) (Lv.suc q) j
  ntl : ∀ {f s t j} n {q : t < c⁺ (f n)} → NT (f n) q j → NT (lim f s) (Lv.lim n q) j

np→nt : ∀ {θ rp j} {Q : Cp (Lv.suc rp) (c⁺ θ)} → NP θ Q j → NT θ (fromCpS Q) j
np→nt (npF e) = ntF e
np→nt (npB e) = ntB e
np→nt (nps n) = nts (np→nt n)
np→nt (npl m n) = ntl m (np→nt n)

nt≈ : ∀ {θ t i} {q : t < c⁺ θ} → NT θ q i → t ≈ ⌜ i ⌝
nt≈ (ntF e) = ⌜≈⌝ (≅ᴵ-sym e)
nt≈ (ntB e) = ⌜≈⌝ e
nt≈ (nts n) = nt≈ n
nt≈ (ntl m n) = nt≈ n

-- 搬运保持规范路径
data NTV (θ j : Ordᴵ) {k} {A : Src → Set} : k ≺⟨ A ⟩ c⁺ θ → Set where
  ntv : ∀ {rp d} {p : rp < c⁺ θ} {t} → NT θ p j → NTV θ j (viaᴸ d p t)

PNT : ∀ {a b} → c⁺ a ⊴ c⁺ b → Set
PNT {a} {b} x = ∀ {k j} (r : k < c⁺ a) → NT a r j → NTV b j (⊴p x r)

pnt-trans : ∀ {a b d} (x : c⁺ a ⊴ c⁺ b) (y : c⁺ b ⊴ c⁺ d) → PNT x → PNT y → PNT (⊴-trans x y)
pnt-trans x y hx hy r n with ⊴p x r | hx r n
... | viaᴸ d p t | ntv n′ with ⊴p y p | hy p n′
...   | viaᴸ d′ p′ t′ | ntv n″ = ntv n″

pnt-refl₀ : ∀ (e : c₁ ≈ c₁) {k j} (r : k < c₁) → NT zero r j → NTV zero j (≈-move e r)
pnt-refl₀ (Lv.o≈ d e h) (Lv.fst Lv.zero) (ntF x) with e
... | Lv.s≈ Lv.z≈ = ntv (ntF x)
pnt-refl₀ (Lv.o≈ d e h) (Lv.bra (suc b) e₁ Lv.zero) (ntB x) with h (suc b) e₁ (suc b) (conv d e₁) (≅ᴰ-refl (suc b))
... | Lv.s≈ y = ntv (ntB x)

pnt-≈ : ∀ {a b} (d : a ≅ᴵ b) → PNT {a} {b} (≈→⊴ (c⁺-≈ d))
pnt-≈ z≅ r n = pnt-refl₀ sf₁ r n
pnt-≈ (s≅ d) (Lv.suc r) (nts n) with ≈-move (c⁺-≈ d) r | pnt-≈ d r n
... | viaᴸ d′ p t | ntv n′ = ntv (nts n′)
pnt-≈ (l≅ h) (Lv.lim m r) (ntl .m n) with ≈-move (c⁺-≈ (h m)) r | pnt-≈ (h m) r n
... | viaᴸ d′ p t | ntv n′ = ntv (ntl m n′)

pnt-suc : ∀ {a b} (x : c⁺ a ⊴ c⁺ b) → PNT x → PNT {a} {suc b} (⊴-suc-r x)
pnt-suc x h r n with ⊴p x r | h r n
... | viaᴸ d p t | ntv n′ = ntv (nts n′)

pnt-lim : ∀ {a f s} m (x : c⁺ a ⊴ c⁺ (f m)) → PNT x → PNT {a} {lim f s} (⊴-lim-r m x)
pnt-lim m x h r n with ⊴p x r | h r n
... | viaᴸ d p t | ntv n′ = ntv (ntl m n′)

pnt-< : ∀ {a b} (q : a <ᴵ b) → PNT {a} {b} (c⁺<⊴ q)
pnt-< {a} zero = pnt-suc (≈→⊴ (sf⁺ a)) (pnt-≈ (≅ᴵ-refl a))
pnt-< (suc q) = pnt-suc (c⁺<⊴ q) (pnt-< q)
pnt-< (lim n q) = pnt-lim n (c⁺<⊴ q) (pnt-< q)

pnt-c₁ : ∀ b → PNT {zero} {b} (c₁⊴ b)
pnt-c₁ zero = pnt-≈ z≅
pnt-c₁ (suc b) = pnt-suc (c₁⊴ b) (pnt-c₁ b)
pnt-c₁ (lim f s) = pnt-lim 0 (c₁⊴ (f 0)) (pnt-c₁ (f 0))

pnt : ∀ {a b} (d : a ⊑ᴵ b) → PNT (⊴⁺ d)
pnt {b = b} z⊑ = pnt-c₁ b
pnt (s⊑ e q) (Lv.suc r) (nts n) = pnt-trans (≈→⊴ (c⁺-≈ e)) (c⁺<⊴ q) (pnt-≈ e) (pnt-< q) r n
pnt (l⊑ h) (Lv.lim m r) (ntl .m n) = pnt (h m) r n

pnt-steps : ∀ {f : ℕ → Ordᴵ} (s : ∀ n → f n ⊑ᴵ f (suc n)) {n m} (l : n <ᴺ m) → PNT {f n} {f m} (stepsˢ (λ i → ⊴⁺ (s i)) l)
pnt-steps s zero = pnt (s _)
pnt-steps s (suc l) = pnt-trans (stepsˢ (λ i → ⊴⁺ (s i)) l) (⊴⁺ (s _)) (pnt-steps s l) (pnt (s _))
```
