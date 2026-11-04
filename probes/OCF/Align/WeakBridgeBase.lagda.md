# 不带高度的树接上带高度的树 (一): 层号族 $c_1+\theta$

> 不含记号. 结论写在 [WeakBridge](WeakBridge.lagda.md). `c⁺ θ`: 层号 $c_1+\theta$, $c_1$ 是 $\Omega$ 的层号 ([GuardTightCert](GuardTightCert.lagda.md)), 后继与极限都是字面的 `Lv.suc`, `Lv.lim`. 这里只有层号上的事实: 互模拟, 单调 (`⊴⁺`), 好层号 (`cf⁺`), 读法 (`tc⁺`), 节点的分类 (`pull⁺`), 闭包的位置 (`key⁺`, `nb⁺`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.WeakBridgeBase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)
open import OCF.Free.Level
open import OCF.Align.GuardTightLv
open Lv Dom₀ hiding (zero; suc; lim) renaming (_⊑_ to _⊑ᴸ_)
open import OCF.Align.GuardTightBase
open import OCF.Align.GuardTightTab Dom₀ using (Strict; st-suc; st-lim; st-fst; st-bra; stCp; toCp)
open import OCF.Align.GuardWeakRel using (⌜_⌝; ⌜≈⌝; ⌜≈⁻⌝; pullG; FrL; fz; fs′; fl; FrG; Fr≈)
open import OCF.Align.GuardWeakRd using (Tc-Ω₁)
open import OCF.Align.GuardTightCert using (c₁; wf₁; sf₁)
open import OCF.Align.GuardCertRel using (fr-cp)
```

## §1 层号族

```agda
c⁺ : Ordᴵ → LG
c⁺ zero = c₁
c⁺ (suc a) = Lv.suc (c⁺ a)
c⁺ (lim f s) = Lv.lim (λ n → c⁺ (f n))

c⁺-≈ : ∀ {a b} → a ≅ᴵ b → c⁺ a ≈ c⁺ b
c⁺-≈ z≅ = sf₁
c⁺-≈ (s≅ e) = Lv.s≈ (c⁺-≈ e)
c⁺-≈ (l≅ h) = Lv.l≈ (λ n → c⁺-≈ (h n))

sf⁺ : ∀ θ → c⁺ θ ≈ c⁺ θ
sf⁺ θ = c⁺-≈ (≅ᴵ-refl θ)

c⁺-≈⁻ : ∀ {a b} → c⁺ a ≈ c⁺ b → a ≅ᴵ b
c⁺-≈⁻ {a = zero} {b = zero} e = z≅
c⁺-≈⁻ {a = suc a} {b = suc b} (Lv.s≈ e) = s≅ (c⁺-≈⁻ e)
c⁺-≈⁻ {a = lim f s} {b = lim g t} (Lv.l≈ h) = l≅ (λ n → c⁺-≈⁻ (h n))

-- 路径
c⁺< : ∀ {a b} → a <ᴵ b → c⁺ a < c⁺ b
c⁺< zero = Lv.zero
c⁺< (suc q) = Lv.suc (c⁺< q)
c⁺< (lim n q) = Lv.lim n (c⁺< q)

c⁺≪ : ∀ {a b} → a <ᴵ b → c⁺ a ≪ c⁺ b
c⁺≪ zero = Lv.zero
c⁺≪ (suc q) = Lv.suc (c⁺≪ q)
c⁺≪ (lim n q) = Lv.lim n (c⁺≪ q)

adm⁺ : ∀ {E : Src} {a b} (q : a <ᴵ b) → Adm E (c⁺< q)
adm⁺ zero = tt
adm⁺ (suc q) = adm⁺ q
adm⁺ (lim n q) = adm⁺ q

-- 字面子项是 ⊴
c⁺<⊴ : ∀ {a b} → a <ᴵ b → c⁺ a ⊴ c⁺ b
c⁺<⊴ {a} zero = ⊴-suc-r (≈→⊴ (sf⁺ a))
c⁺<⊴ (suc q) = ⊴-suc-r (c⁺<⊴ q)
c⁺<⊴ (lim n q) = ⊴-lim-r n (c⁺<⊴ q)

c₁⊴ : ∀ b → c₁ ⊴ c⁺ b
c₁⊴ zero = ≈→⊴ sf₁
c₁⊴ (suc b) = ⊴-suc-r (c₁⊴ b)
c₁⊴ (lim f s) = ⊴-lim-r 0 (c₁⊴ (f 0))

-- 后继在左边
⊴-suc-l : ∀ {a a′ b} → a ≈ a′ → (p : a′ < b) → (∀ E → Adm E p) → a′ ≪ b → a ⊴ b → Lv.suc a ⊴ b
⊴-suc-l {a} {a′} {b} e p ad pf x = ⊴i pp ff kk KK
  where
  pp : Lv.suc a ⊑ᴸ b
  pp Lv.zero = viaᴸ e p (λ E _ → ad E)
  pp (Lv.suc r) = ⊴p x r
  ff : Lv.suc a ⊑ᶠ b
  ff Lv.zero = preᶠ e pf
  ff (Lv.suc r) = ⊴f x r
  kk : Lv.suc a ⊑ᵏ b
  kk (Lv.suc r) = ⊴k x r
  KK : Lv.suc a ⊑ᴷ b
  KK (Lv.suc r) = ⊴K x r

⊴⁺ : ∀ {a b} → a ⊑ᴵ b → c⁺ a ⊴ c⁺ b
⊴⁺ {b = b} z⊑ = c₁⊴ b
⊴⁺ (s⊑ e q) = ⊴-suc-l (c⁺-≈ e) (c⁺< q) (λ E → adm⁺ {E} q) (c⁺≪ q) (⊴-trans (≈→⊴ (c⁺-≈ e)) (c⁺<⊴ q))
⊴⁺ (l⊑ h) = ⊴-lim-l (λ n → ⊴⁺ (h n))

wf⁺ : ∀ θ → WFˢ (c⁺ θ)
wf⁺ zero = wf₁
wf⁺ (suc a) = wf⁺ a
wf⁺ (lim f s) = (λ n → ⊴⁺ (s n)) , (λ n → wf⁺ (f n))

cf⁺ : ∀ θ → Cfˢ (c⁺ θ)
cf⁺ θ = wf⁺ θ , sf⁺ θ

tc⁺ : ∀ θ → Tc (c⁺ θ)
tc⁺ zero = Tc-Ω₁
tc⁺ (suc a) = tc⁺ a
tc⁺ (lim f s) = λ n → tc⁺ (f n)
```

## §2 高层与低层

`NF a`: $a$ 不是无闭包的层. 节点要么是 $c_1+a'$ (`hi`), 要么是 $\lceil a'\rceil$ (`lo`), 而且是字面的.

```agda
NF : LG → Set
NF a = FrL a → ⊥

NF-c : ∀ a → NF (c⁺ a)
NF-c zero ()
NF-c (suc a) (fs′ h) = NF-c a h
NF-c (lim f s) (fl h) = NF-c (f 0) (h 0)

NF-≈ : ∀ {a b} → a ≈ b → NF b → NF a
NF-≈ e n h = n (Fr≈ h e)

NF-hi : ∀ {a j} → a ≈ c⁺ j → NF a
NF-hi {j = j} e = NF-≈ e (NF-c j)

-- 低层的节点不会 ≈ 高层
lo≠hi : ∀ {a i j} → a ≈ ⌜ i ⌝ → a ≈ c⁺ j → ⊥
lo≠hi {i = i} e d = NF-hi d (Fr≈ (FrG i) (≈-sym e))

data K⁺ (θ : Ordᴵ) (k : LG) : Set where
  hi : ∀ {a} → k ≡ c⁺ a → a <ᴵ θ → K⁺ θ k
  lo : ∀ {a} → k ≡ ⌜ a ⌝ → K⁺ θ k

pull⁺ : ∀ θ {k} → k < c⁺ θ → K⁺ θ k
pull⁺ zero (Lv.fst r) with pullG (suc zero) r
... | a , e , _ = lo e
pull⁺ zero (Lv.bra η e₁ r) with pullG η r
... | a , e , _ = lo e
pull⁺ (suc θ) Lv.zero = hi refl zero
pull⁺ (suc θ) (Lv.suc r) with pull⁺ θ r
... | hi e q = hi e (suc q)
... | lo e = lo e
pull⁺ (lim f s) (Lv.lim n r) with pull⁺ (f n) r
... | hi e q = hi e (lim n q)
... | lo e = lo e

-- 路径的语义: 高层的节点比较
hi-sem : ∀ {t k rp i j} → t ≈ c⁺ i → k ≈ c⁺ j → k ≈ rp → rp < t → j ≺ᴵ i
hi-sem {i = i} et ek d s with ≈-move et s
... | viaᴸ d′ s′ _ with pull⁺ i s′
...   | hi refl q = via (c⁺-≈⁻ (≈-trans (≈-sym ek) (≈-trans d d′))) q
...   | lo refl = ⊥-elim (lo≠hi (≈-trans d d′) ek)
```

## §3 无分支的位置

`Nb P`: 位置不走 `bra`. 高层节点与闭包在 `c⁺ θ` 里的位置都是这样的 (`nb⁺`): 分支里都是无闭包的层. 规范化在这样的位置上是恒等 (`nf-nb`).

```agda
data Nb : ∀ {a b} → Cp a b → Set where
  nself : ∀ {c} → Nb (Lv.self {c = c})
  nsuc  : ∀ {a b} {P : Cp a b} → Nb P → Nb (Lv.suc P)
  nlim  : ∀ {a f n} {P : Cp a (f n)} → Nb P → Nb (Lv.lim {f = f} n P)
  nfst  : ∀ {a c t g} {P : Cp a t} → Nb P → Nb (Lv.fst {c = c} {t = t} {g = g} P)

nb⁺ : ∀ θ {a} (P : Cp a (c⁺ θ)) → NF a → Nb P
nb⁺ zero Lv.self n = nself
nb⁺ zero (Lv.fst P) n = ⊥-elim (n (fr-cp (FrG (suc zero)) P))
nb⁺ zero (Lv.bra η e P) n = ⊥-elim (n (fr-cp (FrG η) P))
nb⁺ (suc θ) Lv.self n = nself
nb⁺ (suc θ) (Lv.suc P) n = nsuc (nb⁺ θ P n)
nb⁺ (lim f s) Lv.self n = nself
nb⁺ (lim f s) (Lv.lim m P) n = nlim (nb⁺ (f m) P n)

NF-lc : ∀ {c t g} → NF (Lv.lc c t g)
NF-lc ()

NF-suc : ∀ {a} → NF a → NF (Lv.suc a)
NF-suc n (fs′ h) = n h

emp-nb : ∀ {a b} {P : Cp a b} → Nb P → ∀ {f} → Mem (pF P) f → ⊥
emp-nb nself ()
emp-nb (nsuc h) m = emp-nb h m
emp-nb (nlim h) m = emp-nb h m
emp-nb (nfst h) m = emp-nb h m

-- 闭包的位置: 键就是 c₁
key⁺ : ∀ θ {c t g} (P : Cp (Lv.lc c t g) (c⁺ θ)) → Lv.lc c t g ≡ c₁
key⁺ zero Lv.self = refl
key⁺ zero (Lv.fst P) = ⊥-elim (NF-lc (fr-cp (FrG (suc zero)) P))
key⁺ zero (Lv.bra η e P) = ⊥-elim (NF-lc (fr-cp (FrG η) P))
key⁺ (suc θ) (Lv.suc P) = key⁺ θ P
key⁺ (lim f s) (Lv.lim n P) = key⁺ (f n) P

-- 规范化是恒等
data NfId {k L} (P : Cp k L) : NfC P → Set where
  ni : ∀ {u r} → NfId P (nfc (inj₂ refl) P u r)

nf-nb : ∀ L (tc : Tc L) {k} {P : Cp k L} → Nb P → NfId P (nfC L tc P)
nf-nb L tc nself = ni
nf-nb (Lv.suc b) tc (nsuc {P = P} h) with nfC b tc P | nf-nb b tc h
... | nfc d Q t r | ni = ni
nf-nb (Lv.lim f) tc (nlim {n = n} {P = P} h) with nfC (f n) (tc n) P | nf-nb (f n) (tc n) h
... | nfc d Q t r | ni = ni
nf-nb (Lv.lc c t g) (rd , tt′ , tg) (nfst {P = P} h) with nfC t tt′ P | nf-nb t tt′ h
... | nfc d Q u r | ni = ni
```

## §4 对低层的路径, 对 `Adm`

```agda
nb-toS : ∀ θ {k} (r : k < c⁺ θ) → NF k → Nb (toCpS r)
nb-toS θ r n = nb⁺ θ (toCpS r) (NF-suc n)

adm-nb : ∀ {E : Src} {a b} {P : Cp a b} → Nb P → AdmC E P
adm-nb nself = tt
adm-nb (nsuc h) = adm-nb h
adm-nb (nlim h) = adm-nb h
adm-nb (nfst h) = adm-nb h
```
