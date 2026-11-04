# 证书 (一): 闭包以下的树与 `Ordˢ` 的互模拟, 带求过值的闭包

> 不含记号. 结论写在 [GuardWeak](GuardWeak.lagda.md). 与 [GuardTightCertRel](GuardTightCertRel.lagda.md) 相同 (由脚本取来), 多三个构造子: `rŝ`, `rĉ`, `rĉŝ`: 第 $j$ 层的值里求过值的闭包 (目标在 $\lceil j\rceil$). 这一层的界只要一个方向 ($c\sqsubseteq c'$), 所以 `Rz` 读到 `≲ᶻ`, 不是 $\cong^{\mathsf z}$. `ZZ A B`: 左边的层是 0 当且仅当右边的层是 0, 这是 `⊕` 与 `addˢ` 按层分派一致的条件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GuardWeakRel where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.GuardTightCum
open import OCF.Free.Prefix using (Z; toZ; Ordˢ; Ord₊ˢ; Uˢ; outˢ; intoˢ; out-intoˢ; coeˢ; addˢ; _+ˢ_; trˢ; tr⁻ˢ; resˢ; res⁻ˢ; Restrˢ; Ωˢ)
open import OCF.Align.GuardBridgeZ using (_≲ᶻ_; zl; sl; ll; ĉl)
open Ord₊ˢ
open Restrˢ
open import OCF.Align.GuardTightLv
open Lv Dom₀ hiding (zero; suc; lim)
open import OCF.Align.GuardTightTab Dom₀ using (Strict; st-suc; st-lim; st-fst; st-bra; stCp; st⊙)
open import OCF.Align.GuardTightBase
open import OCF.Align.GuardTightTree
import OCF.Align.GuardTightUni as Uni
private module U = Uni Dom₀
open U using (rb₀; rb-≈₀₀; em; em-≅)
```

## §1 $\lceil a\rceil$

```agda
⌜_⌝ : Ordᴵ → LG
⌜ a ⌝ = rb₀ (em a)

⌜≈⌝ : ∀ {a b} → a ≅ᴵ b → ⌜ a ⌝ ≈ ⌜ b ⌝
⌜≈⌝ e = rb-≈₀₀ (em-≅ e)

⌜≈⁻⌝ : ∀ {a b} → ⌜ a ⌝ ≈ ⌜ b ⌝ → a ≅ᴵ b
⌜≈⁻⌝ {a = zero} {b = zero} Lv.z≈ = z≅
⌜≈⁻⌝ {a = suc a} {b = suc b} (Lv.s≈ e) = s≅ (⌜≈⁻⌝ e)
⌜≈⁻⌝ {a = lim f s} {b = lim g t} (Lv.l≈ h) = l≅ (λ n → ⌜≈⁻⌝ (h n))

pullG : ∀ a {k} → k < ⌜ a ⌝ → Σ Ordᴵ λ a′ → (k ≡ ⌜ a′ ⌝) × (a′ <ᴵ a)
pullG (suc a) Lv.zero = a , refl , zero
pullG (suc a) (Lv.suc r) with pullG a r
... | a′ , e , q = a′ , e , suc q
pullG (lim f s) (Lv.lim n r) with pullG (f n) r
... | a′ , e , q = a′ , e , lim n q

data FrL : LG → Set where
  fz : FrL Lv.zero
  fs′ : ∀ {b} → FrL b → FrL (Lv.suc b)
  fl : ∀ {f} → (∀ n → FrL (f n)) → FrL (Lv.lim f)

FrG : ∀ a → FrL ⌜ a ⌝
FrG zero = fz
FrG (suc a) = fs′ (FrG a)
FrG (lim f s) = fl (λ n → FrG (f n))

Fr≈ : ∀ {a b} → FrL a → a ≈ b → FrL b
Fr≈ fz Lv.z≈ = fz
Fr≈ (fs′ h) (Lv.s≈ e) = fs′ (Fr≈ h e)
Fr≈ (fl h) (Lv.l≈ e) = fl (λ n → Fr≈ (h n) (e n))

-- 比较的语义
cb-sem : ∀ {t k rp i j} → t ≈ ⌜ i ⌝ → k ≈ ⌜ j ⌝ → k ≈ rp → rp < t → j ≺ᴵ i
cb-sem {i = i} et ek d s with ≈-move et s
... | viaᴸ d′ s′ _ with pullG i s′
... | a′ , refl , q = via (⌜≈⁻⌝ (≈-trans (≈-sym ek) (≈-trans d d′))) q

cu-sem : ∀ {t k i j} → t ≈ ⌜ i ⌝ → k ≈ ⌜ j ⌝ → (t ≈ k ⊎ Below t k) → (i ≺ᴵ j) ⊎ (i ≅ᴵ j)
cu-sem et ek (inj₁ d) = inj₂ (⌜≈⁻⌝ (≈-trans (≈-sym et) (≈-trans d ek)))
cu-sem {j = j} et ek (inj₂ (pre d s)) with ≈-move ek s
... | viaᴸ d′ s′ _ with pullG j s′
... | a′ , refl , q = inj₁ (via (⌜≈⁻⌝ (≈-trans (≈-sym et) (≈-trans d d′))) q)

clash : ∀ {i j} → j ≺ᴵ i → (i ≺ᴵ j) ⊎ (i ≅ᴵ j) → ⊥
clash s (inj₁ t) = ≺ᴵ-irrefl (≺ᴵ-trans s t)
clash s (inj₂ c) = ≺ᴵ-irrefl (≺ᴵ-respʳ s c)
```

## §2 关系

```agda
Emp : Fl → Set
Emp ξ = ∀ {f} → Mem ξ f → ⊥

ZZ : LG → Ordᴵ → Set
ZZ Lv.zero zero = ⊤
ZZ Lv.zero (suc _) = ⊥
ZZ Lv.zero (lim _ _) = ⊥
ZZ (Lv.suc _) zero = ⊥
ZZ (Lv.lim _) zero = ⊥
ZZ (Lv.lc _ _ _) zero = ⊥
ZZ (Lv.suc _) (suc _) = ⊤
ZZ (Lv.suc _) (lim _ _) = ⊤
ZZ (Lv.lim _) (suc _) = ⊤
ZZ (Lv.lim _) (lim _ _) = ⊤
ZZ (Lv.lc _ _ _) (suc _) = ⊤
ZZ (Lv.lc _ _ _) (lim _ _) = ⊤

zz-≈ : ∀ {A A′ B} → A ≈ A′ → ZZ A B → ZZ A′ B
zz-≈ {B = zero} Lv.z≈ z = z
zz-≈ {B = suc _} (Lv.s≈ _) z = z
zz-≈ {B = lim _ _} (Lv.s≈ _) z = z
zz-≈ {B = zero} (Lv.s≈ _) ()
zz-≈ {B = zero} (Lv.l≈ _) ()
zz-≈ {B = suc _} (Lv.l≈ _) z = z
zz-≈ {B = lim _ _} (Lv.l≈ _) z = z
zz-≈ {B = zero} (Lv.o≈ _ _ _) ()
zz-≈ {B = suc _} (Lv.o≈ _ _ _) z = z
zz-≈ {B = lim _ _} (Lv.o≈ _ _ _) z = z
zz-≈ {B = suc _} Lv.z≈ ()
zz-≈ {B = lim _ _} Lv.z≈ ()

zz-≅ : ∀ {A a b} → a ≅ᴵ b → ZZ A a → ZZ A b
zz-≅ {Lv.zero} z≅ z = z
zz-≅ {Lv.suc _} (s≅ _) z = z
zz-≅ {Lv.suc _} (l≅ _) z = z
zz-≅ {Lv.lim _} (s≅ _) z = z
zz-≅ {Lv.lim _} (l≅ _) z = z
zz-≅ {Lv.lc _ _ _} (s≅ _) z = z
zz-≅ {Lv.lc _ _ _} (l≅ _) z = z

ZB : Ordᴵ → Set
ZB zero = ⊤
ZB (suc _) = ⊥
ZB (lim _ _) = ⊥

tzb : ∀ {B} → ZB B → Ordˢ B → Z
tzb {B = zero} _ x = toZ x

zb-≅ : ∀ {a b} → a ≅ᴵ b → ZB a → ZB b
zb-≅ z≅ z = z

module _ (B : Ordᴵ) (LR : ∀ {i} → i ◃ B → ∀ {A ξ} → O A ξ → Ordˢ i → Set) where
  data R₊ : ∀ {A π} → O A π → Ordˢ B → Set where
    rz  : ∀ {A π} → R₊ {A} {π} o0 zero
    rs  : ∀ {A π} {x : O A π} {ŷ} → R₊ x ŷ → R₊ (os x) (suc ŷ)
    rl  : ∀ {A π} {F : ℕ → O A π} {f} → (∀ n → R₊ (F n) (f n)) → R₊ (ol F) (lim f)
    rwk : ∀ {A π ρ} {w : Wk π ρ} {x : O A π} {ŷ} → R₊ x ŷ → R₊ (owk w x) ŷ
    rcv : ∀ {A π ρ} {w : Cov π ρ} {x : O A π} {ŷ} → R₊ x ŷ → R₊ (ocv w x) ŷ
    rmk : ∀ {A π ξ k₁ k} {R : Strict k₁ A} {lk : Wk ξ π} {ad : AdmC (cov π) (stCp R)} {z : Vs A R ξ} {x : O A π}
            (r : k ◃₁ B) {ŷ′ : Uˢ k (◃₁→◃ r)} →
            LR (◃₁→◃ r) (outV R z) (outˢ (◃₁→◃ r) ŷ′) → R₊ x (up r ŷ′) → R₊ (omk R lk ad z x) (up r ŷ′)
    rup : ∀ {A π k} {x : O A π} (r : k ◃₁ B) {ŷ′ : Uˢ k (◃₁→◃ r)} → LR (◃₁→◃ r) x (outˢ (◃₁→◃ r) ŷ′) → R₊ x (up r ŷ′)
    rΩ  : ∀ {A π k j} (r : k < A) (cv : Adm (cov π) r) (q : j <ᴵ B) {h : ∀ ξ → Us A r ξ → O A (ξ ∪ π)} {f : Uˢ j (<→◃ q) → Ordˢ B} →
          k ≈ ⌜ j ⌝ →
          (∀ ξ → Emp ξ → (z : O k ξ) (ẑ : Ordˢ j) → LR (<→◃ q) z ẑ → R₊ (h ξ (intoU r z)) (f (intoˢ (<→◃ q) ẑ))) →
          R₊ (oΩ r cv h) (limᵢ q f)
    rŝ  : ∀ {A π c₀ c′} {t : O A π} {g : ∀ η → c₀ ⊑ᴵ η → O A π} {t̂ : Ordˢ B} {ĝ : ∀ η → c′ ⊑ᴵ η → Ordˢ B} →
          ZZ A B → c₀ ⊑ᴵ c′ → R₊ t t̂ → (∀ η e e′ → R₊ (g η e) (ĝ η e′)) → R₊ (oŝ c₀ t g) (ŝ c′ t̂ ĝ)
    rĉ  : ∀ {A π c₀ c′ z ẑ} {zg : ∀ η → c₀ ⊑ᴵ η → Z} {ẑg : ∀ η → c′ ⊑ᴵ η → Z} {o₀ : O A π} {o : ∀ η → c₀ ⊑ᴵ η → O A π} {ô₀ : Ordˢ B} {ô : ∀ η → c′ ⊑ᴵ η → Ordˢ B} →
          c₀ ⊑ᴵ c′ → z ≲ᶻ ẑ → (∀ η e e′ → zg η e ≲ᶻ ẑg η e′) → R₊ o₀ ô₀ → (∀ η e e′ → R₊ (o η e) (ô η e′)) → R₊ (oĉ c₀ z zg o₀ o) (ĉᴸ c′ ẑ ẑg ô₀ ô)
    rĉŝ : ∀ {A π π′ c₀ c′} {t₀ : O Lv.zero π′} {g₀ : ∀ η → c₀ ⊑ᴵ η → O Lv.zero π′} {o₀ : O A π} {o : ∀ η → c₀ ⊑ᴵ η → O A π} {t̂ : Ordˢ B} {ĝ : ∀ η → c′ ⊑ᴵ η → Ordˢ B} →
          ZB B → c₀ ⊑ᴵ c′ → R₊ t₀ t̂ → (∀ η e e′ → R₊ (g₀ η e) (ĝ η e′)) → R₊ o₀ t̂ → (∀ η e e′ → R₊ (o η e) (ĝ η e′)) →
          R₊ (oĉ c₀ (rdZ t₀) (λ η e → rdZ (g₀ η e)) o₀ o) (ŝ c′ t̂ ĝ)

Rs : ∀ B {A π} → O A π → Ordˢ B → Set
LRs : ∀ B {i} → i ◃ B → ∀ {A ξ} → O A ξ → Ordˢ i → Set
Rs B x y = R₊ B (LRs B) x y
LRs (suc k)   zero      x y = Rs k x y
LRs (suc c)   (suc r)   x y = LRs c r x y
LRs (lim f s) (self n)  x y = Rs (f n) x y
LRs (lim f s) (lim n r) x y = LRs (f n) r x y

outR : ∀ {c k} (r : k ◃ c) {A ξ} {z : O A ξ} {ẑ : Ordˢ k} → LRs c r z ẑ → Rs k z ẑ
outR zero      l = l
outR (suc r)   l = outR r l
outR (self n)  l = l
outR (lim n r) l = outR r l

intoR : ∀ {c k} (r : k ◃ c) {A ξ} {z : O A ξ} {ẑ : Ordˢ k} → Rs k z ẑ → LRs c r z ẑ
intoR zero      l = l
intoR (suc r)   l = intoR r l
intoR (self n)  l = l
intoR (lim n r) l = intoR r l

out-intoU : ∀ {L k} (r : k < L) {ξ} (z : O k ξ) → outU r (intoU r z) ≡ z
out-intoU Lv.zero        z = refl
out-intoU (Lv.suc r)     z = out-intoU r z
out-intoU (Lv.lim n r)   z = out-intoU r z
out-intoU (Lv.fst r)     z = out-intoU r z
out-intoU (Lv.bra η e r) z = out-intoU r z
```

## §2′ 第 0 层, 读成 `Z`

```agda
Rz : ∀ {π} {y : O Lv.zero π} {ŷ : Ordˢ zero} → Rs zero y ŷ → rdZ y ≲ᶻ toZ ŷ
Rz rz = zl
Rz (rs r) = sl (Rz r)
Rz (rl h) = ll (λ n → Rz (h n))
Rz (rwk {π = π′} {x = x} r) = Rz {π′} {x} r
Rz (rcv {π = π′} {x = x} r) = Rz {π′} {x} r
Rz (rmk () l r)
Rz (rup () l)
Rz (rΩ () cv q d h)
Rz (rŝ z ec rt rg) = ĉl ec (Rz rt) (λ η e e′ → Rz (rg η e e′)) (Rz rt) (λ η e e′ → Rz (rg η e e′))
Rz (rĉ ec dz dg ro rg) = ĉl ec dz dg (Rz ro) (λ η e e′ → Rz (rg η e e′))
Rz (rĉŝ tt ec rt rg₀ ro rg) = ĉl ec (Rz rt) (λ η e e′ → Rz (rg₀ η e e′)) (Rz ro) (λ η e e′ → Rz (rg η e e′))
```

## §3 加法

```agda
R-⊕ : ∀ {A φ ψ k ℓ} {W : O A φ} {t : O A ψ} {Ŵ : Ordˢ ℓ} {σ : Simᴵ k ℓ} {t̂ : Ordˢ k} → ZZ A ℓ → Rs ℓ W Ŵ → Rs k t t̂ → Rs ℓ (W ⊕ t) (addˢ Ŵ σ t̂)
R-⊕ zz rW rz = rwk rW
R-⊕ zz rW (rs r) = rs (R-⊕ zz rW r)
R-⊕ zz rW (rl h) = rl (λ n → R-⊕ zz rW (h n))
R-⊕ zz rW (rwk r) = rwk (R-⊕ zz rW r)
R-⊕ zz rW (rcv r) = rcv (R-⊕ zz rW r)
R-⊕ zz rW (rmk zero l r) = R-⊕ zz rW r
R-⊕ zz rW (rmk (self n) l r) = R-⊕ zz rW r
R-⊕ zz rW (rup zero l) = R-⊕ zz rW l
R-⊕ zz rW (rup (self n) l) = R-⊕ zz rW l
R-⊕ {ℓ = ℓ} {Ŵ = Ŵ} {σ = σ} zz rW (rΩ r cv q {f = f} d h) =
  rΩ r _ (σ q) d (λ ξ em′ z ẑ l → rwk (subst (λ u → Rs ℓ (_ ⊕ _) (addˢ Ŵ σ (f (intoˢ (<→◃ q) u))))
                                         (sym (out-intoˢ (<→◃ (σ q)) ẑ))
                                         (R-⊕ zz rW (h ξ em′ z ẑ (intoR (<→◃ q) (outR (<→◃ (σ q)) l))))))
R-⊕ {A = Lv.zero} {k = zero} zz rW (rŝ tt ec rt rg) = rĉ ec (Rz rt) (λ η e e′ → Rz (rg η e e′)) (R-⊕ zz rW rt) (λ η e e′ → R-⊕ zz rW (rg η e e′))
R-⊕ {A = Lv.suc _} {k = suc _} zz rW (rŝ z ec rt rg) = rŝ zz ec (R-⊕ zz rW rt) (λ η e e′ → R-⊕ zz rW (rg η e e′))
R-⊕ {A = Lv.suc _} {k = lim _ _} zz rW (rŝ z ec rt rg) = rŝ zz ec (R-⊕ zz rW rt) (λ η e e′ → R-⊕ zz rW (rg η e e′))
R-⊕ {A = Lv.lim _} {k = suc _} zz rW (rŝ z ec rt rg) = rŝ zz ec (R-⊕ zz rW rt) (λ η e e′ → R-⊕ zz rW (rg η e e′))
R-⊕ {A = Lv.lim _} {k = lim _ _} zz rW (rŝ z ec rt rg) = rŝ zz ec (R-⊕ zz rW rt) (λ η e e′ → R-⊕ zz rW (rg η e e′))
R-⊕ {A = Lv.lc _ _ _} {k = suc _} zz rW (rŝ z ec rt rg) = rŝ zz ec (R-⊕ zz rW rt) (λ η e e′ → R-⊕ zz rW (rg η e e′))
R-⊕ {A = Lv.lc _ _ _} {k = lim _ _} zz rW (rŝ z ec rt rg) = rŝ zz ec (R-⊕ zz rW rt) (λ η e e′ → R-⊕ zz rW (rg η e e′))
R-⊕ {A = Lv.zero} {k = suc _} zz rW (rŝ () ec rt rg)
R-⊕ {A = Lv.zero} {k = lim _ _} zz rW (rŝ () ec rt rg)
R-⊕ {A = Lv.suc _} {k = zero} zz rW (rŝ () ec rt rg)
R-⊕ {A = Lv.lim _} {k = zero} zz rW (rŝ () ec rt rg)
R-⊕ {A = Lv.lc _ _ _} {k = zero} zz rW (rŝ () ec rt rg)
R-⊕ zz rW (rĉ ec dz dg ro rg) = rĉ ec dz dg (R-⊕ zz rW ro) (λ η e e′ → R-⊕ zz rW (rg η e e′))
R-⊕ {k = zero} zz rW (rĉŝ tt ec rt rg₀ ro rg) = rĉ ec (Rz rt) (λ η e e′ → Rz (rg₀ η e e′)) (R-⊕ zz rW ro) (λ η e e′ → R-⊕ zz rW (rg η e e′))
```

## §4 搬运

左边 (`trO`, `tr⁻O`): 对 `≈` 与推导字典序递归. 右边 (`trˢ`, `tr⁻ˢ`): 对 `≅ᴵ` 与推导字典序递归.

```agda
BkOK : ∀ {k a b} {r : k < a} → RestrO r b → Set
BkOK w = ∀ {B ξ} {z : O (repO w) ξ} {ẑ : Ordˢ B} → Rs B z ẑ → Rs B (backO w z) ẑ

R-trO  : ∀ {B A A′ π} (e : A ≈ A′) {x : O A π} {ŷ : Ordˢ B} → Rs B x ŷ → Rs B (trO e x) ŷ
R-tr⁻O : ∀ {B A A′ π} (e : A ≈ A′) {x : O A′ π} {ŷ : Ordˢ B} → Rs B x ŷ → Rs B (tr⁻O e x) ŷ
R-bk   : ∀ {k A A′} (q : k < A) (e : A ≈ A′) → BkOK (resO q e)
R-bk⁻  : ∀ {k A A′} (q : k < A′) (e : A ≈ A′) → BkOK (res⁻O q e)
R-trC  : ∀ {B k A A′ ξ} (P : Cp k A) (e : A ≈ A′) (z : Vc A P ξ) {ẑ : Ordˢ B} → Rs B (outC P z) ẑ → Rs B (outC (posC (trC P e z)) (valC (trC P e z))) ẑ
R-tr⁻C : ∀ {B k A A′ ξ} (P : Cp k A′) (e : A ≈ A′) (z : Vc A′ P ξ) {ẑ : Ordˢ B} → Rs B (outC P z) ẑ → Rs B (outC (posC (tr⁻C P e z)) (valC (tr⁻C P e z))) ẑ
R-trV  : ∀ {B k A A′ ξ} (R : Strict k A) (e : A ≈ A′) (z : Vs A R ξ) {ẑ : Ordˢ B} → Rs B (outV R z) ẑ → Rs B (outV (posW (trV R e z)) (valW (trV R e z))) ẑ
R-tr⁻V : ∀ {B k A A′ ξ} (R : Strict k A′) (e : A ≈ A′) (z : Vs A′ R ξ) {ẑ : Ordˢ B} → Rs B (outV R z) ẑ → Rs B (outV (posW (tr⁻V R e z)) (valW (tr⁻V R e z))) ẑ

R-trO e rz = rz
R-trO e (rs r) = rs (R-trO e r)
R-trO e (rl h) = rl (λ n → R-trO e (h n))
R-trO e (rwk r) = rwk (R-trO e r)
R-trO e (rcv r) = rcv (R-trO e r)
R-trO e (rmk {R = R} {z = z} zero l r) with trV R e z | R-trV R e z l
... | restrV R′ u z′ | l′ = rmk zero l′ (R-trO e r)
R-trO e (rmk {R = R} {z = z} (self n) l r) with trV R e z | R-trV R e z l
... | restrV R′ u z′ | l′ = rmk (self n) l′ (R-trO e r)
R-trO e (rup zero l) = rup zero (R-trO e l)
R-trO e (rup (self n) l) = rup (self n) (R-trO e l)
R-trO {B = B} e (rΩ r cv q {h = h₁} {f = f} d h) =
  rΩ (ltO (resO r e)) _ q (≈-trans (≈-sym (eqO (resO r e))) d)
     (λ ξ em′ z ẑ l → R-trO e (subst (λ u → Rs B (h₁ ξ (intoU r (backO (resO r e) u))) (f (intoˢ (<→◃ q) ẑ))) (sym (out-intoU (ltO (resO r e)) z))
                                     (h ξ em′ _ ẑ (intoR (<→◃ q) (R-bk r e (outR (<→◃ q) l))))))
R-trO e (rŝ z ec rt rg) = rŝ (zz-≈ e z) ec (R-trO e rt) (λ η d d′ → R-trO e (rg η d d′))
R-trO e (rĉ ec dz dg ro rg) = rĉ ec dz dg (R-trO e ro) (λ η d d′ → R-trO e (rg η d d′))
R-trO e (rĉŝ zb ec rt rg₀ ro rg) = rĉŝ zb ec rt rg₀ (R-trO e ro) (λ η d d′ → R-trO e (rg η d d′))

R-tr⁻O e rz = rz
R-tr⁻O e (rs r) = rs (R-tr⁻O e r)
R-tr⁻O e (rl h) = rl (λ n → R-tr⁻O e (h n))
R-tr⁻O e (rwk r) = rwk (R-tr⁻O e r)
R-tr⁻O e (rcv r) = rcv (R-tr⁻O e r)
R-tr⁻O e (rmk {R = R} {z = z} zero l r) with tr⁻V R e z | R-tr⁻V R e z l
... | restrV R′ u z′ | l′ = rmk zero l′ (R-tr⁻O e r)
R-tr⁻O e (rmk {R = R} {z = z} (self n) l r) with tr⁻V R e z | R-tr⁻V R e z l
... | restrV R′ u z′ | l′ = rmk (self n) l′ (R-tr⁻O e r)
R-tr⁻O e (rup zero l) = rup zero (R-tr⁻O e l)
R-tr⁻O e (rup (self n) l) = rup (self n) (R-tr⁻O e l)
R-tr⁻O {B = B} e (rΩ r cv q {h = h₁} {f = f} d h) =
  rΩ (ltO (res⁻O r e)) _ q (≈-trans (≈-sym (eqO (res⁻O r e))) d)
     (λ ξ em′ z ẑ l → R-tr⁻O e (subst (λ u → Rs B (h₁ ξ (intoU r (backO (res⁻O r e) u))) (f (intoˢ (<→◃ q) ẑ))) (sym (out-intoU (ltO (res⁻O r e)) z))
                                      (h ξ em′ _ ẑ (intoR (<→◃ q) (R-bk⁻ r e (outR (<→◃ q) l))))))
R-tr⁻O e (rŝ z ec rt rg) = rŝ (zz-≈ (≈-sym e) z) ec (R-tr⁻O e rt) (λ η d d′ → R-tr⁻O e (rg η d d′))
R-tr⁻O e (rĉ ec dz dg ro rg) = rĉ ec dz dg (R-tr⁻O e ro) (λ η d d′ → R-tr⁻O e (rg η d d′))
R-tr⁻O e (rĉŝ zb ec rt rg₀ ro rg) = rĉŝ zb ec rt rg₀ (R-tr⁻O e ro) (λ η d d′ → R-tr⁻O e (rg η d d′))

R-bk Lv.zero (Lv.s≈ e) = R-tr⁻O e
R-bk (Lv.suc r) (Lv.s≈ e) with resO r e | R-bk r e
... | restrO d m t b | H = H
R-bk (Lv.lim n r) (Lv.l≈ h) with resO r (h n) | R-bk r (h n)
... | restrO d m t b | H = H
R-bk (Lv.fst r) (Lv.o≈ d′ e h) with resO r e | R-bk r e
... | restrO d m t b | H = H
R-bk (Lv.bra η e₁ r) (Lv.o≈ d′ e h) with resO r (h η e₁ η (conv d′ e₁) (≅ᴰ-refl η)) | R-bk r (h η e₁ η (conv d′ e₁) (≅ᴰ-refl η))
... | restrO d m t b | H = H

R-bk⁻ Lv.zero (Lv.s≈ e) = R-trO e
R-bk⁻ (Lv.suc r) (Lv.s≈ e) with res⁻O r e | R-bk⁻ r e
... | restrO d m t b | H = H
R-bk⁻ (Lv.lim n r) (Lv.l≈ h) with res⁻O r (h n) | R-bk⁻ r (h n)
... | restrO d m t b | H = H
R-bk⁻ (Lv.fst r) (Lv.o≈ d′ e h) with res⁻O r e | R-bk⁻ r e
... | restrO d m t b | H = H
R-bk⁻ (Lv.bra η e₁ r) (Lv.o≈ d′ e h) with res⁻O r (h η (conv (≅ᴰ-sym d′) e₁) η e₁ (≅ᴰ-refl η)) | R-bk⁻ r (h η (conv (≅ᴰ-sym d′) e₁) η e₁ (≅ᴰ-refl η))
... | restrO d m t b | H = H

R-trC Lv.self e z l = R-trO e l
R-trC (Lv.suc P) (Lv.s≈ e) z l with trC P e z | R-trC P e z l
... | restrC Q u z′ | l′ = l′
R-trC (Lv.lim n P) (Lv.l≈ h) z l with trC P (h n) z | R-trC P (h n) z l
... | restrC Q u z′ | l′ = l′
R-trC (Lv.fst P) (Lv.o≈ d e h) z l with trC P e z | R-trC P e z l
... | restrC Q u z′ | l′ = l′
R-trC (Lv.bra η e₁ P) (Lv.o≈ d e h) z l with trC P (h η e₁ η (conv d e₁) (≅ᴰ-refl η)) z | R-trC P (h η e₁ η (conv d e₁) (≅ᴰ-refl η)) z l
... | restrC Q u z′ | l′ = l′

R-tr⁻C Lv.self e z l = R-tr⁻O e l
R-tr⁻C (Lv.suc P) (Lv.s≈ e) z l with tr⁻C P e z | R-tr⁻C P e z l
... | restrC Q u z′ | l′ = l′
R-tr⁻C (Lv.lim n P) (Lv.l≈ h) z l with tr⁻C P (h n) z | R-tr⁻C P (h n) z l
... | restrC Q u z′ | l′ = l′
R-tr⁻C (Lv.fst P) (Lv.o≈ d e h) z l with tr⁻C P e z | R-tr⁻C P e z l
... | restrC Q u z′ | l′ = l′
R-tr⁻C (Lv.bra η e₁ P) (Lv.o≈ d e h) z l with tr⁻C P (h η (conv (≅ᴰ-sym d) e₁) η e₁ (≅ᴰ-refl η)) z | R-tr⁻C P (h η (conv (≅ᴰ-sym d) e₁) η e₁ (≅ᴰ-refl η)) z l
... | restrC Q u z′ | l′ = l′

R-trV (st-suc P) (Lv.s≈ e) z l with trC P e z | R-trC P e z l
... | restrC Q u z′ | l′ = l′
R-trV (st-lim n P) (Lv.l≈ h) z l with trC P (h n) z | R-trC P (h n) z l
... | restrC Q u z′ | l′ = l′
R-trV (st-fst P) (Lv.o≈ d e h) z l with trC P e z | R-trC P e z l
... | restrC Q u z′ | l′ = l′
R-trV (st-bra η e₁ P) (Lv.o≈ d e h) z l with trC P (h η e₁ η (conv d e₁) (≅ᴰ-refl η)) z | R-trC P (h η e₁ η (conv d e₁) (≅ᴰ-refl η)) z l
... | restrC Q u z′ | l′ = l′

R-tr⁻V (st-suc P) (Lv.s≈ e) z l with tr⁻C P e z | R-tr⁻C P e z l
... | restrC Q u z′ | l′ = l′
R-tr⁻V (st-lim n P) (Lv.l≈ h) z l with tr⁻C P (h n) z | R-tr⁻C P (h n) z l
... | restrC Q u z′ | l′ = l′
R-tr⁻V (st-fst P) (Lv.o≈ d e h) z l with tr⁻C P e z | R-tr⁻C P e z l
... | restrC Q u z′ | l′ = l′
R-tr⁻V (st-bra η e₁ P) (Lv.o≈ d e h) z l with tr⁻C P (h η (conv (≅ᴰ-sym d) e₁) η e₁ (≅ᴰ-refl η)) z | R-tr⁻C P (h η (conv (≅ᴰ-sym d) e₁) η e₁ (≅ᴰ-refl η)) z l
... | restrC Q u z′ | l′ = l′

R-trL⁻ : ∀ {B A A′ π} (d : Lk A A′) {x : O A′ π} {ŷ : Ordˢ B} → Rs B x ŷ → Rs B (trL⁻ d x) ŷ
R-trL⁻ (inj₁ e) r = R-tr⁻O e r
R-trL⁻ (inj₂ refl) r = r

R-trL : ∀ {B A A′ π} (d : Lk A A′) {x : O A π} {ŷ : Ordˢ B} → Rs B x ŷ → Rs B (trL d x) ŷ
R-trL (inj₁ e) r = R-trO e r
R-trL (inj₂ refl) r = r
```

**右边.** `Ordˢ` 上的搬运.

```agda
R-trˢ  : ∀ {a b A π} (e : a ≅ᴵ b) {x : O A π} {ŷ : Ordˢ a} → Rs a x ŷ → Rs b x (trˢ e ŷ)
R-tr⁻ˢ : ∀ {a b A π} (e : a ≅ᴵ b) {x : O A π} {ŷ : Ordˢ b} → Rs b x ŷ → Rs a x (tr⁻ˢ e ŷ)
R-bkˢ  : ∀ {j a b A ξ} (q : j <ᴵ a) (e : a ≅ᴵ b) {z : O A ξ} {ẑ : Ordˢ (repˢ (resˢ q e))} → Rs (repˢ (resˢ q e)) z ẑ → Rs j z (backˢ (resˢ q e) ẑ)
R-bk⁻ˢ : ∀ {j a b A ξ} (q : j <ᴵ b) (e : a ≅ᴵ b) {z : O A ξ} {ẑ : Ordˢ (repˢ (res⁻ˢ q e))} → Rs (repˢ (res⁻ˢ q e)) z ẑ → Rs j z (backˢ (res⁻ˢ q e) ẑ)

R-trˢ e rz = rz
R-trˢ e (rs r) = rs (R-trˢ e r)
R-trˢ e (rl h) = rl (λ n → R-trˢ e (h n))
R-trˢ e (rwk r) = rwk (R-trˢ e r)
R-trˢ e (rcv r) = rcv (R-trˢ e r)
R-trˢ (s≅ e) (rmk zero l r) = rmk zero (R-trˢ e l) (R-trˢ (s≅ e) r)
R-trˢ (l≅ h) (rmk (self n) l r) = rmk (self n) (R-trˢ (h n) l) (R-trˢ (l≅ h) r)
R-trˢ (s≅ e) (rup zero l) = rup zero (R-trˢ e l)
R-trˢ (l≅ h) (rup (self n) l) = rup (self n) (R-trˢ (h n) l)
R-trˢ {b = b} e (rΩ r cv q {h = h₁} {f = f} d h) =
  rΩ r cv (ltˢ (resˢ q e)) (≈-trans d (⌜≈⌝ (eqˢ (resˢ q e))))
     (λ ξ em′ z ẑ l → subst (λ u → Rs b (h₁ ξ (intoU r z)) (trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) u))))) (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) ẑ))
                             (R-trˢ e (h ξ em′ z _ (intoR (<→◃ q) (R-bkˢ q e (outR (<→◃ (ltˢ (resˢ q e))) l))))))
R-trˢ e (rŝ z ec rt rg) = rŝ (zz-≅ e z) ec (R-trˢ e rt) (λ η d d′ → R-trˢ e (rg η d d′))
R-trˢ e (rĉ ec dz dg ro rg) = rĉ ec dz dg (R-trˢ e ro) (λ η d d′ → R-trˢ e (rg η d d′))
R-trˢ e (rĉŝ zb ec rt rg₀ ro rg) = rĉŝ (zb-≅ e zb) ec (R-trˢ e rt) (λ η d d′ → R-trˢ e (rg₀ η d d′)) (R-trˢ e ro) (λ η d d′ → R-trˢ e (rg η d d′))

R-tr⁻ˢ e rz = rz
R-tr⁻ˢ e (rs r) = rs (R-tr⁻ˢ e r)
R-tr⁻ˢ e (rl h) = rl (λ n → R-tr⁻ˢ e (h n))
R-tr⁻ˢ e (rwk r) = rwk (R-tr⁻ˢ e r)
R-tr⁻ˢ e (rcv r) = rcv (R-tr⁻ˢ e r)
R-tr⁻ˢ (s≅ e) (rmk zero l r) = rmk zero (R-tr⁻ˢ e l) (R-tr⁻ˢ (s≅ e) r)
R-tr⁻ˢ (l≅ h) (rmk (self n) l r) = rmk (self n) (R-tr⁻ˢ (h n) l) (R-tr⁻ˢ (l≅ h) r)
R-tr⁻ˢ (s≅ e) (rup zero l) = rup zero (R-tr⁻ˢ e l)
R-tr⁻ˢ (l≅ h) (rup (self n) l) = rup (self n) (R-tr⁻ˢ (h n) l)
R-tr⁻ˢ {a = a} e (rΩ r cv q {h = h₁} {f = f} d h) =
  rΩ r cv (ltˢ (res⁻ˢ q e)) (≈-trans d (⌜≈⌝ (eqˢ (res⁻ˢ q e))))
     (λ ξ em′ z ẑ l → subst (λ u → Rs a (h₁ ξ (intoU r z)) (tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) u))))) (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) ẑ))
                             (R-tr⁻ˢ e (h ξ em′ z _ (intoR (<→◃ q) (R-bk⁻ˢ q e (outR (<→◃ (ltˢ (res⁻ˢ q e))) l))))))
R-tr⁻ˢ e (rŝ z ec rt rg) = rŝ (zz-≅ (≅ᴵ-sym e) z) ec (R-tr⁻ˢ e rt) (λ η d d′ → R-tr⁻ˢ e (rg η d d′))
R-tr⁻ˢ e (rĉ ec dz dg ro rg) = rĉ ec dz dg (R-tr⁻ˢ e ro) (λ η d d′ → R-tr⁻ˢ e (rg η d d′))
R-tr⁻ˢ e (rĉŝ zb ec rt rg₀ ro rg) = rĉŝ (zb-≅ (≅ᴵ-sym e) zb) ec (R-tr⁻ˢ e rt) (λ η d d′ → R-tr⁻ˢ e (rg₀ η d d′)) (R-tr⁻ˢ e ro) (λ η d d′ → R-tr⁻ˢ e (rg η d d′))

R-bkˢ zero (s≅ e) l = R-tr⁻ˢ e l
R-bkˢ (suc q) (s≅ e) l = R-bkˢ q e l
R-bkˢ (lim n q) (l≅ h) l = R-bkˢ q (h n) l

R-bk⁻ˢ zero (s≅ e) l = R-trˢ e l
R-bk⁻ˢ (suc q) (s≅ e) l = R-bk⁻ˢ q e l
R-bk⁻ˢ (lim n q) (l≅ h) l = R-bk⁻ˢ q (h n) l
```

## §5 嵌入, $\dot\Omega$

`R-ι`: 嵌入不改对面的树. `omk` 的一行: 输入的 $z$ 与对面的 $\hat y'$ 有关系, 输出的 $x$ 是 $z$ 嵌到规范位置, 所以记号的两半都还在.

```agda
out-intoC : ∀ {L k} (P : Cp k L) {ξ} (z : O k ξ) → outC P (intoC P z) ≡ z
out-intoC Lv.self z = refl
out-intoC (Lv.suc P) z = out-intoC P z
out-intoC (Lv.lim n P) z = out-intoC P z
out-intoC (Lv.fst P) z = out-intoC P z
out-intoC (Lv.bra η e P) z = out-intoC P z

out-intoV : ∀ {L k} (R : Strict k L) {ξ} (z : O k ξ) → outV R (intoV R z) ≡ z
out-intoV (st-suc P) z = out-intoC P z
out-intoV (st-lim n P) z = out-intoC P z
out-intoV (st-fst P) z = out-intoC P z
out-intoV (st-bra η e P) z = out-intoC P z

cv-into : ∀ {k a b} (P : Cp a b) (s : k < a) {ξ} (z : O k ξ) → outU s (cvP P s (intoU (P ◁ s) z)) ≡ z
cv-into Lv.self s z = out-intoU s z
cv-into (Lv.suc P) s z = cv-into P s z
cv-into (Lv.lim n P) s z = cv-into P s z
cv-into (Lv.fst P) s z = cv-into P s z
cv-into (Lv.bra η e P) s z = cv-into P s z

lk≈ : ∀ {k rep j} → Lk k rep → k ≈ ⌜ j ⌝ → rep ≈ ⌜ j ⌝
lk≈ (inj₁ e) d = ≈-trans (≈-sym e) d
lk≈ (inj₂ refl) d = d

BLOK : ∀ {k a b} {r : k < a} → RL r b → Set
BLOK w = ∀ {B ξ} {z : O (repL w) ξ} {ẑ : Ordˢ B} → Rs B z ẑ → Rs B (backL w z) ẑ

R-bL : ∀ {k a b} (r : k < a) (d : Lk a b) → BLOK (resL r d)
R-bL r (inj₁ e) with resO r e | R-bk r e
... | restrO d′ l t b | H = H
R-bL r (inj₂ refl) = λ l → l

ZNL : LG → Set
ZNL Lv.zero = ⊥
ZNL (Lv.suc _) = ⊤
ZNL (Lv.lim _) = ⊤
ZNL (Lv.lc _ _ _) = ⊤

zz-any : ∀ {L B} → ZNL L → (B ≅ᴵ zero → ⊥) → ZZ L B
zz-any {Lv.suc _} {B = zero} n b = b z≅
zz-any {Lv.suc _} {suc _} n b = tt
zz-any {Lv.suc _} {lim _ _} n b = tt
zz-any {Lv.lim _} {B = zero} n b = b z≅
zz-any {Lv.lim _} {suc _} n b = tt
zz-any {Lv.lim _} {lim _ _} n b = tt
zz-any {Lv.lc _ _ _} {B = zero} n b = b z≅
zz-any {Lv.lc _ _ _} {suc _} n b = tt
zz-any {Lv.lc _ _ _} {lim _ _} n b = tt

zz-nz : ∀ {a B} → ZNL a → ZZ a B → B ≅ᴵ zero → ⊥
zz-nz {Lv.suc _} n () z≅
zz-nz {Lv.lim _} n () z≅
zz-nz {Lv.lc _ _ _} n () z≅

zz-cp₁ : ∀ {a a′ L B} → Lk a a′ → ZZ a B → {n : ZNL a} → Cp a′ L → ZZ L B
zz-cp₁ (inj₂ refl) z Lv.self = z
zz-cp₁ (inj₁ d) z Lv.self = zz-≈ d z
zz-cp₁ d z {n} (Lv.suc P) = zz-any tt (zz-nz n z)
zz-cp₁ d z {n} (Lv.lim m P) = zz-any tt (zz-nz n z)
zz-cp₁ d z {n} (Lv.fst P) = zz-any tt (zz-nz n z)
zz-cp₁ d z {n} (Lv.bra η e P) = zz-any tt (zz-nz n z)

module EmbR (L : LG) (tc : Tc L) where
  open Emb L tc

  ιC-eq : ∀ a {k ξ a′} (Q : Cp k a) (P : Cp a′ L) (d : Lk k a′) (z : Vc a Q ξ) → ιC a Q P d z ≡ ι k P d (outC Q z)
  ιC-eq a Lv.self P d z = refl
  ιC-eq (Lv.suc b) (Lv.suc Q) P d z = ιC-eq b Q P d z
  ιC-eq (Lv.lim f) (Lv.lim n Q) P d z = ιC-eq (f n) Q P d z
  ιC-eq (Lv.lc c t g) (Lv.fst Q) P d z = ιC-eq t Q P d z
  ιC-eq (Lv.lc c t g) (Lv.bra η e Q) P d z = ιC-eq (g η e) Q P d z

  ιV-eq : ∀ a {k ξ a′} (R : Strict k a) (P : Cp a′ L) (d : Lk k a′) (z : Vs a R ξ) → ιV a R P d z ≡ ι k P d (outV R z)
  ιV-eq (Lv.suc b) (st-suc Q) P d z = ιC-eq b Q P d z
  ιV-eq (Lv.lim f) (st-lim n Q) P d z = ιC-eq (f n) Q P d z
  ιV-eq (Lv.lc c t g) (st-fst Q) P d z = ιC-eq t Q P d z
  ιV-eq (Lv.lc c t g) (st-bra η e Q) P d z = ιC-eq (g η e) Q P d z

  R-ι : ∀ {B a a′ π} (P : Cp a′ L) (d : Lk a a′) {z : O a π} {ŷ : Ordˢ B} → Rs B z ŷ → Rs B (ι a P d z) ŷ
  R-ι P d rz = rz
  R-ι P d (rs r) = rs (R-ι P d r)
  R-ι P d (rl h) = rl (λ n → R-ι P d (h n))
  R-ι P d (rwk r) = rwk (R-ι P d r)
  R-ι P d (rcv r) = rcv (R-ι P d r)
  R-ι P d (rup zero l) = rup zero (R-ι P d l)
  R-ι P d (rup (self n) l) = rup (self n) (R-ι P d l)
  R-ι {a = a} P d (rmk {R = R} {z = z} zero l r) with mvL R d
  ... | mvs e R′ u with nfS L tc (st⊙ P R′)
  ...   | nfs e₂ pos t r′ =
    rcv (rmk zero (subst (λ w → Rs _ w _) (sym (out-intoV pos (trL (lkC e e₂) (outV R z)))) (R-trL (lkC e e₂) l))
             (rup zero (subst (λ w → Rs _ w _) (sym (ιV-eq a R (stCp pos) (lkC e e₂) z)) (R-ι (stCp pos) (lkC e e₂) l))))
  R-ι {a = a} P d (rmk {R = R} {z = z} (self n) l r) with mvL R d
  ... | mvs e R′ u with nfS L tc (st⊙ P R′)
  ...   | nfs e₂ pos t r′ =
    rcv (rmk (self n) (subst (λ w → Rs _ w _) (sym (out-intoV pos (trL (lkC e e₂) (outV R z)))) (R-trL (lkC e e₂) l))
             (rup (self n) (subst (λ w → Rs _ w _) (sym (ιV-eq a R (stCp pos) (lkC e e₂) z)) (R-ι (stCp pos) (lkC e e₂) l))))
  R-ι {B = B} {a = a} P d (rΩ {j = j} r cv q {h = h₁} {f = f} dk h) with resL r d | R-bL r d
  ... | rl e′ s u b | H =
    rΩ (P ◁ s) _ q (lk≈ e′ dk)
       (λ ξ em′ z ẑ l → rwk (R-ι P d (subst (λ w → Rs B (h₁ ξ (intoU r (b w))) (f (intoˢ (<→◃ q) ẑ))) (sym (cv-into P s z))
                                             (h ξ em′ (b z) ẑ (intoR (<→◃ q) (H (outR (<→◃ q) l)))))))
  R-ι {B = zero} {a = Lv.zero} P d (rŝ z ec rt rg) = rĉŝ tt ec rt rg (R-ι P d rt) (λ η e e′ → R-ι P d (rg η e e′))
  R-ι {B = suc _} {a = Lv.zero} P d (rŝ () ec rt rg)
  R-ι {B = lim _ _} {a = Lv.zero} P d (rŝ () ec rt rg)
  R-ι {a = Lv.suc _} P d (rŝ z ec rt rg) = rŝ (zz-cp₁ d z {tt} P) ec (R-ι P d rt) (λ η e e′ → R-ι P d (rg η e e′))
  R-ι {a = Lv.lim _} P d (rŝ z ec rt rg) = rŝ (zz-cp₁ d z {tt} P) ec (R-ι P d rt) (λ η e e′ → R-ι P d (rg η e e′))
  R-ι {a = Lv.lc _ _ _} P d (rŝ z ec rt rg) = rŝ (zz-cp₁ d z {tt} P) ec (R-ι P d rt) (λ η e e′ → R-ι P d (rg η e e′))
  R-ι P d (rĉ ec dz dg ro rg) = rĉ ec dz dg (R-ι P d ro) (λ η e e′ → R-ι P d (rg η e e′))
  R-ι P d (rĉŝ zb ec rt rg₀ ro rg) = rĉŝ zb ec rt rg₀ (R-ι P d ro) (λ η e e′ → R-ι P d (rg η e e′))

RΩ̇ : ∀ i {t} → t ≈ ⌜ i ⌝ → (tc : Tc t) → Rs i (Ω̇ t tc) (Ωˢ i)
RΩ̇ zero Lv.z≈ tc = rs rz
RΩ̇ (suc b) {t = Lv.suc t′} (Lv.s≈ e) tc =
  rΩ Lv.zero tt zero e (λ ξ em′ z ẑ l → rmk zero l (rup zero (EmbR.R-ι (Lv.suc t′) tc (Lv.suc Lv.self) (inj₂ refl) l)))
RΩ̇ (lim g s) {t = Lv.lim f′} (Lv.l≈ h) tc =
  rl (λ n → rwk (rmk (self n) (RΩ̇ (g n) (h n) (tc n)) (rup (self n) (EmbR.R-ι (Lv.lim f′) tc (Lv.lim n Lv.self) (inj₂ refl) (RΩ̇ (g n) (h n) (tc n))))))
```
