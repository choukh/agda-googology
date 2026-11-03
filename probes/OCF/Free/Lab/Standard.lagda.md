# Standard (验收副本)

> **验收用, 不在主线闭包内.** 脚本从 [Standard](../../Align/Standard.lagda.md) 切出: 只留 `UniformNF5Accept` 的定义级切片里、主线 `OCF.Free.*` 之外的块, 代码行逐字, 导入改指 `OCF.Free.*`. 讲解见原文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.Lab.Standard where

open import Data.Nat using (ℕ; zero; suc; _+_; z≤n; s≤s) renaming (_≤_ to _≤ℕ_; _<_ to _<ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; m≤n+m; <⇒≤; <-irrefl; +-assoc; ≤-<-trans; <-≤-trans; ≤-pred) renaming (<-trans to <ℕ-trans)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst; subst₂) 
open import OCF.Free.Lab.Closure using (Pen; cmpᴾ-refl; lt→<; lt→<ᴾ; eq→≡; eq→≡ᴾ; <ᵀ-trans; <ᴾ-trans; fsT₊-pen′)
open import OCF.Free.Lab.Bachmann using (<ᵀ-irrefl; <ᵀ-asym; <sucT; pen→<; gt→≤; Hd≤; Hd≤-desc; cofA≢c1; fs-gt; fs<ᵀ)
open import OCF.Free.Lab.Correspond using (cof-ne; fs-rep; fs-ω; fsT-c1; γᴱ; cmp-suc[])
import OCF.Align.EBO as E
```

```agda
open E using (T; PT; Cof; c0; c1; cω; cΩ; lt; eq; gt; cmpᵀ; cof; cofA; cofψ0; cofψ₊;
              pred; sucT; Ωt; Ωs; natT; fsn; fsT; fsT0; γT; dec;
              _<ᵀ_; _<ᴾ_; []<; hd<; tl<; lv<; ar<)
       renaming (ψ to ψᵗ)
```

## §1 句法预备: 非严格序、大小、前缀切分

```agda
_≤ᵀ_ : T → T → Set
a ≤ᵀ b = (a <ᵀ b) ⊎ (a ≡ b)

Pen→≤ : ∀ a b → Pen (cmpᵀ a b) → a ≤ᵀ b
Pen→≤ a b (inj₁ e) = inj₁ (lt→< a b e)
Pen→≤ a b (inj₂ e) = inj₂ (eq→≡ a b e)

<≤-trans : ∀ {a b c} → a <ᵀ b → b ≤ᵀ c → a <ᵀ c
<≤-trans p (inj₁ q)    = <ᵀ-trans p q
<≤-trans p (inj₂ refl) = p

≤-trans′ : ∀ {a b c} → a ≤ᵀ b → b ≤ᵀ c → a ≤ᵀ c
≤-trans′ (inj₁ p) q = inj₁ (<≤-trans p q)
≤-trans′ (inj₂ refl) q = q

<→≱ : ∀ {a b} → a <ᵀ b → b ≤ᵀ a → ⊥
<→≱ p (inj₁ q)    = <ᵀ-asym p q
<→≱ p (inj₂ refl) = <ᵀ-irrefl p

-- comparisons with a common prefix
++-mono : ∀ s {a b} → a <ᵀ b → s ++ a <ᵀ s ++ b
++-mono []      p = p
++-mono (x ∷ s) p = tl< (++-mono s p)
```

```agda
sz  : T → ℕ
szᴾ : PT → ℕ
sz []       = 0
sz (x ∷ xs) = szᴾ x + sz xs
szᴾ (ψᵗ u a) = suc (sz u + sz a)

sz-++ : ∀ s t → sz (s ++ t) ≡ sz s + sz t
sz-++ []      t = refl
sz-++ (x ∷ s) t = trans (cong (szᴾ x +_) (sz-++ s t)) (sym (+-assoc (szᴾ x) (sz s) (sz t)))

sz-arg : ∀ u a → sz a <ℕ szᴾ (ψᵗ u a)
sz-arg u a = s≤s (m≤n+m (sz a) (sz u))

sz-hd : ∀ x xs → szᴾ x ≤ℕ sz (x ∷ xs)
sz-hd x xs = m≤m+n (szᴾ x) (sz xs)

sz-tl : ∀ x xs → sz xs ≤ℕ sz (x ∷ xs)
sz-tl x xs = m≤n+m (sz xs) (szᴾ x)

-- argument of the head summand is strictly smaller than the whole
sz-hdarg : ∀ u a xs → sz a <ℕ sz (ψᵗ u a ∷ xs)
sz-hdarg u a xs = <-≤-trans (sz-arg u a) (sz-hd (ψᵗ u a) xs)

data Split (s R ζ : T) : Set where
  inS  : (∀ R′ → ζ <ᵀ s ++ R′) → Split s R ζ
  past : ∀ ζ′ → ζ ≡ s ++ ζ′ → ζ′ <ᵀ R → Split s R ζ

split : ∀ s {R ζ} → ζ <ᵀ s ++ R → Split s R ζ
split []      p       = past _ refl p
split (x ∷ s) []<     = inS (λ R′ → []<)
split (x ∷ s) (hd< q) = inS (λ R′ → hd< q)
split (x ∷ s) (tl< q) with split s q
... | inS f          = inS (λ R′ → tl< (f R′))
... | past ζ′ refl q′ = past ζ′ refl q′

PFX : ∀ s {R ζ} → ζ <ᵀ s ++ R → sz ζ <ℕ sz s → ∀ R′ → ζ <ᵀ s ++ R′
PFX s p h with split s p
... | inS f = f
... | past ζ′ refl q = ⊥-elim (<-irrefl refl (≤-<-trans (subst (sz s ≤ℕ_) (sym (sz-++ s ζ′)) (m≤m+n (sz s) (sz ζ′))) h))
```

```agda
data V1 (y R : T) : T → Set where
  v[] : V1 y R []
  vlv : ∀ {x a xs} → x <ᵀ y → V1 y R (ψᵗ x a ∷ xs)
  var : ∀ {a xs} → a <ᵀ R → V1 y R (ψᵗ y a ∷ xs)

inv1 : ∀ {W y R} → W <ᵀ (ψᵗ y R ∷ []) → V1 y R W
inv1 []<           = v[]
inv1 (hd< (lv< q)) = vlv q
inv1 (hd< (ar< q)) = var q
inv1 (tl< ())
```

## §2 标准形

```agda
data Ctbl : T → Set where
  c[] : Ctbl []
  c∷  : ∀ {a xs} → Ctbl xs → Ctbl (ψᵗ [] a ∷ xs)

data Vis (w : T) : T → T → Set where
  vh : ∀ {x a xs}   → w ≤ᵀ x → Vis w a (ψᵗ x a ∷ xs)
  vd : ∀ {x a xs ζ} → w ≤ᵀ x → Vis w ζ a → Vis w ζ (ψᵗ x a ∷ xs)
  vt : ∀ {x xs ζ}   → Vis w ζ xs → Vis w ζ (x ∷ xs)

Bnd : T → T → Set
Bnd w a = ∀ {ζ} → Vis w ζ a → ζ <ᵀ a

data NF : T → Set
data NFᴾ : PT → Set
data NF where
  n[] : NF []
  n∷  : ∀ {x xs} → NFᴾ x → NF xs → Hd≤ xs x → NF (x ∷ xs)
data NFᴾ where
  nψ : ∀ {u a} → NF u → Ctbl u → NF a → Bnd u a → NFᴾ (ψᵗ u a)

bnd[] : ∀ {w} → Bnd w []
bnd[] ()
```

```agda
Vis-sz : ∀ {w ζ t} → Vis w ζ t → sz ζ <ℕ sz t
Vis-sz (vh {x = x} {a = a} {xs = xs} _)   = sz-hdarg x a xs
Vis-sz (vd {x = x} {a = a} {xs = xs} _ v) = <ℕ-trans (Vis-sz v) (sz-hdarg x a xs)
Vis-sz (vt {x = x} {xs = xs} v)       = <-≤-trans (Vis-sz v) (sz-tl x xs)

Vis-mono : ∀ {w w′ ζ t} → w ≤ᵀ w′ → Vis w′ ζ t → Vis w ζ t
Vis-mono h (vh h′)   = vh (≤-trans′ h h′)
Vis-mono h (vd h′ v) = vd (≤-trans′ h h′) (Vis-mono h v)
Vis-mono h (vt v)    = vt (Vis-mono h v)

Vis-trans : ∀ {w ζ d t} → Vis w ζ d → Vis w d t → Vis w ζ t
Vis-trans v (vh h)    = vd h v
Vis-trans v (vd h v′) = vd h (Vis-trans v v′)
Vis-trans v (vt v′)   = vt (Vis-trans v v′)
```

```agda
cofA[]≢Ω : ∀ c {μ} → cofA [] c ≡ cΩ μ → ⊥
cofA[]≢Ω c0 ()
cofA[]≢Ω c1 ()
cofA[]≢Ω cω ()
cofA[]≢Ω (cΩ ν) e = go (cmpᵀ (sucT ν) []) (cmp-suc[] ν) e where
  go : ∀ m → m ≡ gt → cofψ₊ [] ν m ≡ cΩ _ → ⊥
  go .gt refl ()

Ctbl-cof : ∀ {u μ} → Ctbl u → cof u ≡ cΩ μ → ⊥
Ctbl-cof c[] ()
Ctbl-cof (c∷ {a = []} c[]) ()
Ctbl-cof (c∷ {a = y ∷ ys} c[]) e = cofA[]≢Ω (cof (y ∷ ys)) e
Ctbl-cof (c∷ (c∷ c)) e = Ctbl-cof (c∷ c) e
```

## §3 共尾性

```agda
repb : ∀ x {vs} → NF vs → Hd≤ vs x → Σ ℕ λ m → vs <ᵀ replicate m x
repb x n[] h = 1 , []<
repb x (n∷ {x = y} ny nzs hz₀) (inj₁ e) = 1 , hd< (lt→<ᴾ y x e)
repb x (n∷ {x = y} ny nzs hz₀) (inj₂ e) with eq→≡ᴾ y x e
... | refl with repb x nzs hz₀
...   | m , q = suc m , tl< q
```

```agda
HdV : T → T → T → Set
HdV ν θ c = ∀ {x ζ θs} → θ ≡ ψᵗ x ζ ∷ θs → ν ≤ᵀ x → Vis ν ζ c

record ΩC (b ν c : T) : Set where
  constructor ωc
  field
    θ  : T
    θ< : θ <ᵀ Ωs ν
    fθ : ∀ {η} → θ <ᵀ η → c <ᵀ fsT b η
    hv : HdV ν θ c

hv[] : ∀ {ν c} → HdV ν [] c
hv[] () _

-- inversion of the cofinality of a ψ-node with nonzero argument
data PenΩ (w b ν : T) : Set where
  penΩ : cof b ≡ cΩ ν → Pen (cmpᵀ (sucT ν) w) → PenΩ w b ν

penInv : ∀ w b k → cof b ≡ k → ∀ {ν} → cofA w k ≡ cΩ ν → PenΩ w b ν
penInv w b c0 _ ()
penInv w b c1 _ ()
penInv w b cω _ ()
penInv w b (cΩ ν′) be e = go (cmpᵀ (sucT ν′) w) refl e where
  go : ∀ m → cmpᵀ (sucT ν′) w ≡ m → cofψ₊ w ν′ m ≡ cΩ _ → PenΩ w b _
  go lt em refl = penΩ be (inj₁ em)
  go eq em refl = penΩ be (inj₂ em)
  go gt em ()

data LeafΩ (u ν : T) : Set where
  leafΩ : cof u ≡ c1 → pred u ≡ ν → LeafΩ u ν

leafInv : ∀ u → Ctbl u → ∀ k → cof u ≡ k → ∀ {ν} → cofψ0 u k ≡ cΩ ν → LeafΩ u ν
leafInv u cu c0 _ ()
leafInv u cu c1 ue refl = leafΩ ue refl
leafInv u cu cω _ ()
leafInv u cu (cΩ μ) ue e = ⊥-elim (Ctbl-cof cu ue)

Ωcof : ∀ {b ν} → NF b → cof b ≡ cΩ ν → ∀ {c} → c <ᵀ b → ΩC b ν c
Ωcof n[] () p
Ωcof (n∷ nx (n∷ ny nys hy) hx) e []<      = ωc [] []< (λ _ → []<) hv[]
Ωcof (n∷ nx (n∷ ny nys hy) hx) e (hd< q)  = ωc [] []< (λ _ → hd< q) hv[]
Ωcof (n∷ nx (n∷ ny nys hy) hx) e (tl< q) with Ωcof (n∷ ny nys hy) e q
... | ωc θ θ< fθ hv = ωc θ θ< (λ r → tl< (fθ r)) (λ eθ h → vt (hv eθ h))
Ωcof (n∷ (nψ {u = []} {a = []} nw cw na g) n[] hx) () p
Ωcof {ν = ν} (n∷ (nψ {u = w ∷ ws} {a = []} nw cw na g) n[] hx) e {c} p
  with leafInv (w ∷ ws) cw (cof (w ∷ ws)) refl e
... | leafΩ ue refl =
  ωc c (subst (λ z → c <ᵀ ψᵗ z [] ∷ []) (sym (E.pred-suc (w ∷ ws) ue)) p)
       (λ {η} r → subst (c <ᵀ_) (sym (fsT-c1 (w ∷ ws) (cof (w ∷ ws)) ue η)) r)
       (λ {x} {ζ} {θs} eθ h → subst (Vis ν ζ) (sym eθ) (vh h))
Ωcof {ν = ν} (n∷ (nψ {u = w} {a = y ∷ ys} nw cw na g) n[] hx) e {c} p
  with penInv w (y ∷ ys) (cof (y ∷ ys)) refl e
... | penΩ be pn = go p
  where
  fsT≡ : ∀ η → fsT (ψᵗ w (y ∷ ys) ∷ []) η ≡ ψᵗ w (fsT (y ∷ ys) η) ∷ []
  fsT≡ η = fsT₊-pen′ w (y ∷ ys) ν (cof (y ∷ ys)) be pn η
  go : c <ᵀ (ψᵗ w (y ∷ ys) ∷ []) → ΩC (ψᵗ w (y ∷ ys) ∷ []) ν c
  go []<           = ωc [] []< (λ {η} _ → subst ([] <ᵀ_) (sym (fsT≡ η)) []<) hv[]
  go (hd< (lv< q)) = ωc [] []< (λ {η} _ → subst (c <ᵀ_) (sym (fsT≡ η)) (hd< (lv< q))) hv[]
  go (hd< (ar< q)) with Ωcof na be q
  ... | ωc θ θ< fθ hv =
    ωc θ θ< (λ {η} r → subst (c <ᵀ_) (sym (fsT≡ η)) (hd< (ar< (fθ r))))
       (λ eθ h → vd (inj₁ (pen→< ν w pn)) (hv eθ h))
  go (tl< ())
```

```agda
γ<Ωs : ∀ b ν k → γT b ν k <ᵀ Ωs ν
γ<Ωs b ν zero    = hd< (lv< (E.<-sucT ν))
γ<Ωs b ν (suc k) = hd< (lv< (E.<-sucT ν))

Cof6 : ∀ m {b ν w c} → NF b → cof b ≡ cΩ ν → w ≤ᵀ ν → sz c ≤ℕ m → c <ᵀ b →
       (∀ {ζ} → Vis w ζ c → ζ <ᵀ b) → Σ ℕ λ n → c <ᵀ fsT b (γT b ν n)
Cof6 m {b} {ν} {w} {c} nb be wν hm p H with Ωcof nb be p
... | ωc [] θ< fθ hv = 0 , fθ []<
... | ωc (ψᵗ x ζ′ ∷ θs) (hd< (lv< q)) fθ hv with <sucT ν q
...   | inj₁ r = 0 , fθ (hd< (lv< r))
...   | inj₂ refl = go m hm
  where
  vz : Vis ν ζ′ c
  vz = hv refl (inj₂ refl)
  go : ∀ m′ → sz c ≤ℕ m′ → Σ ℕ λ n → c <ᵀ fsT b (γT b ν n)
  go zero h = ⊥-elim (<-irrefl refl (<-≤-trans (≤-<-trans z≤n (Vis-sz vz)) h))
  go (suc m′) h with Cof6 m′ nb be wν (≤-pred (≤-trans (Vis-sz vz) h)) (H (Vis-mono wν vz))
                         (λ v → H (Vis-trans v (Vis-mono wν vz)))
  ... | k , r = suc k , fθ (hd< (ar< r))
Cof6 m nb be wν hm p H | ωc (ψᵗ x ζ′ ∷ θs) (hd< (ar< ())) fθ hv
Cof6 m nb be wν hm p H | ωc (ψᵗ x ζ′ ∷ θs) (tl< ()) fθ hv
```

```agda
cofin  : ∀ {u} → NF u → cof u ≡ cω → ∀ {v} → NF v → v <ᵀ u → Σ ℕ λ n → v <ᵀ fsn u n
cofinL : ∀ {w ws} → NF (w ∷ ws) → ∀ k → cof (w ∷ ws) ≡ k → cofψ0 (w ∷ ws) k ≡ cω →
         ∀ {v} → NF v → v <ᵀ Ωt (w ∷ ws) → Σ ℕ λ n → v <ᵀ fsn (Ωt (w ∷ ws)) n
cofinA : ∀ {w y ys} → NF (y ∷ ys) → ∀ k → cof (y ∷ ys) ≡ k → cofA w k ≡ cω →
         ∀ {v} → NF v → v <ᵀ (ψᵗ w (y ∷ ys) ∷ []) → Σ ℕ λ n → v <ᵀ fsn (ψᵗ w (y ∷ ys) ∷ []) n

cofin n[] () nv p
cofin (n∷ nx (n∷ ny nys hy) hx) e nv []<     = 0 , []<
cofin (n∷ nx (n∷ ny nys hy) hx) e nv (hd< q) = 0 , hd< q
cofin (n∷ nx (n∷ ny nys hy) hx) e (n∷ _ nvs _) (tl< q) with cofin (n∷ ny nys hy) e nvs q
... | n , r = n , tl< r
cofin (n∷ (nψ {u = []} {a = []} nw cw na g) n[] hx) () nv p
cofin (n∷ (nψ {u = w ∷ ws} {a = []} nw cw na g) n[] hx) e nv p = cofinL nw (cof (w ∷ ws)) refl e nv p
cofin (n∷ (nψ {u = w} {a = y ∷ ys} nw cw na g) n[] hx) e nv p = cofinA na (cof (y ∷ ys)) refl e nv p

cofinL nw c0 ke () nv p
cofinL nw c1 ke () nv p
cofinL {w} {ws} nw cω ke e nv []< = 0 , subst ([] <ᵀ_) (sym (E.fsn0-eq w ws 0 ke)) []<
cofinL {w} {ws} nw cω ke e (n∷ (nψ nx _ _ _) _ _) (hd< (lv< q)) with cofin nw ke nx q
... | n , r = n , subst (_ <ᵀ_) (sym (E.fsn0-eq w ws n ke)) (hd< (lv< r))
cofinL nw cω ke e nv (hd< (ar< ()))
cofinL nw cω ke e nv (tl< ())
cofinL nw (cΩ μ) ke () nv p

cofinA nb c0 ke e nv p = ⊥-elim (cof-ne _ _ ke)
cofinA {w} {y} {ys} nb c1 ke e n[] []< = 1 , subst ([] <ᵀ_) (sym (fs-rep w y ys ke 1)) []<
cofinA {w} {y} {ys} nb c1 ke e nv (hd< (lv< q)) = 1 , subst (_ <ᵀ_) (sym (fs-rep w y ys ke 1)) (hd< (lv< q))
cofinA {w} {y} {ys} nb c1 ke e (n∷ {x = ψᵗ _ c} {xs = vs} nc nvs hv) (hd< (ar< q))
  with <sucT (pred (y ∷ ys)) (subst (c <ᵀ_) (sym (E.pred-suc (y ∷ ys) ke)) q)
... | inj₁ r = 1 , subst (_ <ᵀ_) (sym (fs-rep w y ys ke 1)) (hd< (ar< r))
... | inj₂ refl with repb (ψᵗ w c) nvs hv
...   | m , r = suc m , subst (_ <ᵀ_) (sym (fs-rep w y ys ke (suc m))) (tl< r)
cofinA nb c1 ke e nv (tl< ())
cofinA {w} {y} {ys} nb cω ke e nv []< = 0 , subst ([] <ᵀ_) (sym (fs-ω w y ys ke 0)) []<
cofinA {w} {y} {ys} nb cω ke e nv (hd< (lv< q)) = 0 , subst (_ <ᵀ_) (sym (fs-ω w y ys ke 0)) (hd< (lv< q))
cofinA {w} {y} {ys} nb cω ke e (n∷ (nψ _ _ nc _) _ _) (hd< (ar< q)) with cofin nb ke nc q
... | n , r = n , subst (_ <ᵀ_) (sym (fs-ω w y ys ke n)) (hd< (ar< r))
cofinA nb cω ke e nv (tl< ())
cofinA {w} {y} {ys} nb (cΩ ν) ke e nv p = go (cmpᵀ (sucT ν) w) refl e
  where
  go : ∀ m → cmpᵀ (sucT ν) w ≡ m → cofψ₊ w ν m ≡ cω → Σ ℕ λ n → _ <ᵀ fsn (ψᵗ w (y ∷ ys) ∷ []) n
  go lt em ()
  go eq em ()
  go gt em _ = h nv p
    where
    h : ∀ {v} → NF v → v <ᵀ (ψᵗ w (y ∷ ys) ∷ []) → Σ ℕ λ n → v <ᵀ fsn (ψᵗ w (y ∷ ys) ∷ []) n
    h nv []< = 0 , subst ([] <ᵀ_) (sym (fs-gt w y ys ν ke em 0)) []<
    h nv (hd< (lv< q)) = 0 , subst (_ <ᵀ_) (sym (fs-gt w y ys ν ke em 0)) (hd< (lv< q))
    h (n∷ (nψ {a = c} _ _ nc gc) _ _) (hd< (ar< q))
      with Cof6 (sz c) nb ke (gt→≤ ν w em) ≤-refl q (λ vz → <ᵀ-trans (gc vz) q)
    ... | n , r = n , subst (_ <ᵀ_) (sym (fs-gt w y ys ν ke em n)) (hd< (ar< r))
    h nv (tl< ())
```

## §4 上下文与提升

```agda
data Fr : Set where
  pre : T → Fr
  nd  : T → Fr

Ctx : Set
Ctx = List Fr

plug : Ctx → T → T
plug []          H = H
plug (pre s ∷ K) H = s ++ plug K H
plug (nd x ∷ K)  H = ψᵗ x (plug K H) ∷ []

plug-++ : ∀ K K′ H → plug (K ++ K′) H ≡ plug K (plug K′ H)
plug-++ []          K′ H = refl
plug-++ (pre s ∷ K) K′ H = cong (s ++_) (plug-++ K K′ H)
plug-++ (nd x ∷ K)  K′ H = cong (λ z → ψᵗ x z ∷ []) (plug-++ K K′ H)

sz-suffix : ∀ s ζ′ → sz ζ′ ≤ℕ sz (s ++ ζ′)
sz-suffix s ζ′ = subst (sz ζ′ ≤ℕ_) (sym (sz-++ s ζ′)) (m≤n+m (sz ζ′) (sz s))

LIFT : ∀ K {H H′} m → (∀ {ζ} → sz ζ ≤ℕ m → ζ <ᵀ H → ζ <ᵀ H′) →
       ∀ {ζ} → sz ζ ≤ℕ m → ζ <ᵀ plug K H → ζ <ᵀ plug K H′
LIFT [] m c h p = c h p
LIFT (pre s ∷ K) m c h p with split s p
... | inS f = f _
... | past ζ′ refl q = ++-mono s (LIFT K m c (≤-trans (sz-suffix s ζ′) h) q)
LIFT (nd x ∷ K) m c h []<              = []<
LIFT (nd x ∷ K) m c h (hd< (lv< q))    = hd< (lv< q)
LIFT (nd x ∷ K) m c {ψᵗ v a ∷ ys} h (hd< (ar< q)) =
  hd< (ar< (LIFT K m c (≤-trans (<⇒≤ (sz-hdarg v a ys)) h) q))
LIFT (nd x ∷ K) m c h (tl< ())
```

```agda
plugR : Ctx → T → T
plugR []          H = H
plugR (pre s ∷ S) H = plugR S (s ++ H)
plugR (nd x ∷ S)  H = plugR S (ψᵗ x H ∷ [])

Core : T → T → ℕ → Set
Core H H′ m = ∀ {ζ} → sz ζ ≤ℕ m → ζ <ᵀ H → ζ <ᵀ H′

LIFTR : ∀ S {H H′} m → Core H H′ m → Core (plugR S H) (plugR S H′) m
LIFTR []          m c = c
LIFTR (pre s ∷ S) m c = LIFTR S m (LIFT (pre s ∷ []) m c)
LIFTR (nd x ∷ S)  m c = LIFTR S m (LIFT (nd x ∷ []) m c)

pfxC : ∀ s {R R′} m → m <ℕ sz s → Core (s ++ R) (s ++ R′) m
pfxC s m hm h p = PFX s p (≤-<-trans h hm) _

c4C : ∀ {y d} → cof d ≡ c1 → ∀ T′ → Core (ψᵗ y d ∷ []) (ψᵗ y (pred d) ∷ T′) (sz (pred d))
c4C ce T′ h []<            = []<
c4C ce T′ h (hd< (lv< q))  = hd< (lv< q)
c4C {y} {d} ce T′ {ψᵗ _ e ∷ ζs} h (hd< (ar< q))
  with <sucT (pred d) (subst (e <ᵀ_) (sym (E.pred-suc d ce)) q)
... | inj₁ r    = hd< (ar< r)
... | inj₂ refl = ⊥-elim (<-irrefl refl (<-≤-trans (sz-hdarg y (pred d) ζs) h))
c4C ce T′ h (tl< ())

data HasNd : Ctx → Set where
  here  : ∀ {x K} → HasNd (nd x ∷ K)
  there : ∀ {f K} → HasNd K → HasNd (f ∷ K)

rv : Ctx → Ctx
rv []      = []
rv (f ∷ S) = rv S ++ (f ∷ [])

HasNd-++ʳ : ∀ K {K′} → HasNd K′ → HasNd (K ++ K′)
HasNd-++ʳ []      h = h
HasNd-++ʳ (f ∷ K) h = there (HasNd-++ʳ K h)

HasNd-++ˡ : ∀ {K} K′ → HasNd K → HasNd (K ++ K′)
HasNd-++ˡ K′ here      = here
HasNd-++ˡ K′ (there h) = there (HasNd-++ˡ K′ h)

HasNd-rv : ∀ {S} → HasNd S → HasNd (rv S)
HasNd-rv {nd x ∷ S} here      = HasNd-++ʳ (rv S) here
HasNd-rv {f ∷ S}    (there h) = HasNd-++ˡ (f ∷ []) (HasNd-rv h)

plugR-++ : ∀ S S′ H → plugR (S ++ S′) H ≡ plugR S′ (plugR S H)
plugR-++ []          S′ H = refl
plugR-++ (pre s ∷ S) S′ H = plugR-++ S S′ (s ++ H)
plugR-++ (nd x ∷ S)  S′ H = plugR-++ S S′ (ψᵗ x H ∷ [])

plug-rv : ∀ S H → plug (rv S) H ≡ plugR S H
plug-rv []          H = refl
plug-rv (pre s ∷ S) H = trans (plug-++ (rv S) (pre s ∷ []) H) (plug-rv S (s ++ H))
plug-rv (nd x ∷ S)  H = trans (plug-++ (rv S) (nd x ∷ []) H) (plug-rv S (ψᵗ x H ∷ []))

plugR-rv : ∀ K H → plugR (rv K) H ≡ plug K H
plugR-rv []          H = refl
plugR-rv (pre s ∷ K) H = trans (plugR-++ (rv K) (pre s ∷ []) H) (cong (s ++_) (plugR-rv K H))
plugR-rv (nd x ∷ K)  H = trans (plugR-++ (rv K) (nd x ∷ []) H) (cong (λ z → ψᵗ x z ∷ []) (plugR-rv K H))

plugR-mix : ∀ S K H → plugR (S ++ rv K) H ≡ plug K (plugR S H)
plugR-mix S K H = trans (plugR-++ S (rv K) H) (plugR-rv K (plugR S H))

sz-plugR≤ : ∀ S W → sz W ≤ℕ sz (plugR S W)
sz-plugR≤ []          W = ≤-refl
sz-plugR≤ (pre s ∷ S) W = ≤-trans (sz-suffix s W) (sz-plugR≤ S (s ++ W))
sz-plugR≤ (nd x ∷ S)  W = ≤-trans (<⇒≤ (sz-hdarg x W [])) (sz-plugR≤ S (ψᵗ x W ∷ []))

sz-plugR< : ∀ S W → HasNd S → sz W <ℕ sz (plugR S W)
sz-plugR< (nd x ∷ S)  W here      = <-≤-trans (sz-hdarg x W []) (sz-plugR≤ S (ψᵗ x W ∷ []))
sz-plugR< (pre s ∷ S) W (there h) = ≤-<-trans (sz-suffix s W) (sz-plugR< S (s ++ W) h)
sz-plugR< (nd x ∷ S)  W (there h) = <ℕ-trans (sz-hdarg x W []) (sz-plugR< S (ψᵗ x W ∷ []) h)
```

```agda
fsn-++ : ∀ s x xs n → fsn (s ++ x ∷ xs) n ≡ s ++ fsn (x ∷ xs) n
fsn-++ []           x xs n = refl
fsn-++ (a ∷ [])     x xs n = refl
fsn-++ (a ∷ b ∷ s)  x xs n = cong (a ∷_) (fsn-++ (b ∷ s) x xs n)

fsT-++ : ∀ s x xs η → fsT (s ++ x ∷ xs) η ≡ s ++ fsT (x ∷ xs) η
fsT-++ []           x xs η = refl
fsT-++ (a ∷ [])     x xs η = refl
fsT-++ (a ∷ b ∷ s)  x xs η = cong (a ∷_) (fsT-++ (b ∷ s) x xs η)

cof-++ : ∀ s x xs → cof (s ++ x ∷ xs) ≡ cof (x ∷ xs)
cof-++ []          x xs = refl
cof-++ (a ∷ [])    x xs = refl
cof-++ (a ∷ b ∷ s) x xs = cof-++ (b ∷ s) x xs

NF-suf : ∀ s {t} → NF (s ++ t) → NF t
NF-suf []      n           = n
NF-suf (x ∷ s) (n∷ _ n _)  = NF-suf s n

<++′ : ∀ s {t} R → t <ᵀ s ++ [] → t <ᵀ s ++ R
<++′ s R p with split s p
... | inS f = f R
... | past ζ′ refl ()

fsT-desc : ∀ {W ν η} → cof W ≡ cΩ ν → η <ᵀ Ωs ν → fsT W η <ᵀ W
fsT-desc {W} e η< = subst (_<ᵀ W) (E.fsT↓-trm W e η<) (dec (E.fsT↓ W e η<))

data ViewA (w : T) (y : PT) (ys : T) : Set where
  v4 : cof (y ∷ ys) ≡ c1 → ViewA w y ys
  v5 : cof (y ∷ ys) ≡ cω → ViewA w y ys
  v6 : ∀ ν → cof (y ∷ ys) ≡ cΩ ν → cmpᵀ (sucT ν) w ≡ gt → ViewA w y ys

viewA : ∀ w y ys → cofA w (cof (y ∷ ys)) ≡ cω → ViewA w y ys
viewA w y ys e = go (cof (y ∷ ys)) refl e where
  go : ∀ k → cof (y ∷ ys) ≡ k → cofA w k ≡ cω → ViewA w y ys
  go c0 ke _ = ⊥-elim (cof-ne y ys ke)
  go c1 ke _ = v4 ke
  go cω ke _ = v5 ke
  go (cΩ ν) ke e′ = go′ (cmpᵀ (sucT ν) w) refl e′ where
    go′ : ∀ m → cmpᵀ (sucT ν) w ≡ m → cofψ₊ w ν m ≡ cω → ViewA w y ys
    go′ lt _ ()
    go′ eq _ ()
    go′ gt em _ = v6 ν ke em

viewL : ∀ w ws → cofψ0 (w ∷ ws) (cof (w ∷ ws)) ≡ cω → cof (w ∷ ws) ≡ cω
viewL w ws e = go (cof (w ∷ ws)) refl e where
  go : ∀ k → cof (w ∷ ws) ≡ k → cofψ0 (w ∷ ws) k ≡ cω → cof (w ∷ ws) ≡ cω
  go c0 _ ()
  go c1 _ ()
  go cω ke _ = ke
  go (cΩ _) _ ()

-- terms below Ω_{x} with x the subscript stay below any ψ_{x′}(R), x ≤ x′
belowΩ : ∀ {t x x′} R → t <ᵀ (ψᵗ x [] ∷ []) → x ≤ᵀ x′ → t <ᵀ (ψᵗ x′ R ∷ [])
belowΩ R []< h = []<
belowΩ R (hd< (lv< q)) h = hd< (lv< (<≤-trans q h))
belowΩ R (hd< (ar< ())) h
belowΩ R (tl< ()) h
```

```agda
cof[]≢ω : cof [] ≡ cω → ⊥
cof[]≢ω ()

cof[]≢Ω : ∀ {ν} → cof [] ≡ cΩ ν → ⊥
cof[]≢Ω ()

nf-arg : ∀ {x a xs} → NF (ψᵗ x a ∷ xs) → NF a
nf-arg (n∷ (nψ _ _ na _) _ _) = na

nf-ctbl : ∀ {x a xs} → NF (ψᵗ x a ∷ xs) → Ctbl x
nf-ctbl (n∷ (nψ _ cx _ _) _ _) = cx
```

## §5 自界引理

```agda
n≮0 : ∀ {n} → n <ℕ 0 → ⊥
n≮0 ()

stepPre : ∀ {S s Kr} → HasNd S ⊎ HasNd (pre s ∷ Kr) → HasNd (pre s ∷ S) ⊎ HasNd Kr
stepPre (inj₁ h)         = inj₁ (there h)
stepPre (inj₂ (there h)) = inj₂ h

SELF  : ∀ m S {Z} → sz Z ≤ℕ m → HasNd S → NF Z → cof Z ≡ cω → Z <ᵀ plugR S Z →
        ∀ n → fsn Z n <ᵀ plugR S (fsn Z n)
SELFΩ : ∀ m S {Z ν η} → sz Z ≤ℕ m → HasNd S → NF Z → cof Z ≡ cΩ ν → η <ᵀ Ωs ν → Z <ᵀ plugR S Z →
        fsT Z η <ᵀ plugR S (fsT Z η)
DESC  : ∀ m S Kr {W} n → sz (plugR S W) ≤ℕ m → HasNd S ⊎ HasNd Kr → NF W → cof W ≡ cω →
        W <ᵀ plug Kr (plugR S W) → fsn W n <ᵀ plug Kr (plugR S (fsn W n))
DESCΩ : ∀ m S Kr {W ν η} → sz (plugR S W) ≤ℕ m → HasNd S ⊎ HasNd Kr → NF W → cof W ≡ cΩ ν → η <ᵀ Ωs ν →
        W <ᵀ plug Kr (plugR S W) → fsT W η <ᵀ plug Kr (plugR S (fsT W η))

SELF m S {Z} h hs nZ e p n =
  subst (fsn Z n <ᵀ_) (plug-rv S (fsn Z n))
        (DESC m [] (rv S) n h (inj₂ (HasNd-rv hs)) nZ e (subst (Z <ᵀ_) (sym (plug-rv S Z)) p))

SELFΩ m S {Z} {η = η} h hs nZ e η< p =
  subst (fsT Z η <ᵀ_) (plug-rv S (fsT Z η))
        (DESCΩ m [] (rv S) h (inj₂ (HasNd-rv hs)) nZ e η< (subst (Z <ᵀ_) (sym (plug-rv S Z)) p))

-- hole
DESC zero    S [] {W} n h (inj₁ hs) nW e p = ⊥-elim (n≮0 (<-≤-trans (sz-plugR< S W hs) h))
DESC (suc m) S [] {W} n h (inj₁ hs) nW e p =
  SELF m S (≤-pred (≤-trans (sz-plugR< S W hs) h)) hs nW e p n
DESC m S [] n h (inj₂ ()) nW e p
-- prefix frame
DESC m S (pre s ∷ Kr) {W} n h hk nW e p with split s p
... | inS f = <ᵀ-trans (fs<ᵀ e n) (f _)
... | past [] refl q = <++′ s _ (fs<ᵀ e n)
... | past (x ∷ xs) refl q =
  subst (λ z → z <ᵀ s ++ plug Kr (plugR S z)) (sym (fsn-++ s x xs n))
        (++-mono s (DESC m (pre s ∷ S) Kr n h (stepPre hk) (NF-suf s nW) (trans (sym (cof-++ s x xs)) e) q))
-- node frame
DESC m S (nd y₀ ∷ Kr) {W} n h hk nW e p with inv1 p
... | v[] = ⊥-elim (cof[]≢ω e)
... | vlv q = <ᵀ-trans (fs<ᵀ e n) (hd< (lv< q))
... | var {a = d} {xs = x ∷ xs} q =
  hd< (ar< (LIFT Kr (sz d) (LIFTR S (sz d) (pfxC (ψᵗ y₀ d ∷ []) (sz d) (sz-hdarg y₀ d []))) ≤-refl q))
... | var {a = []} {xs = []} q = leafω y₀ e
  where
  leafω : ∀ y₀ → cof (ψᵗ y₀ [] ∷ []) ≡ cω →
          fsn (ψᵗ y₀ [] ∷ []) n <ᵀ plug (nd y₀ ∷ Kr) (plugR S (fsn (ψᵗ y₀ [] ∷ []) n))
  leafω [] ()
  leafω (w ∷ ws) e′ =
    subst (λ z → z <ᵀ plug (nd (w ∷ ws) ∷ Kr) (plugR S z)) (sym (E.fsn0-eq w ws n ke)) (hd< (lv< (fs<ᵀ ke n)))
    where ke = viewL w ws e′
... | var {a = y ∷ ys} {xs = []} q with viewA y₀ y ys e
...   | v4 ke = subst (λ z → z <ᵀ plug (nd y₀ ∷ Kr) (plugR S z)) (sym (fs-rep y₀ y ys ke n)) (rep4 n)
  where
  pd = pred (y ∷ ys)
  rep4 : ∀ k → replicate k (ψᵗ y₀ pd) <ᵀ (ψᵗ y₀ (plug Kr (plugR S (replicate k (ψᵗ y₀ pd)))) ∷ [])
  rep4 zero    = []<
  rep4 (suc k) = hd< (ar< (LIFT Kr (sz pd) (LIFTR S (sz pd) (c4C ke (replicate k (ψᵗ y₀ pd)))) ≤-refl
                                (<ᵀ-trans (E.pred-< (y ∷ ys) ke) q)))
...   | v5 ke = subst (λ z → z <ᵀ plug (nd y₀ ∷ Kr) (plugR S z)) (sym (fs-ω y₀ y ys ke n))
                      (hd< (ar< (DESC m (nd y₀ ∷ S) Kr n h (inj₁ here) (nf-arg nW) ke q)))
...   | v6 ν ke em = subst (λ z → z <ᵀ plug (nd y₀ ∷ Kr) (plugR S z)) (sym (fs-gt y₀ y ys ν ke em n)) (go m h)
  where
  d = y ∷ ys
  γ = γT d ν n
  go : ∀ m′ → sz (plugR S (ψᵗ y₀ d ∷ [])) ≤ℕ m′ →
       (ψᵗ y₀ (fsT d γ) ∷ []) <ᵀ (ψᵗ y₀ (plug Kr (plugR S (ψᵗ y₀ (fsT d γ) ∷ []))) ∷ [])
  go zero h′ = ⊥-elim (n≮0 (<-≤-trans (sz-plugR< (nd y₀ ∷ S) d here) h′))
  go (suc m′) h′ = hd< (ar< (subst (fsT d γ <ᵀ_) (plugR-mix (nd y₀ ∷ S) Kr (fsT d γ))
    (SELFΩ m′ (nd y₀ ∷ S ++ rv Kr) (≤-pred (≤-trans (sz-plugR< (nd y₀ ∷ S) d here) h′))
           here (nf-arg nW) ke (γ<Ωs d ν n) (subst (d <ᵀ_) (sym (plugR-mix (nd y₀ ∷ S) Kr d)) q))))

-- Ω version
DESCΩ zero    S [] {W} h (inj₁ hs) nW e η< p = ⊥-elim (n≮0 (<-≤-trans (sz-plugR< S W hs) h))
DESCΩ (suc m) S [] {W} h (inj₁ hs) nW e η< p =
  SELFΩ m S (≤-pred (≤-trans (sz-plugR< S W hs) h)) hs nW e η< p
DESCΩ m S [] h (inj₂ ()) nW e η< p
DESCΩ m S (pre s ∷ Kr) {W} {η = η} h hk nW e η< p with split s p
... | inS f = <ᵀ-trans (fsT-desc e η<) (f _)
... | past [] refl q = <++′ s _ (fsT-desc e η<)
... | past (x ∷ xs) refl q =
  subst (λ z → z <ᵀ s ++ plug Kr (plugR S z)) (sym (fsT-++ s x xs η))
        (++-mono s (DESCΩ m (pre s ∷ S) Kr h (stepPre hk) (NF-suf s nW) (trans (sym (cof-++ s x xs)) e) η< q))
DESCΩ m S (nd y₀ ∷ Kr) {W} {ν} {η} h hk nW e η< p with inv1 p
... | v[] = ⊥-elim (cof[]≢Ω e)
... | vlv q = <ᵀ-trans (fsT-desc e η<) (hd< (lv< q))
... | var {a = d} {xs = x ∷ xs} q =
  hd< (ar< (LIFT Kr (sz d) (LIFTR S (sz d) (pfxC (ψᵗ y₀ d ∷ []) (sz d) (sz-hdarg y₀ d []))) ≤-refl q))
... | var {a = []} {xs = []} q = leafΩ′ y₀ nW e η<
  where
  leafΩ′ : ∀ y₀ → NF (ψᵗ y₀ [] ∷ []) → cof (ψᵗ y₀ [] ∷ []) ≡ cΩ ν → η <ᵀ Ωs ν →
           fsT (ψᵗ y₀ [] ∷ []) η <ᵀ plug (nd y₀ ∷ Kr) (plugR S (fsT (ψᵗ y₀ [] ∷ []) η))
  leafΩ′ [] _ ()
  leafΩ′ (w ∷ ws) nW′ e′ η<′ with leafInv (w ∷ ws) (nf-ctbl nW′) (cof (w ∷ ws)) refl e′
  ... | leafΩ ue refl =
    subst (λ z → z <ᵀ plug (nd (w ∷ ws) ∷ Kr) (plugR S z)) (sym (fsT-c1 (w ∷ ws) (cof (w ∷ ws)) ue η))
          (belowΩ _ (subst (λ z → η <ᵀ ψᵗ z [] ∷ []) (E.pred-suc (w ∷ ws) ue) η<′) (inj₂ refl))
... | var {a = y ∷ ys} {xs = []} q with penInv y₀ (y ∷ ys) (cof (y ∷ ys)) refl e
...   | penΩ be pn =
  subst (λ z → z <ᵀ plug (nd y₀ ∷ Kr) (plugR S z)) (sym (fsT₊-pen′ y₀ (y ∷ ys) ν (cof (y ∷ ys)) be pn η))
        (hd< (ar< (DESCΩ m (nd y₀ ∷ S) Kr h (inj₁ here) (nf-arg nW) be η< q)))
```

## §6 可见参数的保持与标准形的闭包

```agda
[]<plugR : ∀ S {x xs} → [] <ᵀ plugR S (x ∷ xs)
[]<plugR []                {x} {xs} = []<
[]<plugR (pre [] ∷ S)      {x} {xs} = []<plugR S
[]<plugR (pre (a ∷ s) ∷ S) {x} {xs} = []<plugR S
[]<plugR (nd y ∷ S)        {x} {xs} = []<plugR S

plugR-mono : ∀ S {A B} → A <ᵀ B → plugR S A <ᵀ plugR S B
plugR-mono []          p = p
plugR-mono (pre s ∷ S) p = plugR-mono S (++-mono s p)
plugR-mono (nd x ∷ S)  p = plugR-mono S (hd< (ar< p))

fsT-ne : ∀ {d ν η} → cof d ≡ cΩ ν → [] <ᵀ η → [] <ᵀ fsT d η
fsT-ne {d = []} () hη
fsT-ne {d = x ∷ y ∷ ys} e hη = []<
fsT-ne {d = ψᵗ [] [] ∷ []} () hη
fsT-ne {d = ψᵗ (w ∷ ws) [] ∷ []} {η = η} e hη = go (cof (w ∷ ws)) where
  go : ∀ c → [] <ᵀ fsT0 (w ∷ ws) c η
  go c0     = []<
  go c1     = hη
  go cω     = []<
  go (cΩ μ) = []<
fsT-ne {d = ψᵗ u (y ∷ ys) ∷ []} {η = η} e hη = go (cof (y ∷ ys)) where
  go : ∀ c → [] <ᵀ E.fsT₊ u (y ∷ ys) c η
  go c0     = []<
  go c1     = []<
  go cω     = []<
  go (cΩ μ) = go′ (cmpᵀ (sucT μ) u) where
    go′ : ∀ m → [] <ᵀ E.fsTc u (y ∷ ys) μ m η
    go′ lt = []<
    go′ eq = []<
    go′ gt = []<

fsT-mono : ∀ {d ν η η′} → NF d → cof d ≡ cΩ ν → η <ᵀ η′ → fsT d η <ᵀ fsT d η′
fsT-mono n[] () p
fsT-mono (n∷ nx (n∷ ny nys hy) hx) e p = tl< (fsT-mono (n∷ ny nys hy) e p)
fsT-mono (n∷ (nψ {u = []} {a = []} _ _ _ _) n[] _) () p
fsT-mono {η = η} {η′ = η′} (n∷ (nψ {u = w ∷ ws} {a = []} _ cw _ _) n[] _) e p
  with leafInv (w ∷ ws) cw (cof (w ∷ ws)) refl e
... | leafΩ ue refl = subst₂ _<ᵀ_ (sym (fsT-c1 (w ∷ ws) (cof (w ∷ ws)) ue η)) (sym (fsT-c1 (w ∷ ws) (cof (w ∷ ws)) ue η′)) p
fsT-mono {ν = ν} {η = η} {η′ = η′} (n∷ (nψ {u = x} {a = y ∷ ys} _ _ nb _) n[] _) e p
  with penInv x (y ∷ ys) (cof (y ∷ ys)) refl e
... | penΩ be pn = subst₂ _<ᵀ_ (sym (fsT₊-pen′ x (y ∷ ys) ν (cof (y ∷ ys)) be pn η))
                               (sym (fsT₊-pen′ x (y ∷ ys) ν (cof (y ∷ ys)) be pn η′))
                               (hd< (ar< (fsT-mono nb be p)))

γ-mono : ∀ {d ν} → NF d → cof d ≡ cΩ ν → ∀ k → γT d ν k <ᵀ γT d ν (suc k)
γ-mono nD e zero    = hd< (ar< (fsT-ne e []<))
γ-mono nD e (suc k) = hd< (ar< (fsT-mono nD e (γ-mono nD e k)))
```

```agda
Vis-pred : ∀ {w ζ d} → cof d ≡ c1 → Vis w ζ (pred d) → Vis w ζ d
Vis-pred {d = []} e v = v
Vis-pred {d = x ∷ y ∷ ys} e (vh h)   = vh h
Vis-pred {d = x ∷ y ∷ ys} e (vd h v) = vd h v
Vis-pred {d = x ∷ y ∷ ys} e (vt v)   = vt (Vis-pred e v)
Vis-pred {d = ψᵗ [] [] ∷ []} e ()
Vis-pred {d = ψᵗ [] (y ∷ ys) ∷ []} e v = v
Vis-pred {d = ψᵗ (w ∷ ws) a ∷ []} e v = v

Vis-rep : ∀ k {w ζ y} → Vis w ζ (replicate (suc k) y) → Vis w ζ (y ∷ [])
Vis-rep zero    v        = v
Vis-rep (suc k) (vh h)   = vh h
Vis-rep (suc k) (vd h v) = vd h v
Vis-rep (suc k) (vt v)   = Vis-rep k v

Bnd-pred : ∀ {w d} → Bnd w d → cof d ≡ c1 → Bnd w (pred d)
Bnd-pred {d = d} g e {ζ} v with <sucT (pred d) (subst (ζ <ᵀ_) (sym (E.pred-suc d e)) (g (Vis-pred e v)))
... | inj₁ r    = r
... | inj₂ refl = ⊥-elim (<-irrefl refl (Vis-sz v))

cofψ0≢c1 : ∀ u c → cofψ0 u c ≡ c1 → ⊥
cofψ0≢c1 u c0 ()
cofψ0≢c1 u c1 ()
cofψ0≢c1 u cω ()
cofψ0≢c1 u (cΩ μ) ()

NF-pred : ∀ {t} → NF t → cof t ≡ c1 → NF (pred t)
NF-pred n[] ()
NF-pred (n∷ nx (n∷ {x = y} {xs = ys} ny nys hy) hx) e =
  n∷ nx (NF-pred (n∷ ny nys hy) e) (Hd≤-desc (E.pred-< (y ∷ ys) e) hx)
NF-pred (n∷ (nψ {u = []} {a = []} _ _ _ _) n[] _) e = n[]
NF-pred (n∷ (nψ {u = w ∷ ws} {a = []} _ _ _ _) n[] _) e = ⊥-elim (cofψ0≢c1 (w ∷ ws) (cof (w ∷ ws)) e)
NF-pred (n∷ (nψ {u = u} {a = y ∷ ys} _ _ _ _) n[] _) e = ⊥-elim (cofA≢c1 u (cof (y ∷ ys)) e)

Ctbl-pred : ∀ {u} → Ctbl u → Ctbl (pred u)
Ctbl-pred c[] = c[]
Ctbl-pred (c∷ {a = []} c[]) = c[]
Ctbl-pred (c∷ {a = y ∷ ys} c[]) = c∷ c[]
Ctbl-pred (c∷ (c∷ c)) = c∷ (Ctbl-pred (c∷ c))

Ctbl-rep : ∀ {a} n → Ctbl (replicate n (ψᵗ [] a))
Ctbl-rep zero    = c[]
Ctbl-rep (suc n) = c∷ (Ctbl-rep n)

Ctbl-fsn : ∀ {u} → Ctbl u → cof u ≡ cω → ∀ n → Ctbl (fsn u n)
Ctbl-fsn c[] () n
Ctbl-fsn (c∷ {a = []} c[]) () n
Ctbl-fsn (c∷ {a = y ∷ ys} c[]) e n with viewA [] y ys e
... | v4 ke      = subst Ctbl (sym (fs-rep [] y ys ke n)) (Ctbl-rep n)
... | v5 ke      = subst Ctbl (sym (fs-ω [] y ys ke n)) (c∷ c[])
... | v6 ν ke em = subst Ctbl (sym (fs-gt [] y ys ν ke em n)) (c∷ c[])
Ctbl-fsn (c∷ (c∷ c)) e n = c∷ (Ctbl-fsn (c∷ c) e n)

NF-rep : ∀ {x} → NFᴾ x → ∀ n → NF (replicate n x)
NF-rep nx zero          = n[]
NF-rep nx (suc zero)    = n∷ nx n[] tt
NF-rep {x = x} nx (suc (suc n)) = n∷ nx (NF-rep nx (suc n)) (inj₂ (cmpᴾ-refl x))
```

```agda
NF-ν : ∀ {b ν} → NF b → cof b ≡ cΩ ν → NF ν × Ctbl ν
NF-ν n[] ()
NF-ν (n∷ nx (n∷ ny nys hy) hx) e = NF-ν (n∷ ny nys hy) e
NF-ν (n∷ (nψ {u = []} {a = []} _ _ _ _) n[] _) ()
NF-ν (n∷ (nψ {u = w ∷ ws} {a = []} nw cw _ _) n[] _) e with leafInv (w ∷ ws) cw (cof (w ∷ ws)) refl e
... | leafΩ ue refl = NF-pred nw ue , Ctbl-pred cw
NF-ν (n∷ (nψ {u = x} {a = y ∷ ys} _ _ nb _) n[] _) e with penInv x (y ∷ ys) (cof (y ∷ ys)) refl e
... | penΩ be pn = NF-ν nb be

tail< : ∀ {zs x p} → Hd≤ zs x → x <ᴾ p → zs <ᵀ (p ∷ [])
tail< {zs = []} h q = []<
tail< {zs = y ∷ ys} {x = x} (inj₁ e) q = hd< (<ᴾ-trans (lt→<ᴾ y x e) q)
tail< {zs = y ∷ ys} {x = x} (inj₂ e) q = hd< (subst (_<ᴾ _) (sym (eq→≡ᴾ y x e)) q)

noVis : ∀ {η ν x ζ} → NF η → η <ᵀ Ωs ν → sucT ν ≤ᵀ x → Vis x ζ η → ⊥
noVis nη (hd< (lv< q)) h (vh h′)   = <→≱ q (≤-trans′ h h′)
noVis nη (hd< (lv< q)) h (vd h′ _) = <→≱ q (≤-trans′ h h′)
noVis (n∷ _ nzs hz) (hd< p) h (vt v) = noVis nzs (tail< hz p) h v
noVis nη (hd< (ar< ())) h v
noVis nη (tl< ()) h v
```

```agda
GFS : ∀ u S {X} n → NF X → cof X ≡ cω → (∀ {ζ} → Vis u ζ X → ζ <ᵀ plugR S X) →
      ∀ {ζ′} → Vis u ζ′ (fsn X n) → ζ′ <ᵀ plugR S (fsn X n)
GFS5 : ∀ u S x {d} n → NF d → cof d ≡ cω → (∀ {ζ} → Vis u ζ (ψᵗ x d ∷ []) → ζ <ᵀ plugR S (ψᵗ x d ∷ [])) →
       ∀ {ζ′} → Vis u ζ′ (ψᵗ x (fsn d n) ∷ []) → ζ′ <ᵀ plugR S (ψᵗ x (fsn d n) ∷ [])
GFS6 : ∀ u S x {d ν} n → NF d → cof d ≡ cΩ ν → (∀ {ζ} → Vis u ζ (ψᵗ x d ∷ []) → ζ <ᵀ plugR S (ψᵗ x d ∷ [])) →
       ∀ {ζ′} → Vis u ζ′ (ψᵗ x (fsT d (γT d ν n)) ∷ []) → ζ′ <ᵀ plugR S (ψᵗ x (fsT d (γT d ν n)) ∷ [])
GΩ  : ∀ u S {X ν η} → NF X → cof X ≡ cΩ ν → η <ᵀ Ωs ν → (∀ {ζ} → Vis u ζ X → ζ <ᵀ plugR S X) →
      (∀ {ζ} → Vis u ζ η → ζ <ᵀ plugR S (fsT X η)) →
      ∀ {ζ′} → Vis u ζ′ (fsT X η) → ζ′ <ᵀ plugR S (fsT X η)
GΩp : ∀ u S x {d ν η} → NF d → cof d ≡ cΩ ν → η <ᵀ Ωs ν →
      (∀ {ζ} → Vis u ζ (ψᵗ x d ∷ []) → ζ <ᵀ plugR S (ψᵗ x d ∷ [])) →
      (∀ {ζ} → Vis u ζ η → ζ <ᵀ plugR S (ψᵗ x (fsT d η) ∷ [])) →
      ∀ {ζ′} → Vis u ζ′ (ψᵗ x (fsT d η) ∷ []) → ζ′ <ᵀ plugR S (ψᵗ x (fsT d η) ∷ [])
Gγ  : ∀ u S {d ν} → NF d → cof d ≡ cΩ ν → (∀ {ζ} → Vis u ζ d → ζ <ᵀ plugR S d) →
      (∀ k → fsT d (γT d ν k) ≤ᵀ plugR S (fsT d (γT d ν k))) →
      ∀ k {ζ} → Vis u ζ (γT d ν k) → ζ <ᵀ plugR S (fsT d (γT d ν k))

-- fixed head summand
fixHd : ∀ u S {x₀ a R R′ ζ} → (∀ {ζ} → Vis u ζ (ψᵗ x₀ a ∷ R) → ζ <ᵀ plugR S (ψᵗ x₀ a ∷ R)) →
        Vis u ζ (ψᵗ x₀ a ∷ []) → ζ <ᵀ plugR S (ψᵗ x₀ a ∷ R′)
fixHd u S {x₀ = x₀} {a = a} H (vh h) = LIFTR S (sz a) (pfxC (ψᵗ x₀ a ∷ []) (sz a) (sz-hdarg x₀ a [])) ≤-refl (H (vh h))
fixHd u S {x₀ = x₀} {a = a} {ζ = ζ} H (vd h v) =
  LIFTR S (sz ζ) (pfxC (ψᵗ x₀ a ∷ []) (sz ζ) (<ℕ-trans (Vis-sz v) (sz-hdarg x₀ a []))) ≤-refl (H (vd h v))
fixHd u S H (vt ())

GFS4 : ∀ u S x {d} n → cof d ≡ c1 → (∀ {ζ} → Vis u ζ (ψᵗ x d ∷ []) → ζ <ᵀ plugR S (ψᵗ x d ∷ [])) →
       ∀ {ζ′} → Vis u ζ′ (replicate n (ψᵗ x (pred d))) → ζ′ <ᵀ plugR S (replicate n (ψᵗ x (pred d)))
GFS4 u S x {d} (suc m) ke H v′ = k1 (Vis-rep m v′)
  where
  pd = pred d
  k1 : ∀ {ζ′} → Vis u ζ′ (ψᵗ x pd ∷ []) → ζ′ <ᵀ plugR S (ψᵗ x pd ∷ replicate m (ψᵗ x pd))
  k1 (vh h)    = LIFTR S (sz pd) (c4C ke _) ≤-refl (<ᵀ-trans (E.pred-< d ke) (H (vh h)))
  k1 (vd h v″) = LIFTR S (sz pd) (c4C ke _) (<⇒≤ (Vis-sz v″)) (H (vd h (Vis-pred ke v″)))
  k1 (vt ())

GFS u S n n[] () v
GFS u S n (n∷ nx (n∷ ny nys hy) hx) e H (vh h)   = fixHd u S H (vh h)
GFS u S n (n∷ nx (n∷ ny nys hy) hx) e H (vd h v) = fixHd u S H (vd h v)
GFS u S {X = x ∷ _} n (n∷ nx (n∷ ny nys hy) hx) e H (vt v) = GFS u (pre (x ∷ []) ∷ S) n (n∷ ny nys hy) e (λ v′ → H (vt v′)) v
GFS u S n (n∷ (nψ {u = []} {a = []} _ _ _ _) n[] _) () v
GFS u S {X = ψᵗ (w ∷ ws) [] ∷ []} n nX e H {ζ′} v =
  subst (λ z → Vis u ζ′ z → ζ′ <ᵀ plugR S z) (sym (E.fsn0-eq w ws n ke)) k v
  where
  ke = viewL w ws e
  k : Vis u ζ′ (ψᵗ (fsn (w ∷ ws) n) [] ∷ []) → ζ′ <ᵀ plugR S (ψᵗ (fsn (w ∷ ws) n) [] ∷ [])
  k (vh h) = []<plugR S
  k (vd h ())
  k (vt ())
GFS u S {X = ψᵗ x (y ∷ ys) ∷ []} n (n∷ (nψ nx cx nb g) n[] hx) e H {ζ′} v with viewA x y ys e
... | v4 ke = subst (λ z → Vis u ζ′ z → ζ′ <ᵀ plugR S z) (sym (fs-rep x y ys ke n)) (GFS4 u S x n ke H) v
... | v5 ke = subst (λ z → Vis u ζ′ z → ζ′ <ᵀ plugR S z) (sym (fs-ω x y ys ke n)) (GFS5 u S x n nb ke H) v
... | v6 ν ke em = subst (λ z → Vis u ζ′ z → ζ′ <ᵀ plugR S z) (sym (fs-gt x y ys ν ke em n)) (GFS6 u S x n nb ke H) v

GFS5 u S x {d} n nb ke H (vh h)    = SELF (sz d) (nd x ∷ S) ≤-refl here nb ke (H (vh h)) n
GFS5 u S x n nb ke H (vd h v′) = GFS u (nd x ∷ S) n nb ke (λ v″ → H (vd h v″)) v′
GFS5 u S x n nb ke H (vt ())

GFS6 u S x {d} {ν} n nb ke H (vh h)    = SELFΩ (sz d) (nd x ∷ S) ≤-refl here nb ke (γ<Ωs d ν n) (H (vh h))
GFS6 u S x {d} {ν} n nb ke H (vd h v′) =
  GΩ u (nd x ∷ S) nb ke (γ<Ωs d ν n) (λ v″ → H (vd h v″))
     (Gγ u (nd x ∷ S) nb ke (λ v″ → H (vd h v″))
         (λ j → inj₁ (SELFΩ (sz d) (nd x ∷ S) ≤-refl here nb ke (γ<Ωs d ν j) (H (vh h)))) n) v′
GFS6 u S x n nb ke H (vt ())

GΩ u S n[] () η< H Hη v
GΩ u S (n∷ nx (n∷ ny nys hy) hx) e η< H Hη (vh h)   = fixHd u S H (vh h)
GΩ u S (n∷ nx (n∷ ny nys hy) hx) e η< H Hη (vd h v) = fixHd u S H (vd h v)
GΩ u S {X = x ∷ _} (n∷ nx (n∷ ny nys hy) hx) e η< H Hη (vt v) =
  GΩ u (pre (x ∷ []) ∷ S) (n∷ ny nys hy) e η< (λ v′ → H (vt v′)) Hη v
GΩ u S (n∷ (nψ {u = []} {a = []} _ _ _ _) n[] _) () η< H Hη v
GΩ u S {X = ψᵗ (w ∷ ws) [] ∷ []} {η = η} nX e η< H Hη {ζ′} v with leafInv (w ∷ ws) (nf-ctbl nX) (cof (w ∷ ws)) refl e
... | leafΩ ue refl = Hη (subst (Vis u ζ′) (fsT-c1 (w ∷ ws) (cof (w ∷ ws)) ue η) v)
GΩ u S {X = ψᵗ x (y ∷ ys) ∷ []} {ν = ν} {η = η} (n∷ (nψ nx cx nb g) n[] hx) e η< H Hη {ζ′} v
  with penInv x (y ∷ ys) (cof (y ∷ ys)) refl e
... | penΩ be pn = subst (λ z → Vis u ζ′ z → ζ′ <ᵀ plugR S z) (sym eqT)
                         (GΩp u S x nb be η< H (λ {ζ} vη → subst (λ z → ζ <ᵀ plugR S z) eqT (Hη vη))) v
  where
  eqT : fsT (ψᵗ x (y ∷ ys) ∷ []) η ≡ ψᵗ x (fsT (y ∷ ys) η) ∷ []
  eqT = fsT₊-pen′ x (y ∷ ys) ν (cof (y ∷ ys)) be pn η

GΩp u S x {d} nb be η< H Hη (vh h)    = SELFΩ (sz d) (nd x ∷ S) ≤-refl here nb be η< (H (vh h))
GΩp u S x nb be η< H Hη (vd h v′) = GΩ u (nd x ∷ S) nb be η< (λ v″ → H (vd h v″)) Hη v′
GΩp u S x nb be η< H Hη (vt ())

Gγ u S nD e H Sγ zero (vh h) = <≤-trans (fsT-ne e []<) (Sγ zero)
Gγ u S nD e H Sγ zero (vd h ())
Gγ u S nD e H Sγ zero (vt ())
Gγ u S nD e H Sγ (suc k) (vh h) = <≤-trans (fsT-mono nD e (γ-mono nD e k)) (Sγ (suc k))
Gγ u S {d = d} {ν = ν} nD e H Sγ (suc k) (vd h v) =
  <ᵀ-trans (GΩ u S nD e (γ<Ωs d ν k) H (Gγ u S nD e H Sγ k) v) (plugR-mono S (fsT-mono nD e (γ-mono nD e k)))
Gγ u S nD e H Sγ (suc k) (vt ())
```

```agda
NF-fsT : ∀ {d ν η} → NF d → cof d ≡ cΩ ν → NF η → η <ᵀ Ωs ν → NF (fsT d η)
NF-fsT n[] () nη η<
NF-fsT (n∷ nx (n∷ {x = y} {xs = ys} ny nys hy) hx) e nη η< =
  n∷ nx (NF-fsT (n∷ ny nys hy) e nη η<) (Hd≤-desc (fsT-desc {W = y ∷ ys} e η<) hx)
NF-fsT (n∷ (nψ {u = []} {a = []} _ _ _ _) n[] _) () nη η<
NF-fsT {η = η} (n∷ (nψ {u = w ∷ ws} {a = []} _ cw _ _) n[] _) e nη η< with leafInv (w ∷ ws) cw (cof (w ∷ ws)) refl e
... | leafΩ ue refl = subst NF (sym (fsT-c1 (w ∷ ws) (cof (w ∷ ws)) ue η)) nη
NF-fsT {ν = ν} {η = η} (n∷ (nψ {u = x} {a = y ∷ ys} nx cx nb g) n[] _) e nη η< with penInv x (y ∷ ys) (cof (y ∷ ys)) refl e
... | penΩ be pn = subst NF (sym (fsT₊-pen′ x (y ∷ ys) ν (cof (y ∷ ys)) be pn η))
  (n∷ (nψ nx cx (NF-fsT nb be nη η<)
          (λ v → GΩ x [] nb be η< g (λ vη → ⊥-elim (noVis nη η< (Pen→≤ (sucT ν) x pn) vη)) v)) n[] tt)

NF-γ : ∀ {d ν} → NF d → cof d ≡ cΩ ν → NF ν → Ctbl ν → Bnd ν d → ∀ k → NF (γT d ν k)
NF-γ nD e nν cν g zero    = n∷ (nψ nν cν n[] bnd[]) n[] tt
NF-γ {d = d} {ν = ν} nD e nν cν g (suc k) =
  n∷ (nψ nν cν (NF-fsT nD e (NF-γ nD e nν cν g k) (γ<Ωs d ν k))
         (λ v → GΩ ν [] nD e (γ<Ωs d ν k) g (Gγ ν [] nD e g (λ _ → inj₂ refl) k) v)) n[] tt

NF-fsn : ∀ {t} → NF t → cof t ≡ cω → ∀ n → NF (fsn t n)
NF-fsn n[] () n
NF-fsn (n∷ nx (n∷ {x = y} {xs = ys} ny nys hy) hx) e n =
  n∷ nx (NF-fsn (n∷ ny nys hy) e n) (Hd≤-desc (fs<ᵀ {u = y ∷ ys} e n) hx)
NF-fsn (n∷ (nψ {u = []} {a = []} _ _ _ _) n[] _) () n
NF-fsn (n∷ (nψ {u = w ∷ ws} {a = []} nw cw _ _) n[] _) e n =
  subst NF (sym (E.fsn0-eq w ws n ke)) (n∷ (nψ (NF-fsn nw ke n) (Ctbl-fsn cw ke n) n[] bnd[]) n[] tt)
  where ke = viewL w ws e
NF-fsn (n∷ (nψ {u = x} {a = y ∷ ys} nx cx nb g) n[] _) e n with viewA x y ys e
... | v4 ke = subst NF (sym (fs-rep x y ys ke n)) (NF-rep (nψ nx cx (NF-pred nb ke) (Bnd-pred g ke)) n)
... | v5 ke = subst NF (sym (fs-ω x y ys ke n)) (n∷ (nψ nx cx (NF-fsn nb ke n) (λ v → GFS x [] n nb ke g v)) n[] tt)
... | v6 ν ke em = subst NF (sym (fs-gt x y ys ν ke em n))
  (n∷ (nψ nx cx (NF-fsT nb ke (NF-γ nb ke (proj₁ nνc) (proj₂ nνc) (λ v → g (Vis-mono xν v)) n) (γ<Ωs (y ∷ ys) ν n))
          (λ v → GΩ x [] nb ke (γ<Ωs (y ∷ ys) ν n) g (Gγ x [] nb ke g (λ _ → inj₂ refl) n) v)) n[] tt)
  where
  nνc = NF-ν nb ke
  xν : x ≤ᵀ ν
  xν = gt→≤ ν x em
```

## §7 对角线与可数性

```agda
diag-Ctbl : ∀ k → Ctbl (γᴱ k)
diag-Ctbl zero    = c∷ c[]
diag-Ctbl (suc k) = c∷ c[]

diag-NF : ∀ k → NF (γᴱ k)
diag-NF zero    = n∷ (nψ n[] c[] n[] bnd[]) n[] tt
diag-NF (suc k) = n∷ (nψ n[] c[] (n∷ (nψ (diag-NF k) (diag-Ctbl k) n[] bnd[]) n[] tt) bΩ) n[] tt
  where
  bΩ : Bnd [] (Ωt (γᴱ k))
  bΩ (vh h) = []<
  bΩ (vd h ())
  bΩ (vt ())

[]≤ : ∀ β → [] ≤ᵀ β
[]≤ []      = inj₂ refl
[]≤ (x ∷ β) = inj₁ []<

-- a normal form below a countable term is countable
Ctbl-tl : ∀ {a ws} → NF (ψᵗ [] a ∷ ws) → Ctbl ws
Ctbl-tl (n∷ _ n[] _) = c[]
Ctbl-tl (n∷ _ (n∷ {x = ψᵗ z b} nz nzs hz) (inj₁ e)) with lt→<ᴾ (ψᵗ z b) (ψᵗ [] _) e
... | lv< ()
... | ar< _ = c∷ (Ctbl-tl (n∷ nz nzs hz))
Ctbl-tl (n∷ _ (n∷ {x = ψᵗ z b} nz nzs hz) (inj₂ e)) with eq→≡ᴾ (ψᵗ z b) (ψᵗ [] _) e
... | refl = c∷ (Ctbl-tl (n∷ nz nzs hz))

Ctbl-≤ : ∀ {w β} → NF w → Ctbl β → w ≤ᵀ β → Ctbl w
Ctbl-≤ n[] cβ le = c[]
Ctbl-≤ nw cβ (inj₂ refl) = cβ
Ctbl-≤ nw@(n∷ (nψ {u = []} _ _ _ _) _ _) (c∷ cβ) (inj₁ _) = c∷ (Ctbl-tl nw)
Ctbl-≤ (n∷ (nψ {u = z ∷ zs} _ _ _ _) _ _) (c∷ cβ) (inj₁ (hd< (lv< ())))
Ctbl-≤ (n∷ (nψ {u = z ∷ zs} _ _ _ _) _ _) c[] (inj₁ ())
```

```agda
data Desc (t₀ : T) : T → Set where
  d₀ : Desc t₀ t₀
  dω : ∀ {t} → Desc t₀ t → cof t ≡ cω → ∀ n → Desc t₀ (fsn t n)
  d₁ : ∀ {t} → Desc t₀ t → cof t ≡ c1 → Desc t₀ (pred t)
```

## §9 结论与边界
