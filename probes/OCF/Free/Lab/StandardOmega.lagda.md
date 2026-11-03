# StandardOmega (验收副本)

> **验收用, 不在主线闭包内.** 脚本从 [StandardOmega](../../Align/StandardOmega.lagda.md) 切出: 只留 `UniformNF5Accept` 的定义级切片里、主线 `OCF.Free.*` 之外的块, 代码行逐字, 导入改指 `OCF.Free.*`. 讲解见原文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.Lab.StandardOmega where

open import Data.Nat using (ℕ; zero; suc; _+_; z≤n; s≤s) renaming (_≤_ to _≤ℕ_; _<_ to _<ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; m≤n+m; <⇒≤; <-irrefl; ≤-<-trans; <-≤-trans; ≤-pred) renaming (<-trans to <ℕ-trans)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst; subst₂) 
open import OCF.Free.Lab.Closure using (Pen; cmpᴾ-refl; cmpᵀ-refl; lt→<; lt→<ᴾ; eq→≡; eq→≡ᴾ; <→lt; <ᵀ-trans; <ᴾ-trans; fsT₊-pen′)
open import OCF.Free.Lab.Bachmann using (<ᵀ-irrefl; <ᵀ-asym; <sucT; pen→<; gt→≤; Hd≤; Hd≤-desc; cofA≢c1; fs-gt; fs<ᵀ)
open import OCF.Free.Lab.Correspond using (cof-ne; fs-rep; fs-ω; fsT-c1; γᴱ; βᴱ; diag-fs)
open import OCF.Free.Lab.Standard using (_≤ᵀ_; Pen→≤; <≤-trans; ≤-trans′; <→≱; ++-mono; sz; szᴾ; sz-++; sz-hd; sz-tl; sz-hdarg; sz-suffix; split; inS; past; PFX; V1; v[]; vlv; var; inv1; fsn-++; fsT-++; cof-++; Ctbl; c[]; c∷; Ctbl-cof; Ctbl-pred; Ctbl-fsn; PenΩ; penΩ; penInv; γ<Ωs; <++′; fsT-desc; ViewA; v4; v5; v6; viewA; viewL; belowΩ; cof[]≢ω; cof[]≢Ω; fsT-ne; cofψ0≢c1; tail<; []≤; Desc; d₀; dω; d₁)
open import OCF.Free.Lab.Stage2 using (Ωᵗ; t2; b₂; γ′ᴱ)
import OCF.Align.EBO as E
import OCF.Free.Lab.Standard as Std 
```

```agda
open E using (T; PT; Cof; c0; c1; cω; cΩ; Cmp; lt; eq; gt; cmpᵀ; cof; cofA; cofψ0; cofψ₊;
              pred; sucT; Ωt; Ωs; natT; fsn; fsT; fsT0; γT; dec;
              _<ᵀ_; _<ᴾ_; []<; hd<; tl<; lv<; ar<)
       renaming (ψ to ψᵗ)
```

## §1 下标类与可见参数

```agda
Ω₁ : PT
Ω₁ = ψᵗ (natT 1) []

data Sb : T → Set where
  sC : ∀ {w} → Ctbl w → Sb w
  sΩ : ∀ {c} → Ctbl c → Sb (Ω₁ ∷ c)

data Vis₁ (w : T) : T → T → Set where
  vh : ∀ {x a xs}   → w ≤ᵀ x → Vis₁ w a (ψᵗ x a ∷ xs)
  vd : ∀ {x a xs ζ} → w ≤ᵀ x → Vis₁ w ζ a → Vis₁ w ζ (ψᵗ x a ∷ xs)
  vs : ∀ {x a xs ζ} → w ≤ᵀ x → Vis₁ w ζ x → Vis₁ w ζ (ψᵗ x a ∷ xs)
  vt : ∀ {x xs ζ}   → Vis₁ w ζ xs → Vis₁ w ζ (x ∷ xs)

Bnd₁ : T → T → Set
Bnd₁ w a = ∀ {ζ} → Vis₁ w ζ a → ζ <ᵀ a

data NF₁ : T → Set
data NFᴾ₁ : PT → Set
data NF₁ where
  n[] : NF₁ []
  n∷  : ∀ {x xs} → NFᴾ₁ x → NF₁ xs → Hd≤ xs x → NF₁ (x ∷ xs)
data NFᴾ₁ where
  nψ : ∀ {u a} → NF₁ u → Sb u → NF₁ a → Bnd₁ u a → NFᴾ₁ (ψᵗ u a)

bnd[] : ∀ {w} → Bnd₁ w []
bnd[] ()
```

```agda
sz-sub : ∀ x a xs → sz x <ℕ sz (ψᵗ x a ∷ xs)
sz-sub x a xs = <-≤-trans (s≤s (m≤m+n (sz x) (sz a))) (sz-hd (ψᵗ x a) xs)

Vis-sz : ∀ {w ζ t} → Vis₁ w ζ t → sz ζ <ℕ sz t
Vis-sz (vh {x = x} {a = a} {xs = xs} _)   = sz-hdarg x a xs
Vis-sz (vd {x = x} {a = a} {xs = xs} _ v) = <ℕ-trans (Vis-sz v) (sz-hdarg x a xs)
Vis-sz (vs {x = x} {a = a} {xs = xs} _ v) = <ℕ-trans (Vis-sz v) (sz-sub x a xs)
Vis-sz (vt {x = x} {xs = xs} v)           = <-≤-trans (Vis-sz v) (sz-tl x xs)

Vis-mono : ∀ {w w′ ζ t} → w ≤ᵀ w′ → Vis₁ w′ ζ t → Vis₁ w ζ t
Vis-mono h (vh h′)   = vh (≤-trans′ h h′)
Vis-mono h (vd h′ v) = vd (≤-trans′ h h′) (Vis-mono h v)
Vis-mono h (vs h′ v) = vs (≤-trans′ h h′) (Vis-mono h v)
Vis-mono h (vt v)    = vt (Vis-mono h v)

Vis-trans : ∀ {w ζ d t} → Vis₁ w ζ d → Vis₁ w d t → Vis₁ w ζ t
Vis-trans v (vh h)    = vd h v
Vis-trans v (vd h v′) = vd h (Vis-trans v v′)
Vis-trans v (vs h v′) = vs h (Vis-trans v v′)
Vis-trans v (vt v′)   = vt (Vis-trans v v′)

Vis-++ : ∀ {w ζ s} t → Vis₁ w ζ s → Vis₁ w ζ (s ++ t)
Vis-++ t (vh h)   = vh h
Vis-++ t (vd h v) = vd h v
Vis-++ t (vs h v) = vs h v
Vis-++ t (vt v)   = vt (Vis-++ t v)

≤<-trans : ∀ {a b c} → a ≤ᵀ b → b <ᵀ c → a <ᵀ c
≤<-trans (inj₁ p) q = <ᵀ-trans p q
≤<-trans (inj₂ refl) q = q
```

```agda
data Leaf₁ : T → T → Set where
  reg  : ∀ {u} → cof u ≡ c1 → Leaf₁ u (pred u)
  sing : Leaf₁ Ωᵗ []

leafInv₁ : ∀ u → Sb u → ∀ k → cof u ≡ k → ∀ {ν} → cofψ0 u k ≡ cΩ ν → Leaf₁ u ν
leafInv₁ u su c0 _ ()
leafInv₁ u su c1 ue refl = reg ue
leafInv₁ u su cω _ ()
leafInv₁ u (sC cu) (cΩ μ) ue e = ⊥-elim (Ctbl-cof cu ue)
leafInv₁ .(Ω₁ ∷ []) (sΩ c[]) (cΩ .[]) refl refl = sing
leafInv₁ .(Ω₁ ∷ ψᵗ [] _ ∷ _) (sΩ (c∷ cc)) (cΩ μ) ue e = ⊥-elim (Ctbl-cof (c∷ cc) ue)

Sb-pred : ∀ {u} → Sb u → Sb (pred u)
Sb-pred (sC c)       = sC (Ctbl-pred c)
Sb-pred (sΩ c[])     = sΩ c[]
Sb-pred (sΩ (c∷ cc)) = sΩ (Ctbl-pred (c∷ cc))

Sb-fsn : ∀ {u} → Sb u → cof u ≡ cω → ∀ n → Sb (fsn u n)
Sb-fsn (sC c) e n       = sC (Ctbl-fsn c e n)
Sb-fsn (sΩ c[]) () n
Sb-fsn (sΩ (c∷ cc)) e n = sΩ (Ctbl-fsn (c∷ cc) e n)

ctblΩ : ∀ {η} → NF₁ η → η <ᵀ Ωᵗ → Ctbl η
ctblΩ n[] p = c[]
ctblΩ (n∷ {x = ψᵗ z b} nz nzs hz) (hd< (lv< q)) with <sucT [] q
... | inj₁ ()
... | inj₂ refl = c∷ (ctblΩ nzs (tail< hz (lv< q)))
ctblΩ (n∷ _ _ _) (hd< (ar< ()))
ctblΩ (n∷ _ _ _) (tl< ())

NF₁-pred : ∀ {t} → NF₁ t → cof t ≡ c1 → NF₁ (pred t)
NF₁-pred n[] ()
NF₁-pred (n∷ nx (n∷ {x = y} {xs = ys} ny nys hy) hx) e =
  n∷ nx (NF₁-pred (n∷ ny nys hy) e) (Hd≤-desc (E.pred-< (y ∷ ys) e) hx)
NF₁-pred (n∷ (nψ {u = []} {a = []} _ _ _ _) n[] _) e = n[]
NF₁-pred (n∷ (nψ {u = w ∷ ws} {a = []} _ _ _ _) n[] _) e = ⊥-elim (cofψ0≢c1 (w ∷ ws) (cof (w ∷ ws)) e)
NF₁-pred (n∷ (nψ {u = u} {a = y ∷ ys} _ _ _ _) n[] _) e = ⊥-elim (cofA≢c1 u (cof (y ∷ ys)) e)

NF-ν₁ : ∀ {b ν} → NF₁ b → cof b ≡ cΩ ν → NF₁ ν × Sb ν
NF-ν₁ n[] ()
NF-ν₁ (n∷ nx (n∷ ny nys hy) hx) e = NF-ν₁ (n∷ ny nys hy) e
NF-ν₁ (n∷ (nψ {u = []} {a = []} _ _ _ _) n[] _) ()
NF-ν₁ (n∷ (nψ {u = w ∷ ws} {a = []} nw sw _ _) n[] _) e with leafInv₁ (w ∷ ws) sw (cof (w ∷ ws)) refl e
... | reg ue = NF₁-pred nw ue , Sb-pred sw
... | sing   = n[] , sC c[]
NF-ν₁ (n∷ (nψ {u = x} {a = y ∷ ys} _ _ nb _) n[] _) e with penInv x (y ∷ ys) (cof (y ∷ ys)) refl e
... | penΩ be pn = NF-ν₁ nb be
```

## §2 共尾性

```agda
repb : ∀ x {vs} → NF₁ vs → Hd≤ vs x → Σ ℕ λ m → vs <ᵀ replicate m x
repb x n[] h = 1 , []<
repb x (n∷ {x = y} ny nzs hz₀) (inj₁ e) = 1 , hd< (lt→<ᴾ y x e)
repb x (n∷ {x = y} ny nzs hz₀) (inj₂ e) with eq→≡ᴾ y x e
... | refl with repb x nzs hz₀
...   | m , q = suc m , tl< q

HdV : T → T → T → Set
HdV ν θ c = ∀ {x ζ θs} → θ ≡ ψᵗ x ζ ∷ θs → ν ≤ᵀ x → Vis₁ ν ζ c

record ΩC (b ν c : T) : Set where
  constructor ωc
  field
    θ  : T
    θ< : θ <ᵀ Ωs ν
    fθ : ∀ {η} → θ <ᵀ η → c <ᵀ fsT b η
    hv : HdV ν θ c

hv[] : ∀ {ν c} → HdV ν [] c
hv[] () _

singΩ : ∀ {c} → c <ᵀ βᴱ → ΩC βᴱ [] c
singΩ []< = ωc [] []< (λ _ → []<) hv[]
singΩ {c = ψᵗ x a ∷ cs} (hd< (lv< q)) =
  ωc x q (λ r → hd< (lv< r)) (λ {y} {ζ} {θs} eθ h → vs ([]≤ x) (subst (Vis₁ [] ζ) (sym eθ) (vh h)))
singΩ (hd< (ar< ()))
singΩ (tl< ())

Ωcof : ∀ {b ν} → NF₁ b → cof b ≡ cΩ ν → ∀ {c} → c <ᵀ b → ΩC b ν c
Ωcof n[] () p
Ωcof (n∷ nx (n∷ ny nys hy) hx) e []<      = ωc [] []< (λ _ → []<) hv[]
Ωcof (n∷ nx (n∷ ny nys hy) hx) e (hd< q)  = ωc [] []< (λ _ → hd< q) hv[]
Ωcof (n∷ nx (n∷ ny nys hy) hx) e (tl< q) with Ωcof (n∷ ny nys hy) e q
... | ωc θ θ< fθ hv = ωc θ θ< (λ r → tl< (fθ r)) (λ eθ h → vt (hv eθ h))
Ωcof (n∷ (nψ {u = []} {a = []} nw cw na g) n[] hx) () p
Ωcof (n∷ (nψ {u = w ∷ ws} {a = []} nw cw na g) n[] hx) e {c} p
  with leafInv₁ (w ∷ ws) cw (cof (w ∷ ws)) refl e
... | reg ue =
  ωc c (subst (λ z → c <ᵀ ψᵗ z [] ∷ []) (sym (E.pred-suc (w ∷ ws) ue)) p)
       (λ {η} r → subst (c <ᵀ_) (sym (fsT-c1 (w ∷ ws) (cof (w ∷ ws)) ue η)) r)
       (λ {x} {ζ} {θs} eθ h → subst (Vis₁ _ ζ) (sym eθ) (vh h))
... | sing = singΩ p
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
Cof6 : ∀ m {b ν w c} → NF₁ b → cof b ≡ cΩ ν → w ≤ᵀ ν → sz c ≤ℕ m → c <ᵀ b →
       (∀ {ζ} → Vis₁ w ζ c → ζ <ᵀ b) → Σ ℕ λ n → c <ᵀ fsT b (γT b ν n)
Cof6 m {b} {ν} {w} {c} nb be wν hm p H with Ωcof nb be p
... | ωc [] θ< fθ hv = 0 , fθ []<
... | ωc (ψᵗ x ζ′ ∷ θs) (hd< (lv< q)) fθ hv with <sucT ν q
...   | inj₁ r = 0 , fθ (hd< (lv< r))
...   | inj₂ refl = go m hm
  where
  vz : Vis₁ ν ζ′ c
  vz = hv refl (inj₂ refl)
  go : ∀ m′ → sz c ≤ℕ m′ → Σ ℕ λ n → c <ᵀ fsT b (γT b ν n)
  go zero h = ⊥-elim (<-irrefl refl (<-≤-trans (≤-<-trans z≤n (Vis-sz vz)) h))
  go (suc m′) h with Cof6 m′ nb be wν (≤-pred (≤-trans (Vis-sz vz) h)) (H (Vis-mono wν vz))
                         (λ v → H (Vis-trans v (Vis-mono wν vz)))
  ... | k , r = suc k , fθ (hd< (ar< r))
Cof6 m nb be wν hm p H | ωc (ψᵗ x ζ′ ∷ θs) (hd< (ar< ())) fθ hv
Cof6 m nb be wν hm p H | ωc (ψᵗ x ζ′ ∷ θs) (tl< ()) fθ hv

cofin₁  : ∀ {u} → NF₁ u → cof u ≡ cω → ∀ {v} → NF₁ v → v <ᵀ u → Σ ℕ λ n → v <ᵀ fsn u n
cofinL : ∀ {w ws} → NF₁ (w ∷ ws) → ∀ k → cof (w ∷ ws) ≡ k → cofψ0 (w ∷ ws) k ≡ cω →
         ∀ {v} → NF₁ v → v <ᵀ Ωt (w ∷ ws) → Σ ℕ λ n → v <ᵀ fsn (Ωt (w ∷ ws)) n
cofinA : ∀ {w y ys} → NF₁ (y ∷ ys) → ∀ k → cof (y ∷ ys) ≡ k → cofA w k ≡ cω →
         ∀ {v} → NF₁ v → v <ᵀ (ψᵗ w (y ∷ ys) ∷ []) → Σ ℕ λ n → v <ᵀ fsn (ψᵗ w (y ∷ ys) ∷ []) n

cofin₁ n[] () nv p
cofin₁ (n∷ nx (n∷ ny nys hy) hx) e nv []<     = 0 , []<
cofin₁ (n∷ nx (n∷ ny nys hy) hx) e nv (hd< q) = 0 , hd< q
cofin₁ (n∷ nx (n∷ ny nys hy) hx) e (n∷ _ nvs _) (tl< q) with cofin₁ (n∷ ny nys hy) e nvs q
... | n , r = n , tl< r
cofin₁ (n∷ (nψ {u = []} {a = []} nw cw na g) n[] hx) () nv p
cofin₁ (n∷ (nψ {u = w ∷ ws} {a = []} nw cw na g) n[] hx) e nv p = cofinL nw (cof (w ∷ ws)) refl e nv p
cofin₁ (n∷ (nψ {u = w} {a = y ∷ ys} nw cw na g) n[] hx) e nv p = cofinA na (cof (y ∷ ys)) refl e nv p

cofinL nw c0 ke () nv p
cofinL nw c1 ke () nv p
cofinL {w} {ws} nw cω ke e nv []< = 0 , subst ([] <ᵀ_) (sym (E.fsn0-eq w ws 0 ke)) []<
cofinL {w} {ws} nw cω ke e (n∷ (nψ nx _ _ _) _ _) (hd< (lv< q)) with cofin₁ nw ke nx q
... | n , r = n , subst (_ <ᵀ_) (sym (E.fsn0-eq w ws n ke)) (hd< (lv< r))
cofinL nw cω ke e nv (hd< (ar< ()))
cofinL nw cω ke e nv (tl< ())
cofinL nw (cΩ μ) ke () nv p

cofinA nb c0 ke e nv p = ⊥-elim (cof-ne _ _ ke)
cofinA {w} {y} {ys} nb c1 ke e n[] []< = 1 , subst ([] <ᵀ_) (sym (fs-rep w y ys ke 1)) []<
cofinA {w} {y} {ys} nb c1 ke e nv (hd< (lv< q)) = 1 , subst (_ <ᵀ_) (sym (fs-rep w y ys ke 1)) (hd< (lv< q))
cofinA {w} {y} {ys} nb c1 ke e (n∷ {x = ψᵗ _ c} {xs = vs′} nc nvs hv) (hd< (ar< q))
  with <sucT (pred (y ∷ ys)) (subst (c <ᵀ_) (sym (E.pred-suc (y ∷ ys) ke)) q)
... | inj₁ r = 1 , subst (_ <ᵀ_) (sym (fs-rep w y ys ke 1)) (hd< (ar< r))
... | inj₂ refl with repb (ψᵗ w c) nvs hv
...   | m , r = suc m , subst (_ <ᵀ_) (sym (fs-rep w y ys ke (suc m))) (tl< r)
cofinA nb c1 ke e nv (tl< ())
cofinA {w} {y} {ys} nb cω ke e nv []< = 0 , subst ([] <ᵀ_) (sym (fs-ω w y ys ke 0)) []<
cofinA {w} {y} {ys} nb cω ke e nv (hd< (lv< q)) = 0 , subst (_ <ᵀ_) (sym (fs-ω w y ys ke 0)) (hd< (lv< q))
cofinA {w} {y} {ys} nb cω ke e (n∷ (nψ _ _ nc _) _ _) (hd< (ar< q)) with cofin₁ nb ke nc q
... | n , r = n , subst (_ <ᵀ_) (sym (fs-ω w y ys ke n)) (hd< (ar< r))
cofinA nb cω ke e nv (tl< ())
cofinA {w} {y} {ys} nb (cΩ ν) ke e nv p = go (cmpᵀ (sucT ν) w) refl e
  where
  go : ∀ m → cmpᵀ (sucT ν) w ≡ m → cofψ₊ w ν m ≡ cω → Σ ℕ λ n → _ <ᵀ fsn (ψᵗ w (y ∷ ys) ∷ []) n
  go lt em ()
  go eq em ()
  go gt em _ = h nv p
    where
    h : ∀ {v} → NF₁ v → v <ᵀ (ψᵗ w (y ∷ ys) ∷ []) → Σ ℕ λ n → v <ᵀ fsn (ψᵗ w (y ∷ ys) ∷ []) n
    h nv []< = 0 , subst ([] <ᵀ_) (sym (fs-gt w y ys ν ke em 0)) []<
    h nv (hd< (lv< q)) = 0 , subst (_ <ᵀ_) (sym (fs-gt w y ys ν ke em 0)) (hd< (lv< q))
    h (n∷ (nψ {a = c} _ _ nc gc) _ _) (hd< (ar< q))
      with Cof6 (sz c) nb ke (gt→≤ ν w em) ≤-refl q (λ vz → <ᵀ-trans (gc vz) q)
    ... | n , r = n , subst (_ <ᵀ_) (sym (fs-gt w y ys ν ke em n)) (hd< (ar< r))
    h nv (tl< ())
```

## §3 上下文与提升

```agda
data Fr : Set where
  pre : T → Fr
  nd  : T → Fr
  sb  : Fr

Ctx : Set
Ctx = List Fr

plug : Ctx → T → T
plug []          H = H
plug (pre s ∷ K) H = s ++ plug K H
plug (nd x ∷ K)  H = ψᵗ x (plug K H) ∷ []
plug (sb ∷ K)    H = ψᵗ (plug K H) [] ∷ []

plug-++ : ∀ K K′ H → plug (K ++ K′) H ≡ plug K (plug K′ H)
plug-++ []          K′ H = refl
plug-++ (pre s ∷ K) K′ H = cong (s ++_) (plug-++ K K′ H)
plug-++ (nd x ∷ K)  K′ H = cong (λ z → ψᵗ x z ∷ []) (plug-++ K K′ H)
plug-++ (sb ∷ K)    K′ H = cong (λ z → ψᵗ z [] ∷ []) (plug-++ K K′ H)

Core : T → T → ℕ → Set
Core H H′ m = ∀ {ζ} → sz ζ ≤ℕ m → ζ <ᵀ H → ζ <ᵀ H′

LIFT : ∀ K {H H′} m → Core H H′ m → Core (plug K H) (plug K H′) m
LIFT [] m c h p = c h p
LIFT (pre s ∷ K) m c h p with split s p
... | inS f = f _
... | past ζ′ refl q = ++-mono s (LIFT K m c (≤-trans (sz-suffix s ζ′) h) q)
LIFT (nd x ∷ K) m c h []<              = []<
LIFT (nd x ∷ K) m c h (hd< (lv< q))    = hd< (lv< q)
LIFT (nd x ∷ K) m c {ψᵗ v a ∷ ys} h (hd< (ar< q)) =
  hd< (ar< (LIFT K m c (≤-trans (<⇒≤ (sz-hdarg v a ys)) h) q))
LIFT (nd x ∷ K) m c h (tl< ())
LIFT (sb ∷ K) m c h []<              = []<
LIFT (sb ∷ K) m c {ψᵗ v a ∷ ys} h (hd< (lv< q)) =
  hd< (lv< (LIFT K m c (≤-trans (<⇒≤ (sz-sub v a ys)) h) q))
LIFT (sb ∷ K) m c h (hd< (ar< ()))
LIFT (sb ∷ K) m c h (tl< ())

plugR : Ctx → T → T
plugR []          H = H
plugR (pre s ∷ S) H = plugR S (s ++ H)
plugR (nd x ∷ S)  H = plugR S (ψᵗ x H ∷ [])
plugR (sb ∷ S)    H = plugR S (ψᵗ H [] ∷ [])

LIFTR : ∀ S {H H′} m → Core H H′ m → Core (plugR S H) (plugR S H′) m
LIFTR []          m c = c
LIFTR (pre s ∷ S) m c = LIFTR S m (LIFT (pre s ∷ []) m c)
LIFTR (nd x ∷ S)  m c = LIFTR S m (LIFT (nd x ∷ []) m c)
LIFTR (sb ∷ S)    m c = LIFTR S m (LIFT (sb ∷ []) m c)
```

```agda
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

hdC : ∀ {x d} d′ T′ m → m ≤ℕ sz x → Core (ψᵗ x d ∷ []) (ψᵗ x d′ ∷ T′) m
hdC d′ T′ m hm h []< = []<
hdC d′ T′ m hm h (hd< (lv< q)) = hd< (lv< q)
hdC {x} d′ T′ m hm {ψᵗ _ e ∷ ζs} h (hd< (ar< q)) =
  ⊥-elim (<-irrefl refl (<-≤-trans (sz-sub x e ζs) (≤-trans h hm)))
hdC d′ T′ m hm h (tl< ())

leafC : ∀ {u ν} → sucT ν ≡ u → ∀ e r m → m ≤ℕ sz ν → Core (ψᵗ u [] ∷ []) (ψᵗ ν e ∷ r) m
leafC eu e r m hm h []< = []<
leafC {ν = ν} eu e r m hm {ψᵗ z a ∷ ζs} h (hd< (lv< q)) with <sucT ν (subst (z <ᵀ_) (sym eu) q)
... | inj₁ q′  = hd< (lv< q′)
... | inj₂ refl = ⊥-elim (<-irrefl refl (<-≤-trans (sz-sub ν a ζs) (≤-trans h hm)))
leafC eu e r m hm h (hd< (ar< ()))
leafC eu e r m hm h (tl< ())
```

```agda
data HasNd : Ctx → Set where
  here  : ∀ {x K} → HasNd (nd x ∷ K)
  hsb   : ∀ {K} → HasNd (sb ∷ K)
  there : ∀ {f K} → HasNd K → HasNd (f ∷ K)

data NoSb : Ctx → Set where
  ns[]  : NoSb []
  nspre : ∀ {s K} → NoSb K → NoSb (pre s ∷ K)
  nsnd  : ∀ {x K} → NoSb K → NoSb (nd x ∷ K)

rv : Ctx → Ctx
rv []      = []
rv (f ∷ S) = rv S ++ (f ∷ [])

HasNd-++ʳ : ∀ K {K′} → HasNd K′ → HasNd (K ++ K′)
HasNd-++ʳ []      h = h
HasNd-++ʳ (f ∷ K) h = there (HasNd-++ʳ K h)

HasNd-++ˡ : ∀ {K} K′ → HasNd K → HasNd (K ++ K′)
HasNd-++ˡ K′ here      = here
HasNd-++ˡ K′ hsb       = hsb
HasNd-++ˡ K′ (there h) = there (HasNd-++ˡ K′ h)

HasNd-rv : ∀ {S} → HasNd S → HasNd (rv S)
HasNd-rv {nd x ∷ S} here      = HasNd-++ʳ (rv S) here
HasNd-rv {sb ∷ S}   hsb       = HasNd-++ʳ (rv S) hsb
HasNd-rv {f ∷ S}    (there h) = HasNd-++ˡ (f ∷ []) (HasNd-rv h)

NoSb-++ : ∀ {K K′} → NoSb K → NoSb K′ → NoSb (K ++ K′)
NoSb-++ ns[]      n′ = n′
NoSb-++ (nspre n) n′ = nspre (NoSb-++ n n′)
NoSb-++ (nsnd n)  n′ = nsnd (NoSb-++ n n′)

NoSb-rv : ∀ {S} → NoSb S → NoSb (rv S)
NoSb-rv ns[]      = ns[]
NoSb-rv (nspre n) = NoSb-++ (NoSb-rv n) (nspre ns[])
NoSb-rv (nsnd n)  = NoSb-++ (NoSb-rv n) (nsnd ns[])
```

```agda
plugR-++ : ∀ S S′ H → plugR (S ++ S′) H ≡ plugR S′ (plugR S H)
plugR-++ []          S′ H = refl
plugR-++ (pre s ∷ S) S′ H = plugR-++ S S′ (s ++ H)
plugR-++ (nd x ∷ S)  S′ H = plugR-++ S S′ (ψᵗ x H ∷ [])
plugR-++ (sb ∷ S)    S′ H = plugR-++ S S′ (ψᵗ H [] ∷ [])

plug-rv : ∀ S H → plug (rv S) H ≡ plugR S H
plug-rv []          H = refl
plug-rv (pre s ∷ S) H = trans (plug-++ (rv S) (pre s ∷ []) H) (plug-rv S (s ++ H))
plug-rv (nd x ∷ S)  H = trans (plug-++ (rv S) (nd x ∷ []) H) (plug-rv S (ψᵗ x H ∷ []))
plug-rv (sb ∷ S)    H = trans (plug-++ (rv S) (sb ∷ []) H) (plug-rv S (ψᵗ H [] ∷ []))

plugR-rv : ∀ K H → plugR (rv K) H ≡ plug K H
plugR-rv []          H = refl
plugR-rv (pre s ∷ K) H = trans (plugR-++ (rv K) (pre s ∷ []) H) (cong (s ++_) (plugR-rv K H))
plugR-rv (nd x ∷ K)  H = trans (plugR-++ (rv K) (nd x ∷ []) H) (cong (λ z → ψᵗ x z ∷ []) (plugR-rv K H))
plugR-rv (sb ∷ K)    H = trans (plugR-++ (rv K) (sb ∷ []) H) (cong (λ z → ψᵗ z [] ∷ []) (plugR-rv K H))

plugR-mix : ∀ S K H → plugR (S ++ rv K) H ≡ plug K (plugR S H)
plugR-mix S K H = trans (plugR-++ S (rv K) H) (plugR-rv K (plugR S H))

plugKS : ∀ K S H → plug (K ++ rv S) H ≡ plug K (plugR S H)
plugKS K S H = trans (plug-++ K (rv S) H) (cong (plug K) (plug-rv S H))

sz-plugR≤ : ∀ S W → sz W ≤ℕ sz (plugR S W)
sz-plugR≤ []          W = ≤-refl
sz-plugR≤ (pre s ∷ S) W = ≤-trans (sz-suffix s W) (sz-plugR≤ S (s ++ W))
sz-plugR≤ (nd x ∷ S)  W = ≤-trans (<⇒≤ (sz-hdarg x W [])) (sz-plugR≤ S (ψᵗ x W ∷ []))
sz-plugR≤ (sb ∷ S)    W = ≤-trans (<⇒≤ (sz-sub W [] [])) (sz-plugR≤ S (ψᵗ W [] ∷ []))

sz-plugR< : ∀ S W → HasNd S → sz W <ℕ sz (plugR S W)
sz-plugR< (nd x ∷ S)  W here      = <-≤-trans (sz-hdarg x W []) (sz-plugR≤ S (ψᵗ x W ∷ []))
sz-plugR< (sb ∷ S)    W hsb       = <-≤-trans (sz-sub W [] []) (sz-plugR≤ S (ψᵗ W [] ∷ []))
sz-plugR< (pre s ∷ S) W (there h) = ≤-<-trans (sz-suffix s W) (sz-plugR< S (s ++ W) h)
sz-plugR< (nd x ∷ S)  W (there h) = <ℕ-trans (sz-hdarg x W []) (sz-plugR< S (ψᵗ x W ∷ []) h)
sz-plugR< (sb ∷ S)    W (there h) = <ℕ-trans (sz-sub W [] []) (sz-plugR< S (ψᵗ W [] ∷ []) h)

[]<plug : ∀ K {x xs} → [] <ᵀ plug K (x ∷ xs)
[]<plug []                = []<
[]<plug (pre [] ∷ K)      = []<plug K
[]<plug (pre (a ∷ s) ∷ K) = []<
[]<plug (nd y ∷ K)        = []<
[]<plug (sb ∷ K)          = []<

[]<plugR : ∀ S {x xs} → [] <ᵀ plugR S (x ∷ xs)
[]<plugR []                = []<
[]<plugR (pre [] ∷ S)      = []<plugR S
[]<plugR (pre (a ∷ s) ∷ S) = []<plugR S
[]<plugR (nd y ∷ S)        = []<plugR S
[]<plugR (sb ∷ S)          = []<plugR S

plugR-mono : ∀ S {A B} → A <ᵀ B → plugR S A <ᵀ plugR S B
plugR-mono []          p = p
plugR-mono (pre s ∷ S) p = plugR-mono S (++-mono s p)
plugR-mono (nd x ∷ S)  p = plugR-mono S (hd< (ar< p))
plugR-mono (sb ∷ S)    p = plugR-mono S (hd< (lv< p))
```

```agda
sub< : ∀ t a r → t <ᵀ ψᵗ t a ∷ r
sub< []            a r = []<
sub< (ψᵗ y b ∷ ys) a r = hd< (lv< (sub< y b ys))

η<Ω-hd : ∀ {η} → η <ᵀ Ωᵗ → ∀ {y} → natT 1 ≤ᵀ y → ∀ R T′ → η <ᵀ ψᵗ y R ∷ T′
η<Ω-hd []< h R T′ = []<
η<Ω-hd (hd< (lv< q)) h R T′ = hd< (lv< (<≤-trans q h))
η<Ω-hd (hd< (ar< ())) h R T′
η<Ω-hd (tl< ()) h R T′

swapΩ : ∀ C {η} → Ωᵗ <ᵀ plug C βᴱ → η <ᵀ Ωᵗ → η <ᵀ plug C (Ωt η)
swapΩ [] p η< = sub< _ [] []
swapΩ (pre [] ∷ C) p η< = swapΩ C p η<
swapΩ (pre (ψᵗ y R ∷ s) ∷ C) (hd< (lv< q)) η< = η<Ω-hd η< (inj₁ q) R _
swapΩ (pre (ψᵗ y R ∷ s) ∷ C) (hd< (ar< q)) η< = η<Ω-hd η< (inj₂ refl) R _
swapΩ (pre (ψᵗ y R ∷ s) ∷ C) (tl< q) η< = η<Ω-hd η< (inj₂ refl) [] _
swapΩ (nd y ∷ C) p η< with inv1 p
... | vlv q = η<Ω-hd η< (inj₁ q) _ []
... | var q = η<Ω-hd η< (inj₂ refl) _ []
swapΩ (sb ∷ C) p []< = []<
swapΩ (sb ∷ C) p (hd< (lv< q)) with <sucT [] q
... | inj₁ ()
... | inj₂ refl = hd< (lv< ([]<plug C))
swapΩ (sb ∷ C) p (hd< (ar< ()))
swapΩ (sb ∷ C) p (tl< ())
```

## §4 自界引理

```agda
n≮0 : ∀ {n} → n <ℕ 0 → ⊥
n≮0 ()

data V0 (y : T) : T → Set where
  w[] : V0 y []
  wlv : ∀ {x a xs} → x <ᵀ y → V0 y (ψᵗ x a ∷ xs)

inv0 : ∀ {W y} → W <ᵀ (ψᵗ y [] ∷ []) → V0 y W
inv0 []<           = w[]
inv0 (hd< (lv< q)) = wlv q
inv0 (hd< (ar< ()))
inv0 (tl< ())

c1≢cω : c1 ≡ cω → ⊥
c1≢cω ()

c1≢cΩ : ∀ {ν} → c1 ≡ cΩ ν → ⊥
c1≢cΩ ()

stepPre : ∀ {S s Kr} → HasNd S ⊎ HasNd (pre s ∷ Kr) → HasNd (pre s ∷ S) ⊎ HasNd Kr
stepPre (inj₁ h)         = inj₁ (there h)
stepPre (inj₂ (there h)) = inj₂ h

HdIs : T → T → Set
HdIs ν η = Σ T λ e → Σ T λ r → η ≡ ψᵗ ν e ∷ r

hdγ : ∀ d ν n → HdIs ν (γT d ν n)
hdγ d ν zero    = [] , [] , refl
hdγ d ν (suc n) = _ , [] , refl

OkΩ : Ctx → Ctx → T → T → Set
OkΩ S Kr ν η = (NoSb S × NoSb Kr) ⊎ HdIs ν η

okH : ∀ {S ν η} → OkΩ S [] ν η → NoSb S ⊎ HdIs ν η
okH (inj₁ (a , _)) = inj₁ a
okH (inj₂ h)       = inj₂ h

okPre : ∀ {S s Kr ν η} → OkΩ S (pre s ∷ Kr) ν η → OkΩ (pre s ∷ S) Kr ν η
okPre (inj₁ (a , nspre b)) = inj₁ (nspre a , b)
okPre (inj₂ h)             = inj₂ h

okNd : ∀ {S y Kr ν η} → OkΩ S (nd y ∷ Kr) ν η → OkΩ (nd y ∷ S) Kr ν η
okNd (inj₁ (a , nsnd b)) = inj₁ (nsnd a , b)
okNd (inj₂ h)            = inj₂ h

okR : ∀ {S ν η} → NoSb S ⊎ HdIs ν η → OkΩ [] (rv S) ν η
okR (inj₁ a) = inj₁ (ns[] , NoSb-rv a)
okR (inj₂ h) = inj₂ h

okP : ∀ {S s ν η} → NoSb S ⊎ HdIs ν η → NoSb (pre s ∷ S) ⊎ HdIs ν η
okP (inj₁ a) = inj₁ (nspre a)
okP (inj₂ h) = inj₂ h

okN : ∀ {S x ν η} → NoSb S ⊎ HdIs ν η → NoSb (nd x ∷ S) ⊎ HdIs ν η
okN (inj₁ a) = inj₁ (nsnd a)
okN (inj₂ h) = inj₂ h
```

```agda
nf-arg : ∀ {x a xs} → NF₁ (ψᵗ x a ∷ xs) → NF₁ a
nf-arg (n∷ (nψ _ _ na _) _ _) = na

nf-sub : ∀ {x a xs} → NF₁ (ψᵗ x a ∷ xs) → NF₁ x
nf-sub (n∷ (nψ nx _ _ _) _ _) = nx

nf-sb : ∀ {x a xs} → NF₁ (ψᵗ x a ∷ xs) → Sb x
nf-sb (n∷ (nψ _ sx _ _) _ _) = sx

NF₁-suf : ∀ s {t} → NF₁ (s ++ t) → NF₁ t
NF₁-suf []      n          = n
NF₁-suf (x ∷ s) (n∷ _ n _) = NF₁-suf s n
```

```agda
sbHd : ∀ Kr S {x a} a′ T′ → x <ᵀ plug Kr (plugR S (ψᵗ x a ∷ [])) →
       (ψᵗ x a′ ∷ T′) <ᵀ plug (sb ∷ Kr) (plugR S (ψᵗ x a′ ∷ T′))
sbHd Kr S {x} a′ T′ q = hd< (lv< (LIFT Kr (sz x) (LIFTR S (sz x) (hdC a′ T′ (sz x) ≤-refl)) ≤-refl q))

sbPfx : ∀ Kr S {x a} R R′ → x <ᵀ plug Kr (plugR S (ψᵗ x a ∷ R)) →
        (ψᵗ x a ∷ R′) <ᵀ plug (sb ∷ Kr) (plugR S (ψᵗ x a ∷ R′))
sbPfx Kr S {x} {a} R R′ q =
  hd< (lv< (LIFT Kr (sz x) (LIFTR S (sz x) (pfxC (ψᵗ x a ∷ []) (sz x) (sz-sub x a []))) ≤-refl q))

sbRep : ∀ Kr S {x a} pd n → x <ᵀ plug Kr (plugR S (ψᵗ x a ∷ [])) →
        replicate n (ψᵗ x pd) <ᵀ plug (sb ∷ Kr) (plugR S (replicate n (ψᵗ x pd)))
sbRep Kr S pd zero    q = []<
sbRep Kr S pd (suc n) q = sbHd Kr S pd (replicate n (ψᵗ _ pd)) q

regSb : ∀ Kr S {u ν} → sucT ν ≡ u → ∀ {η} → OkΩ S (sb ∷ Kr) ν η →
        u <ᵀ plug Kr (plugR S (ψᵗ u [] ∷ [])) → η <ᵀ plug (sb ∷ Kr) (plugR S η)
regSb Kr S eu (inj₁ (_ , ())) q
regSb Kr S {u} {ν} eu (inj₂ (e′ , r , refl)) q =
  hd< (lv< (LIFT Kr (sz ν) (LIFTR S (sz ν) (leafC eu e′ r (sz ν) ≤-refl)) ≤-refl
           (<ᵀ-trans (subst (ν <ᵀ_) eu (E.<-sucT ν)) q)))

sbLeafΩ : ∀ Kr S {w ws ν η} → Sb (w ∷ ws) → cof (ψᵗ (w ∷ ws) [] ∷ []) ≡ cΩ ν → η <ᵀ Ωs ν →
          OkΩ S (sb ∷ Kr) ν η → (w ∷ ws) <ᵀ plug Kr (plugR S (ψᵗ (w ∷ ws) [] ∷ [])) →
          fsT (ψᵗ (w ∷ ws) [] ∷ []) η <ᵀ plug (sb ∷ Kr) (plugR S (fsT (ψᵗ (w ∷ ws) [] ∷ []) η))
sbLeafΩ Kr S {w} {ws} {η = η} s e η< ok q with leafInv₁ (w ∷ ws) s (cof (w ∷ ws)) refl e
... | reg ue = subst (λ z → z <ᵀ plug (sb ∷ Kr) (plugR S z)) (sym (fsT-c1 (w ∷ ws) (cof (w ∷ ws)) ue η))
                     (regSb Kr S (E.pred-suc (w ∷ ws) ue) ok q)
... | sing = hd< (lv< (subst (η <ᵀ_) (plugKS Kr S (Ωt η))
                        (swapΩ (Kr ++ rv S) (subst (Ωᵗ <ᵀ_) (sym (plugKS Kr S βᴱ)) q) η<)))

leafVar : ∀ Kr S {y₀ ν η} → Sb y₀ → cof (ψᵗ y₀ [] ∷ []) ≡ cΩ ν → η <ᵀ Ωs ν →
          fsT (ψᵗ y₀ [] ∷ []) η <ᵀ plug (nd y₀ ∷ Kr) (plugR S (fsT (ψᵗ y₀ [] ∷ []) η))
leafVar Kr S {y₀ = []} s () η<
leafVar Kr S {y₀ = w ∷ ws} {η = η} s e η< with leafInv₁ (w ∷ ws) s (cof (w ∷ ws)) refl e
... | reg ue = subst (λ z → z <ᵀ plug (nd (w ∷ ws) ∷ Kr) (plugR S z)) (sym (fsT-c1 (w ∷ ws) (cof (w ∷ ws)) ue η))
                     (belowΩ _ (subst (λ z → η <ᵀ ψᵗ z [] ∷ []) (E.pred-suc (w ∷ ws) ue) η<) (inj₂ refl))
... | sing = hd< (lv< η<)
```

```agda
SELF  : ∀ m S {Z} → sz Z ≤ℕ m → HasNd S → NF₁ Z → cof Z ≡ cω → Z <ᵀ plugR S Z →
        ∀ n → fsn Z n <ᵀ plugR S (fsn Z n)
SELFΩ : ∀ m S {Z ν η} → sz Z ≤ℕ m → HasNd S → NF₁ Z → cof Z ≡ cΩ ν → η <ᵀ Ωs ν →
        NoSb S ⊎ HdIs ν η → Z <ᵀ plugR S Z → fsT Z η <ᵀ plugR S (fsT Z η)
DESC  : ∀ m S Kr {W} n → sz (plugR S W) ≤ℕ m → HasNd S ⊎ HasNd Kr → NF₁ W → cof W ≡ cω →
        W <ᵀ plug Kr (plugR S W) → fsn W n <ᵀ plug Kr (plugR S (fsn W n))
DESCΩ : ∀ m S Kr {W ν η} → sz (plugR S W) ≤ℕ m → HasNd S ⊎ HasNd Kr → NF₁ W → cof W ≡ cΩ ν →
        η <ᵀ Ωs ν → OkΩ S Kr ν η →
        W <ᵀ plug Kr (plugR S W) → fsT W η <ᵀ plug Kr (plugR S (fsT W η))
```

```agda
SELF m S {Z} h hs nZ e p n =
  subst (fsn Z n <ᵀ_) (plug-rv S (fsn Z n))
        (DESC m [] (rv S) n h (inj₂ (HasNd-rv hs)) nZ e (subst (Z <ᵀ_) (sym (plug-rv S Z)) p))

SELFΩ m S {Z} {η = η} h hs nZ e η< ok p =
  subst (fsT Z η <ᵀ_) (plug-rv S (fsT Z η))
        (DESCΩ m [] (rv S) h (inj₂ (HasNd-rv hs)) nZ e η< (okR ok) (subst (Z <ᵀ_) (sym (plug-rv S Z)) p))
```

```agda
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
        (++-mono s (DESC m (pre s ∷ S) Kr n h (stepPre hk) (NF₁-suf s nW) (trans (sym (cof-++ s x xs)) e) q))
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
           here (nf-arg nW) ke (γ<Ωs d ν n) (inj₂ (hdγ d ν n))
           (subst (d <ᵀ_) (sym (plugR-mix (nd y₀ ∷ S) Kr d)) q))))
```

```agda
DESC m S (sb ∷ Kr) {W} n h hk nW e p with inv0 p
... | w[] = ⊥-elim (cof[]≢ω e)
... | wlv {x = x} {a = a} {xs = y ∷ ys} q = sbPfx Kr S (y ∷ ys) (fsn (y ∷ ys) n) q
... | wlv {x = []} {a = []} {xs = []} q = ⊥-elim (c1≢cω e)
... | wlv {x = w ∷ ws} {a = []} {xs = []} q =
  subst (λ z → z <ᵀ plug (sb ∷ Kr) (plugR S z)) (sym (E.fsn0-eq w ws n (viewL w ws e)))
        (hd< (lv< (DESC m (sb ∷ S) Kr n h (inj₁ hsb) (nf-sub nW) (viewL w ws e) q)))
... | wlv {x = x} {a = y ∷ ys} {xs = []} q with viewA x y ys e
...   | v4 ke = subst (λ z → z <ᵀ plug (sb ∷ Kr) (plugR S z)) (sym (fs-rep x y ys ke n)) (sbRep Kr S _ n q)
...   | v5 ke = subst (λ z → z <ᵀ plug (sb ∷ Kr) (plugR S z)) (sym (fs-ω x y ys ke n)) (sbHd Kr S _ [] q)
...   | v6 ν ke em = subst (λ z → z <ᵀ plug (sb ∷ Kr) (plugR S z)) (sym (fs-gt x y ys ν ke em n)) (sbHd Kr S _ [] q)
```

```agda
DESCΩ zero    S [] {W} h (inj₁ hs) nW e η< ok p = ⊥-elim (n≮0 (<-≤-trans (sz-plugR< S W hs) h))
DESCΩ (suc m) S [] {W} h (inj₁ hs) nW e η< ok p =
  SELFΩ m S (≤-pred (≤-trans (sz-plugR< S W hs) h)) hs nW e η< (okH ok) p
DESCΩ m S [] h (inj₂ ()) nW e η< ok p
DESCΩ m S (pre s ∷ Kr) {W} {η = η} h hk nW e η< ok p with split s p
... | inS f = <ᵀ-trans (fsT-desc e η<) (f _)
... | past [] refl q = <++′ s _ (fsT-desc e η<)
... | past (x ∷ xs) refl q =
  subst (λ z → z <ᵀ s ++ plug Kr (plugR S z)) (sym (fsT-++ s x xs η))
        (++-mono s (DESCΩ m (pre s ∷ S) Kr h (stepPre hk) (NF₁-suf s nW) (trans (sym (cof-++ s x xs)) e) η<
                          (okPre ok) q))
DESCΩ m S (nd y₀ ∷ Kr) {W} {ν} {η} h hk nW e η< ok p with inv1 p
... | v[] = ⊥-elim (cof[]≢Ω e)
... | vlv q = <ᵀ-trans (fsT-desc e η<) (hd< (lv< q))
... | var {a = d} {xs = x ∷ xs} q =
  hd< (ar< (LIFT Kr (sz d) (LIFTR S (sz d) (pfxC (ψᵗ y₀ d ∷ []) (sz d) (sz-hdarg y₀ d []))) ≤-refl q))
... | var {a = []} {xs = []} q = leafVar Kr S (nf-sb nW) e η<
... | var {a = y ∷ ys} {xs = []} q with penInv y₀ (y ∷ ys) (cof (y ∷ ys)) refl e
...   | penΩ be pn =
  subst (λ z → z <ᵀ plug (nd y₀ ∷ Kr) (plugR S z)) (sym (fsT₊-pen′ y₀ (y ∷ ys) ν (cof (y ∷ ys)) be pn η))
        (hd< (ar< (DESCΩ m (nd y₀ ∷ S) Kr h (inj₁ here) (nf-arg nW) be η< (okNd ok) q)))
DESCΩ m S (sb ∷ Kr) {W} {ν} {η} h hk nW e η< ok p with inv0 p
... | w[] = ⊥-elim (cof[]≢Ω e)
... | wlv {x = x} {a = a} {xs = y ∷ ys} q = sbPfx Kr S (y ∷ ys) (fsT (y ∷ ys) η) q
... | wlv {x = []} {a = []} {xs = []} q = ⊥-elim (c1≢cΩ e)
... | wlv {x = w ∷ ws} {a = []} {xs = []} q = sbLeafΩ Kr S (nf-sb nW) e η< ok q
... | wlv {x = x} {a = y ∷ ys} {xs = []} q with penInv x (y ∷ ys) (cof (y ∷ ys)) refl e
...   | penΩ be pn = subst (λ z → z <ᵀ plug (sb ∷ Kr) (plugR S z))
                           (sym (fsT₊-pen′ x (y ∷ ys) ν (cof (y ∷ ys)) be pn η)) (sbHd Kr S _ [] q)
```

## §5 闭包

```agda
fsT-mono₁ : ∀ {d ν η η′} → NF₁ d → cof d ≡ cΩ ν → η <ᵀ η′ → fsT d η <ᵀ fsT d η′
fsT-mono₁ n[] () p
fsT-mono₁ (n∷ nx (n∷ ny nys hy) hx) e p = tl< (fsT-mono₁ (n∷ ny nys hy) e p)
fsT-mono₁ (n∷ (nψ {u = []} {a = []} _ _ _ _) n[] _) () p
fsT-mono₁ {η = η} {η′ = η′} (n∷ (nψ {u = w ∷ ws} {a = []} _ sw _ _) n[] _) e p
  with leafInv₁ (w ∷ ws) sw (cof (w ∷ ws)) refl e
... | reg ue = subst₂ _<ᵀ_ (sym (fsT-c1 (w ∷ ws) (cof (w ∷ ws)) ue η)) (sym (fsT-c1 (w ∷ ws) (cof (w ∷ ws)) ue η′)) p
... | sing   = hd< (lv< p)
fsT-mono₁ {ν = ν} {η = η} {η′ = η′} (n∷ (nψ {u = x} {a = y ∷ ys} _ _ nb _) n[] _) e p
  with penInv x (y ∷ ys) (cof (y ∷ ys)) refl e
... | penΩ be pn = subst₂ _<ᵀ_ (sym (fsT₊-pen′ x (y ∷ ys) ν (cof (y ∷ ys)) be pn η))
                               (sym (fsT₊-pen′ x (y ∷ ys) ν (cof (y ∷ ys)) be pn η′))
                               (hd< (ar< (fsT-mono₁ nb be p)))

γ-mono₁ : ∀ {d ν} → NF₁ d → cof d ≡ cΩ ν → ∀ k → γT d ν k <ᵀ γT d ν (suc k)
γ-mono₁ nD e zero    = hd< (ar< (fsT-ne e []<))
γ-mono₁ nD e (suc k) = hd< (ar< (fsT-mono₁ nD e (γ-mono₁ nD e k)))

Vis-pred : ∀ {w ζ d} → cof d ≡ c1 → Vis₁ w ζ (pred d) → Vis₁ w ζ d
Vis-pred {d = []} e v = v
Vis-pred {d = x ∷ y ∷ ys} e (vh h)   = vh h
Vis-pred {d = x ∷ y ∷ ys} e (vd h v) = vd h v
Vis-pred {d = x ∷ y ∷ ys} e (vs h v) = vs h v
Vis-pred {d = x ∷ y ∷ ys} e (vt v)   = vt (Vis-pred e v)
Vis-pred {d = ψᵗ [] [] ∷ []} e ()
Vis-pred {d = ψᵗ [] (y ∷ ys) ∷ []} e v = v
Vis-pred {d = ψᵗ (w ∷ ws) a ∷ []} e v = v

Vis-rep : ∀ k {w ζ y} → Vis₁ w ζ (replicate (suc k) y) → Vis₁ w ζ (y ∷ [])
Vis-rep zero    v        = v
Vis-rep (suc k) (vh h)   = vh h
Vis-rep (suc k) (vd h v) = vd h v
Vis-rep (suc k) (vs h v) = vs h v
Vis-rep (suc k) (vt v)   = Vis-rep k v

Bnd-pred : ∀ {w d} → Bnd₁ w d → cof d ≡ c1 → Bnd₁ w (pred d)
Bnd-pred {d = d} g e {ζ} v with <sucT (pred d) (subst (ζ <ᵀ_) (sym (E.pred-suc d e)) (g (Vis-pred e v)))
... | inj₁ r    = r
... | inj₂ refl = ⊥-elim (<-irrefl refl (Vis-sz v))

NF₁-rep : ∀ {x} → NFᴾ₁ x → ∀ n → NF₁ (replicate n x)
NF₁-rep nx zero          = n[]
NF₁-rep nx (suc zero)    = n∷ nx n[] tt
NF₁-rep {x = x} nx (suc (suc n)) = n∷ nx (NF₁-rep nx (suc n)) (inj₂ (cmpᴾ-refl x))

noVis₁ : ∀ {η ν x ζ} → NF₁ η → η <ᵀ Ωs ν → sucT ν ≤ᵀ x → Vis₁ x ζ η → ⊥
noVis₁ nη (hd< (lv< q)) h (vh h′)   = <→≱ q (≤-trans′ h h′)
noVis₁ nη (hd< (lv< q)) h (vd h′ _) = <→≱ q (≤-trans′ h h′)
noVis₁ nη (hd< (lv< q)) h (vs h′ _) = <→≱ q (≤-trans′ h h′)
noVis₁ (n∷ _ nzs hz) (hd< p) h (vt v) = noVis₁ nzs (tail< hz p) h v
noVis₁ nη (hd< (ar< ())) h v
noVis₁ nη (tl< ()) h v
```

```agda
visLeaf : ∀ {d ν u ζ} → NF₁ d → cof d ≡ cΩ ν → u ≤ᵀ ν → Vis₁ u ζ ν → Vis₁ u ζ d
visLeaf n[] () h v
visLeaf (n∷ nx (n∷ ny nys hy) hx) e h v = vt (visLeaf (n∷ ny nys hy) e h v)
visLeaf (n∷ (nψ {u = []} {a = []} _ _ _ _) n[] _) () h v
visLeaf {u = u} {ζ = ζ} (n∷ (nψ {u = w ∷ ws} {a = []} _ sw _ _) n[] _) e h v
  with leafInv₁ (w ∷ ws) sw (cof (w ∷ ws)) refl e
... | reg ue = vs (inj₁ (≤<-trans h (subst (pred (w ∷ ws) <ᵀ_) (E.pred-suc (w ∷ ws) ue) (E.<-sucT _))))
                  (subst (Vis₁ u ζ) (E.pred-suc (w ∷ ws) ue) (Vis-++ (E.𝟏 ∷ []) v))
... | sing = ⊥-elim (noV v)
  where noV : ∀ {u ζ} → Vis₁ u ζ [] → ⊥
        noV ()
visLeaf {ν = ν} (n∷ (nψ {u = x} {a = y ∷ ys} _ _ nb _) n[] _) e h v
  with penInv x (y ∷ ys) (cof (y ∷ ys)) refl e
... | penΩ be pn = vd (inj₁ (≤<-trans h (pen→< ν x pn))) (visLeaf nb be h v)

sz0< : ∀ {ζ} → sz ζ ≤ℕ 0 → ∀ S {x xs} → ζ <ᵀ plugR S (x ∷ xs)
sz0< {ζ = []} h S = []<plugR S
sz0< {ζ = ψᵗ _ _ ∷ _} () S

leafLift : ∀ S {d ν ζ} → NF₁ d → cof d ≡ cΩ ν → sz ζ ≤ℕ sz ν → ζ <ᵀ plugR S d →
           ∀ e r → ζ <ᵀ plugR S (fsT d (ψᵗ ν e ∷ r))
leafLift S n[] () hz p e r
leafLift S {d = x ∷ _} (n∷ nx (n∷ ny nys hy) hx) ce hz p e r =
  leafLift (pre (x ∷ []) ∷ S) (n∷ ny nys hy) ce hz p e r
leafLift S (n∷ (nψ {u = []} {a = []} _ _ _ _) n[] _) () hz p e r
leafLift S {ζ = ζ} (n∷ (nψ {u = w ∷ ws} {a = []} _ sw _ _) n[] _) ce hz p e r
  with leafInv₁ (w ∷ ws) sw (cof (w ∷ ws)) refl ce
... | reg ue = subst (λ z → ζ <ᵀ plugR S z) (sym (fsT-c1 (w ∷ ws) (cof (w ∷ ws)) ue _))
                     (LIFTR S (sz ζ) (leafC (E.pred-suc (w ∷ ws) ue) e r (sz ζ) hz) ≤-refl p)
... | sing = sz0< hz S
leafLift S {ν = ν} {ζ = ζ} (n∷ (nψ {u = x} {a = y ∷ ys} _ _ nb _) n[] _) ce hz p e r
  with penInv x (y ∷ ys) (cof (y ∷ ys)) refl ce
... | penΩ be pn = subst (λ z → ζ <ᵀ plugR S z) (sym (fsT₊-pen′ x (y ∷ ys) ν (cof (y ∷ ys)) be pn _))
                         (leafLift (nd x ∷ S) nb be hz p e r)

gLeaf : ∀ u S {d ν} → NF₁ d → cof d ≡ cΩ ν → (∀ {ζ} → Vis₁ u ζ d → ζ <ᵀ plugR S d) →
        u ≤ᵀ ν → ∀ {ζ} → Vis₁ u ζ ν → ∀ e r → ζ <ᵀ plugR S (fsT d (ψᵗ ν e ∷ r))
gLeaf u S nD e H h v e′ r = leafLift S nD e (<⇒≤ (Vis-sz v)) (H (visLeaf nD e h v)) e′ r
```

```agda
GFS : ∀ u S {X} n → NF₁ X → cof X ≡ cω → (∀ {ζ} → Vis₁ u ζ X → ζ <ᵀ plugR S X) →
      ∀ {ζ′} → Vis₁ u ζ′ (fsn X n) → ζ′ <ᵀ plugR S (fsn X n)
GFSL : ∀ u S {w ws} n → NF₁ (w ∷ ws) → cof (w ∷ ws) ≡ cω →
       (∀ {ζ} → Vis₁ u ζ (Ωt (w ∷ ws)) → ζ <ᵀ plugR S (Ωt (w ∷ ws))) →
       ∀ {ζ′} → Vis₁ u ζ′ (Ωt (fsn (w ∷ ws) n)) → ζ′ <ᵀ plugR S (Ωt (fsn (w ∷ ws) n))
GFS5 : ∀ u S x {d} n → NF₁ d → cof d ≡ cω → (∀ {ζ} → Vis₁ u ζ (ψᵗ x d ∷ []) → ζ <ᵀ plugR S (ψᵗ x d ∷ [])) →
       ∀ {ζ′} → Vis₁ u ζ′ (ψᵗ x (fsn d n) ∷ []) → ζ′ <ᵀ plugR S (ψᵗ x (fsn d n) ∷ [])
GFS6 : ∀ u S x {d ν} n → NF₁ d → cof d ≡ cΩ ν → (∀ {ζ} → Vis₁ u ζ (ψᵗ x d ∷ []) → ζ <ᵀ plugR S (ψᵗ x d ∷ [])) →
       ∀ {ζ′} → Vis₁ u ζ′ (ψᵗ x (fsT d (γT d ν n)) ∷ []) → ζ′ <ᵀ plugR S (ψᵗ x (fsT d (γT d ν n)) ∷ [])
GΩ  : ∀ u S {X ν η} → NF₁ X → cof X ≡ cΩ ν → η <ᵀ Ωs ν → NoSb S ⊎ HdIs ν η →
      (∀ {ζ} → Vis₁ u ζ X → ζ <ᵀ plugR S X) →
      (∀ {ζ} → Vis₁ u ζ η → ζ <ᵀ plugR S (fsT X η)) →
      ∀ {ζ′} → Vis₁ u ζ′ (fsT X η) → ζ′ <ᵀ plugR S (fsT X η)
GΩp : ∀ u S x {d ν η} → NF₁ d → cof d ≡ cΩ ν → η <ᵀ Ωs ν → NoSb S ⊎ HdIs ν η →
      (∀ {ζ} → Vis₁ u ζ (ψᵗ x d ∷ []) → ζ <ᵀ plugR S (ψᵗ x d ∷ [])) →
      (∀ {ζ} → Vis₁ u ζ η → ζ <ᵀ plugR S (ψᵗ x (fsT d η) ∷ [])) →
      ∀ {ζ′} → Vis₁ u ζ′ (ψᵗ x (fsT d η) ∷ []) → ζ′ <ᵀ plugR S (ψᵗ x (fsT d η) ∷ [])
Gγ  : ∀ u S {d ν} → NF₁ d → cof d ≡ cΩ ν → (∀ {ζ} → Vis₁ u ζ d → ζ <ᵀ plugR S d) →
      (∀ k → fsT d (γT d ν k) ≤ᵀ plugR S (fsT d (γT d ν k))) →
      ∀ k {ζ} → Vis₁ u ζ (γT d ν k) → ζ <ᵀ plugR S (fsT d (γT d ν k))
```

```agda
fixHd : ∀ u S {x₀ a R R′ ζ} → (∀ {ζ} → Vis₁ u ζ (ψᵗ x₀ a ∷ R) → ζ <ᵀ plugR S (ψᵗ x₀ a ∷ R)) →
        Vis₁ u ζ (ψᵗ x₀ a ∷ []) → ζ <ᵀ plugR S (ψᵗ x₀ a ∷ R′)
fixHd u S {x₀ = x₀} {a = a} H (vh h) = LIFTR S (sz a) (pfxC (ψᵗ x₀ a ∷ []) (sz a) (sz-hdarg x₀ a [])) ≤-refl (H (vh h))
fixHd u S {x₀ = x₀} {a = a} {ζ = ζ} H (vd h v) =
  LIFTR S (sz ζ) (pfxC (ψᵗ x₀ a ∷ []) (sz ζ) (<ℕ-trans (Vis-sz v) (sz-hdarg x₀ a []))) ≤-refl (H (vd h v))
fixHd u S {x₀ = x₀} {a = a} {ζ = ζ} H (vs h v) =
  LIFTR S (sz ζ) (pfxC (ψᵗ x₀ a ∷ []) (sz ζ) (<ℕ-trans (Vis-sz v) (sz-sub x₀ a []))) ≤-refl (H (vs h v))
fixHd u S H (vt ())

-- a subscript-visible argument of a node whose subscript is unchanged
fixSb : ∀ u S {x d} d′ T′ {ζ} → (∀ {ζ} → Vis₁ u ζ (ψᵗ x d ∷ []) → ζ <ᵀ plugR S (ψᵗ x d ∷ [])) →
        u ≤ᵀ x → Vis₁ u ζ x → ζ <ᵀ plugR S (ψᵗ x d′ ∷ T′)
fixSb u S d′ T′ {ζ} H h v = LIFTR S (sz ζ) (hdC d′ T′ (sz ζ) (<⇒≤ (Vis-sz v))) ≤-refl (H (vs h v))

GFS4 : ∀ u S x {d} n → cof d ≡ c1 → (∀ {ζ} → Vis₁ u ζ (ψᵗ x d ∷ []) → ζ <ᵀ plugR S (ψᵗ x d ∷ [])) →
       ∀ {ζ′} → Vis₁ u ζ′ (replicate n (ψᵗ x (pred d))) → ζ′ <ᵀ plugR S (replicate n (ψᵗ x (pred d)))
GFS4 u S x {d} (suc m) ke H v′ = k1 (Vis-rep m v′)
  where
  pd = pred d
  k1 : ∀ {ζ′} → Vis₁ u ζ′ (ψᵗ x pd ∷ []) → ζ′ <ᵀ plugR S (ψᵗ x pd ∷ replicate m (ψᵗ x pd))
  k1 (vh h)    = LIFTR S (sz pd) (c4C ke _) ≤-refl (<ᵀ-trans (E.pred-< d ke) (H (vh h)))
  k1 (vd h v″) = LIFTR S (sz pd) (c4C ke _) (<⇒≤ (Vis-sz v″)) (H (vd h (Vis-pred ke v″)))
  k1 (vs h v″) = fixSb u S pd _ H h v″
  k1 (vt ())
```

```agda
GFS u S n n[] () v
GFS u S n (n∷ nx (n∷ ny nys hy) hx) e H (vh h)   = fixHd u S H (vh h)
GFS u S n (n∷ nx (n∷ ny nys hy) hx) e H (vd h v) = fixHd u S H (vd h v)
GFS u S n (n∷ nx (n∷ ny nys hy) hx) e H (vs h v) = fixHd u S H (vs h v)
GFS u S {X = x ∷ _} n (n∷ nx (n∷ ny nys hy) hx) e H (vt v) =
  GFS u (pre (x ∷ []) ∷ S) n (n∷ ny nys hy) e (λ v′ → H (vt v′)) v
GFS u S n (n∷ (nψ {u = []} {a = []} _ _ _ _) n[] _) () v
GFS u S {X = ψᵗ (w ∷ ws) [] ∷ []} n (n∷ (nψ nw sw na g) n[] hx) e H {ζ′} v =
  subst (λ z → Vis₁ u ζ′ z → ζ′ <ᵀ plugR S z) (sym (E.fsn0-eq w ws n (viewL w ws e)))
        (GFSL u S n nw (viewL w ws e) H) v
GFS u S {X = ψᵗ x (y ∷ ys) ∷ []} n (n∷ (nψ nx cx nb g) n[] hx) e H {ζ′} v with viewA x y ys e
... | v4 ke = subst (λ z → Vis₁ u ζ′ z → ζ′ <ᵀ plugR S z) (sym (fs-rep x y ys ke n)) (GFS4 u S x n ke H) v
... | v5 ke = subst (λ z → Vis₁ u ζ′ z → ζ′ <ᵀ plugR S z) (sym (fs-ω x y ys ke n)) (GFS5 u S x n nb ke H) v
... | v6 ν ke em = subst (λ z → Vis₁ u ζ′ z → ζ′ <ᵀ plugR S z) (sym (fs-gt x y ys ν ke em n)) (GFS6 u S x n nb ke H) v

GFSL u S n nw ke H (vh h) = []<plugR S
GFSL u S n nw ke H (vd h ())
GFSL u S n nw ke H (vt ())
GFSL u S n nw ke H (vs h v′) =
  GFS u (sb ∷ S) n nw ke (λ v → H (vs (inj₁ (≤<-trans h (fs<ᵀ ke n))) v)) v′
```

```agda
GFS5 u S x {d} n nb ke H (vh h)    = SELF (sz d) (nd x ∷ S) ≤-refl here nb ke (H (vh h)) n
GFS5 u S x n nb ke H (vd h v′) = GFS u (nd x ∷ S) n nb ke (λ v″ → H (vd h v″)) v′
GFS5 u S x n nb ke H (vs h v′) = fixSb u S _ [] H h v′
GFS5 u S x n nb ke H (vt ())

GFS6 u S x {d} {ν} n nb ke H (vh h) =
  SELFΩ (sz d) (nd x ∷ S) ≤-refl here nb ke (γ<Ωs d ν n) (inj₂ (hdγ d ν n)) (H (vh h))
GFS6 u S x {d} {ν} n nb ke H (vd h v′) =
  GΩ u (nd x ∷ S) nb ke (γ<Ωs d ν n) (inj₂ (hdγ d ν n)) (λ v″ → H (vd h v″))
     (Gγ u (nd x ∷ S) nb ke (λ v″ → H (vd h v″))
         (λ j → inj₁ (SELFΩ (sz d) (nd x ∷ S) ≤-refl here nb ke (γ<Ωs d ν j) (inj₂ (hdγ d ν j)) (H (vh h)))) n) v′
GFS6 u S x n nb ke H (vs h v′) = fixSb u S _ [] H h v′
GFS6 u S x n nb ke H (vt ())
```

```agda
singG : ∀ u S {η} → (∀ {ζ} → Vis₁ u ζ η → ζ <ᵀ plugR S (ψᵗ η [] ∷ [])) →
        ∀ {ζ′} → Vis₁ u ζ′ (ψᵗ η [] ∷ []) → ζ′ <ᵀ plugR S (ψᵗ η [] ∷ [])
singG u S Hη (vh h)   = []<plugR S
singG u S Hη (vd h ())
singG u S Hη (vs h v) = Hη v
singG u S Hη (vt ())

GΩ u S n[] () η< ok H Hη v
GΩ u S (n∷ nx (n∷ ny nys hy) hx) e η< ok H Hη (vh h)   = fixHd u S H (vh h)
GΩ u S (n∷ nx (n∷ ny nys hy) hx) e η< ok H Hη (vd h v) = fixHd u S H (vd h v)
GΩ u S (n∷ nx (n∷ ny nys hy) hx) e η< ok H Hη (vs h v) = fixHd u S H (vs h v)
GΩ u S {X = x ∷ _} (n∷ nx (n∷ ny nys hy) hx) e η< ok H Hη (vt v) =
  GΩ u (pre (x ∷ []) ∷ S) (n∷ ny nys hy) e η< (okP ok) (λ v′ → H (vt v′)) Hη v
GΩ u S (n∷ (nψ {u = []} {a = []} _ _ _ _) n[] _) () η< ok H Hη v
GΩ u S {X = ψᵗ (w ∷ ws) [] ∷ []} {η = η} (n∷ (nψ nw sw _ _) n[] _) e η< ok H Hη {ζ′} v
  with leafInv₁ (w ∷ ws) sw (cof (w ∷ ws)) refl e
... | reg ue = Hη (subst (Vis₁ u ζ′) (fsT-c1 (w ∷ ws) (cof (w ∷ ws)) ue η) v)
... | sing   = singG u S Hη v
GΩ u S {X = ψᵗ x (y ∷ ys) ∷ []} {ν = ν} {η = η} (n∷ (nψ nx cx nb g) n[] hx) e η< ok H Hη {ζ′} v
  with penInv x (y ∷ ys) (cof (y ∷ ys)) refl e
... | penΩ be pn = subst (λ z → Vis₁ u ζ′ z → ζ′ <ᵀ plugR S z) (sym eqT)
                         (GΩp u S x nb be η< ok H (λ {ζ} vη → subst (λ z → ζ <ᵀ plugR S z) eqT (Hη vη))) v
  where
  eqT : fsT (ψᵗ x (y ∷ ys) ∷ []) η ≡ ψᵗ x (fsT (y ∷ ys) η) ∷ []
  eqT = fsT₊-pen′ x (y ∷ ys) ν (cof (y ∷ ys)) be pn η

GΩp u S x {d} nb be η< ok H Hη (vh h)    = SELFΩ (sz d) (nd x ∷ S) ≤-refl here nb be η< (okN ok) (H (vh h))
GΩp u S x nb be η< ok H Hη (vd h v′) = GΩ u (nd x ∷ S) nb be η< (okN ok) (λ v″ → H (vd h v″)) Hη v′
GΩp u S x nb be η< ok H Hη (vs h v′) = fixSb u S _ [] H h v′
GΩp u S x nb be η< ok H Hη (vt ())
```

```agda
Gγ u S nD e H Sγ zero (vh h) = <≤-trans (fsT-ne e []<) (Sγ zero)
Gγ u S nD e H Sγ zero (vd h ())
Gγ u S nD e H Sγ zero (vs h v) = gLeaf u S nD e H h v [] []
Gγ u S nD e H Sγ zero (vt ())
Gγ u S nD e H Sγ (suc k) (vh h) = <≤-trans (fsT-mono₁ nD e (γ-mono₁ nD e k)) (Sγ (suc k))
Gγ u S {d = d} {ν = ν} nD e H Sγ (suc k) (vd h v) =
  <ᵀ-trans (GΩ u S nD e (γ<Ωs d ν k) (inj₂ (hdγ d ν k)) H (Gγ u S nD e H Sγ k) v)
           (plugR-mono S (fsT-mono₁ nD e (γ-mono₁ nD e k)))
Gγ u S nD e H Sγ (suc k) (vs h v) = gLeaf u S nD e H h v _ []
Gγ u S nD e H Sγ (suc k) (vt ())
```

```agda
NF₁-fsT : ∀ {d ν η} → NF₁ d → cof d ≡ cΩ ν → NF₁ η → η <ᵀ Ωs ν → NF₁ (fsT d η)
NF₁-fsT n[] () nη η<
NF₁-fsT (n∷ nx (n∷ {x = y} {xs = ys} ny nys hy) hx) e nη η< =
  n∷ nx (NF₁-fsT (n∷ ny nys hy) e nη η<) (Hd≤-desc (fsT-desc {W = y ∷ ys} e η<) hx)
NF₁-fsT (n∷ (nψ {u = []} {a = []} _ _ _ _) n[] _) () nη η<
NF₁-fsT {η = η} (n∷ (nψ {u = w ∷ ws} {a = []} _ sw _ _) n[] _) e nη η<
  with leafInv₁ (w ∷ ws) sw (cof (w ∷ ws)) refl e
... | reg ue = subst NF₁ (sym (fsT-c1 (w ∷ ws) (cof (w ∷ ws)) ue η)) nη
... | sing   = n∷ (nψ nη (sC (ctblΩ nη η<)) n[] bnd[]) n[] tt
NF₁-fsT {ν = ν} {η = η} (n∷ (nψ {u = x} {a = y ∷ ys} nx cx nb g) n[] _) e nη η<
  with penInv x (y ∷ ys) (cof (y ∷ ys)) refl e
... | penΩ be pn = subst NF₁ (sym (fsT₊-pen′ x (y ∷ ys) ν (cof (y ∷ ys)) be pn η))
  (n∷ (nψ nx cx (NF₁-fsT nb be nη η<)
          (λ v → GΩ x [] nb be η< (inj₁ ns[]) g (λ vη → ⊥-elim (noVis₁ nη η< (Pen→≤ (sucT ν) x pn) vη)) v)) n[] tt)

NF₁-γ : ∀ {d ν} → NF₁ d → cof d ≡ cΩ ν → NF₁ ν → Sb ν → Bnd₁ ν d → ∀ k → NF₁ (γT d ν k)
NF₁-γ nD e nν sν g zero    = n∷ (nψ nν sν n[] bnd[]) n[] tt
NF₁-γ {d = d} {ν = ν} nD e nν sν g (suc k) =
  n∷ (nψ nν sν (NF₁-fsT nD e (NF₁-γ nD e nν sν g k) (γ<Ωs d ν k))
         (λ v → GΩ ν [] nD e (γ<Ωs d ν k) (inj₁ ns[]) g (Gγ ν [] nD e g (λ _ → inj₂ refl) k) v)) n[] tt

NF₁-fsn : ∀ {t} → NF₁ t → cof t ≡ cω → ∀ n → NF₁ (fsn t n)
NF₁-fsn n[] () n
NF₁-fsn (n∷ nx (n∷ {x = y} {xs = ys} ny nys hy) hx) e n =
  n∷ nx (NF₁-fsn (n∷ ny nys hy) e n) (Hd≤-desc (fs<ᵀ {u = y ∷ ys} e n) hx)
NF₁-fsn (n∷ (nψ {u = []} {a = []} _ _ _ _) n[] _) () n
NF₁-fsn (n∷ (nψ {u = w ∷ ws} {a = []} nw sw _ _) n[] _) e n =
  subst NF₁ (sym (E.fsn0-eq w ws n (viewL w ws e)))
        (n∷ (nψ (NF₁-fsn nw (viewL w ws e) n) (Sb-fsn sw (viewL w ws e) n) n[] bnd[]) n[] tt)
NF₁-fsn (n∷ (nψ {u = x} {a = y ∷ ys} nx cx nb g) n[] _) e n with viewA x y ys e
... | v4 ke = subst NF₁ (sym (fs-rep x y ys ke n)) (NF₁-rep (nψ nx cx (NF₁-pred nb ke) (Bnd-pred g ke)) n)
... | v5 ke = subst NF₁ (sym (fs-ω x y ys ke n)) (n∷ (nψ nx cx (NF₁-fsn nb ke n) (λ v → GFS x [] n nb ke g v)) n[] tt)
... | v6 ν ke em = subst NF₁ (sym (fs-gt x y ys ν ke em n))
  (n∷ (nψ nx cx (NF₁-fsT nb ke (NF₁-γ nb ke (proj₁ (NF-ν₁ nb ke)) (proj₂ (NF-ν₁ nb ke))
                                       (λ v → g (Vis-mono (gt→≤ ν x em) v)) n) (γ<Ωs (y ∷ ys) ν n))
          (λ v → GΩ x [] nb ke (γ<Ωs (y ∷ ys) ν n) (inj₁ ns[]) g (Gγ x [] nb ke g (λ _ → inj₂ refl) n) v)) n[] tt)

desc-NF₁ : ∀ {t₀ t} → NF₁ t₀ → Desc t₀ t → NF₁ t
desc-NF₁ n₀ d₀         = n₀
desc-NF₁ n₀ (dω d e n) = NF₁-fsn (desc-NF₁ n₀ d) e n
desc-NF₁ n₀ (d₁ d e)   = NF₁-pred (desc-NF₁ n₀ d) e
```

## §6 对角线与检验

```agda
data Flat : T → Set where
  f[] : Flat []
  f∷  : ∀ {u xs} → Flat u → Flat xs → Flat (ψᵗ u [] ∷ xs)

flatVis : ∀ {w ζ t} → Flat t → Vis₁ w ζ t → ζ ≡ []
flatVis (f∷ fu fx) (vh h)   = refl
flatVis (f∷ fu fx) (vd h ())
flatVis (f∷ fu fx) (vs h v) = flatVis fu v
flatVis (f∷ fu fx) (vt v)   = flatVis fx v

flatBnd : ∀ {w x xs} → Flat (x ∷ xs) → Bnd₁ w (x ∷ xs)
flatBnd f v with flatVis f v
... | refl = []<
```

```agda
f1 : Flat (natT 1)
f1 = f∷ f[] f[]

fΩ : Flat Ωᵗ
fΩ = f∷ f1 f[]

nf1 : NF₁ (natT 1)
nf1 = n∷ (nψ n[] (sC c[]) n[] bnd[]) n[] tt

nfΩ : NF₁ Ωᵗ
nfΩ = n∷ (nψ nf1 (sC (c∷ c[])) n[] bnd[]) n[] tt

nfβ : NFᴾ₁ (ψᵗ Ωᵗ [])
nfβ = nψ nfΩ (sΩ c[]) n[] bnd[]

nfβᴱ : NF₁ βᴱ
nfβᴱ = n∷ nfβ n[] tt

nfb₂ : NF₁ b₂
nfb₂ = n∷ nfβ nfβᴱ (inj₂ (cmpᴾ-refl (ψᵗ Ωᵗ [])))

fb₂ : Flat b₂
fb₂ = f∷ fΩ (f∷ fΩ f[])

t2-NF : NF₁ t2
t2-NF = n∷ (nψ n[] (sC c[]) nfb₂ (flatBnd fb₂)) n[] tt

diag₁-desc-NF : ∀ {t} → Desc t2 t → NF₁ t
diag₁-desc-NF = desc-NF₁ t2-NF

γ′-NF : ∀ k → NF₁ (γ′ᴱ k)
γ′-NF = NF₁-γ nfb₂ refl n[] (sC c[]) (flatBnd fb₂)
```

```agda
walk : T → List ℕ → T
walk t []       = t
walk t (n ∷ ns) = walk (fsn t n) ns

AllLim : T → List ℕ → Set
AllLim t []       = ⊤
AllLim t (n ∷ ns) = (cof t ≡ cω) × AllLim (fsn t n) ns

walkD : ∀ {t₀ t} → Desc t₀ t → ∀ ns → AllLim t ns → Desc t₀ (walk t ns)
walkD d []       _        = d
walkD d (n ∷ ns) (e , es) = walkD (dω d e n) ns es
```

## §9 结论与边界
