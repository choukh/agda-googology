# 统一形 (四): $\psi_{\Omega+t}$ 的标签定理

> 接 [Uniform4Tail](Uniform4Tail.lagda.md), [Uniform4Head](Uniform4Head.lagda.md). 结论先说:
>
> 1. **`Ld-ψ q : Ld c m x u → Ld t m (ψᵒ q x) (ψ_{Ω+t}(u))`, 对一切 $t<c$ 与一切模式.** 这是全部工作的核心, 它取代 Uniform3 的 `OMain`/`WHd`/`HΩ̂ᵍ`/`goodΩ⁺` 与未写的 `Ω⁺⁺`.
> 2. **$\Omega+t$ 对 $t$ 一致, 比深度更彻底.** 证明没有对 $t$ 的归纳, 没有对 $c$ 的归纳; 每行用 `HeadRules (μ t)`. `lΩ` 的三种情形 (`lt`, `eq`, `gt`) 收成两种 (`Pen`), 由 `cmp<` 的规格 `spec` 对上记号比较.
> 3. **(A), (B) 的落点.** (A): `ls` 行的副本经 `Ld-rep`/`Ld-⊕` 在数据层相加, 链自然含前缀. (B): `lΩ` 的字段已经量化符号输入 $z$. 第 $n$ 个链点的标签是 `chainL` 对 $n$ 归纳.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Uniform4Psi where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import OCF.Align.Level
open import OCF.Align.Prefix using (Z; Ord₊ˢ; Ordˢ; Ωˢ)
import OCF.Align.EBO as E
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; 𝟏; sucT; cmpᵀ; lt; eq; gt) renaming (ψ to ψᵗ; _<ᵀ_ to _<ᵗ_)
open import OCF.Align.Correspond using (Lab; l0; l1; lω; Lab-≅; cof-ne)
open import OCF.Align.StandardOmega using (NF₁; NF₁-fsn; NF₁-pred)
open import OCF.Align.SystemOmega using (Occ; oh; od; os; ot)
open import OCF.Align.Decouple using (Idx; lvI; Lab0[])
open import OCF.Align.DecoupleBase using (ΩΩ)
open import OCF.Align.Stage2Label using (one⁰)
open import OCF.Align.Stage2 using (Ωᵗ)
open import OCF.Align.OmegaExpBase using (OccΣ; cofΣ; predΣ; πw; repW; ωW; γW; gtW)
open import OCF.Align.Closure using (cmpᵀ-refl) renaming (Pen to CPen)
open import OCF.Align.StandardOmega using ()
open import OCF.Align.GoodLBase
open import OCF.Align.UniformS
open import OCF.Align.Uniform3Base hiding (_⊕_) renaming (FW to FW₀)
open import OCF.Align.Uniform3Rel
open import OCF.Align.Uniform3SqABase
open import OCF.Align.Uniform3Hon
open import OCF.Align.Uniform3Depth2Class
open import OCF.Align.Uniform3Depth2W using (InpW; CH; FHν; fsTΩ)
open import OCF.Align.Uniform3Depth2Fold using (Zc₀; Zc₀-of)
open import OCF.Align.Uniform3Full using (FlrLab[]-up; LWʰ-up; FH-pred; pred-Pr)
open import OCF.Align.Uniform4Head
open import OCF.Align.Uniform4Base
open import OCF.Align.Uniform4Class
open import OCF.Align.Uniform4Close
open import OCF.Align.Uniform4Tail
```

## §1 层号比较的规格

```agda
down< : ∀ {a b} → suc a <ᴸ b → a <ᴸ b
down< zero = suc zero
down< (suc q) = suc (down< q)

uns< : ∀ {a b} → suc a <ᴸ suc b → a <ᴸ b
uns< zero = zero
uns< (suc q) = down< q

cl : ∀ k t → k <ᴸ t → cmpᵀ (natT k) (natT t) ≡ lt
cl zero (suc t) q = refl
cl (suc k) (suc t) q = cl k t (uns< q)

penN : ∀ {k t} → k <ᴸ t → CPen (cmpᵀ (natT (suc k)) (natT t))
penN {k} zero = inj₂ (cmpᵀ-refl (natT (suc k)))
penN {k} {suc t} (suc q) = inj₁ (cl k t q)

Sp : ∀ k t → Pen k t → Set
Sp k t (pen s) = ⊤
Sp k t chain   = cmpᵀ (natT (suc k)) (natT t) ≡ gt

upSp : ∀ {k t} (p : Pen k t) → Sp k t p → Sp (suc k) (suc t) (upP p)
upSp (pen s) sp = tt
upSp chain sp = sp

spec : ∀ k t → Sp k t (cmp< k t)
spec k zero = refl
spec zero (suc t) = tt
spec (suc k) (suc t) = upSp (cmp< k t) (spec k t)

cmpμ≡ : ∀ k t → cmpᵀ (μ (suc k)) (μ t) ≡ cmpᵀ (natT (suc k)) (natT t)
cmpμ≡ k t = trans (cong (λ a → cmpᵀ a (tailμ t)) (tailμ≡ (suc k))) (cong (cmpᵀ (natT (suc k))) (tailμ≡ t))

penμ : ∀ {k t} → k <ᴸ t → CPen (cmpᵀ (μ (suc k)) (μ t))
penμ {k} {t} s = subst CPen (sym (cmpμ≡ k t)) (penN s)

gtμ′ : ∀ k t → Sp k t chain → cmpᵀ (μ (suc k)) (μ t) ≡ gt
gtμ′ k t sp = trans (cmpμ≡ k t) sp
```

## §2 重复

```agda
I₁ : Idx (natT 1)
I₁ = one⁰ , hs hz , lab1 , nf1

FlU→μ : ∀ {m φ b} t → FlU m φ b → FlM m (Fl ⊔ φ) (ψᵗ (μ t) b ∷ [])
FlU→μ {m = hon} t F (inl (inr ink)) = inj₁ z≅
FlU→μ {m = hon} t F (inr k) with F k
... | inj₁ e = inj₁ e
... | inj₂ (inj₁ e) = inj₂ (natT 1 , I₁ , inj₂ e , os oh)
... | inj₂ (inj₂ (w , Iw , kw , o)) = inj₂ (w , Iw , kw , od o)
FlU→μ {m = wkm c} t F (inl (inr ink)) = inj₁ (inj₁ (inj₁ z≅))
FlU→μ {m = wkm c} t F (inr k) with F k
... | inj₁ e = inj₁ e
... | inj₂ (inj₁ e) = inj₂ (natT 1 , I₁ , inj₂ e , os oh)
... | inj₂ (inj₂ (w , Iw , kw , o)) = inj₂ (w , Iw , kw , od o)

occ-rep : ∀ {w x} n → Occ w (x ∷ []) → Occ w (replicate (suc n) x)
occ-rep n oh = oh
occ-rep n (od o) = od o
occ-rep n (os o) = os o
occ-rep n (ot ())

FlM-rep : ∀ {m φ x} n → FlM m φ (x ∷ []) → FlM m φ (replicate (suc n) x)
FlM-rep {m = hon} n F = FlrLab-mono (occ-rep n) F
FlM-rep {m = wkm c} n F = FlrLab[]-mono (occ-rep n) F

rep-snoc′ : ∀ n (x : PT) → replicate (suc n) x ++ (x ∷ []) ≡ replicate (suc (suc n)) x
rep-snoc′ zero x = refl
rep-snoc′ (suc n) x = cong (x ∷_) (rep-snoc′ n x)

Ld-rep : ∀ {c m φ} {X̂ : O c φ} {X} → Ld c m X̂ (X ∷ []) → FlM m φ (X ∷ []) → ∀ n → Ld c m (repᵒ X̂ n) (replicate n X)
Ld-rep l F zero = lz
Ld-rep l F (suc zero) = l
Ld-rep {X = X} l F (suc (suc n)) = lwk (re (rep-snoc′ n X) (Ld-⊕ (Ld-rep l F (suc n)) (FlM-rep n F) l))
```

## §3 主定理

```agda
Fw-ψ : ∀ {m φ ps y ys} t → cof (y ∷ ys) ≡ cΩ [] → Fw m (φ ⊔ fk zero) ps y ys →
       Fw m ((Fl ⊔ φ) ⊔ fk zero) [] (ψᵗ (μ t) (ps ++ (y ∷ ys))) []
Fw-ψ {m = hon} t cc G (inr ink) = inj₁ z≅
Fw-ψ {m = hon} t cc G (inl (inl (inr ink))) = inj₁ z≅
Fw-ψ {m = hon} {ps = ps} {y} {ys} t cc G (inl (inr k)) with G (inl k)
... | inj₁ e = inj₁ e
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , λ θ → subst (Occ w) (sym (HeadRules.penh (μ t) {ps} {y} {ys} cc (inj₁ (ltμ t I0)) θ)) (od (o θ)))
Fw-ψ {m = wkm c} t cc G (inr ink) = inj₁ (inj₁ (inj₁ z≅))
Fw-ψ {m = wkm c} t cc G (inl (inl (inr ink))) = inj₁ (inj₁ (inj₁ z≅))
Fw-ψ {m = wkm c} {ps = ps} {y} {ys} t cc G (inl (inr k)) with G (inl k)
... | inj₁ e = inj₁ e
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , λ θ → subst (Occ w) (sym (HeadRules.penh (μ t) {ps} {y} {ys} cc (inj₁ (ltμ t I0)) θ)) (od (o θ)))

Ld-ψ : ∀ {c t m φ} (q : t <ᴸ c) {x : O c φ} {u} → Ld c m x u → Ld t m (ψᵒ q x) (ψᵗ (μ t) u ∷ [])
Ld-ψΩ : ∀ {c t m k φ ps y ys} (q : t <ᴸ c) {fe : ∀ {L} → Ev L φ → Ev L Fl} {r : k <ᴸ c} {h : ∀ ξ → Us c r ξ → O c (ξ ⊔ φ)} → cof (y ∷ ys) ≡ cΩ (μ k) →
        (∀ {m′} → Cv m m′ → LL c r m′ {Fl} (Ω̇ k) (Ωt (μ k))) →
        (∀ {m′} → Cv m m′ → ∀ ξ (z : O k ξ) θ → LL c r m′ z θ → Ld c m′ (h ξ (intoU r z)) (ps ++ fsT (y ∷ ys) θ)) →
        (p : Pen k t) → Sp k t p → Ld t m (ψᵒΩ q fe r h p) (ψᵗ (μ t) (ps ++ (y ∷ ys)) ∷ [])
chainL : ∀ {c k m φ ps y ys} {r : k <ᴸ c} {h : ∀ ξ → Us c r ξ → O c (ξ ⊔ φ)} →
         (∀ {m′} → Cv m m′ → LL c r m′ {Fl} (Ω̇ k) (Ωt (μ k))) →
         (∀ {m′} → Cv m m′ → ∀ ξ (z : O k ξ) θ → LL c r m′ z θ → Ld c m′ (h ξ (intoU r z)) (ps ++ fsT (y ∷ ys) θ)) →
         ∀ n → Ld k m (chainᵒ proj₁ (λ z → owk dupr2 (ψᵒ r (h (Fl ⊔ φ) (intoU r z)))) n) (γW ps (y ∷ ys) (μ k) n)

Ld-ψ {t = t} {m} q lz = lwk (LdΩ̇ t m)
Ld-ψ {t = t} q (ls {ps = ps} {y} {ys} cc F l) =
  ll {ps = []} {y = ψᵗ (μ t) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.c1h (μ t) {ps} {y} {ys} cc)
     (λ n → re (sym (repW (μ t) ps y ys cc n)) (Ld-rep (Ld-ψ q l) (FlU→μ t F) n))
Ld-ψ {t = t} q (ll {ps = ps} {y} {ys} cc h) =
  ll {ps = []} {y = ψᵗ (μ t) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.cωh (μ t) {ps} {y} {ys} cc)
     (λ n → re (sym (ωW (μ t) ps y ys cc n)) (Ld-ψ q (h n)))
Ld-ψ {t = t} q (li {ps = ps} {y} {ys} cc I e hP hI) =
  li {ps = []} {y = ψᵗ (μ t) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.cΩh (μ t) {ps} {y} {ys} cc (inj₁ (ltμ t I))) I e
     (λ η x l s v → re (sym (HeadRules.penh (μ t) {ps} {y} {ys} cc (inj₁ (ltμ t I)) η)) (Ld-ψ q (hP η x l s v)))
     (λ η x i → re (sym (HeadRules.penh (μ t) {ps} {y} {ys} cc (inj₁ (ltμ t I)) η)) (Ld-ψ q (hI η x i)))
Ld-ψ {t = t} q (lĉ {ps = ps} {y} {ys} cc K h₀ hk) =
  lĉ {ps = []} {y = ψᵗ (μ t) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.cωh (μ t) {ps} {y} {ys} cc) K
     (re (sym (ωW (μ t) ps y ys cc 0)) (Ld-ψ q h₀))
     (λ k → re (sym (ωW (μ t) ps y ys cc (suc k))) (Ld-ψ q (hk k)))
Ld-ψ {t = t} q (lŝ {ps = ps} {y} {ys} cc I b ob h₀ hg) =
  lŝ {ps = []} {y = ψᵗ (μ t) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.cΩh (μ t) {ps} {y} {ys} cc (inj₁ (ltμ t I0))) I b
     (λ θ → subst (Occ _) (sym (HeadRules.penh (μ t) {ps} {y} {ys} cc (inj₁ (ltμ t I0)) θ)) (od (ob θ)))
     (re (sym (HeadRules.penh (μ t) {ps} {y} {ys} cc (inj₁ (ltμ t I0)) (natT 1))) (Ld-ψ q h₀))
     (λ θ Y hY lY nθ lt e → re (sym (HeadRules.penh (μ t) {ps} {y} {ys} cc (inj₁ (ltμ t I0)) θ)) (Ld-ψ q (hg θ Y hY lY nθ lt e)))
Ld-ψ {t = t} q (lclo {ps = ps} {y} {ys} G cc h₀ hg) =
  lwk (lclo {ps = []} {y = ψᵗ (μ t) (ps ++ (y ∷ ys))} {ys = []} (Fw-ψ t cc G) (HeadRules.cΩh (μ t) {ps} {y} {ys} cc (inj₁ (ltμ t I0)))
     (lwk (re (sym (HeadRules.penh (μ t) {ps} {y} {ys} cc (inj₁ (ltμ t I0)) (natT 1))) (Ld-ψ q h₀)))
     (λ θ Y hY lY nθ lt → lwk (re (sym (HeadRules.penh (μ t) {ps} {y} {ys} cc (inj₁ (ltμ t I0)) θ)) (Ld-ψ q (hg θ Y hY lY nθ lt)))))
Ld-ψ q (lwk l) = lwk (Ld-ψ q l)
Ld-ψ {t = t} q (lΩ {ps = ps} {y} {ys} {k} {fe} {r} {h} cc b f) = Ld-ψΩ {ps = ps} {y} {ys} q {fe} {r} {h} cc b f (cmp< k t) (spec k t)

Ld-ψΩ {t = t} {k = k} {ps = ps} {y} {ys} q {r = r} {h = h} cc b f (pen s) sp =
  lΩ {ps = []} {y = ψᵗ (μ t) (ps ++ (y ∷ ys))} {ys = []} {r = s} (HeadRules.cΩh (μ t) {ps} {y} {ys} cc (penμ s))
     (λ v → intoL s (outL r (b v)))
     (λ {m′} v ξ z θ l → lwk (re (sym (HeadRules.penh (μ t) {ps} {y} {ys} cc (penμ s) θ))
        (subst (λ w → Ld t m′ (ψᵒ q (h ξ (intoU r w))) (ψᵗ (μ t) (ps ++ fsT (y ∷ ys) θ) ∷ [])) (sym (out-intoU s z))
               (Ld-ψ q (f v ξ z θ (intoL r (outL s l)))))))
Ld-ψΩ {t = t} {m = m} {k = k} {φ = φ} {ps = ps} {y} {ys} q {r = r} {h = h} cc b f chain sp =
  ll {ps = []} {y = ψᵗ (μ t) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.cgth (μ t) {ps} {y} {ys} cc (gtμ′ k t sp))
     (λ n → re (sym (gtW (μ t) ps y ys (μ k) cc (gtμ′ k t sp) n))
               (lwk (Ld-ψ q (f (Cv-refl m) (Fl ⊔ φ) _ _ (intoL r (chainL {r = r} {h = h} b f n))))))

chainL {r = r} b f zero = lwk (outL r (b (Cv-refl _)))
chainL {m = m} {φ = φ} {r = r} {h = h} b f (suc n) =
  lwk (Ld-ψ r (f (Cv-refl m) (Fl ⊔ φ) _ _ (intoL r (chainL {r = r} {h = h} b f n))))
```
