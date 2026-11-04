#!/usr/bin/env python3
"""由 LadderLabZStandardOmega 生成 EmbVVLZStandardOmega: Sb 多一族 ψ₁(1)·(k+2) + Ω·n + c (sψ⁺, singψ⁺). 其余逐字."""
import re,os,sys
root=os.path.join(os.path.dirname(os.path.abspath(__file__)),'..','..','..','OCF','Align')
s=open(os.path.join(root,'LadderLabZStandardOmega.lagda.md'),encoding='utf8').read()
def rep(a,b,cnt=1):
    global s
    assert a in s, a[:60]
    s=s.replace(a,b,cnt)
s=s.replace('module OCF.Align.LadderLabZStandardOmega where','module OCF.Align.EmbVVLZStandardOmega where')
# A
rep('''data Sb : T → Set where
''','''pk : ℕ → T → T
pk zero t = t
pk (suc k) t = ψ¹ ∷ pk k t

data Sb : T → Set where
  sψ⁺ : ∀ k n {c} → Ctbl c → Sb (ψ¹ ∷ pk k (ψ¹ ∷ Ωᵐ n c))
''')
# B
rep('''  singψ : ∀ n → Leaf₁ (ψ¹ ∷ Ω₁ ∷ Ωᵐ n []) []
''','''  singψ : ∀ n → Leaf₁ (ψ¹ ∷ Ω₁ ∷ Ωᵐ n []) []
  singψ⁺ : ∀ k n → Leaf₁ (ψ¹ ∷ pk k (ψ¹ ∷ Ω₁ ∷ Ωᵐ n [])) []
''')
# C
rep('''leafInv₁ : ∀ u → Sb u → ∀ k → cof u ≡ k → ∀ {ν} → cofψ0 u k ≡ cΩ ν → Leaf₁ u ν
''','''cof-pk : ∀ k x xs → cof (ψ¹ ∷ pk k (x ∷ xs)) ≡ cof (x ∷ xs)
cof-pk zero x xs = refl
cof-pk (suc k) x xs = cof-pk k x xs

pred-pk : ∀ k x xs → pred (ψ¹ ∷ pk k (x ∷ xs)) ≡ ψ¹ ∷ pk k (pred (x ∷ xs))
pred-pk zero x xs = refl
pred-pk (suc k) x xs = cong (ψ¹ ∷_) (pred-pk k x xs)

fsn-pk : ∀ k x xs j → fsn (ψ¹ ∷ pk k (x ∷ xs)) j ≡ ψ¹ ∷ pk k (fsn (x ∷ xs) j)
fsn-pk zero x xs j = refl
fsn-pk (suc k) x xs j = cong (ψ¹ ∷_) (fsn-pk k x xs j)

fsT-pk : ∀ k x xs η → fsT (ψ¹ ∷ pk k (x ∷ xs)) η ≡ ψ¹ ∷ pk k (fsT (x ∷ xs) η)
fsT-pk zero x xs η = refl
fsT-pk (suc k) x xs η = cong (ψ¹ ∷_) (fsT-pk k x xs η)

pk-snoc : ∀ k t → pk (suc k) t ≡ pk k (ψ¹ ∷ t)
pk-snoc zero t = refl
pk-snoc (suc k) t = cong (ψ¹ ∷_) (pk-snoc k t)

cofW : ∀ k n → cof (ψ¹ ∷ pk k (ψ¹ ∷ Ω₁ ∷ Ωᵐ n [])) ≡ cΩ []
cofW k n = trans (cof-pk k ψ¹ (Ω₁ ∷ Ωᵐ n [])) (cof-Ωᵐ[] n)

fsT-singψ⁺ : ∀ k n η → fsT (ψᵗ (ψ¹ ∷ pk k (ψ¹ ∷ Ω₁ ∷ Ωᵐ n [])) [] ∷ []) η ≡ Ωt (ψ¹ ∷ pk k (ψ¹ ∷ Ωᵐ n η))
fsT-singψ⁺ k n η = trans (fsT0-sing (ψ¹ ∷ pk k (ψ¹ ∷ Ω₁ ∷ Ωᵐ n [])) _ η (cofW k n))
  (cong (λ z → ψᵗ z [] ∷ []) (trans (fsT-pk k ψ¹ (Ω₁ ∷ Ωᵐ n []) η) (cong (λ z → ψ¹ ∷ pk k (ψ¹ ∷ z)) (fsT-Ωᵐ n η))))

leaf-singψ⁺ : ∀ k n {μ ν} → cof (ψ¹ ∷ pk k (ψ¹ ∷ Ω₁ ∷ Ωᵐ n [])) ≡ cΩ μ → cΩ μ ≡ cΩ ν → Leaf₁ (ψ¹ ∷ pk k (ψ¹ ∷ Ω₁ ∷ Ωᵐ n [])) ν
leaf-singψ⁺ k n ue e with trans (sym (cofW k n)) ue
leaf-singψ⁺ k n ue refl | refl = singψ⁺ k n

leafInv₁ : ∀ u → Sb u → ∀ k → cof u ≡ k → ∀ {ν} → cofψ0 u k ≡ cΩ ν → Leaf₁ u ν
''')
# D
rep('''leafInv₁ u (sC cu) (cΩ μ) ue e = ⊥-elim (Ctbl-cof cu ue)
''','''leafInv₁ u (sC cu) (cΩ μ) ue e = ⊥-elim (Ctbl-cof cu ue)
leafInv₁ .(ψ¹ ∷ pk k (ψ¹ ∷ [])) (sψ⁺ k zero c[]) (cΩ μ) ue e with trans (sym (cof-pk k ψ¹ [])) ue
... | ()
leafInv₁ .(ψ¹ ∷ pk k (ψ¹ ∷ ψᵗ [] _ ∷ _)) (sψ⁺ k zero (c∷ cc)) (cΩ μ) ue e = ⊥-elim (Ctbl-cof (c∷ cc) (trans (sym (cof-pk k ψ¹ (ψᵗ [] _ ∷ _))) ue))
leafInv₁ .(ψ¹ ∷ pk k (ψ¹ ∷ Ω₁ ∷ Ωᵐ n [])) (sψ⁺ k (suc n) c[]) (cΩ μ) ue e = leaf-singψ⁺ k n ue e
leafInv₁ .(ψ¹ ∷ pk k (ψ¹ ∷ Ω₁ ∷ Ωᵐ n (ψᵗ [] _ ∷ _))) (sψ⁺ k (suc n) (c∷ cc)) (cΩ μ) ue e = ⊥-elim (Ctbl-cof (c∷ cc) (trans (sym (trans (cof-pk k ψ¹ (Ω₁ ∷ Ωᵐ n (ψᵗ [] _ ∷ _))) (cof-Ωᵐ+ n _ _))) ue))
''')
# E
rep('''Sb-pred (sψ n c[])     =''','''Sb-pred (sψ⁺ k n c[]) = subst Sb (sym (trans (pred-pk k ψ¹ (Ωᵐ n [])) (cong (λ z → ψ¹ ∷ pk k z) (pred-ψ¹[] n)))) (sψ⁺ k n c[])
Sb-pred (sψ⁺ k n (c∷ cc)) = subst Sb (sym (trans (pred-pk k ψ¹ (Ωᵐ n (ψᵗ [] _ ∷ _))) (cong (λ z → ψ¹ ∷ pk k z) (pred-ψ¹+ n _ _)))) (sψ⁺ k n (Ctbl-pred (c∷ cc)))
Sb-pred (sψ n c[])     =''')
# F
rep('''Sb-fsn : ∀ {u} → Sb u → cof u ≡ cω → ∀ n → Sb (fsn u n)
''','''Sb-pre : ∀ k j → Sb (ψ¹ ∷ pk k (Ωᵐ j []))
Sb-pre zero j = sψ j c[]
Sb-pre (suc k) j = subst (λ z → Sb (ψ¹ ∷ z)) (sym (pk-snoc k (Ωᵐ j []))) (sψ⁺ k j c[])

Sb-fsn : ∀ {u} → Sb u → cof u ≡ cω → ∀ n → Sb (fsn u n)
Sb-fsn (sψ⁺ k zero c[]) e j = subst Sb (sym (trans (fsn-pk k ψ¹ [] j) (cong (λ z → ψ¹ ∷ pk k z) (fsn-ψ¹ j)))) (Sb-pre k j)
Sb-fsn (sψ⁺ k (suc m) c[]) e j with trans (sym (cofW k m)) e
... | ()
Sb-fsn (sψ⁺ k m (c∷ cc)) e j = subst Sb (sym (trans (fsn-pk k ψ¹ (Ωᵐ m (ψᵗ [] _ ∷ _)) j) (cong (λ z → ψ¹ ∷ pk k z) (fsn-ψ¹+ m _ _ j))))
  (sψ⁺ k m (Ctbl-fsn (c∷ cc) (trans (sym (trans (cof-pk k ψ¹ (Ωᵐ m (ψᵗ [] _ ∷ _))) (cof-ψ¹+ m _ _))) e) j))
''')
# G
rep('''... | singψ _ = n[] , sC c[]
''','''... | singψ _ = n[] , sC c[]
... | singψ⁺ _ _ = n[] , sC c[]
''')
# H
rep('''Ωcof : ∀ {b ν} → NF₁ b → cof b ≡ cΩ ν → ∀ {c} → c <ᵀ b → ΩC b ν c
''','''record PkW (k n : ℕ) (e : T) : Set where
  constructor pkW
  field
    θW : T
    θ<W : θW <ᵀ Ωs []
    fθW : ∀ {η} → θW <ᵀ η → e <ᵀ pk k (ψ¹ ∷ Ωᵐ n η)
    hvW : ∀ {y ζ θs} → θW ≡ ψᵗ y ζ ∷ θs → [] ≤ᵀ y → Vis₁ [] ζ e

pickW : ∀ k n {e} → e <ᵀ pk k (ψ¹ ∷ Ω₁ ∷ Ωᵐ n []) → PkW k n e
pickW zero n []< = pkW [] []< (λ _ → []<) (λ ())
pickW zero n {x ∷ e} (hd< p) = pkW [] []< (λ _ → hd< p) (λ ())
pickW zero n {x ∷ e} (tl< q) with pick² n q
... | pk² θ θ< f h = pkW θ θ< (λ r → tl< (f r)) (λ eθ hh → vt (h eθ hh))
pickW (suc k) n []< = pkW [] []< (λ _ → []<) (λ ())
pickW (suc k) n {x ∷ e} (hd< p) = pkW [] []< (λ _ → hd< p) (λ ())
pickW (suc k) n {x ∷ e} (tl< q) with pickW k n q
... | pkW θ θ< f h = pkW θ θ< (λ r → tl< (f r)) (λ eθ hh → vt (h eθ hh))

singΩψ⁺ : ∀ k n {c} → c <ᵀ (ψᵗ (ψ¹ ∷ pk k (ψ¹ ∷ Ω₁ ∷ Ωᵐ n [])) [] ∷ []) → ΩC (ψᵗ (ψ¹ ∷ pk k (ψ¹ ∷ Ω₁ ∷ Ωᵐ n [])) [] ∷ []) [] c
singΩψ⁺ k n []< = ωc [] []< (λ {η} _ → subst ([] <ᵀ_) (sym (fsT-singψ⁺ k n η)) []<) hv[]
singΩψ⁺ k n {c = ψᵗ [] a ∷ cs} (hd< (lv< q)) = ωc [] []< (λ {η} _ → subst (_ <ᵀ_) (sym (fsT-singψ⁺ k n η)) (hd< (lv< []<))) hv[]
singΩψ⁺ k n {c = ψᵗ (ψᵗ y b ∷ ys) a ∷ cs} (hd< (lv< (hd< p))) = ωc [] []< (λ {η} _ → subst (_ <ᵀ_) (sym (fsT-singψ⁺ k n η)) (hd< (lv< (hd< p)))) hv[]
singΩψ⁺ k n {c = ψᵗ (x₀ ∷ e) a ∷ cs} (hd< (lv< (tl< q))) with pickW k n q
... | pkW θ θ< f h = ωc θ θ< (λ {η} r → subst (_ <ᵀ_) (sym (fsT-singψ⁺ k n η)) (hd< (lv< (tl< (f r))))) (λ eθ hh → vs ([]≤ _) (vt (h eθ hh)))
singΩψ⁺ k n (hd< (ar< ()))
singΩψ⁺ k n (tl< ())

Ωcof : ∀ {b ν} → NF₁ b → cof b ≡ cΩ ν → ∀ {c} → c <ᵀ b → ΩC b ν c
''')
rep('''... | singψ n = singΩψ n p
''','''... | singψ n = singΩψ n p
... | singψ⁺ k n = singΩψ⁺ k n p
''')
# I: SW
a=s.index('SWψ₀ : ∀ a b C {η}'); b=s.index('SWψ : ∀ b C {η}')
sw0=s[a:b]
sw0=sw0.replace('SWψ₀','SWW₀').replace('Ωt (ψ¹ ∷ Ωᵐ (suc b) [])','Ωt (ψ¹ ∷ pk k (ψ¹ ∷ Ωᵐ (suc b) []))').replace('Ωt (ψ¹ ∷ Ωᵐ b η)','Ωt (ψ¹ ∷ pk k (ψ¹ ∷ Ωᵐ b η))')
sw0=re.sub(r'^(SWW₀ )',r'\1k ',sw0,flags=re.M)
sw0=sw0.replace('SWW₀ k : ∀ a b C','SWW₀ : ∀ k a b C')
sw0=re.sub(r'\(SWW₀ a b',r'(SWW₀ k a b',sw0)
sw0=sw0.replace('= SWW₀ a b','= SWW₀ k a b')
c=s.index('\n',s.index('SWψ b (sb ∷ C) p η<'))+1
swp='''
'''+sw0+'''SWP : ∀ k j b C {η} → pk j (ψ¹ ∷ Ωᵐ (suc b) []) <ᵀ plug C (Ωt (ψ¹ ∷ pk k (ψ¹ ∷ Ωᵐ (suc b) []))) → η <ᵀ Ωᵗ → pk j (ψ¹ ∷ Ωᵐ b η) <ᵀ plug C (Ωt (ψ¹ ∷ pk k (ψ¹ ∷ Ωᵐ b η)))
SWP k zero b [] p η< = hd< (lv< (hd< (lv< []<)))
SWP k (suc j) b [] p η< = hd< (lv< (hd< (lv< []<)))
SWP k j b (pre [] ∷ C) p η< = SWP k j b C p η<
SWP k zero b (pre (ψᵗ y R ∷ s) ∷ C) (hd< (lv< q)) η< = hd< (lv< q)
SWP k zero b (pre (ψᵗ y R ∷ s) ∷ C) (hd< (ar< q)) η< = hd< (ar< q)
SWP k zero b (pre (ψᵗ y R ∷ s) ∷ C) (tl< q) η< = tl< (SWW₀ k b b (pre s ∷ C) q η<)
SWP k (suc j) b (pre (ψᵗ y R ∷ s) ∷ C) (hd< (lv< q)) η< = hd< (lv< q)
SWP k (suc j) b (pre (ψᵗ y R ∷ s) ∷ C) (hd< (ar< q)) η< = hd< (ar< q)
SWP k (suc j) b (pre (ψᵗ y R ∷ s) ∷ C) (tl< q) η< = tl< (SWP k j b (pre s ∷ C) q η<)
SWP k zero b (nd y ∷ C) p η< with inv1 p
... | vlv q = hd< (lv< q)
... | var q = hd< (ar< (1<plug′ C (hd< (lv< []<))))
SWP k (suc j) b (nd y ∷ C) p η< with inv1 p
... | vlv q = hd< (lv< q)
... | var q = hd< (ar< (1<plug′ C (hd< (lv< []<))))
SWP k zero b (sb ∷ C) p η< = hd< (lv< (1<plug′ C (hd< (lv< []<))))
SWP k (suc j) b (sb ∷ C) p η< = hd< (lv< (1<plug′ C (hd< (lv< []<))))

pk-mono : ∀ k {e e′} → e <ᵀ e′ → pk k e <ᵀ pk k e′
pk-mono zero p = p
pk-mono (suc k) p = tl< (pk-mono k p)
'''
s=s[:c]+swp+s[c:]
rep('''leafVar : ∀ Kr S {y₀ ν η} →''','''leafVar : ∀ Kr S {y₀ ν η} →''')
rep('''                    (SWψ n (Kr ++ rv S) (subst ((ψ¹ ∷ Ωᵐ (suc n) []) <ᵀ_) (sym (plugKS Kr S (Ωt (ψ¹ ∷ Ωᵐ (suc n) [])))) q) η<))))
''','''                    (SWψ n (Kr ++ rv S) (subst ((ψ¹ ∷ Ωᵐ (suc n) []) <ᵀ_) (sym (plugKS Kr S (Ωt (ψ¹ ∷ Ωᵐ (suc n) [])))) q) η<))))
... | singψ⁺ k n = subst (λ z → z <ᵀ plug (sb ∷ Kr) (plugR S z)) (sym (fsT-singψ⁺ k n η))
                 (hd< (lv< (subst ((ψ¹ ∷ pk k (ψ¹ ∷ Ωᵐ n η)) <ᵀ_) (plugKS Kr S (Ωt (ψ¹ ∷ pk k (ψ¹ ∷ Ωᵐ n η))))
                    (SWP k (suc k) n (Kr ++ rv S) (subst ((ψ¹ ∷ pk k (ψ¹ ∷ Ωᵐ (suc n) [])) <ᵀ_) (sym (plugKS Kr S (Ωt (ψ¹ ∷ pk k (ψ¹ ∷ Ωᵐ (suc n) []))))) q) η<))))
''')
# J
rep('''... | singψ n = subst (λ z → z <ᵀ plug (nd (ψ¹ ∷ Ω₁ ∷ Ωᵐ n []) ∷ Kr) (plugR S z)) (sym (fsT-singψ n η)) (hd< (lv< (tl< (Ωᵐ-η n η<))))
''','''... | singψ n = subst (λ z → z <ᵀ plug (nd (ψ¹ ∷ Ω₁ ∷ Ωᵐ n []) ∷ Kr) (plugR S z)) (sym (fsT-singψ n η)) (hd< (lv< (tl< (Ωᵐ-η n η<))))
... | singψ⁺ k n = subst (λ z → z <ᵀ plug (nd (ψ¹ ∷ pk k (ψ¹ ∷ Ω₁ ∷ Ωᵐ n [])) ∷ Kr) (plugR S z)) (sym (fsT-singψ⁺ k n η)) (hd< (lv< (tl< (pk-mono k (tl< (Ωᵐ-η n η<))))))
''')
rep('''... | singψ n = subst₂ _<ᵀ_ (sym (fsT-singψ n η)) (sym (fsT-singψ n η′)) (hd< (lv< (tl< (Ωᵐ-mono n p))))
''','''... | singψ n = subst₂ _<ᵀ_ (sym (fsT-singψ n η)) (sym (fsT-singψ n η′)) (hd< (lv< (tl< (Ωᵐ-mono n p))))
... | singψ⁺ k n = subst₂ _<ᵀ_ (sym (fsT-singψ⁺ k n η)) (sym (fsT-singψ⁺ k n η′)) (hd< (lv< (tl< (pk-mono k (tl< (Ωᵐ-mono n p))))))
''')
# K
rep('''... | singψ n = ⊥-elim (noV″ v)
  where noV″ : ∀ {u ζ} → Vis₁ u ζ [] → ⊥
        noV″ ()
''','''... | singψ n = ⊥-elim (noV″ v)
  where noV″ : ∀ {u ζ} → Vis₁ u ζ [] → ⊥
        noV″ ()
... | singψ⁺ k n = ⊥-elim (noV⁗ v)
  where noV⁗ : ∀ {u ζ} → Vis₁ u ζ [] → ⊥
        noV⁗ ()
''')
rep('''... | singψ n = subst (λ z → ζ <ᵀ plugR S z) (sym (fsT-singψ n _)) (sz0< hz S)
''','''... | singψ n = subst (λ z → ζ <ᵀ plugR S z) (sym (fsT-singψ n _)) (sz0< hz S)
... | singψ⁺ k n = subst (λ z → ζ <ᵀ plugR S z) (sym (fsT-singψ⁺ k n _)) (sz0< hz S)
''')
# L
rep('''GΩ u S n[] () η< ok H Hη v
''','''visψ¹ : ∀ {u ζ′ r x xs} S → (Vis₁ u ζ′ r → ζ′ <ᵀ plugR S (x ∷ xs)) → natT 1 <ᵀ x ∷ xs → Vis₁ u ζ′ (ψ¹ ∷ r) → ζ′ <ᵀ plugR S (x ∷ xs)
visψ¹ S k o (vh h′) = 1<plugR S o
visψ¹ S k o (vd h′ (vh h″)) = []<plugR S
visψ¹ S k o (vd h′ (vd h″ ()))
visψ¹ S k o (vd h′ (vs h″ ()))
visψ¹ S k o (vd h′ (vt ()))
visψ¹ S k o (vs h′ (vh h″)) = []<plugR S
visψ¹ S k o (vs h′ (vd h″ ()))
visψ¹ S k o (vs h′ (vs h″ ()))
visψ¹ S k o (vs h′ (vt ()))
visψ¹ S k o (vt v) = k v

singGψ⁺ : ∀ k n u S {η} → (∀ {ζ} → Vis₁ u ζ η → ζ <ᵀ plugR S (ψᵗ (ψ¹ ∷ pk k (ψ¹ ∷ Ωᵐ n η)) [] ∷ [])) →
          ∀ {ζ′} → Vis₁ u ζ′ (ψᵗ (ψ¹ ∷ pk k (ψ¹ ∷ Ωᵐ n η)) [] ∷ []) → ζ′ <ᵀ plugR S (ψᵗ (ψ¹ ∷ pk k (ψ¹ ∷ Ωᵐ n η)) [] ∷ [])
singGψ⁺ k n u S Hη (vh h)   = []<plugR S
singGψ⁺ k n u S Hη (vd h ())
singGψ⁺ k n u S Hη (vs h v) = go k v
  where
  o : natT 1 <ᵀ _
  o = hd< (lv< []<)
  go : ∀ j {ζ′} → Vis₁ u ζ′ (ψ¹ ∷ pk j (ψ¹ ∷ Ωᵐ n _)) → ζ′ <ᵀ plugR S _
  go zero w = visψ¹ S (visψ¹ S (visΩᵐ n S Hη) o) o w
  go (suc j) w = visψ¹ S (go j) o w
singGψ⁺ k n u S Hη (vt ())

GΩ u S n[] () η< ok H Hη v
''')
rep('''... | singψ n = subst (λ z → ζ′ <ᵀ plugR S z) (sym (fsT-singψ n η)) (singGψ n u S (λ v′ → subst (λ z → _ <ᵀ plugR S z) (fsT-singψ n η) (Hη v′)) (subst (Vis₁ u ζ′) (fsT-singψ n η) v))
''','''... | singψ n = subst (λ z → ζ′ <ᵀ plugR S z) (sym (fsT-singψ n η)) (singGψ n u S (λ v′ → subst (λ z → _ <ᵀ plugR S z) (fsT-singψ n η) (Hη v′)) (subst (Vis₁ u ζ′) (fsT-singψ n η) v))
... | singψ⁺ k n = subst (λ z → ζ′ <ᵀ plugR S z) (sym (fsT-singψ⁺ k n η)) (singGψ⁺ k n u S (λ v′ → subst (λ z → _ <ᵀ plugR S z) (fsT-singψ⁺ k n η) (Hη v′)) (subst (Vis₁ u ζ′) (fsT-singψ⁺ k n η) v))
''')
# M
rep('''NF₁-fsT : ∀ {d ν η} → NF₁ d → cof d ≡ cΩ ν → NF₁ η → η <ᵀ Ωs ν → NF₁ (fsT d η)
''','''NFψ⁺ : ∀ k n {θ} → NF₁ θ → Ctbl θ → NF₁ (ψ¹ ∷ pk k (ψ¹ ∷ Ωᵐ n θ))
NFψ⁺ zero n nθ c = n∷ nfψ¹ (NFψ¹ n nθ c) (inj₂ (cmpᴾ-refl ψ¹))
NFψ⁺ (suc k) n nθ c = n∷ nfψ¹ (NFψ⁺ k n nθ c) (inj₂ (cmpᴾ-refl ψ¹))

NF₁-fsT : ∀ {d ν η} → NF₁ d → cof d ≡ cΩ ν → NF₁ η → η <ᵀ Ωs ν → NF₁ (fsT d η)
''')
rep('''... | singψ n = subst NF₁ (sym (fsT-singψ n η)) (n∷ (nψ (NFψ¹ n nη (ctblΩ nη η<)) (sψ n (ctblΩ nη η<)) n[] bnd[]) n[] tt)
''','''... | singψ n = subst NF₁ (sym (fsT-singψ n η)) (n∷ (nψ (NFψ¹ n nη (ctblΩ nη η<)) (sψ n (ctblΩ nη η<)) n[] bnd[]) n[] tt)
... | singψ⁺ k n = subst NF₁ (sym (fsT-singψ⁺ k n η)) (n∷ (nψ (NFψ⁺ k n nη (ctblΩ nη η<)) (sψ⁺ k n (ctblΩ nη η<)) n[] bnd[]) n[] tt)
''')
i=s.index('```agda')
open(os.path.join(root,'EmbVVLZStandardOmega.lagda.md'),'w',encoding='utf8').write('> **机械克隆, 验收用.** 由 `LadderLabZStandardOmega` 经 `Survey/scripts/embvv/mk_nf.py` 生成: `Sb` 多一族下标 $\\psi_1(1)\\cdot(k+2)+\\Omega\\cdot n+c$ (`sψ⁺`, `singψ⁺`), 其余逐字. 入口 [EmbVV](EmbVV.lagda.md).\n\n'+s[i:])
