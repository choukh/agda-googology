# -*- coding: utf-8 -*-
# 生成 probes/OCF/Align/LadderLabZ*: 标签路线的克隆世界.
# 来源是已有的 ScafLadderZ* (StandardOmega 再打下面的补丁), ScafLadderQ, LadderNFW*, LadderInfW*, LadderInfTop2.
# 补丁只有一件数学: Sb 加 ψ₁(1)+Ω·n+c (`sψ`), 奇异叶加 Ω_{ψ₁(1)+Ω·(n+1)} (`singψ`). 其余全是改模块名.
# 用法: python3 mkworld.py [输出目录], 默认写回 probes/OCF/Align/. 逐字节可重复.
import re,os,sys
HERE=os.path.dirname(os.path.abspath(__file__))
A=os.path.abspath(os.path.join(HERE,'..','..','..','OCF','Align'))+'/'
OUT=(sys.argv[1].rstrip('/')+'/') if len(sys.argv)>1 else A

ZMODS='Decouple DecoupleBase GoodL GoodLBase NonTight NonTightBase Omega2 Omega2Base OmegaExp OmegaExpBase OmegaK OmegaKBase OmegaSq OmegaSqBase Prefix Relative RelativeBase Stage2Label StandardOmega SystemOmega TopDown Uniform2 Uniform2Base Uniform2Depth1 Uniform3 Uniform3Base Uniform3Depth1 Uniform3Depth2Class Uniform3Depth2Fold Uniform3Depth2W Uniform3Full Uniform3Hon Uniform3Rel Uniform3SqA Uniform3SqABase Uniform4Base Uniform4Head Uniform4Two Uniform5Class Uniform5Close Uniform5Eval Uniform5Head Uniform5Psi Uniform5Rel Uniform5RelPsi Uniform5Tail Uniform5Tr UniformS'.split()
NFW='Aux Base Eq FT Floor Force Prefix Tree'.split()
INFW='Add Class ClassF Cx Eval Good Iota Main Mono Omega Psi PsiH Read Rel Root Rules Rules2 Rules3 Strict Strict2 Strict3 Tail Top Tr Tree Vis'.split()

def rename(s):
    s=re.sub(r'OCF\.Align\.ScafLadderZ(?=[A-Z])','OCF.Align.LadderLabZ',s)
    s=re.sub(r'OCF\.Align\.ScafLadderQ\b','OCF.Align.LadderLabZQ',s)
    s=re.sub(r'OCF\.Align\.LadderNFW(?=[A-Z])','OCF.Align.LadderLabZNFW',s)
    s=re.sub(r'OCF\.Align\.LadderInfW(?=[A-Z])','OCF.Align.LadderLabZInfW',s)
    return s

def sub1(s,a,b):
    assert s.count(a)==1,('sub1',a,s.count(a))
    return s.replace(a,b)

NOTE='> **机械克隆, 验收用.** 由 `%s` 经 `Survey/scripts/ladderlab/mkworld.py` 复制, 只改模块名%s; 见 [LadderLab](LadderLab.lagda.md). 下面的文字是原文.\n\n'

def patch_standard(s):
    s=sub1(s,"data Sb : T → Set where\n  sC : ∀ {w} → Ctbl w → Sb w\n",
"""-- ψ₁(1) 这一项. `ψ¹ ∷ Ωᵐ n c` 是 ψ₁(1) + Ω·n + c
ψ¹ : PT
ψ¹ = ψᵗ (natT 1) (natT 1)

data Sb : T → Set where
  sψ : ∀ n {c} → Ctbl c → Sb (ψ¹ ∷ Ωᵐ n c)
  sC : ∀ {w} → Ctbl w → Sb w
""")
    s=sub1(s,"  sing² : ∀ n → Leaf₁ (Ω₁ ∷ Ω₁ ∷ Ωᵐ n []) []\n",
"""  sing² : ∀ n → Leaf₁ (Ω₁ ∷ Ω₁ ∷ Ωᵐ n []) []
  singψ : ∀ n → Leaf₁ (ψ¹ ∷ Ω₁ ∷ Ωᵐ n []) []
""")
    s=sub1(s,"leafInv₁ : ∀ u → Sb u → ∀ k → cof u ≡ k → ∀ {ν} → cofψ0 u k ≡ cΩ ν → Leaf₁ u ν\n",
"""cof-ψ¹+ : ∀ n x xs → cof (ψ¹ ∷ Ωᵐ n (x ∷ xs)) ≡ cof (x ∷ xs)
cof-ψ¹+ zero x xs = refl
cof-ψ¹+ (suc n) x xs = cof-Ωᵐ+ n x xs

pred-ψ¹[] : ∀ n → pred (ψ¹ ∷ Ωᵐ n []) ≡ ψ¹ ∷ Ωᵐ n []
pred-ψ¹[] zero = refl
pred-ψ¹[] (suc n) = cong (ψ¹ ∷_) (pred-Ωᵐ[] n)

pred-ψ¹+ : ∀ n x xs → pred (ψ¹ ∷ Ωᵐ n (x ∷ xs)) ≡ ψ¹ ∷ Ωᵐ n (pred (x ∷ xs))
pred-ψ¹+ zero x xs = refl
pred-ψ¹+ (suc n) x xs = cong (ψ¹ ∷_) (pred-Ωᵐ+ n x xs)

fsn-ψ¹+ : ∀ n x xs k → fsn (ψ¹ ∷ Ωᵐ n (x ∷ xs)) k ≡ ψ¹ ∷ Ωᵐ n (fsn (x ∷ xs) k)
fsn-ψ¹+ zero x xs k = refl
fsn-ψ¹+ (suc n) x xs k = cong (ψ¹ ∷_) (fsn-Ωᵐ+ n x xs k)

fsT-singψ : ∀ n η → fsT (ψᵗ (ψ¹ ∷ Ω₁ ∷ Ωᵐ n []) [] ∷ []) η ≡ Ωt (ψ¹ ∷ Ωᵐ n η)
fsT-singψ n η = trans (fsT0-sing (ψ¹ ∷ Ω₁ ∷ Ωᵐ n []) _ η (cof-Ωᵐ[] n)) (cong (λ z → ψᵗ (ψ¹ ∷ z) [] ∷ []) (fsT-Ωᵐ n η))

leaf-singψ : ∀ n {μ ν} → cof (ψ¹ ∷ Ω₁ ∷ Ωᵐ n []) ≡ cΩ μ → cΩ μ ≡ cΩ ν → Leaf₁ (ψ¹ ∷ Ω₁ ∷ Ωᵐ n []) ν
leaf-singψ n ue e with trans (sym (cof-Ωᵐ[] n)) ue
leaf-singψ n ue refl | refl = singψ n

leafInv₁ : ∀ u → Sb u → ∀ k → cof u ≡ k → ∀ {ν} → cofψ0 u k ≡ cΩ ν → Leaf₁ u ν
""")
    s=sub1(s,"leafInv₁ .(Ω₁ ∷ []) (sΩ c[]) (cΩ .[]) refl refl = sing\n",
"""leafInv₁ .(ψ¹ ∷ []) (sψ zero c[]) (cΩ μ) () e
leafInv₁ .(ψ¹ ∷ ψᵗ [] _ ∷ _) (sψ zero (c∷ cc)) (cΩ μ) ue e = ⊥-elim (Ctbl-cof (c∷ cc) ue)
leafInv₁ .(ψ¹ ∷ Ω₁ ∷ Ωᵐ n []) (sψ (suc n) c[]) (cΩ μ) ue e = leaf-singψ n ue e
leafInv₁ .(ψ¹ ∷ Ω₁ ∷ Ωᵐ n (ψᵗ [] _ ∷ _)) (sψ (suc n) (c∷ cc)) (cΩ μ) ue e = ⊥-elim (Ctbl-cof (c∷ cc) (trans (sym (cof-ψ¹+ (suc n) _ _)) ue))
leafInv₁ .(Ω₁ ∷ []) (sΩ c[]) (cΩ .[]) refl refl = sing
""")
    s=sub1(s,"Sb-pred (sC c)       = sC (Ctbl-pred c)\n",
"""Sb-pred (sψ n c[])     = subst Sb (sym (pred-ψ¹[] n)) (sψ n c[])
Sb-pred (sψ n (c∷ cc)) = subst Sb (sym (pred-ψ¹+ n _ _)) (sψ n (Ctbl-pred (c∷ cc)))
Sb-pred (sC c)       = sC (Ctbl-pred c)
""")
    s=sub1(s,"Sb-fsn : ∀ {u} → Sb u → cof u ≡ cω → ∀ n → Sb (fsn u n)\nSb-fsn (sC c) e n       = sC (Ctbl-fsn c e n)\n",
"""SbΩᵐ[] : ∀ k → Sb (Ωᵐ k [])
SbΩᵐ[] zero = sC c[]
SbΩᵐ[] (suc zero) = sΩ c[]
SbΩᵐ[] (suc (suc k)) = sΩ² k c[]

rep-Ωᵐ : ∀ k → replicate k Ω₁ ≡ Ωᵐ k []
rep-Ωᵐ zero = refl
rep-Ωᵐ (suc k) = cong (Ω₁ ∷_) (rep-Ωᵐ k)

fsn-ψ¹ : ∀ k → fsn (ψ¹ ∷ []) k ≡ Ωᵐ k []
fsn-ψ¹ k = trans (fs-rep (natT 1) E.𝟏 [] refl k) (rep-Ωᵐ k)

Sb-fsn : ∀ {u} → Sb u → cof u ≡ cω → ∀ n → Sb (fsn u n)
Sb-fsn (sψ zero c[]) e k = subst Sb (sym (fsn-ψ¹ k)) (SbΩᵐ[] k)
Sb-fsn (sψ (suc m) c[]) e k with trans (sym (cof-Ωᵐ[] m)) e
... | ()
Sb-fsn (sψ m (c∷ cc)) e k = subst Sb (sym (fsn-ψ¹+ m _ _ k)) (sψ m (Ctbl-fsn (c∷ cc) (trans (sym (cof-ψ¹+ m _ _)) e) k))
Sb-fsn (sC c) e n       = sC (Ctbl-fsn c e n)
""")
    s=sub1(s,"... | sing² _ = n[] , sC c[]\n","... | sing² _ = n[] , sC c[]\n... | singψ _ = n[] , sC c[]\n")
    s=sub1(s,"Ωcof : ∀ {b ν} → NF₁ b → cof b ≡ cΩ ν → ∀ {c} → c <ᵀ b → ΩC b ν c\n",
"""singΩψ : ∀ n {c} → c <ᵀ (ψᵗ (ψ¹ ∷ Ω₁ ∷ Ωᵐ n []) [] ∷ []) → ΩC (ψᵗ (ψ¹ ∷ Ω₁ ∷ Ωᵐ n []) [] ∷ []) [] c
singΩψ n []< = ωc [] []< (λ {η} _ → subst ([] <ᵀ_) (sym (fsT-singψ n η)) []<) hv[]
singΩψ n {c = ψᵗ [] a ∷ cs} (hd< (lv< q)) = ωc [] []< (λ {η} _ → subst (_ <ᵀ_) (sym (fsT-singψ n η)) (hd< (lv< []<))) hv[]
singΩψ n {c = ψᵗ (ψᵗ y b ∷ ys) a ∷ cs} (hd< (lv< (hd< p))) = ωc [] []< (λ {η} _ → subst (_ <ᵀ_) (sym (fsT-singψ n η)) (hd< (lv< (hd< p)))) hv[]
singΩψ n {c = ψᵗ (x₀ ∷ e) a ∷ cs} (hd< (lv< (tl< q))) with pick² n q
... | pk² θ θ< f h = ωc θ θ< (λ {η} r → subst (_ <ᵀ_) (sym (fsT-singψ n η)) (hd< (lv< (tl< (f r))))) (λ eθ hh → vs ([]≤ _) (vt (h eθ hh)))
singΩψ n (hd< (ar< ()))
singΩψ n (tl< ())

Ωcof : ∀ {b ν} → NF₁ b → cof b ≡ cΩ ν → ∀ {c} → c <ᵀ b → ΩC b ν c
""")
    s=sub1(s,"... | sing² n = singΩ² n p\n","... | sing² n = singΩ² n p\n... | singψ n = singΩψ n p\n")
    # SW 的 ψ¹ 版: 叶子换成 Ω_{ψ¹+…}
    i=s.index("SW : ∀ a b C {η} →"); j=s.index("```",i)
    sw=s[i:j]
    swz=sw.replace("SW : ∀ a b C {η} → Ωᵐ (suc a) [] <ᵀ plug C (Ωt (Ωᵐ (suc (suc b)) [])) → η <ᵀ Ωᵗ → Ωᵐ a η <ᵀ plug C (Ωt (Ωᵐ (suc b) η))",
                   "SWψ₀ : ∀ a b C {η} → Ωᵐ (suc a) [] <ᵀ plug C (Ωt (ψ¹ ∷ Ωᵐ (suc b) [])) → η <ᵀ Ωᵗ → Ωᵐ a η <ᵀ plug C (Ωt (ψ¹ ∷ Ωᵐ b η))")
    swz=re.sub(r'\bSW\b','SWψ₀',swz).replace("(1<plug C)","(1<plug′ C (hd< (lv< []<)))")
    new="""1<plug′ : ∀ C {H} → natT 1 <ᵀ H → natT 1 <ᵀ plug C H
1<plug′ [] p = p
1<plug′ (pre [] ∷ C) p = 1<plug′ C p
1<plug′ (pre (ψᵗ [] [] ∷ s) ∷ C) {H} p = tl< (go s)
  where
  ne : ∀ {K} → natT 1 <ᵀ K → [] <ᵀ plug C K
  ne {x ∷ xs} q = []<plug C
  go : ∀ s → [] <ᵀ s ++ plug C H
  go [] = ne p
  go (_ ∷ _) = []<
1<plug′ (pre (ψᵗ [] (_ ∷ _) ∷ s) ∷ C) p = hd< (ar< []<)
1<plug′ (pre (ψᵗ (_ ∷ _) R ∷ s) ∷ C) p = hd< (lv< []<)
1<plug′ (nd [] ∷ C) {x ∷ xs} p = hd< (ar< ([]<plug C))
1<plug′ (nd (_ ∷ _) ∷ C) p = hd< (lv< []<)
1<plug′ (sb ∷ C) {x ∷ xs} p = hd< (lv< ([]<plug C))

"""+swz+"""
SWψ : ∀ b C {η} → (ψ¹ ∷ Ωᵐ (suc b) []) <ᵀ plug C (Ωt (ψ¹ ∷ Ωᵐ (suc b) [])) → η <ᵀ Ωᵗ → (ψ¹ ∷ Ωᵐ b η) <ᵀ plug C (Ωt (ψ¹ ∷ Ωᵐ b η))
SWψ b [] p η< = hd< (lv< (hd< (lv< []<)))
SWψ b (pre [] ∷ C) p η< = SWψ b C p η<
SWψ b (pre (ψᵗ y R ∷ s) ∷ C) (hd< (lv< q)) η< = hd< (lv< q)
SWψ b (pre (ψᵗ y R ∷ s) ∷ C) (hd< (ar< q)) η< = hd< (ar< q)
SWψ b (pre (ψᵗ y R ∷ s) ∷ C) (tl< q) η< = tl< (SWψ₀ b b (pre s ∷ C) q η<)
SWψ b (nd y ∷ C) p η< with inv1 p
... | vlv q = hd< (lv< q)
... | var q = hd< (ar< (1<plug′ C (hd< (lv< []<))))
SWψ b (sb ∷ C) p η< = hd< (lv< (1<plug′ C (hd< (lv< []<))))
"""
    s=s[:j]+"\n"+new+s[j:]
    s=sub1(s,"""                    (SW (suc n) n (Kr ++ rv S) (subst (Ωᵐ (suc (suc n)) [] <ᵀ_) (sym (plugKS Kr S (Ωt (Ωᵐ (suc (suc n)) [])))) q) η<))))
""","""                    (SW (suc n) n (Kr ++ rv S) (subst (Ωᵐ (suc (suc n)) [] <ᵀ_) (sym (plugKS Kr S (Ωt (Ωᵐ (suc (suc n)) [])))) q) η<))))
... | singψ n = subst (λ z → z <ᵀ plug (sb ∷ Kr) (plugR S z)) (sym (fsT-singψ n η))
                 (hd< (lv< (subst ((ψ¹ ∷ Ωᵐ n η) <ᵀ_) (plugKS Kr S (Ωt (ψ¹ ∷ Ωᵐ n η)))
                    (SWψ n (Kr ++ rv S) (subst ((ψ¹ ∷ Ωᵐ (suc n) []) <ᵀ_) (sym (plugKS Kr S (Ωt (ψ¹ ∷ Ωᵐ (suc n) [])))) q) η<))))
""")
    s=sub1(s,"""... | sing² n = subst (λ z → z <ᵀ plug (nd (Ω₁ ∷ Ω₁ ∷ Ωᵐ n []) ∷ Kr) (plugR S z)) (sym (fsT-sing n η)) (hd< (lv< (tl< (Ωᵐ-η n η<))))
""","""... | sing² n = subst (λ z → z <ᵀ plug (nd (Ω₁ ∷ Ω₁ ∷ Ωᵐ n []) ∷ Kr) (plugR S z)) (sym (fsT-sing n η)) (hd< (lv< (tl< (Ωᵐ-η n η<))))
... | singψ n = subst (λ z → z <ᵀ plug (nd (ψ¹ ∷ Ω₁ ∷ Ωᵐ n []) ∷ Kr) (plugR S z)) (sym (fsT-singψ n η)) (hd< (lv< (tl< (Ωᵐ-η n η<))))
""")
    s=sub1(s,"""... | sing² n = subst₂ _<ᵀ_ (sym (fsT-sing n η)) (sym (fsT-sing n η′)) (hd< (lv< (tl< (Ωᵐ-mono n p))))
""","""... | sing² n = subst₂ _<ᵀ_ (sym (fsT-sing n η)) (sym (fsT-sing n η′)) (hd< (lv< (tl< (Ωᵐ-mono n p))))
... | singψ n = subst₂ _<ᵀ_ (sym (fsT-singψ n η)) (sym (fsT-singψ n η′)) (hd< (lv< (tl< (Ωᵐ-mono n p))))
""")
    s=sub1(s,"""... | sing² n = ⊥-elim (noV′ v)
  where noV′ : ∀ {u ζ} → Vis₁ u ζ [] → ⊥
        noV′ ()
""","""... | sing² n = ⊥-elim (noV′ v)
  where noV′ : ∀ {u ζ} → Vis₁ u ζ [] → ⊥
        noV′ ()
... | singψ n = ⊥-elim (noV″ v)
  where noV″ : ∀ {u ζ} → Vis₁ u ζ [] → ⊥
        noV″ ()
""")
    s=sub1(s,"""... | sing² n = subst (λ z → ζ <ᵀ plugR S z) (sym (fsT-sing n _)) (sz0< hz S)
""","""... | sing² n = subst (λ z → ζ <ᵀ plugR S z) (sym (fsT-sing n _)) (sz0< hz S)
... | singψ n = subst (λ z → ζ <ᵀ plugR S z) (sym (fsT-singψ n _)) (sz0< hz S)
""")
    s=sub1(s,"GΩ u S n[] () η< ok H Hη v\n",
"""1<plugR : ∀ S {H} → natT 1 <ᵀ H → natT 1 <ᵀ plugR S H
1<plugR [] p = p
1<plugR (pre [] ∷ S) p = 1<plugR S p
1<plugR (pre (ψᵗ [] [] ∷ s) ∷ S) {x ∷ xs} p = 1<plugR S (tl< (go s))
  where
  go : ∀ s → [] <ᵀ s ++ (x ∷ xs)
  go [] = []<
  go (_ ∷ _) = []<
1<plugR (pre (ψᵗ [] (_ ∷ _) ∷ s) ∷ S) p = 1<plugR S (hd< (ar< []<))
1<plugR (pre (ψᵗ (_ ∷ _) R ∷ s) ∷ S) p = 1<plugR S (hd< (lv< []<))
1<plugR (nd [] ∷ S) {x ∷ xs} p = 1<plugR S (hd< (ar< []<))
1<plugR (nd (_ ∷ _) ∷ S) p = 1<plugR S (hd< (lv< []<))
1<plugR (sb ∷ S) {x ∷ xs} p = 1<plugR S (hd< (lv< []<))

singGψ : ∀ n u S {η} → (∀ {ζ} → Vis₁ u ζ η → ζ <ᵀ plugR S (ψᵗ (ψ¹ ∷ Ωᵐ n η) [] ∷ [])) →
         ∀ {ζ′} → Vis₁ u ζ′ (ψᵗ (ψ¹ ∷ Ωᵐ n η) [] ∷ []) → ζ′ <ᵀ plugR S (ψᵗ (ψ¹ ∷ Ωᵐ n η) [] ∷ [])
singGψ n u S Hη (vh h)   = []<plugR S
singGψ n u S Hη (vd h ())
singGψ n u S Hη (vs h (vh h′)) = 1<plugR S (hd< (lv< []<))
singGψ n u S Hη (vs h (vd h′ (vh h″))) = []<plugR S
singGψ n u S Hη (vs h (vd h′ (vd h″ ())))
singGψ n u S Hη (vs h (vd h′ (vs h″ ())))
singGψ n u S Hη (vs h (vd h′ (vt ())))
singGψ n u S Hη (vs h (vs h′ (vh h″))) = []<plugR S
singGψ n u S Hη (vs h (vs h′ (vd h″ ())))
singGψ n u S Hη (vs h (vs h′ (vs h″ ())))
singGψ n u S Hη (vs h (vs h′ (vt ())))
singGψ n u S Hη (vs h (vt v)) = visΩᵐ n S Hη v
singGψ n u S Hη (vt ())

GΩ u S n[] () η< ok H Hη v
""")
    s=sub1(s,"""... | sing² n = subst (λ z → ζ′ <ᵀ plugR S z) (sym (fsT-sing n η)) (singG² n u S (λ v′ → subst (λ z → _ <ᵀ plugR S z) (fsT-sing n η) (Hη v′)) (subst (Vis₁ u ζ′) (fsT-sing n η) v))
""","""... | sing² n = subst (λ z → ζ′ <ᵀ plugR S z) (sym (fsT-sing n η)) (singG² n u S (λ v′ → subst (λ z → _ <ᵀ plugR S z) (fsT-sing n η) (Hη v′)) (subst (Vis₁ u ζ′) (fsT-sing n η) v))
... | singψ n = subst (λ z → ζ′ <ᵀ plugR S z) (sym (fsT-singψ n η)) (singGψ n u S (λ v′ → subst (λ z → _ <ᵀ plugR S z) (fsT-singψ n η) (Hη v′)) (subst (Vis₁ u ζ′) (fsT-singψ n η) v))
""")
    s=sub1(s,"NF₁-fsT : ∀ {d ν η} → NF₁ d → cof d ≡ cΩ ν → NF₁ η → η <ᵀ Ωs ν → NF₁ (fsT d η)\n",
"""nfψ¹ : NFᴾ₁ ψ¹
nfψ¹ = nψ nf1′ (sC (c∷ c[])) nf1′ b
  where
  b : Bnd₁ (natT 1) (natT 1)
  b (vh (inj₁ ()))
  b (vh (inj₂ ()))
  b (vd (inj₁ ()) _)
  b (vd (inj₂ ()) _)
  b (vs (inj₁ ()) _)
  b (vs (inj₂ ()) _)
  b (vt ())

hdψ¹ : ∀ n {θ} → Ctbl θ → Hd≤ (Ωᵐ n θ) ψ¹
hdψ¹ zero c[] = tt
hdψ¹ zero (c∷ ct) = inj₁ refl
hdψ¹ (suc n) c = inj₁ refl

NFψ¹ : ∀ n {θ} → NF₁ θ → Ctbl θ → NF₁ (ψ¹ ∷ Ωᵐ n θ)
NFψ¹ n nθ c = n∷ nfψ¹ (NFΩᵐ n nθ c) (hdψ¹ n c)

NF₁-fsT : ∀ {d ν η} → NF₁ d → cof d ≡ cΩ ν → NF₁ η → η <ᵀ Ωs ν → NF₁ (fsT d η)
""")
    s=sub1(s,"""... | sing² n = subst NF₁ (sym (fsT-sing n η)) (n∷ (nψ (NFΩᵐ (suc n) nη (ctblΩ nη η<)) (SbΩᵐ n (ctblΩ nη η<)) n[] bnd[]) n[] tt)
""","""... | sing² n = subst NF₁ (sym (fsT-sing n η)) (n∷ (nψ (NFΩᵐ (suc n) nη (ctblΩ nη η<)) (SbΩᵐ n (ctblΩ nη η<)) n[] bnd[]) n[] tt)
... | singψ n = subst NF₁ (sym (fsT-singψ n η)) (n∷ (nψ (NFψ¹ n nη (ctblΩ nη η<)) (sψ n (ctblΩ nη η<)) n[] bnd[]) n[] tt)
""")
    return s

def patch_system(s):
    s=sub1(s,"Sb-suc (sC c) = sC (Ctbl-suc c)\n","Sb-suc (sψ n c) = subst Sb (sym (cong (ψ¹ ∷_) (suc-Ωᵐ n _))) (sψ n (Ctbl-suc c))\nSb-suc (sC c) = sC (Ctbl-suc c)\n")
    s=sub1(s,"leafSb su (sing² n) = sC (c∷ c[])\n","leafSb su (sing² n) = sC (c∷ c[])\nleafSb su (singψ n) = sC (c∷ c[])\n")
    return s

PATCH={'StandardOmega':patch_standard,'SystemOmega':patch_system}
EXTRA={}   # 其余模块上的补丁, 见下

def gen(src,dst,patch=None,why=''):
    s=open(A+src+'.lagda.md',encoding='utf-8').read()
    if patch: s=patch(s)
    s=rename(s)
    s=NOTE%(src,why)+s
    open(OUT+dst+'.lagda.md','w',encoding='utf-8').write(s)

for m in ZMODS:
    gen('ScafLadderZ'+m,'LadderLabZ'+m,PATCH.get(m) or EXTRA.get(m),'' if m not in PATCH else ', 加 `sψ`, `singψ`')
gen('ScafLadderQ','LadderLabZQ')
for m in NFW:  gen('LadderNFW'+m,'LadderLabZNFW'+m)
for m in INFW: gen('LadderInfW'+m,'LadderLabZInfW'+m)
# ω+ω 实例没有现成的 W 克隆, 从主线改导入 (规则同 laddernf/mk_infw.py)
s=open(A+'LadderInfTop2.lagda.md',encoding='utf-8').read()
s=s.replace('OCF.Align.LadderNFTree','OCF.Align.LadderNFWTree')
s=re.sub(r'OCF\.Align\.LadderInfTop2\b','OCF.Align.LadderInfWTop2',s)
s=rename(s)
s=NOTE%('LadderInfTop2','')+s
open(OUT+'LadderLabZInfWTop2.lagda.md','w',encoding='utf-8').write(s)
