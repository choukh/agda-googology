# -*- coding: utf-8 -*-
# 生成 probes/OCF/Align/ScafLadderZ*: 标签阶梯用的机械克隆 (NF₁, Occ 的扩展, 标记 omk, 标签类的档位).
# 用法 (任意目录): python3 mkworld.py [输出目录], 默认写回 probes/OCF/Align/. 补丁文件与本脚本同目录.
import re,os,subprocess,shutil,sys,tempfile
HERE=os.path.dirname(os.path.abspath(__file__))
A=os.path.abspath(os.path.join(HERE,'..','..','..','OCF','Align'))+'/'
OUT=(sys.argv.pop(1).rstrip('/')+'/') if len(sys.argv)>1 else A
MODS='Decouple DecoupleBase GoodL GoodLBase NonTight NonTightBase Omega2 Omega2Base OmegaExp OmegaExpBase OmegaK OmegaKBase OmegaSq OmegaSqBase Prefix Relative RelativeBase Stage2Label StandardOmega SystemOmega TopDown Uniform2 Uniform2Base Uniform2Depth1 Uniform3 Uniform3Base Uniform3Depth1 Uniform3Depth2Class Uniform3Depth2Fold Uniform3Depth2W Uniform3Full Uniform3Hon Uniform3Rel Uniform3SqA Uniform3SqABase Uniform4Base Uniform4Head Uniform4Two Uniform5Class Uniform5Close Uniform5Eval Uniform5Head Uniform5Psi Uniform5Rel Uniform5RelPsi Uniform5Tail Uniform5Tr UniformS'.split()
extra=sys.argv[1:]  # further modules
MODS=sorted(set(MODS+extra))
P='ScafLadderZ'
pat=re.compile(r'OCF\.Align\.('+'|'.join(sorted(MODS,key=len,reverse=True))+r')(?![\wᴸᴺ₀-₉²])')
tmp=tempfile.mkdtemp()+'/'
os.makedirs(tmp,exist_ok=True)
for name,patchf in [('StandardOmega','StandardOmega-Sb2.patch'),('SystemOmega','SystemOmega-Sb2.patch')]:
    shutil.copy(A+name+'.lagda.md',tmp+name+'.lagda.md')
    subprocess.check_call(['patch','-s',tmp+name+'.lagda.md',HERE+'/'+patchf])
for m in MODS:
    src=(tmp+m+'.lagda.md') if os.path.exists(tmp+m+'.lagda.md') else A+m+'.lagda.md'
    s=open(src).read()
    s=pat.sub(lambda mt:'OCF.Align.'+P+mt.group(1),s)
    note='> **机械克隆.** 由 `'+m+'` 经脚本复制, 只为把 `NF₁`, `Occ` 换成 [ScafLadderZStandardOmega](ScafLadderZStandardOmega.lagda.md), [ScafLadderZSystemOmega](ScafLadderZSystemOmega.lagda.md) 的版本; 见 [ScafLadder](ScafLadder.lagda.md). 下面的文字是原文.\n\n'
    open(OUT+P+m+'.lagda.md','w').write(note+s)
# Occ 补丁: 下标的尾巴也算出现 (Ω+τ 里的 τ)
def sub(m,a,b,cnt=1):
    p=OUT+P+m+'.lagda.md'; s=open(p).read()
    assert a in s,(m,a)
    open(p,'w').write(s.replace(a,b,cnt))
sub('SystemOmega','data Occ (x : T) : T → Set where\n','data TailOf (x : T) : T → Set where\n  th : ∀ {y} → TailOf x (y ∷ x)\n  ts : ∀ {y u} → TailOf x u → TailOf x (y ∷ u)\n\ndata Occ (x : T) : T → Set where\n')
sub('SystemOmega','  os : ∀ {y a xs} → Occ x y → Occ x (ψᵗ y a ∷ xs)\n','  os : ∀ {y a xs} → Occ x y → Occ x (ψᵗ y a ∷ xs)\n  oτ : ∀ {u a xs} → TailOf x u → Occ x (ψᵗ u a ∷ xs)\n')
sub('SystemOmega','occVis : ∀ {y e xs t} → Occ (ψᵗ y e ∷ xs) t → Vis₁ [] e t\n','tailVis : ∀ {y e xs u} → TailOf (ψᵗ y e ∷ xs) u → Vis₁ [] e u\ntailVis th = vt (vh ([]≤ _))\ntailVis (ts t) = vt (tailVis t)\n\nocc-tailNF : ∀ {x u} → TailOf x u → NF₁ u → NF₁ x\nocc-tailNF th (n∷ _ r _) = r\nocc-tailNF (ts t) (n∷ _ r _) = occ-tailNF t r\n\noccVis : ∀ {y e xs t} → Occ (ψᵗ y e ∷ xs) t → Vis₁ [] e t\n')
sub('SystemOmega','occVis (os o) = vs ([]≤ _) (occVis o)\n','occVis (os o) = vs ([]≤ _) (occVis o)\noccVis (oτ t) = vs ([]≤ _) (tailVis t)\n')
sub('SystemOmega','Occ-NF (n∷ (nψ nx _ _ _) _ _) (os o) = Occ-NF nx o\n','Occ-NF (n∷ (nψ nx _ _ _) _ _) (os o) = Occ-NF nx o\nOcc-NF (n∷ (nψ nx _ _ _) _ _) (oτ t) = occ-tailNF t nx\n')
sub('SystemOmega','occ< nt (c∷ ct) (os ()) cx\n','occ< nt (c∷ ct) (os ()) cx\nocc< nt (c∷ ct) (oτ ()) cx\n')
for m in ['NonTightBase','Uniform2Base','Uniform3Base']:
    sub(m,'OccPre b (os o) = os o\n','OccPre b (os o) = os o\nOccPre b (oτ t) = oτ t\n')
sub('Uniform3SqABase','occ-hd (os o) = os o\n','occ-hd (os o) = os o\nocc-hd (oτ t) = oτ t\n')
sub('Uniform5Psi','occ-rep n (os o) = os o\n','occ-rep n (os o) = os o\nocc-rep n (oτ t) = oτ t\n')
sub('RelativeBase','occ1′ (os ())\n','occ1′ (os ())\nocc1′ (oτ ())\n')
sub('Uniform2Base','occ1 (os ())\n','occ1 (os ())\nocc1 (oτ ())\n')
sub('RelativeBase','lvl-small Iw (ot ())\n','lvl-small (Y , hY , lY , nY) (oτ th) = inj₁ (lab[]≅0 hY lY)\nlvl-small Iw (oτ (ts ()))\nlvl-small (Y , hY , lY , nY) (os (oτ th)) = inj₁ (lab[]≅0 hY lY)\nlvl-small Iw (os (oτ (ts ())))\nlvl-small Iw (ot ())\n')
for m in MODS:
    p=OUT+P+m+'.lagda.md'; s=open(p).read()
    s2=re.sub(r'(open import OCF\.Align\.ScafLadderZSystemOmega using \(Occ; oh; od; os; ot)',r'\1; oτ; TailOf; th; ts',s)
    if s2!=s: open(p,'w').write(s2)
# ------ ob: 紧地板的记号 (ι↓ 用, 其余函数忘掉) ------
def subre(m,pat_,rep_,cnt=0):
    p=OUT+P+m+'.lagda.md'; s=open(p).read()
    s2,n=re.subn(pat_,rep_,s,count=cnt,flags=re.M)
    assert n>0,(m,pat_)
    open(p,'w').write(s2)
U2='Uniform4Two'
sub(U2,"    oΩ   : ∀ {φ k} → (∀ {ℓ} → Ev ℓ φ → Ev ℓ Fl) → (q : k <ᴵ α) → (∀ ξ → U k (<→◃ q) ξ → O₊ (ξ ⊔ φ)) → O₊ φ\n",
"    oΩ   : ∀ {φ k} → (∀ {ℓ} → Ev ℓ φ → Ev ℓ Fl) → (q : k <ᴵ α) → (∀ ξ → U k (<→◃ q) ξ → O₊ (ξ ⊔ φ)) → O₊ φ\n    omk  : ∀ {φ k} → (r : k ◃₁ α) → U k (◃₁→◃ r) φ → O₊ φ → O₊ φ\n")
sub(U2,"W ⊕ oΩ fe q h = oΩ (λ e → fe (proj₂ e)) q (λ ξ z → owk swp (W ⊕ h ξ z))\n","W ⊕ oΩ fe q h = oΩ (λ e → fe (proj₂ e)) q (λ ξ z → owk swp (W ⊕ h ξ z))\nW ⊕ omk r z x = W ⊕ x\n")
sub(U2,"ι r (oΩ fe q h) = oΩ fe (<◃ q r) (λ ξ z → ι r (h ξ (intoU (<→◃ q) (outU (<→◃ (<◃ q r)) z))))\n","ι r (oΩ fe q h) = oΩ fe (<◃ q r) (λ ξ z → ι r (h ξ (intoU (<→◃ q) (outU (<→◃ (<◃ q r)) z))))\nι r (omk q z x) = ι r x\n")
sub(U2,"\ntr⁻O e o0 = o0\n","trO (s≅ e) (omk zero z x) = omk zero (trO e z) (trO (s≅ e) x)\ntrO (l≅ h) (omk (self n) z x) = omk (self n) (trO (h n) z) (trO (l≅ h) x)\n\ntr⁻O e o0 = o0\n")
sub(U2,"\nresO zero      (s≅ e) = restrO e zero (tr⁻O e)\n","tr⁻O (s≅ e) (omk zero z x) = omk zero (tr⁻O e z) (tr⁻O (s≅ e) x)\ntr⁻O (l≅ h) (omk (self n) z x) = omk (self n) (tr⁻O (h n) z) (tr⁻O (l≅ h) x)\n\nresO zero      (s≅ e) = restrO e zero (tr⁻O e)\n")
sub(U2,"Ω̇ (suc α) = oΩ (λ e → e) zero (λ ξ z → owk proj₁ (ι zero z))\nΩ̇ (lim f s) = ol (λ n → ι (self n) (Ω̇ (f n)))\n",
"Ω̇ (suc α) = oΩ (λ e → e) zero (λ ξ z → owk proj₁ (omk zero z (ι zero z)))\nΩ̇ (lim f s) = ol (λ n → omk (self n) (Ω̇ (f n)) (ι (self n) (Ω̇ (f n))))\n")
sub(U2,"ψᵒ q (owk le x) = owk (λ e → proj₁ e , le (proj₂ e)) (ψᵒ q x)\n","ψᵒ q (owk le x) = owk (λ e → proj₁ e , le (proj₂ e)) (ψᵒ q x)\nψᵒ q (omk r z x) = ψᵒ q x\n")
sub(U2,"ψ̄ (owk le x) = wk 0 le (ψ̄ x)\n","ψ̄ (owk le x) = wk 0 le (ψ̄ x)\nψ̄ (omk r z x) = ψ̄ x\n")
# ------ 档位 b: 标签类分两档. true 档在 `ls` 行多记 "c 的地板在标签里出现" ------
C5='Uniform5Class'
sub(C5,"## §2 `Ld`\n","""## §2 `Ld`

```agda
FC : Bool → Ordᴵ → T → Set
FC false c u = ⊤
FC true  c u = FlrLab (flo c) u
```
""")
p=OUT+P+C5+'.lagda.md'; s=open(p).read()
s=s.replace("module _ (c : Ordᴵ) (L : ∀ {k} → k ◃ c → Mode → ∀ {ξ} → O k ξ → T → Set) where\n  data Ld₊ : Mode → ∀ {φ} → O c φ → T → Set where",
            "module _ (c : Ordᴵ) (L : ∀ {k} → k ◃ c → Mode → ∀ {ξ} → O k ξ → T → Set) where\n  data Ld₊ : Bool → Mode → ∀ {φ} → O c φ → T → Set where")
s=s.replace("FlU m φ (ps ++ pred (y ∷ ys)) → Ld₊ m a (ps ++ pred (y ∷ ys))","FlU m φ (ps ++ pred (y ∷ ys)) → FC b c (ps ++ pred (y ∷ ys)) → Ld₊ m a (ps ++ pred (y ∷ ys))")
s=s.replace("""         (∀ {m′} → Cv m m′ → ∀ ξ (z : O k ξ) θ → L (<→◃ r) m′ z θ → Ld₊ m′ (h ξ (intoU (<→◃ r) z)) (ps ++ fsT (y ∷ ys) θ)) → Ld₊ m (oΩ fe r h) (ps ++ (y ∷ ys))
""","""         (∀ {m′} → Cv m m′ → ∀ ξ (z : O k ξ) θ → L (<→◃ r) m′ z θ → Ld₊ m′ (h ξ (intoU (<→◃ r) z)) (ps ++ fsT (y ∷ ys) θ)) → Ld₊ m (oΩ fe r h) (ps ++ (y ∷ ys))
    lob : ∀ {m φ u k} {r : k ◃₁ c} {z : Us k (◃₁→◃ r) φ} {x : O c φ} → L (◃₁→◃ r) m (outU (◃₁→◃ r) z) u → Ld₊ m x u → Ld₊ m (omk r z x) u
""")
s=s.replace("""Ld : ∀ c → Mode → ∀ {φ} → O c φ → T → Set
LL : ∀ c {k} → k ◃ c → Mode → ∀ {ξ} → O k ξ → T → Set
Ld c m x u = Ld₊ c (LL c) m x u
LL (suc c)   zero      m x u = Ld c m x u
""","""Ld : ∀ c → Bool → Mode → ∀ {φ} → O c φ → T → Set
LL : ∀ c {k} → k ◃ c → Mode → ∀ {ξ} → O k ξ → T → Set
Ld c b m x u = Ld₊ c (LL c) b m x u
LL (suc c)   zero      m x u = Ld c true m x u
""")
s=s.replace("LL (lim f s) (self n)  m x u = Ld (f n) m x u","LL (lim f s) (self n)  m x u = Ld (f n) true m x u")
s=s.replace("→ LL c r m z θ → Ld k m z θ","→ LL c r m z θ → Ld k true m z θ").replace("→ Ld k m z θ → LL c r m z θ","→ Ld k true m z θ → LL c r m z θ")
i=s.index("  data Ld₊ : Bool"); j=s.index("\nLd : ∀ c")
row=s[i:j]
hd,rest=row.split("\n",1)
rest=rest.replace("Ld₊ ","Ld₊ b ").replace("∀ {m φ","∀ {b m φ").replace("(wkm i) (f x)","(wkm i) (f x)")
rest=rest.replace("→ Ld₊ b m x u → Ld₊ b m (omk r z x) u","→ Ld₊ false m x u → Ld₊ b m (omk r z x) u")
s=s[:i]+hd+"\n"+rest+s[j:]
s=s.replace("Ld-cv : ∀ {c a b φ} {x : O c φ} {u} → Cv a b → Ld c a x u → Ld c b x u","Ld-cv : ∀ {c t a b φ} {x : O c φ} {u} → Cv a b → Ld c t a x u → Ld c t b x u")
s=s.replace("Ld-cv v (ls cc F l) = ls cc (FlU-cv v F) (Ld-cv v l)","Ld-cv v (ls cc F Fc l) = ls cc (FlU-cv v F) Fc (Ld-cv v l)")
s=s.replace("Ld-cv v (lΩ cc I e f) = lΩ cc I e (λ v′ → f (Cv-tr v v′))","Ld-cv v (lΩ cc I e f) = lΩ cc I e (λ v′ → f (Cv-tr v v′))\nLd-cv v (lob {r = zero} l x) = lob (Ld-cv v l) (Ld-cv v x)\nLd-cv v (lob {r = self n} l x) = lob (Ld-cv v l) (Ld-cv v x)")
open(p,'w').write(s)
# Close
p=OUT+P+'Uniform5Close.lagda.md'; s=open(p).read()
s=s.replace("re : ∀ {c m φ} {x : O c φ} {u v} → u ≡ v → Ld c m x u → Ld c m x v","re : ∀ {c b m φ} {x : O c φ} {u v} → u ≡ v → Ld c b m x u → Ld c b m x v")
s=s.replace("Ld-⊕ : ∀ {c m φ ψ} {W : O c φ} {t : O c ψ} {x y} → Ld c m W x → FlM m φ x → Ld c m t y → Ld c m (W ⊕ t) (x ++ y)\n",
"""FC-pre : ∀ {b c x} v → FC b c x → FC b c (x ++ v)
FC-pre {b = false} v F = tt
FC-pre {b = true}  v F = FlrLab-mono (OccPre v) F

Ld-⊕ : ∀ {c b b′ m φ ψ} {W : O c φ} {t : O c ψ} {x y} → Ld c b m W x → FlM m φ x → FC b c x → Ld c b′ m t y → Ld c b m (W ⊕ t) (x ++ y)
""")
i=s.index('Ld-⊕ : ∀'); head,tail=s[:i],s[i:]
tail=tail.replace("Ld-⊕ {x = x} lW F lz","Ld-⊕ {x = x} lW F Fc lz")
tail=tail.replace("Ld-⊕ {x = x} lW F (ls {ps = ps} {y} {ys} cc Fa l) =\n  re (++-assoc x ps (y ∷ ys)) (ls {ps = x ++ ps} cc (subst (FlU _ _) (sym (++-assoc x ps _)) (FlU-⊔ F Fa)) (re (sym (++-assoc x ps _)) (Ld-⊕ lW F l)))",
"Ld-⊕ {x = x} lW F Fc (ls {ps = ps} {y} {ys} cc Fa _ l) =\n  re (++-assoc x ps (y ∷ ys)) (ls {ps = x ++ ps} cc (subst (FlU _ _) (sym (++-assoc x ps _)) (FlU-⊔ F Fa)) (subst (FC _ _) (sym (++-assoc x ps _)) (FC-pre _ Fc)) (re (sym (++-assoc x ps _)) (Ld-⊕ lW F Fc l)))")
tail=re.sub(r'Ld-⊕ \{x = x\} lW F \(',r'Ld-⊕ {x = x} lW F Fc (',tail)
tail=re.sub(r'\(Ld-⊕ (\(Ld-cv v lW\)) (\(FlM-cv v F\)) ',r'(Ld-⊕ \1 \2 Fc ',tail)
tail=re.sub(r'\(Ld-⊕ lW F (?!Fc)',r'(Ld-⊕ lW F Fc ',tail)
tail=re.sub(r'^Ld-⊕ lW F (?!Fc)',r'Ld-⊕ lW F Fc ',tail,flags=re.M)
s=head+tail.rstrip('`\n ')+"\nLd-⊕ lW F Fc (lob l x) = Ld-⊕ lW F Fc x\n```\n"
open(p,'w').write(s)
# Tail
p=OUT+P+'Uniform5Tail.lagda.md'; s=open(p).read()
s=s.replace("Ld-ι : ∀ {c d m φ} (q : c ◃ d) {x : O c φ} {u} → Ld c m x u → Ld d m (ι q x) u","Ld-ι : ∀ {c d b m φ} (q : c ◃ d) {x : O c φ} {u} → Ld c b m x u → Ld d false m (ι q x) u")
s=s.replace("Ld-ι q (ls cc F l) = ls cc F (Ld-ι q l)","Ld-ι q (ls cc F _ l) = ls cc F tt (Ld-ι q l)\nLd-ι q (lob l x) = Ld-ι q x")
s=s.replace("subst (λ w → Ld d m′ (ι q (h ξ","subst (λ w → Ld d false m′ (ι q (h ξ")
s=s.replace("→ Lab0ᴸ t y → Ld c m (tl φ cv t) y","→ Lab0ᴸ t y → Ld c false m (tl φ cv t) y")
s=s.replace("tlA {y = y ∷ ys} fp (ls cc l) = ls {ps = []} cc (fp _) (tlA fp l)","tlA {y = y ∷ ys} fp (ls cc l) = ls {ps = []} cc (fp _) tt (tlA fp l)")
s=s.replace("Ld c (wkm i) (tl φ cv t) y","Ld c false (wkm i) (tl φ cv t) y")
s=s.replace("ls {ps = []} cc (FP→U fp _) (tl₊ fp lv l)","ls {ps = []} cc (FP→U fp _) tt (tl₊ fp lv l)")
s=s.replace("→ LabL₊ k Ll t y → Ld c m (tl φ cv t) y","→ LabL₊ k Ll t y → Ld c false m (tl φ cv t) y")
s=s.replace("        Ld c m (tl φ cv (Ωˢ k)) (Ωt θ)","        Ld c false m (tl φ cv (Ωˢ k)) (Ωt θ)")
s=s.replace("→ InpW j η x → Ld c m (tl (flo j) (cvFlo j) x) η","→ InpW j η x → Ld c false m (tl (flo j) (cvFlo j) x) η")
s=s.replace("ls {ps = []} cc (FH→U (proj₂ (proj₂ (pred-Pr nb cc))) (FH-pred nb cc fp)) (tlH","ls {ps = []} cc (FH→U (proj₂ (proj₂ (pred-Pr nb cc))) (FH-pred nb cc fp)) tt (tlH")
s=s.replace("""LdΩ̇ : ∀ {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → ∀ {α} → α ≅ᴵ toLevel Y hY → ∀ m → Ld α m (Ω̇ α) (Ωt (μ θ))
""","""Ld-up : ∀ {m φ} {x : O zero φ} {u} → Ld zero false m x u → Ld zero true m x u
Ld-up lz = lz
Ld-up (ls cc F _ l) = ls cc F (λ ()) (Ld-up l)
Ld-up (ll cc h) = ll cc (λ n → Ld-up (h n))
Ld-up (li cc I e hP hI) = li cc I e (λ η x l s v → Ld-up (hP η x l s v)) (λ η x i → Ld-up (hI η x i))
Ld-up (lĉ cc K h₀ hk) = lĉ cc K (Ld-up h₀) (λ k → Ld-up (hk k))
Ld-up (lŝ cc I b ob′ h₀ hg) = lŝ cc I b ob′ (Ld-up h₀) (λ θ Y hY lY nθ lt e → Ld-up (hg θ Y hY lY nθ lt e))
Ld-up (lclo F cc h₀ hg) = lclo F cc (Ld-up h₀) (λ θ Y hY lY nθ lt → Ld-up (hg θ Y hY lY nθ lt))
Ld-up (lwk l) = lwk (Ld-up l)

LdΩ̇ : ∀ {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → ∀ {α} → α ≅ᴵ toLevel Y hY → ∀ m → Ld α true m (Ω̇ α) (Ωt (μ θ))
""")
s=s.replace("""  lclo {ps = []} {y = ΩΩ} {ys = []} (Fw-Ω̂ m) refl
       (tlΩ""","""  Ld-up (lclo {ps = []} {y = ΩΩ} {ys = []} (Fw-Ω̂ m) refl
       (tlΩ""")
s=s.replace("{λ e q → proj₂ e (suc q)} (ZuK m (toLevel Y hY)))\n","{λ e q → proj₂ e (suc q)} (ZuK m (toLevel Y hY))))\n")
s=s.replace("(λ v ξ z θ l′ → lwk (re (sym (fsTΩ {Ωp} {w ∷ ws} c₁ θ)) (Ld-ι zero l′)))","(λ v ξ z θ l′ → lwk (re (sym (fsTΩ {Ωp} {w ∷ ws} c₁ θ)) (lob l′ (Ld-ι zero l′))))")
s=s.replace("(Ld-ι (self n) (LdΩ̇ (F′ n) (hl₁ hY n) (Lab-≅ (k′ n) (h n)) (NF₁-fsn nθ c₁ n) (ee n) m)))","(lob (LdΩ̇ (F′ n) (hl₁ hY n) (Lab-≅ (k′ n) (h n)) (NF₁-fsn nθ c₁ n) (ee n) m) (Ld-ι (self n) (LdΩ̇ (F′ n) (hl₁ hY n) (Lab-≅ (k′ n) (h n)) (NF₁-fsn nθ c₁ n) (ee n) m))))")
s=s.replace("LdΩ̇ᴵ : ∀ {ν α} (I : Idx ν) → α ≅ᴵ lvI I → ∀ m → Ld α m (Ω̇ α) (Ωt (μ ν))","LdΩ̇ᴵ : ∀ {ν α} (I : Idx ν) → α ≅ᴵ lvI I → ∀ m → Ld α true m (Ω̇ α) (Ωt (μ ν))")
open(p,'w').write(s)
# Tr
p=OUT+P+'Uniform5Tr.lagda.md'; s=open(p).read()
s=s.replace("""Ld-tr  : ∀ {a b m φ} (e : a ≅ᴵ b) {x : O a φ} {u} → Ld a m x u → Ld b m (trO e x) u
Ld-tr⁻ : ∀ {a b m φ} (e : a ≅ᴵ b) {x : O b φ} {u} → Ld b m x u → Ld a m (tr⁻O e x) u
""","""FC-≅ : ∀ {t a b u} → a ≅ᴵ b → FC t a u → FC t b u
FC-≅ {t = false} e F = tt
FC-≅ {t = true} {a = zero} {b = zero} z≅ F = λ ()
FC-≅ {t = true} {a = suc a} {b = suc b} (s≅ e) F ink with F ink
... | inj₁ e0 = inj₁ (≅ᴵ-trans (≅ᴵ-sym e) e0)
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , ≼-trans (inj₂ (≅ᴵ-sym e)) kw , o)
FC-≅ {t = true} {a = lim f s} {b = lim g r} e F inb with F inb
... | inj₁ ()
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , ≼-trans (inj₂ (≅ᴵ-sym e)) kw , o)

Ld-tr  : ∀ {t a b m φ} (e : a ≅ᴵ b) {x : O a φ} {u} → Ld a t m x u → Ld b t m (trO e x) u
Ld-tr⁻ : ∀ {t a b m φ} (e : a ≅ᴵ b) {x : O b φ} {u} → Ld b t m x u → Ld a t m (tr⁻O e x) u
""")
s=s.replace("→ Ld _ m z θ → Ld j m (backO (resO q e) z) θ","→ Ld _ true m z θ → Ld j true m (backO (resO q e) z) θ")
s=s.replace("→ Ld _ m z θ → Ld j m (backO (res⁻O q e) z) θ","→ Ld _ true m z θ → Ld j true m (backO (res⁻O q e) z) θ")
s=s.replace("Ld-tr e (ls cc F l) = ls cc F (Ld-tr e l)","Ld-tr e (ls cc F Fc l) = ls cc F (FC-≅ e Fc) (Ld-tr e l)\nLd-tr (s≅ e) (lob {r = zero} l x) = lob (Ld-tr e l) (Ld-tr (s≅ e) x)\nLd-tr (l≅ h) (lob {r = self n} l x) = lob (Ld-tr (h n) l) (Ld-tr (l≅ h) x)")
s=s.replace("Ld-tr⁻ e (ls cc F l) = ls cc F (Ld-tr⁻ e l)","Ld-tr⁻ e (ls cc F Fc l) = ls cc F (FC-≅ (≅ᴵ-sym e) Fc) (Ld-tr⁻ e l)\nLd-tr⁻ (s≅ e) (lob {r = zero} l x) = lob (Ld-tr⁻ e l) (Ld-tr⁻ (s≅ e) x)\nLd-tr⁻ (l≅ h) (lob {r = self n} l x) = lob (Ld-tr⁻ (h n) l) (Ld-tr⁻ (l≅ h) x)")
s=s.replace("subst (λ w → Ld b m′ (trO e","subst (λ w → Ld b _ m′ (trO e").replace("subst (λ w → Ld a m′ (tr⁻O e","subst (λ w → Ld a _ m′ (tr⁻O e")
s=s.replace("Ld-tr {b = b} e (lΩ","Ld-tr {b = b} e (lΩ").replace("Ld-tr⁻ {a = a} e (lΩ","Ld-tr⁻ {a = a} e (lΩ")
open(p,'w').write(s)
# Psi
p=OUT+P+'Uniform5Psi.lagda.md'; s=open(p).read()
s=s.replace("Ld-rep : ∀ {c m φ} {X̂ : O c φ} {X} → Ld c m X̂ (X ∷ []) → FlM m φ (X ∷ []) → ∀ n → Ld c m (repᵒ X̂ n) (replicate n X)",
"""FC-rep : ∀ {b c x} n → FC b c (x ∷ []) → FC b c (replicate (suc n) x)
FC-rep {b = false} n F = tt
FC-rep {b = true}  n F = FlrLab-mono (occ-rep n) F

FC-τ : ∀ {t τ u} (Iτ : Idx τ) → t ≅ᴵ lvI Iτ → FC true t (ψᵗ (μ τ) u ∷ [])
FC-τ {suc t} Iτ e ink = inj₂ (_ , Iτ , inj₁ (≺ᴵ-respʳ (via (≅ᴵ-refl t) zero) e) , oτ th)
FC-τ {lim f s} Iτ e inb = inj₂ (_ , Iτ , inj₂ e , oτ th)

Ld-rep : ∀ {c b m φ} {X̂ : O c φ} {X} → Ld c b m X̂ (X ∷ []) → FlM m φ (X ∷ []) → FC b c (X ∷ []) → ∀ n → Ld c b m (repᵒ X̂ n) (replicate n X)""")
s=s.replace("Ld-rep l F zero = lz\nLd-rep l F (suc zero) = l\nLd-rep {X = X} l F (suc (suc n)) = lwk (re (rep-snoc′ n X) (Ld-⊕ (Ld-rep l F (suc n)) (FlM-rep n F) l))",
"Ld-rep l F Fc zero = lz\nLd-rep l F Fc (suc zero) = l\nLd-rep {X = X} l F Fc (suc (suc n)) = lwk (re (rep-snoc′ n X) (Ld-⊕ (Ld-rep l F Fc (suc n)) (FlM-rep n F) (FC-rep n Fc) l))")
s=s.replace("Ld-ψ : ∀ {c t τ m φ} (q : t <ᴵ c) (Iτ : Idx τ) → t ≅ᴵ lvI Iτ → {x : O c φ} {u : T} → Ld c m x u → Ld t m (ψᵒ q x) (ψᵗ (μ τ) u ∷ [])",
            "Ld-ψ : ∀ {c t τ b m φ} (q : t <ᴵ c) (Iτ : Idx τ) → t ≅ᴵ lvI Iτ → {x : O c φ} {u : T} → Ld c b m x u → Ld t true m (ψᵒ q x) (ψᵗ (μ τ) u ∷ [])")
s=s.replace("chainL : ∀ {c k ν m φ ps y ys}","chainL : ∀ {c k ν b m φ ps y ys}")
s=s.replace("→ LL c (<→◃ r) m′ z θ → Ld c m′ (h ξ (intoU (<→◃ r) z)) (ps ++ fsT (y ∷ ys) θ)) →\n         ∀ n → Ld k m (chainᵒ proj₁","→ LL c (<→◃ r) m′ z θ → Ld c b m′ (h ξ (intoU (<→◃ r) z)) (ps ++ fsT (y ∷ ys) θ)) →\n         ∀ n → Ld k true m (chainᵒ proj₁")
s=s.replace("Ld-ψ {t = t} {τ} {m} q Iτ et lz","Ld-ψ {t = t} {τ} {m = m} q Iτ et lz")
s=s.replace("(ls {ps = ps} {y} {ys} cc F l) =","(ls {ps = ps} {y} {ys} cc F _ l) =")
s=s.replace("(λ n → re (sym (repW (μ τ) ps y ys cc n)) (Ld-rep (Ld-ψ q Iτ et l) (FlU→μ τ F) n))","(λ n → re (sym (repW (μ τ) ps y ys cc n)) (Ld-rep (Ld-ψ q Iτ et l) (FlU→μ τ F) (FC-τ Iτ et) n))")
s=s.replace("Ld-ψ q Iτ et (lwk l) = lwk (Ld-ψ q Iτ et l)","Ld-ψ q Iτ et (lwk l) = lwk (Ld-ψ q Iτ et l)\nLd-ψ q Iτ et (lob l x) = Ld-ψ q Iτ et x")
s=s.replace("subst (λ w → Ld t m′ (ψᵒ q","subst (λ w → Ld t true m′ (ψᵒ q")
open(p,'w').write(s)
# Eval
p=OUT+P+'Uniform5Eval.lagda.md'; s=open(p).read()
s=s.replace("chainR : ∀ {c k ν m φ ps y ys}","chainR : ∀ {c k ν b m φ ps y ys}")
s=s.replace("→ LL c (<→◃ r) m′ z θ → Ld c m′ (h ξ (intoU (<→◃ r) z)) (ps ++ fsT (y ∷ ys) θ)) →\n         ∀ n → Ld k m (chainᵒ fe","→ LL c (<→◃ r) m′ z θ → Ld c b m′ (h ξ (intoU (<→◃ r) z)) (ps ++ fsT (y ∷ ys) θ)) →\n         ∀ n → Ld k true m (chainᵒ fe")
s=s.replace("Ld→W : ∀ {c′ c m φ} {x : O c′ φ} {u} → OkW m c → Ld c′ m x u → Wd c 0 (ψ̄ x) u","Ld→W : ∀ {c′ c b m φ} {x : O c′ φ} {u} → OkW m c → Ld c′ b m x u → Wd c 0 (ψ̄ x) u")
s=s.replace("Ld→W ok (ls {ps = ps} {y} {ys} {a = a} cc F l)","Ld→W ok (lob l x) = Ld→W ok x\nLd→W ok (ls {ps = ps} {y} {ys} {a = a} cc F _ l)")
s=s.replace("Ld→W {c = c} {m} ok (li","Ld→W {c = c} {m = m} ok (li")
s=s.replace("Ld→O : ∀ {c φ} {x : O c φ} {u} → Ld c hon x u → Rᵒ c c x x → Od 0 (ψ̄ x) u","Ld→O : ∀ {c b φ} {x : O c φ} {u} → Ld c b hon x u → Rᵒ c c x x → Od 0 (ψ̄ x) u")
s=s.replace("Ld→O (ls {ps = ps} {y} {ys} {a = a} cc F l) (rs s r)","Ld→O (lob l x) (rob _ _ r) = Ld→O x r\nLd→O (ls {ps = ps} {y} {ys} {a = a} cc F _ l) (rs s r)")
s=s.replace("Ld→H : ∀ {c φ} {x : O c φ} {u} → Ld c hon x u → Rᵒ c c x x → Hd 0 (ψ̄ x) u","Ld→H : ∀ {c b φ} {x : O c φ} {u} → Ld c b hon x u → Rᵒ c c x x → Hd 0 (ψ̄ x) u")
s=s.replace("label : ∀ {c φ} {x : O c φ} {u} → Ld c hon x u → Rᵒ c c x x → NF₁","label : ∀ {c b φ} {x : O c φ} {u} → Ld c b hon x u → Rᵒ c c x x → NF₁")
open(p,'w').write(s)
# Rel
p=OUT+P+'Uniform5Rel.lagda.md'; s=open(p).read()
s=s.replace("""→ LR (<→◃ r) z z′ → R₊ (h ξ (intoU (<→◃ r) z)) (h′ ξ′ (intoU (<→◃ r′) z′))) → R₊ (oΩ fe r h) (oΩ fe′ r′ h′)
""","""→ LR (<→◃ r) z z′ → R₊ (h ξ (intoU (<→◃ r) z)) (h′ ξ′ (intoU (<→◃ r′) z′))) → R₊ (oΩ fe r h) (oΩ fe′ r′ h′)
    rob : ∀ {φ ψ k k′} {r : k ◃₁ a} {r′ : k′ ◃₁ b} {z : Us k (◃₁→◃ r) φ} {z′ : Us k′ (◃₁→◃ r′) ψ} {x : O a φ} {x′ : O b ψ} →
          k ≅ᴵ k′ → LR (◃₁→◃ r) (outU (◃₁→◃ r) z) (outU (◃₁→◃ r′) z′) → R₊ x x′ → R₊ (omk r z x) (omk r′ z′ x′)
""")
s=s.replace("R-⊕ s rW (rwk r) = rwk (R-⊕ s rW r)\n","R-⊕ s rW (rwk r) = rwk (R-⊕ s rW r)\nR-⊕ s rW (rob _ l r) = R-⊕ s rW r\n")
s=s.replace("R-ι q q′ (rwk r) = rwk (R-ι q q′ r)\n","R-ι q q′ (rwk r) = rwk (R-ι q q′ r)\nR-ι q q′ (rob _ l r) = R-ι q q′ r\n")
s=s.replace("RΩ̇ (s≅ e) = rΩ e (⊔∼ (∼ᶠ-refl fz) (fk∼ z≅)) (λ ξ ξ′ d z z′ l → rwk (R-ι zero zero l))\nRΩ̇ (l≅ h) = rl (λ n → R-ι (self n) (self n) (RΩ̇ (h n)))",
"RΩ̇ (s≅ e) = rΩ e (⊔∼ (∼ᶠ-refl fz) (fk∼ z≅)) (λ ξ ξ′ d z z′ l → rwk (rob {r = zero} {r′ = zero} e l (R-ι zero zero l)))\nRΩ̇ (l≅ h) = rl (λ n → rob {r = self n} {r′ = self n} (h n) (RΩ̇ (h n)) (R-ι (self n) (self n) (RΩ̇ (h n))))")
s=s.replace("R-trˡ e (rwk r) = rwk (R-trˡ e r)\n","R-trˡ e (rwk r) = rwk (R-trˡ e r)\nR-trˡ (s≅ e) (rob {r = zero} ek l r) = rob (≅ᴵ-trans (≅ᴵ-sym e) ek) (R-trˡ e l) (R-trˡ (s≅ e) r)\nR-trˡ (l≅ h) (rob {r = self n} ek l r) = rob (≅ᴵ-trans (≅ᴵ-sym (h n)) ek) (R-trˡ (h n) l) (R-trˡ (l≅ h) r)\n")
s=s.replace("R-tr⁻ˡ e (rwk r) = rwk (R-tr⁻ˡ e r)\n","R-tr⁻ˡ e (rwk r) = rwk (R-tr⁻ˡ e r)\nR-tr⁻ˡ (s≅ e) (rob {r = zero} ek l r) = rob (≅ᴵ-trans e ek) (R-tr⁻ˡ e l) (R-tr⁻ˡ (s≅ e) r)\nR-tr⁻ˡ (l≅ h) (rob {r = self n} ek l r) = rob (≅ᴵ-trans (h n) ek) (R-tr⁻ˡ (h n) l) (R-tr⁻ˡ (l≅ h) r)\n")
open(p,'w').write(s)
p=OUT+P+'Uniform5RelPsi.lagda.md'; s=open(p).read()
s=s.replace("R-trʳ e (rwk r) = rwk (R-trʳ e r)\n","R-trʳ e (rwk r) = rwk (R-trʳ e r)\nR-trʳ (s≅ e) (rob {r = zero} {r′ = zero} ek l r) = rob (≅ᴵ-trans ek e) (R-trʳ e l) (R-trʳ (s≅ e) r)\nR-trʳ (l≅ h) (rob {r = zero} {r′ = self n} ek l r) = rob (≅ᴵ-trans ek (h n)) (R-trʳ (h n) l) (R-trʳ (l≅ h) r)\nR-trʳ (s≅ e) (rob {r = self m} {r′ = zero} ek l r) = rob (≅ᴵ-trans ek e) (R-trʳ e l) (R-trʳ (s≅ e) r)\nR-trʳ (l≅ h) (rob {r = self m} {r′ = self n} ek l r) = rob (≅ᴵ-trans ek (h n)) (R-trʳ (h n) l) (R-trʳ (l≅ h) r)\n")
s=s.replace("R-tr⁻ʳ e (rwk r) = rwk (R-tr⁻ʳ e r)\n","R-tr⁻ʳ e (rwk r) = rwk (R-tr⁻ʳ e r)\nR-tr⁻ʳ (s≅ e) (rob {r = zero} {r′ = zero} ek l r) = rob (≅ᴵ-trans ek (≅ᴵ-sym e)) (R-tr⁻ʳ e l) (R-tr⁻ʳ (s≅ e) r)\nR-tr⁻ʳ (l≅ h) (rob {r = zero} {r′ = self n} ek l r) = rob (≅ᴵ-trans ek (≅ᴵ-sym (h n))) (R-tr⁻ʳ (h n) l) (R-tr⁻ʳ (l≅ h) r)\nR-tr⁻ʳ (s≅ e) (rob {r = self m} {r′ = zero} ek l r) = rob (≅ᴵ-trans ek (≅ᴵ-sym e)) (R-tr⁻ʳ e l) (R-tr⁻ʳ (s≅ e) r)\nR-tr⁻ʳ (l≅ h) (rob {r = self m} {r′ = self n} ek l r) = rob (≅ᴵ-trans ek (≅ᴵ-sym (h n))) (R-tr⁻ʳ (h n) l) (R-tr⁻ʳ (l≅ h) r)\n")
s=s.replace("R-ψ q q′ et (rwk r) = rwk (R-ψ q q′ et r)\n","R-ψ q q′ et (rwk r) = rwk (R-ψ q q′ et r)\nR-ψ q q′ et (rob _ l r) = R-ψ q q′ et r\n")
s=s.replace("R→Rd (rwk {le = le} {le′ = le′} r) = wkRd 0 le le′ (R→Rd r)\n","R→Rd (rwk {le = le} {le′ = le′} r) = wkRd 0 le le′ (R→Rd r)\nR→Rd (rob _ l r) = R→Rd r\n")
open(p,'w').write(s)
for m in ['Uniform5Class','Uniform5Close','Uniform5Tail','Uniform5Tr','Uniform5Psi','Uniform5Eval','Uniform5Rel','Uniform5RelPsi']:
    p=OUT+P+m+'.lagda.md'; s=open(p).read()
    if 'Data.Bool using' not in s:
        s=s.replace('open import Data.Nat using (ℕ; zero; suc)\n','open import Data.Nat using (ℕ; zero; suc)\nopen import Data.Bool using (Bool; true; false)\n',1)
        open(p,'w').write(s)
# ------ Sb 对一切 Ω·(n+2)+c ------
SO='StandardOmega'
def so(a,b,cnt=1):
    p=OUT+P+SO+'.lagda.md'; s=open(p).read()
    assert a in s,a[:60]
    open(p,'w').write(s.replace(a,b,cnt))
so("  sΩ² : ∀ {c} → Ctbl c → Sb (Ω₁ ∷ Ω₁ ∷ c)\n","  sΩ² : ∀ n {c} → Ctbl c → Sb (Ω₁ ∷ Ω₁ ∷ Ωᵐ n c)\n")
p=OUT+P+SO+'.lagda.md'; s=open(p).read()
i=s.index("data Sb : ")
s=s[:i]+"""Ωᵐ : ℕ → T → T
Ωᵐ zero    c = c
Ωᵐ (suc n) c = Ω₁ ∷ Ωᵐ n c

"""+s[i:]
s=s.replace("  sing² : Leaf₁ (Ω₁ ∷ Ω₁ ∷ []) []\n","  sing² : ∀ n → Leaf₁ (Ω₁ ∷ Ω₁ ∷ Ωᵐ n []) []\n")
s=s.replace("""leafInv₁ : ∀ u → Sb u → ∀ k → cof u ≡ k → ∀ {ν} → cofψ0 u k ≡ cΩ ν → Leaf₁ u ν
""","""cof-Ωᵐ[] : ∀ n → cof (Ω₁ ∷ Ωᵐ n []) ≡ cΩ []
cof-Ωᵐ[] zero = refl
cof-Ωᵐ[] (suc n) = cof-Ωᵐ[] n

cof-Ωᵐ+ : ∀ n x xs → cof (Ω₁ ∷ Ωᵐ n (x ∷ xs)) ≡ cof (x ∷ xs)
cof-Ωᵐ+ zero x xs = refl
cof-Ωᵐ+ (suc n) x xs = cof-Ωᵐ+ n x xs

pred-Ωᵐ[] : ∀ n → pred (Ω₁ ∷ Ωᵐ n []) ≡ Ω₁ ∷ Ωᵐ n []
pred-Ωᵐ[] zero = refl
pred-Ωᵐ[] (suc n) = cong (Ω₁ ∷_) (pred-Ωᵐ[] n)

pred-Ωᵐ+ : ∀ n x xs → pred (Ω₁ ∷ Ωᵐ n (x ∷ xs)) ≡ Ω₁ ∷ Ωᵐ n (pred (x ∷ xs))
pred-Ωᵐ+ zero x xs = refl
pred-Ωᵐ+ (suc n) x xs = cong (Ω₁ ∷_) (pred-Ωᵐ+ n x xs)

fsn-Ωᵐ+ : ∀ n x xs k → fsn (Ω₁ ∷ Ωᵐ n (x ∷ xs)) k ≡ Ω₁ ∷ Ωᵐ n (fsn (x ∷ xs) k)
fsn-Ωᵐ+ zero x xs k = refl
fsn-Ωᵐ+ (suc n) x xs k = cong (Ω₁ ∷_) (fsn-Ωᵐ+ n x xs k)

fsT-Ωᵐ : ∀ n η → fsT (Ω₁ ∷ Ωᵐ n []) η ≡ Ωᵐ n η
fsT-Ωᵐ zero η = refl
fsT-Ωᵐ (suc n) η = cong (Ω₁ ∷_) (fsT-Ωᵐ n η)

fsT0-sing : ∀ u k η → k ≡ cΩ [] → E.fsT0 u k η ≡ ψᵗ (fsT u η) [] ∷ []
fsT0-sing u .(cΩ []) η refl = refl

fsT-sing : ∀ n η → fsT (ψᵗ (Ω₁ ∷ Ω₁ ∷ Ωᵐ n []) [] ∷ []) η ≡ Ωt (Ω₁ ∷ Ωᵐ n η)
fsT-sing n η = trans (fsT0-sing (Ω₁ ∷ Ω₁ ∷ Ωᵐ n []) _ η (cof-Ωᵐ[] (suc n))) (cong (λ z → ψᵗ (Ω₁ ∷ z) [] ∷ []) (fsT-Ωᵐ n η))

leaf-sing : ∀ n {μ ν} → cof (Ω₁ ∷ Ω₁ ∷ Ωᵐ n []) ≡ cΩ μ → cΩ μ ≡ cΩ ν → Leaf₁ (Ω₁ ∷ Ω₁ ∷ Ωᵐ n []) ν
leaf-sing n ue e with trans (sym (cof-Ωᵐ[] (suc n))) ue
leaf-sing n ue refl | refl = sing² n

leafInv₁ : ∀ u → Sb u → ∀ k → cof u ≡ k → ∀ {ν} → cofψ0 u k ≡ cΩ ν → Leaf₁ u ν
""")
s=s.replace("""leafInv₁ .(Ω₁ ∷ Ω₁ ∷ []) (sΩ² c[]) (cΩ .[]) refl refl = sing²
leafInv₁ .(Ω₁ ∷ Ω₁ ∷ ψᵗ [] _ ∷ _) (sΩ² (c∷ cc)) (cΩ μ) ue e = ⊥-elim (Ctbl-cof (c∷ cc) ue)
""","""leafInv₁ .(Ω₁ ∷ Ω₁ ∷ Ωᵐ n []) (sΩ² n c[]) (cΩ μ) ue e = leaf-sing n ue e
leafInv₁ .(Ω₁ ∷ Ω₁ ∷ Ωᵐ n (ψᵗ [] _ ∷ _)) (sΩ² n (c∷ cc)) (cΩ μ) ue e = ⊥-elim (Ctbl-cof (c∷ cc) (trans (sym (cof-Ωᵐ+ (suc n) _ _)) ue))
""")
s=s.replace("""Sb-pred (sΩ² c[])     = sΩ² c[]
Sb-pred (sΩ² (c∷ cc)) = sΩ² (Ctbl-pred (c∷ cc))
""","""Sb-pred (sΩ² n c[])     = subst Sb (sym (pred-Ωᵐ[] (suc n))) (sΩ² n c[])
Sb-pred (sΩ² n (c∷ cc)) = subst Sb (sym (pred-Ωᵐ+ (suc n) _ _)) (sΩ² n (Ctbl-pred (c∷ cc)))
""")
s=s.replace("""Sb-fsn (sΩ² c[]) () n
Sb-fsn (sΩ² (c∷ cc)) e n = sΩ² (Ctbl-fsn (c∷ cc) e n)
""","""Sb-fsn (sΩ² m c[]) e n with trans (sym (cof-Ωᵐ[] (suc m))) e
... | ()
Sb-fsn (sΩ² m (c∷ cc)) e n = subst Sb (sym (fsn-Ωᵐ+ (suc m) _ _ n)) (sΩ² m (Ctbl-fsn (c∷ cc) (trans (sym (cof-Ωᵐ+ (suc m) _ _)) e) n))
""")
s=s.replace("... | sing²  = n[] , sC c[]\n","... | sing² _ = n[] , sC c[]\n")
# singΩ²
a=s.index("singΩ² : ∀ {c}"); b=s.index("singΩ² (tl< ())",a)+len("singΩ² (tl< ())")
s=s[:a]+"""record Pk² (n : ℕ) (e : T) : Set where
  constructor pk²
  field
    θ′ : T
    θ<′ : θ′ <ᵀ Ωs []
    fθ′ : ∀ {η} → θ′ <ᵀ η → e <ᵀ Ωᵐ n η
    hv′ : ∀ {y ζ θs} → θ′ ≡ ψᵗ y ζ ∷ θs → [] ≤ᵀ y → Vis₁ [] ζ e

pick² : ∀ n {e} → e <ᵀ Ω₁ ∷ Ωᵐ n [] → Pk² n e
pick² zero {e} q = pk² e q (λ r → r) (λ {y} {ζ} {θs} eθ h → subst (Vis₁ [] ζ) (sym eθ) (vh h))
pick² (suc n) []< = pk² [] []< (λ _ → []<) (λ ())
pick² (suc n) {x ∷ e} (hd< p) = pk² [] []< (λ _ → hd< p) (λ ())
pick² (suc n) {x ∷ e} (tl< q) with pick² n q
... | pk² θ θ< f h = pk² θ θ< (λ r → tl< (f r)) (λ eθ hh → vt (h eθ hh))

singΩ² : ∀ n {c} → c <ᵀ (ψᵗ (Ω₁ ∷ Ω₁ ∷ Ωᵐ n []) [] ∷ []) → ΩC (ψᵗ (Ω₁ ∷ Ω₁ ∷ Ωᵐ n []) [] ∷ []) [] c
singΩ² n []< = ωc [] []< (λ {η} _ → subst ([] <ᵀ_) (sym (fsT-sing n η)) []<) hv[]
singΩ² n {c = ψᵗ [] a ∷ cs} (hd< (lv< q)) = ωc [] []< (λ {η} _ → subst (_ <ᵀ_) (sym (fsT-sing n η)) (hd< (lv< []<))) hv[]
singΩ² n {c = ψᵗ (ψᵗ y b ∷ ys) a ∷ cs} (hd< (lv< (hd< p))) = ωc [] []< (λ {η} _ → subst (_ <ᵀ_) (sym (fsT-sing n η)) (hd< (lv< (hd< p)))) hv[]
singΩ² n {c = ψᵗ (x₀ ∷ e) a ∷ cs} (hd< (lv< (tl< q))) with pick² n q
... | pk² θ θ< f h = ωc θ θ< (λ {η} r → subst (_ <ᵀ_) (sym (fsT-sing n η)) (hd< (lv< (tl< (f r))))) (λ eθ hh → vs ([]≤ _) (vt (h eθ hh)))
singΩ² n (hd< (ar< ()))
singΩ² n (tl< ())"""+s[b:]
s=s.replace("... | sing² = singΩ² p\n","... | sing² n = singΩ² n p\n")
# swap
a=s.index("swapΩ₂ : ∀ C {η}"); b=s.index("\n```",a)
s=s[:a]+"""SW : ∀ a b C {η} → Ωᵐ (suc a) [] <ᵀ plug C (Ωt (Ωᵐ (suc (suc b)) [])) → η <ᵀ Ωᵗ → Ωᵐ a η <ᵀ plug C (Ωt (Ωᵐ (suc b) η))
SW zero b [] p []< = []<
SW zero b [] p (hd< (lv< q)) = hd< (lv< (<ᵀ-trans q (hd< (lv< []<))))
SW zero b [] p (hd< (ar< ()))
SW zero b [] p (tl< ())
SW (suc a) b [] p η< = hd< (lv< (hd< (lv< []<)))
SW a b (pre [] ∷ C) p η< = SW a b C p η<
SW zero b (pre (ψᵗ y R ∷ s) ∷ C) (hd< (lv< q)) η< = η<Ω-hd η< (inj₁ q) R _
SW zero b (pre (ψᵗ y R ∷ s) ∷ C) (hd< (ar< q)) η< = η<Ω-hd η< (inj₂ refl) R _
SW zero b (pre (ψᵗ y R ∷ s) ∷ C) (tl< q) η< = η<Ω-hd η< (inj₂ refl) [] _
SW (suc a) b (pre (ψᵗ y R ∷ s) ∷ C) (hd< (lv< q)) η< = hd< (lv< q)
SW (suc a) b (pre (ψᵗ y R ∷ s) ∷ C) (hd< (ar< q)) η< = hd< (ar< q)
SW (suc a) b (pre (ψᵗ y R ∷ s) ∷ C) (tl< q) η< = tl< (SW a b (pre s ∷ C) q η<)
SW zero b (nd y ∷ C) p η< with inv1 p
... | vlv q = η<Ω-hd η< (inj₁ q) _ []
... | var q = η<Ω-hd η< (inj₂ refl) _ []
SW (suc a) b (nd y ∷ C) p η< with inv1 p
... | vlv q = hd< (lv< q)
... | var q = hd< (ar< ([]<plug C))
SW zero b (sb ∷ C) p []< = []<
SW zero b (sb ∷ C) p (hd< (lv< q)) with <sucT [] q
... | inj₁ ()
... | inj₂ refl = hd< (lv< ([]<plug C))
SW zero b (sb ∷ C) p (hd< (ar< ()))
SW zero b (sb ∷ C) p (tl< ())
SW (suc a) b (sb ∷ C) p η< = hd< (lv< (1<plug C))"""+s[b:]
s=s.replace("""... | sing² = hd< (lv< (subst ((Ω₁ ∷ η) <ᵀ_) (plugKS Kr S (Ωt (Ω₁ ∷ η)))
                        (swapΩ² (Kr ++ rv S) (subst ((Ω₁ ∷ Ω₁ ∷ []) <ᵀ_) (sym (plugKS Kr S (Ωt (Ω₁ ∷ Ω₁ ∷ [])))) q) η<)))
""","""... | sing² n = subst (λ z → z <ᵀ plug (sb ∷ Kr) (plugR S z)) (sym (fsT-sing n η))
                 (hd< (lv< (subst (Ωᵐ (suc n) η <ᵀ_) (plugKS Kr S (Ωt (Ωᵐ (suc n) η)))
                    (SW (suc n) n (Kr ++ rv S) (subst (Ωᵐ (suc (suc n)) [] <ᵀ_) (sym (plugKS Kr S (Ωt (Ωᵐ (suc (suc n)) [])))) q) η<))))
""")
s=s.replace("... | sing² = hd< (lv< (tl< η<))\n","""... | sing² n = subst (λ z → z <ᵀ plug (nd (Ω₁ ∷ Ω₁ ∷ Ωᵐ n []) ∷ Kr) (plugR S z)) (sym (fsT-sing n η)) (hd< (lv< (tl< (Ωᵐ-η n η<))))
""")
s=s.replace("... | sing²  = hd< (lv< (tl< p))\n","... | sing² n = subst₂ _<ᵀ_ (sym (fsT-sing n η)) (sym (fsT-sing n η′)) (hd< (lv< (tl< (Ωᵐ-mono n p))))\n")
s=s.replace("... | sing² = ⊥-elim (noV′ v)\n","... | sing² n = ⊥-elim (noV′ v)\n")
s=s.replace("... | sing² = sz0< hz S\n","... | sing² n = subst (λ z → ζ <ᵀ plugR S z) (sym (fsT-sing n _)) (sz0< hz S)\n")
a=s.index("singG² : ∀ u S {η}")
s2=s[a:]
end=s2.index("\n\n")
s=s[:a]+"""visΩᵐ : ∀ {u ζ′ η x xs} n S → (∀ {ζ} → Vis₁ u ζ η → ζ <ᵀ plugR S (x ∷ xs)) → Vis₁ u ζ′ (Ωᵐ n η) → ζ′ <ᵀ plugR S (x ∷ xs)
visΩᵐ zero S Hη v = Hη v
visΩᵐ (suc n) S Hη (vh h) = []<plugR S
visΩᵐ (suc n) S Hη (vd h ())
visΩᵐ (suc n) S Hη (vs h (vh h′)) = []<plugR S
visΩᵐ (suc n) S Hη (vs h (vd h′ ()))
visΩᵐ (suc n) S Hη (vs h (vs h′ ()))
visΩᵐ (suc n) S Hη (vs h (vt ()))
visΩᵐ (suc n) S Hη (vt v) = visΩᵐ n S Hη v

singG² : ∀ n u S {η} → (∀ {ζ} → Vis₁ u ζ η → ζ <ᵀ plugR S (ψᵗ (Ω₁ ∷ Ωᵐ n η) [] ∷ [])) →
         ∀ {ζ′} → Vis₁ u ζ′ (ψᵗ (Ω₁ ∷ Ωᵐ n η) [] ∷ []) → ζ′ <ᵀ plugR S (ψᵗ (Ω₁ ∷ Ωᵐ n η) [] ∷ [])
singG² n u S Hη (vh h)   = []<plugR S
singG² n u S Hη (vd h ())
singG² n u S Hη (vs h v) = visΩᵐ (suc n) S Hη v
singG² n u S Hη (vt ())"""+s2[end:]
s=s.replace("... | sing²  = singG² u S Hη v\n","... | sing² n = subst (λ z → ζ′ <ᵀ plugR S z) (sym (fsT-sing n η)) (singG² n u S (λ v′ → subst (λ z → _ <ᵀ plugR S z) (fsT-sing n η) (Hη v′)) (subst (Vis₁ u ζ′) (fsT-sing n η) v))\n")
s=s.replace("... | sing²  = n∷ (nψ (n∷ (nψ nf1′ (sC (c∷ c[])) n[] bnd[]) nη (hdΩ (ctblΩ nη η<))) (sΩ (ctblΩ nη η<)) n[] bnd[]) n[] tt\n","... | sing² n = subst NF₁ (sym (fsT-sing n η)) (n∷ (nψ (NFΩᵐ (suc n) nη (ctblΩ nη η<)) (SbΩᵐ n (ctblΩ nη η<)) n[] bnd[]) n[] tt)\n")
s=s.replace("""hdΩ : ∀ {θ} → Ctbl θ → Hd≤ θ Ω₁
hdΩ c[] = tt
hdΩ (c∷ ct) = inj₁ refl
""","""hdΩ : ∀ {θ} → Ctbl θ → Hd≤ θ Ω₁
hdΩ c[] = tt
hdΩ (c∷ ct) = inj₁ refl

nfΩ₁ : NFᴾ₁ Ω₁
nfΩ₁ = nψ nf1′ (sC (c∷ c[])) n[] bnd[]

hdΩᵐ : ∀ n {θ} → Ctbl θ → Hd≤ (Ωᵐ n θ) Ω₁
hdΩᵐ zero c = hdΩ c
hdΩᵐ (suc n) c = inj₂ refl

NFΩᵐ : ∀ n {θ} → NF₁ θ → Ctbl θ → NF₁ (Ωᵐ n θ)
NFΩᵐ zero nθ c = nθ
NFΩᵐ (suc n) nθ c = n∷ nfΩ₁ (NFΩᵐ n nθ c) (hdΩᵐ n c)

SbΩᵐ : ∀ n {θ} → Ctbl θ → Sb (Ω₁ ∷ Ωᵐ n θ)
SbΩᵐ zero c = sΩ c
SbΩᵐ (suc n) c = sΩ² n c
""")
s=s.replace("""SW : ∀ a b C {η}""","""Ωᵐ-η : ∀ n {η} → η <ᵀ Ωᵗ → Ωᵐ n η <ᵀ Ω₁ ∷ Ωᵐ n []
Ωᵐ-η zero q = q
Ωᵐ-η (suc n) q = tl< (Ωᵐ-η n q)

Ωᵐ-mono : ∀ n {η η′} → η <ᵀ η′ → Ωᵐ n η <ᵀ Ωᵐ n η′
Ωᵐ-mono zero p = p
Ωᵐ-mono (suc n) p = tl< (Ωᵐ-mono n p)

SW : ∀ a b C {η}""")
open(p,'w').write(s)

p=OUT+P+'SystemOmega.lagda.md'; s=open(p).read()
s=s.replace("Sb-suc (sΩ² c) = sΩ² (Ctbl-suc c)\n","Sb-suc (sΩ² n c) = subst Sb (sym (suc-Ωᵐ (suc (suc n)) _)) (sΩ² n (Ctbl-suc c))\n")
s=s.replace("Sb-suc : ","suc-Ωᵐ : ∀ n c → sucT (Ωᵐ n c) ≡ Ωᵐ n (sucT c)\nsuc-Ωᵐ zero c = refl\nsuc-Ωᵐ (suc n) c = cong (Ω₁ ∷_) (suc-Ωᵐ n c)\n\nSb-suc : ",1)
s=s.replace("leafSb su sing²    = sC (c∷ c[])\n","leafSb su (sing² n) = sC (c∷ c[])\n")
open(p,'w').write(s)
