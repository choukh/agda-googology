from common import *
s=rd('NoCumPsi'); s=common(s)
s=s.replace('''# 不累加的世界: 折叠的同余

> 不含记号. 结论写在 [NoCum](NoCum.lagda.md). `ψQ`: 与 [CumUpPsi](CumUpPsi.lagda.md) 同形, 少了第 0 层的 `ψ₀`.''','''# 树的算子语言 (三): 折叠的同余

> 不含记号. 入口 [TLOps](TLOps.lagda.md). 由 [NoCumPsi](NoCumPsi.lagda.md) 改写. 两边的高度比较各走各的公共上界 (`H`, `H′`), 结果模 `◁` 相同: 错配由 `no◁◁`, `<irr` 排除, 这是这里唯一新增的东西. 目标高度 $q$, $q′$ 分开写, 只在需要的分支合一, 否则 `teq` 对 `teq` 要 K.''')
s=s.replace('open import OCF.Align.CumReadCF using (A; azero;','open import Relation.Binary.PropositionalEquality using (sym)\nopen import OCF.Align.CumReadCF using (A; azero;',1)
# signatures
for name in ['ψmQ','ψQ','ψ⁰lm','ψ⁰rm','ψ⁰l','ψ⁰r']:
    s=re.sub(r'^'+name+r' *: ∀ \{p a u p′ a′ u′ q t t′\}', name+r' : ∀ {p a u p′ a′ u′ q q′ t t′} (H : Hk p q) (H′ : Hk p′ q′) (Q : q ≡ q′)', s, flags=re.M)
s=s.replace('ψLl : ∀ {p h k u p′ a′ u′ q t t′}','ψLl : ∀ {p h k u p′ a′ u′ q q′ t t′} (H : Hk h q) (H′ : Hk p′ q′) (Q : q ≡ q′)')
s=s.replace('ψLr : ∀ {p a u p′ h k u′ q t t′}','ψLr : ∀ {p a u p′ h k u′ q q′ t t′} (H : Hk p q) (H′ : Hk h q′) (Q : q ≡ q′)')
# statements' ψ terms
s=re.sub(r'ψ(ᵐ|⁰|) q t x gu', lambda m:'ψ'+m.group(1)+' q t H x gu', s)
s=re.sub(r'ψ(ᵐ|⁰|) q t′ y gu′', lambda m:'ψ'+m.group(1)+' q′ t′ H′ y gu′', s)
s=s.replace('ψL q t j x gu m','ψL q t H j x gu m').replace('ψL q t′ j y gu′','ψL q′ t′ H′ j y gu′')
# ψmQ / ψ⁰rm with-rhs had q t x handled; heads
def head(name):
    global s
    s=re.sub(r'^'+name+r' ((?:\{[^}]*\} )*)', name+r' \1H H′ Q ', s, flags=re.M)
for name in ['ψ⁰Q','ψmQ','ψQ','ψ⁰lm','ψ⁰rm','ψ⁰l','ψ⁰r','ψLl','ψLr']:
    pass
# handle line by line
out=[]
for line in s.split('\n'):
    m=re.match(r'^(ψ⁰Q|ψmQ|ψQ|ψ⁰lm|ψ⁰rm|ψ⁰l|ψ⁰r|ψLl|ψLr) ((?:\{[^}]*\} )*)(.*)$',line)
    if m and not m.group(3).startswith(':'):
        line=m.group(1)+' '+m.group(2)+'H H′ Q '+m.group(3)
        # rhs
    out.append(line)
s='\n'.join(out)
# rhs calls (not at line head) of the lemma family
def rhs(l):
    # find positions after '=' or space
    l=re.sub(r'(?<=[ (])ψ⁰l (?=x y|X y)', 'ψ⁰l H H′ Q ', l)
    l=re.sub(r'(?<=[ (])ψ⁰r (?=x y|X y)', 'ψ⁰r H H′ Q ', l)
    l=re.sub(r'(?<=[ (])ψ⁰lm (?=x y)', 'ψ⁰lm H H′ Q ', l)
    l=re.sub(r'(?<=[ (])ψ⁰rm (?=x y)', 'ψ⁰rm H H′ Q ', l)
    l=re.sub(r'(?<=[ (])ψmQ (?=x y)', 'ψmQ H H′ Q ', l)
    l=re.sub(r'(?<=[ (])ψ⁰Q (?=x y)', 'ψ⁰Q H H′ Q ', l)
    l=re.sub(r'(?<=[ (])ψQ (?=x y|\(F n\)|\(f )', 'ψQ H H′ Q ', l)
    l=re.sub(r'= ψLl j x y', '= ψLl (hk◁ j H) H′ Q j x y', l)
    l=re.sub(r'= ψLr X j₂ y', '= ψLr H (hk◁ j₂ H′) Q X j₂ y', l)
    return l
lines=s.split('\n')
new=[]
for l in lines:
    if re.match(r'^(ψ⁰Q|ψmQ|ψQ|ψ⁰lm|ψ⁰rm|ψ⁰l|ψ⁰r|ψLl|ψLr) ',l) and ' = ' in l:
        lhs,r=l.split(' = ',1)
        new.append(lhs+' = '+rhs(' '+r)[1:] if not r.startswith('ψ') else lhs+' = '+rhs('= '+r)[2:])
        continue
    new.append(rhs(l))
s='\n'.join(new)
# path recursions in ψLl/ψLr keep H
s=s.replace('ψLl H H′ Q (suc j) x y gu gu′ m gm um tm km m′ gm′ um′ tm′ am′ is′ et e = ψLl j x y','ψLl H H′ Q (suc j) x y gu gu′ m gm um tm km m′ gm′ um′ tm′ am′ is′ et e = ψLl H H′ Q j x y')
s=s.replace('ψLr H H′ Q x (suc j) y gu gu′ m gm um tm am is m′ gm′ um′ tm′ km′ et e = ψLr x j y','ψLr H H′ Q x (suc j) y gu gu′ m gm um tm am is m′ gm′ um′ tm′ km′ et e = ψLr H H′ Q x j y')
s=s.replace('ψ⁰Q H H′ Q (oL j k e₁ x) y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψLl j x y','ψ⁰Q H H′ Q (oL j k e₁ x) y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψLl (hk◁ j H) H′ Q j x y')
s=re.sub(r'= ψLr X j₂ y','= ψLr H (hk◁ j₂ H′) Q X j₂ y',s)
# ψᵐ rhs in ψmQ etc
s=s.replace('ψ⁰ q t x gu m gm um tm am','ψ⁰ q t H x gu m gm um tm am').replace('ψ⁰ q t′ y gu′','ψ⁰ q′ t′ H′ y gu′')
# diag clauses
s=s.replace('ψ⁰Q {q = q} H H′ Q o0 o0 gu','ψ⁰Q {q = q} H H′ refl o0 o0 gu')
s=s.replace('ψ⁰Q H H′ Q (os x) (os y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et (_ , ea , eu , e) =','ψ⁰Q H H′ refl (os x) (os y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et (_ , ea , eu , e) =')
s=s.replace('(ψQ H H′ Q x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ et e) gm gm′ n','(ψQ H H′ refl x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ et e) gm gm′ n')
s=s.replace('ψ⁰Q H H′ Q (oc x f) (oc y f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et (_ , ea , eu , e , N) =\n  refl , et ,','ψ⁰Q H H′ Q (oc x f) (oc y f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et (_ , ea , eu , e , N) =\n  Q , et ,')
# oi and od blocks
a=s.index('ψ⁰Q {p} {a} {q = q} {t} {t′} H H′ Q (oi')
b=s.index('ψ⁰Q H H′ Q (oc x f) (oc y f′)')
blk=s[a:b]
def fix_blk(blk,kind):
    return blk
blk=blk.replace('with ◁-dec p q','with trH H | trH H′').replace('with ◁-dec h₀ q','with trH (hk◁ j H) | trH (hk◁ j′ H′)')
blk=blk.replace('ψ⁰Q {p} {a} {q = q} {t} {t′} H H′ Q (oi','ψ⁰Q {p} {a} {q = q} {t = t} {t′ = t′} H H′ Q (oi')
blk=blk.replace('ψ⁰Q {q = q} {t} {t′} H H′ Q (od','ψ⁰Q {q = q} {t = t} {t′ = t′} H H′ Q (od')
blk=blk.replace('... | injᵃ i = refl , refl , et ,','... | tlt i | tlt i′ = Q , refl , et ,')
blk=blk.replace('(W→ i i y y′ d)','(W→ i i′ y y′ d)')
blk=blk.replace('... | injᵇ _ = λ n →','... | tgt _ | tgt _ = λ n →')
blk=blk.replace('... | injᶜ refl with','... | teq | teq with')
blk=blk.replace('ψ p k (f um','ψ p k (hkR H) (f um').replace('ψ p k′ (f′ um′','ψ p k′ (hkR H′) (f′ um′')
blk=blk.replace('ψ h₀ k (f um','ψ h₀ k (hkD j H) (f um').replace('ψ h₀ k′ (f′ um′','ψ h₀ k′ (hkD j′ H′) (f′ um′')
blk=blk.replace('ψQ H H′ Q (f um','ψQ H H′ Q (f um')
# ch (suc n)
parts=blk.split('ψ⁰Q {q = q} {t = t} {t′ = t′} H H′ Q (od')
p0=parts[0].replace('ch (suc n) = ψQ H H′ Q ','ch (suc n) = ψQ (hkR H) (hkR H′) refl ')
p1=parts[1].replace('ch (suc n) = ψQ H H′ Q ','ch (suc n) = ψQ (hkD j H) (hkD j′ H′) refl ')
# keep branch in teq: first comp refl stays; heights now equal
bad_oi='''... | tlt i | tgt i′ = ⊥-elim (no◁◁ (subst (_ ◁_) Q i) i′)
... | tgt i | tlt i′ = ⊥-elim (no◁◁ i′ (subst (_◁ _) Q i))
... | tlt i | teq = ⊥-elim (<irr (subst (_ ◁_) Q i))
... | teq | tlt i′ = ⊥-elim (<irr (subst (_ ◁_) (sym Q) i′))
... | tgt i | teq = ⊥-elim (<irr (subst (_◁ _) Q i))
... | teq | tgt i′ = ⊥-elim (<irr (subst (_◁ _) (sym Q) i′))
'''
def addbad(p):
    idx=p.index('... | teq | teq with')
    return p[:idx]+bad_oi+p[idx:]
blk=addbad(p0)+'ψ⁰Q {q = q} {t = t} {t′ = t′} H H′ Q (od'+addbad(p1)
s=s[:a]+blk+s[b:]
s=s.replace('open import Relation.Binary.PropositionalEquality using (_≡_; refl)','open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)')
s=s.replace('(suc j) x y gu gu′ m gm um tm km m′ gm′ um′ tm′ am′ is′ et e = ψLl (hk◁ j H) H′ Q j x y','(suc j) x y gu gu′ m gm um tm km m′ gm′ um′ tm′ am′ is′ et e = ψLl H H′ Q j x y')
s=s.replace('ψ⁰Q : ∀ {p a u p′ a′ u′ q t t′}','ψ⁰Q : ∀ {p a u p′ a′ u′ q q′ t t′} (H : Hk p q) (H′ : Hk p′ q′) (Q : q ≡ q′)')
s=s.replace('{q = q} {t} {t′} H H′ Q x y','{q = q} {q′ = q′} {t = t} {t′ = t′} H H′ Q x y')
s=dup_paths(s)
wr('TLOpsPsi',s)
