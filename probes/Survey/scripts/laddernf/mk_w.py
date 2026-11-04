# 由 LadderNF* 生成标签世界里的证书克隆 LadderNFW*: 只改导入, 代码行逐字.
import re,os,glob,collections
R=os.environ.get('REPO') or os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)),'..','..','..','..'))
A=R+'/probes/OCF/Align/'
F=R+'/probes/OCF/Free/'
MODS='Rel Cx Rules Rules2 Rules3 Strict Strict2 Strict3 Class ClassF Good Vis Read Iota Tr Add Psi PsiH Eval Tail Mono Root Omega Main'.split()
def code(p):
    t=open(p,encoding='utf-8').read()
    return '\n'.join(re.findall(r'^```agda[ \t]*\n(.*?)^```',t,re.S|re.M))
def tops(p):
    out=[]
    for l in code(p).split('\n'):
        m=re.match(r'^(?:data |record )([^\s(){}]+)',l) or re.match(r'^([^\s(){}]+)\s*(?::|where)\s',l+' ')
        if m and m.group(1) not in('open','import','module','infix','infixl','infixr','private','abstract','mutual','postulate','field','constructor'): out.append(m.group(1))
    return out
def cons(p):
    out=[]; ind=False
    for l in code(p).split('\n'):
        if re.match(r'^(data |record )',l): ind=True; continue
        if l and not l.startswith(' '): ind=False
        if ind:
            m=re.match(r'^  ([^\s(){}]+(?: [^\s(){}:]+)*)\s*:',l)
            if m:
                for x in m.group(1).split(): out.append(x)
            m=re.match(r'^  constructor (\S+)',l)
            if m: out.append(m.group(1))
    return out
order=['ScafLadderZUniform3Base','ScafLadderZUniformS','ScafLadderZUniform4Base','ScafLadderZUniform4Two','ScafLadderZPrefix','ScafLadderZNonTightBase','Symbolic','ScafLadderZOmegaExpBase','ScafLadderZUniform5Rel','ScafLadderZUniform5RelPsi','ScafLadderZUniform5Tail','Closure','Bachmann','Label','Correspond','Standard','Uniform','ScafLadderZGoodLBase','ScafLadderZDecoupleBase']
idx=collections.defaultdict(list)
for m in order:
    p=A+m+'.lagda.md'
    for n in tops(p)+cons(p):
        if m not in idx[n]: idx[n].append(m)
for n in ['Eq₊ˢ','z≅','s≅','l≅','lᵢ≅','upˡ','upʳ','ŝ≅','ĉ≅']: idx[n]=['ScafLadderZUniformS']
for n in ['Bd','Fc','FB','FM','ubd','evF','iF','Top','InF']: idx[n]=['ScafLadderZUniform3Base']
idx['one⁰']=['ScafLadderZDecouple']
for n in ['zᶻ','sᶻ','lᶻ','ĉᶻ','≅ᶻ-sym','≅ᶻ-trans','𝟎ˢ']: idx[n]=['ScafLadderZUniformS']
used=collections.defaultdict(set)
for m in ['Tree']+MODS:
    c=code(A+'LadderNF'+m+'.lagda.md')
    for mod,lst in re.findall(r'open import OCF\.Free\.(\w+)\s+using\s+\(([^)]*)\)',c,re.S):
        for n in lst.split(';'):
            n=n.strip()
            if n: used[mod].add(n)
for X in ['Floor','Aux','Tree']:
    for n in tops(F+X+'.lagda.md')+cons(F+X+'.lagda.md'):
        used[X].add(n)
    for lst in re.findall(r'public\s+using\s+\(([^)]*)\)',code(F+X+'.lagda.md'),re.S):
        for n in lst.split(';'):
            if n.strip(): used[X].add(n.strip())
shim={'Floor':'WFloor','Aux':'WAux','Tree':'WFT','Base':'WBase'}
hdr='{-# OPTIONS --safe --without-K --lossy-unification #-}\n'
for X,W in shim.items():
    by=collections.defaultdict(list); miss=[]
    for n in sorted(used[X]):
        if X=='Base': continue
        if n in idx: by[idx[n][0]].append(n)
        else: miss.append(n)
    if miss: print('MISSING',X,miss)
    s=f'# 标签世界的名字表 ({X})\n\n> 验收用. 把 `OCF.Free.{X}` 的名字指向标签阶梯世界的原定义. 见 [LadderNFAccept](LadderNFAccept.lagda.md).\n\n```agda\n'+hdr+f'module OCF.Align.LadderNF{W} where\n\n'
    for m,ns in by.items():
        s+=f'open import OCF.Align.{m} public using ({"; ".join(ns)})\n'
    if X=='Base':
        s+='''open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import OCF.Align.Level
open import OCF.Align.ScafLadderZUniform3Base using (∅ᴿ)
open import OCF.Align.LadderNFWEq using (_≈ᴿ_; Ωˢ-≅)

clash : ∀ {i j} → j ≺ᴵ i → (i ≺ᴵ j) ⊎ (i ≅ᴵ j) → ⊥
clash s (inj₁ t) = ≺ᴵ-irrefl (≺ᴵ-trans s t)
clash s (inj₂ c) = ≺ᴵ-irrefl (≺ᴵ-respʳ s c)

r∅ : ∅ᴿ ≈ᴿ ∅ᴿ
r∅ ev p ev′ p′ ei = Ωˢ-≅ ei
'''
    s+='```\n'
    open(A+f'LadderNF{W}.lagda.md','w',encoding='utf-8').write(s)
    print(W,{m:len(v) for m,v in by.items()})
def rewrite(s):
    s=s.replace('OCF.Free.Eq','OCF.Align.LadderNFWEq')
    s=re.sub(r'OCF\.Align\.LadderNF(?=Tree\b)','OCF.Align.LadderNFW',s)
    for m in sorted(MODS,key=len,reverse=True):
        s=re.sub(r'OCF\.Align\.LadderNF'+m+r'\b','OCF.Align.LadderNFW'+m,s)
    s=s.replace('OCF.Free.Level','OCF.Align.Level').replace('OCF.Free.Prefix','OCF.Align.LadderNFWPrefix')
    s=s.replace('OCF.Free.Force','OCF.Align.LadderNFWForce')
    for X,W in shim.items():
        s=s.replace('OCF.Free.'+X,'OCF.Align.LadderNF'+W)
    return s
for m in MODS:
    t=open(A+'LadderNF'+m+'.lagda.md',encoding='utf-8').read()
    t=rewrite(t)
    t='> **机械克隆, 验收用.** 由 `LadderNF'+m+'` 经脚本复制, 只改导入, 把证书搬到标签阶梯的世界. 见 [LadderNFAccept](LadderNFAccept.lagda.md).\n\n'+t
    open(A+'LadderNFW'+m+'.lagda.md','w',encoding='utf-8').write(t)
# 树
s='# 标签世界的树\n\n> 验收用. `ScafLadderQ` 就是 `LadderNFTree`, 只差 §0 与导入. 见 [LadderNFAccept](LadderNFAccept.lagda.md).\n\n```agda\n'+hdr+'''module OCF.Align.LadderNFWTree where

open import Data.Product using (proj₁; _,_)
open import OCF.Align.Level
open import OCF.Align.Symbolic using (Mlev)
open import OCF.Align.ScafLadderZUniform3Base using (Flr; _⊔_; fk; Ev; Top; Bd; Fc; FB; evF; liftEv)
open import OCF.Align.ScafLadderQ public
open import OCF.Align.ScafLadderZUniform4Base public using (_<ᴸ_; zero; suc; tr<)

evη : ∀ {i ℓ} (φ : Flr) (B : Top i ℓ (φ ⊔ fk zero)) η (e : Bd B ⊑ᴵ η) → Ev (Mlev (Fc B) (suc η) (FB B e)) (φ ⊔ fk η)
evη φ B η e = liftEv φ (λ q → lim 0 q) (proj₁ (evF B)) , (λ q → lim 1 q)
```
'''
open(A+'LadderNFWTree.lagda.md','w',encoding='utf-8').write(s)
# Prefix: 主线的 Prefix 还带 ≅ᶻ
open(A+'LadderNFWPrefix.lagda.md','w',encoding='utf-8').write('# 标签世界的名字表 (Prefix)\n\n> 验收用. 见 [LadderNFAccept](LadderNFAccept.lagda.md).\n\n```agda\n'+hdr+'module OCF.Align.LadderNFWPrefix where\n\nopen import OCF.Align.ScafLadderZPrefix public\nopen import OCF.Align.ScafLadderZUniformS public using (_≅ᶻ_; zᶻ; sᶻ; lᶻ; ĉᶻ; ≅ᶻ-sym; ≅ᶻ-trans; 𝟎ˢ)\n```\n')
# Eq: 主线的 ≅ˢ 多一个层号字段, 这里重新实例化, 不用标签世界的那份
t=open(F+'Eq.lagda.md',encoding='utf-8').read()
t=t.replace('module OCF.Free.Eq where','module OCF.Align.LadderNFWEq where')
t=t.replace('OCF.Free.Level','OCF.Align.Level').replace('OCF.Free.Prefix','OCF.Align.LadderNFWPrefix')
for X,W in shim.items():
    t=t.replace('OCF.Free.'+X,'OCF.Align.LadderNF'+W)
t='> **机械克隆, 验收用.** 由 `OCF.Free.Eq` 经脚本复制, 只改导入.\n\n'+t
open(A+'LadderNFWEq.lagda.md','w',encoding='utf-8').write(t)
# Force
t=open(F+'Force.lagda.md',encoding='utf-8').read()
t=t.replace('module OCF.Free.Force where','module OCF.Align.LadderNFWForce where')
t=t.replace('OCF.Free.Eq','OCF.Align.LadderNFWEq')
t=t.replace('OCF.Free.Level','OCF.Align.Level').replace('OCF.Free.Prefix','OCF.Align.LadderNFWPrefix')
for X,W in shim.items():
    t=t.replace('OCF.Free.'+X,'OCF.Align.LadderNF'+W)
t='> **机械克隆, 验收用.** 由 `OCF.Free.Force` 经脚本复制, 只改导入.\n\n'+t
open(A+'LadderNFWForce.lagda.md','w',encoding='utf-8').write(t)
print(re.findall(r'open import [^\n]*',code(A+'LadderNFWForce.lagda.md')))
