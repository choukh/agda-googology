# -*- coding: utf-8 -*-
# 由定义级切片生成 probes/OCF/Free/{*,Lab/*}. 用法: 先对 OCF.Align.UniformNF5Accept 与 UniformNF5Main 跑 agda --html --html-highlight=all, 输出目录设为 $FREE_SCRATCH/html, 再运行本脚本. bfiles.json 写到 $FREE_SCRATCH.
import sys,re,os,io,collections,json
HERE=os.path.dirname(os.path.abspath(__file__))
R0=os.path.abspath(os.path.join(HERE,'..','..','..','..'))
S=os.environ['FREE_SCRATCH']
DS=R0+'/probes/Survey/scripts/depslice.py'
sys.argv=['depslice',S+'/html']
exec(open(DS,encoding='utf-8').read().replace('os.path.abspath(__file__)','"%s"'%DS))
A='OCF.Align.'
def all_chunks(m):
    f=chunk(m); return [(m,i) for i in range(len(f.chunks))]
def by_mod(par):
    r=collections.defaultdict(set)
    for n in par: r[n[0]].add(n[1])
    return r
EXTRA_FREE=['OCF.Align.Level:FGH','OCF.Align.Level:FGH-≅','OCF.Align.Level:iter-ext']
st=all_chunks(A+'UniformNF5Main')
for a in EXTRA_FREE:
    m,n=a.split(':',1); s_=find(m,n)
    if not s_: print('extra not found',a)
    st+=s_
RF=by_mod(bfs(st))
# depslice 的盲点: `module D = Diagonal Uniform` 的引用 D.x 链到 Diagonal 内部, 看不见 D 这一块和它的实参.
def fix_alias(starts):
    par=bfs(starts); added=[]
    while True:
        more=[]
        for (m,c) in list(par):
            f=chunk(m)
            txt='\n'.join(f.chunks[c]['text'])
            for i,ch in enumerate(f.chunks):
                if ch['name'].startswith('module ') and (m,i) not in par and ' = ' in (ch['text'][0] if ch['text'] else ''):
                    nm=ch['name'].split()[1]
                    if re.search(r'(?<![\w′])'+re.escape(nm)+r'\.',txt) or re.search(r'open\s+'+re.escape(nm)+r'\b',txt):
                        more.append((m,i))
        if not more: break
        for x in set(more): added.append(x)
        par=bfs(list(par)+list(set(more)))
    return par,added
_par,_added=fix_alias(all_chunks(A+'UniformNF5Accept'))
print('alias chunks added:',[(m[9:],chunk(m).chunks[c]['name']) for m,c in _added])
RA=by_mod(_par)
# Accept 需要而 Free 还没有的 NF5 块: 加根
need=[(m,c) for m in RA if m.startswith(A+'UniformNF5') and m!=A+'UniformNF5Accept' for c in RA[m]-RF[m]]
print('Accept-only NF5 chunks:',[(m[9:],chunk(m).chunks[c]['name']) for m,c in need if chunk(m).chunks[c]['name'] not in('<open>','<root>')])
RF=by_mod(bfs(st+need))

US_Z={'_≅ᶻ_','≅ᶻ-sym','≅ᶻ-trans','𝟎ˢ'}
FREE_PLAN=[
 ('Level',[(A+'Level',None)]),
 ('Aux',[(A+'Symbolic',None),(A+'UniformS',lambda n:n not in US_Z),(A+'OmegaExpBase',None),(A+'Stage2Label',None)]),
 ('Prefix',[(A+'Prefix',None),(A+'UniformS',lambda n:n in US_Z)]),
 ('Floor',[(A+'Uniform3Base',None)]),
 ('Eq',[(A+'UniformNF3Eq',None)]),
 ('Force',[(A+'NotFree',None),(A+'UniformNF3NBase',None)]),
 ('Tree',[(A+'Uniform4Base',None),(A+'Uniform4Two',None)]),
]+[(n,[(A+'UniformNF5'+n,None)]) for n in 'Base Rules Strict Class ClassF Good Tr Add Psi Eval Tail Omega Main'.split()]
FREE_MAP={A+'Level':'Level',A+'Symbolic':'Aux',A+'Stage2Label':'Aux',A+'OmegaExpBase':'Aux',A+'Prefix':'Prefix',
  A+'UniformS':'Eq',A+'Uniform3Base':'Floor',A+'UniformNF3Eq':'Eq',A+'NotFree':'Force',A+'UniformNF3NBase':'Force',A+'Uniform4Base':'Tree',A+'Uniform4Two':'Tree'}
for n in 'Base Rules Strict Class ClassF Good Tr Add Psi Eval Tail Omega Main'.split(): FREE_MAP[A+'UniformNF5'+n]=n
HEAD=json.load(open(HERE+'/heads.json',encoding='utf-8'))
PATCHF={}; PATCHB={}
exec(open(HERE+'/patch2.py',encoding='utf-8').read())
SP={'<root>','<open>','<mutual>','<private>','<abstract>','<instance>','<interleaved>'}
def hdr(nm): return nm.startswith('module ') or nm in SP
def src_path(m):
    for base in ('probes','src'):
        for ext in ('.lagda.md','.agda'):
            p=os.path.join(R0,base,*m.split('.'))+ext
            if os.path.exists(p): return p
def select(m,keep,sel=None):
    """(body lines, imports) of module m restricted to chunk set keep"""
    f=chunk(m); out=[]; imps=[]
    lit=src_path(m).endswith('.md')
    off=0; incode=not lit; lastimp=None
    # 头块只在有孩子时保留
    live=set()
    for c in keep:
        if (sel is None or sel(f.chunks[c]['name'])):
            nm=f.chunks[c]['name']
            if not hdr(nm):
                live.add(c)
                live.update(f.chunks[c]['hdrs'])
            elif nm.startswith('module ') and sel is None and ' = ' in '\n'.join(f.chunks[c]['text']): live.add(c)
    for line in f.text.split('\n'):
        ln=len(line)+1; st=line.strip(); k=at(f,off)
        if st.startswith('```'):
            incode=st.startswith('```agda')
            if incode: out.append(None)
            off+=ln; continue
        if not incode:
            if st.startswith('## '): out.append('\x01'+st)
            off+=ln; continue
        if st.startswith('{-# OPTIONS') or re.match(r'module OCF\.',st):
            off+=ln; continue
        if k is None:
            if st=='': out.append('')
            off+=ln; continue
        c=f.chunks[k]; name=c['name']; hd=c['hdrs']
        if name=='<root>': ok=True
        elif name=='<open>': ok=all(h in live for h in hd)
        elif hdr(name): ok=k in live
        else: ok=k in keep and (sel is None or sel(name))
        if ok:
            if re.match(r'(open\s+)?import\b',st): imps.append(st); lastimp=k
            elif name=='<open>' and k==lastimp: imps[-1]+=' '+st
            else: out.append(line)
        off+=ln
    return out,imps
TOK=re.compile(r'[\s(){};.]+')
def tokens(lines):
    t=set()
    for l in lines:
        if l and not l.startswith('\x01'): t.update(TOK.split(l))
    return t
def modnames(lines):
    t=set()
    for l in lines:
        if not l or l.startswith('\x01'): continue
        m=re.match(r'\s*(?:module|record)\s+(\S+)',l)
        if m: t.add(m.group(1))
    return t
def render(mod,title,quote,imports,bodies,known):
    txt=['# '+title,'']+[('> '+h).rstrip() for h in quote]
    txt+=['','```agda','{-# OPTIONS --safe --without-K --lossy-unification #-}','module %s where'%mod,'']+imports+['```','']
    for b in bodies:
        cur=[]
        def flush():
            c='\n'.join(cur).strip('\n')
            if c.strip(): txt.extend(['```agda',c,'```',''])
            cur.clear()
        for l in b:
            if l is None: flush(); continue
            if l.startswith('\x01'):
                flush(); txt.extend([l[1:],'']); continue
            cur.append(l)
        flush()
    t='\n'.join(txt)
    deftok=set()
    for l in t.split('\n'):
        if not re.match(r'\s*infix',l):
            m_=re.match(r'\s*(?:data\s+|record\s+)?(\S+)\s*:',l)
            if m_: deftok.add(m_.group(1))
            m_=re.match(r'\s*(?:data|record)\s+(\S+)',l)
            if m_: deftok.add(m_.group(1))
    t=re.sub(r'(?m)^(\s*infix[lr]? \d+)((?: \S+)+)$',lambda m:(lambda ops:(m.group(1)+' '+' '.join(ops)) if ops else '')([o for o in m.group(2).split() if o in deftok]),t)
    seen=set()
    def opf(m):
        if m.group(1) not in known: return ''
        k=m.group(0)
        if k in seen: return ''
        seen.add(k); return k
    t=re.sub(r'(?m)^open (?!import)(\S+)(.*)((?:\n  +\S.*)*)$',opf,t)
    seen2=set()
    def fxd(m):
        if m.group(0) in seen2: return ''
        seen2.add(m.group(0)); return m.group(0)
    t=re.sub(r'(?m)^infix[lr]? .*$',fxd,t)
    t=re.sub(r'(?m)^## [^\n]*\n\n(?=(## |\Z))','',t)
    t=re.sub(r'```agda\n+```\n*','',t)
    t=re.sub(r'(?m)^## [^\n]*\n\n(?=(## |\Z))','',t)
    t=re.sub(r'\n{3,}','\n\n',t)
    return t
PAT_=None
STDOPEN={'Ord-Ord','Trich','Nat-Lt','Restr','Restrˢ','RestrO','Top'}
# ---------- Free 世界 ----------
Fb={};Fexp={};Fmods={}
for new,srcs in FREE_PLAN:
    bl=[];il=[]
    for m,sel in srcs:
        b,i=select(m,RF.get(m,set()),sel); bl.append(b); il+=i
    Fb[new]=(bl,il); ls=[l for b in bl for l in b]
    Fexp[new]=tokens(ls); Fmods[new]=modnames(ls)
Fexp['Eq'].update('_≅ᶻ_ zᶻ sᶻ lᶻ ĉᶻ ≅ᶻ-sym ≅ᶻ-trans 𝟎ˢ kd kd-≅ ≅ᴵ→⊑ᴵ ⊑ᴵ-≅ˡ ⊑ᴵ-≅ʳ tf'.split())
allmods=set().union(*Fmods.values())
def rw(st,mapf,me,exports):
    m=re.match(r'(open\s+)?import\s+(\S+)(.*)$',st,re.S)
    mod=m.group(2)
    if not mod.startswith('OCF.'): return st
    if mod=='OCF.BTBO': return st
    tgt=mapf(mod)
    if tgt is None or tgt==me: return None
    rest=m.group(3)
    u=re.search(r'using\s*\((.*?)\)',rest,re.S)
    if u and tgt in exports:
        names=[x.strip() for x in u.group(1).split(';') if x.strip()]
        names=[x for x in names if x.split()[-1] in exports[tgt]]
        if not names and 'renaming' not in rest and 'hiding' not in rest: return None
        rest=rest[:u.start()]+'using ('+'; '.join(names)+')'+rest[u.end():]
    return (m.group(1) or '')+'import '+tgt+rest
FE={'OCF.Free.'+k:v for k,v in Fexp.items()}
outdir=R0+'/probes/OCF/Free'
os.makedirs(outdir,exist_ok=True); os.makedirs(outdir+'/Lab',exist_ok=True)
def fmap(mod):
    n=FREE_MAP.get(mod)
    return 'OCF.Free.'+n if n else None
for new,srcs in FREE_PLAN:
    bl,il=Fb[new]; h=HEAD[new]
    if 'imports' in h: imports=h['imports']
    else:
        seen=set(); imports=[]
        for l in il:
            r=rw(l,fmap,'OCF.Free.'+new,FE)
            if r and r not in seen: seen.add(r); imports.append(r)
    imports=imports+h.get('after',[])
    t=render('OCF.Free.'+new,h['title'],h['quote'],imports,bl,allmods|STDOPEN)
    for a,b in PATCHF.get(new,[]):
        if a not in t: print('PATCH MISS',new,a[:60])
        t=t.replace(a,b)
    io.open(outdir+'/%s.lagda.md'%new,'w',encoding='utf-8').write(t.rstrip('\n')+'\n')
# ---------- 标签世界 (验收用) ----------
RE={A+'Symbolic':[('Aux','Fs Fst Mlev')],
    A+'UniformS':[('Aux','kd kd-≅ ≅ᴵ→⊑ᴵ ⊑ᴵ-≅ˡ ⊑ᴵ-≅ʳ tf'),('Prefix','_≅ᶻ_ zᶻ sᶻ lᶻ ĉᶻ ≅ᶻ-sym ≅ᶻ-trans 𝟎ˢ')],
    A+'OmegaExpBase':[('Aux','σ⊥')],A+'Stage2Label':[('Aux','one⁰ two⁰')],
    A+'NotFree':[('Force','Goodᴺ gz gs gl gc forceᴺ forceᴺ-HS forceᴺ-≅ outsᴺ outsᴺ-HS outsᴺ-step outsᴺ-≅ ys-≅')],
    A+'UniformNF3NBase':[('Force','Goodᴺ-tr')],A+'Uniform4Base':[('Tree','Fl asl asr swp dupr dupr2')],
    A+'Level':[('Level',None)],A+'Prefix':[('Prefix',None)],A+'Uniform3Base':[('Floor',None)],A+'UniformNF3Eq':[('Eq',None)],A+'Uniform4Two':[('Tree',None)]}
for n in 'Base Rules Strict Class ClassF Good Tr Add Psi Eval Tail Omega Main'.split(): RE[A+'UniformNF5'+n]=[(n,None)]
Bb={};Bexp={}
bmods=set()
for m in RA:
    if not m.startswith(A) or m==A+'EBO': continue
    keep=RA[m]-RF.get(m,set())
    b,i=select(m,keep)
    Bb[m]=(b,i)
real=[l for l in (Bb[m][0] if m in Bb else []) for m in []]
def has_body(m):
    f=chunk(m)
    return any(not hdr(f.chunks[c]['name']) for c in RA[m]-RF.get(m,set()))
BFILE={m for m in Bb if has_body(m)}
print('label-side modules',len(BFILE))
def short(m): return 'OCF.Free.Lab.'+m[len(A):]
def bmap(mod):
    if mod==A+'EBO' : return mod
    if mod=='OCF.Barrier' or not mod.startswith(A):
        return mod if mod.startswith('OCF.Free') else None
    if mod in BFILE: return short(mod)
    if mod in RE and mod in Bb:
        # 只剩转出: 直接指向 Free
        r=RE[mod]
        if len(r)==1 : return 'OCF.Free.'+r[0][0]
    return None
for m in BFILE:
    ls=[l for l in Bb[m][0]]
    e=tokens(ls)
    for fm,names in RE.get(m,[]):
        e|= Fexp[fm] if names is None else set(names.split())
    Bexp[short(m)]=e; bmods|=modnames(ls)
BE=dict(FE); BE.update(Bexp)
known=allmods|bmods|STDOPEN
for m in BFILE:
    b,il=Bb[m]
    imports=[];seen=set()
    aliases=set()
    for l in il:
        r=rw(l,bmap,short(m),BE)
        if r and r not in seen:
            seen.add(r); imports.append(r)
            a=re.search(r'\bas\s+(\S+)',r)
            if a: aliases.add(a.group(1))
    for fm,names in RE.get(m,[]):
        if names is None: imports.append('open import OCF.Free.%s public'%fm)
        else: imports.append('open import OCF.Free.%s public using (%s)'%(fm,'; '.join(x for x in names.split() if x in Fexp[fm] or fm=='Eq')))
    t=render(short(m),m[len(A):]+' (验收副本)',['**验收用, 不在主线闭包内.** 脚本从 [%s](../../Align/%s.lagda.md) 切出: 只留 `UniformNF5Accept` 的定义级切片里、主线 `OCF.Free.*` 之外的块, 代码行逐字, 导入改指 `OCF.Free.*`. 讲解见原文件.'%(m[len(A):],m[len(A):])],imports,[b],known|aliases|{'E'})
    for a,bb in PATCHB.get(m[len(A):],[]):
        if a not in t: print('PATCH MISS',m,a[:60])
        t=t.replace(a,bb)
    io.open(outdir+'/Lab/%s.lagda.md'%m[len(A):],'w',encoding='utf-8').write(t.rstrip('\n')+'\n')
json.dump(sorted(m[len(A):] for m in BFILE),open(S+'/bfiles.json','w'))
print('BFILE',sorted(m[len(A):] for m in BFILE))
