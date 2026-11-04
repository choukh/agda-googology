# -*- coding: utf-8 -*-
# 把 LadderLab 的标签链搬到主线上: 生成 probes/OCF/Align/OrdLabZ* 与 OrdLab{Base,Class,Rel,Psi,Eval,Inst,NFOmega,NFTop,Forget,Top}.
# 证书不克隆: 标签类直接贴在主线的 OCF.Free.*, LadderInf*, LadderNFTree 上.
# 做法 (同 Survey/scripts/freeextract):
#   1. 从 LadderLab* 的全部块出发做定义级切片, 边界是主线 (OCF.Free.*, LadderInf*, LadderNFTree) 与 EBO.
#      克隆的证书 LadderLabZInfW*, LadderLabZNFW* 换成主线的同名模块, 不进切片.
#   2. 与主线逐字相同的块 (Level, Prefix, Floor, Tree, Aux) 丢掉, 从 OCF.Free.* 转出.
#   3. 不碰树的纯记号块 (到达不了 Level 和主线) 不复制, 从原模块转出. 这样 NF₁, Sb, Ctbl 与克隆世界是同一个类型.
#   4. 其余块代码行逐字, 只改导入.
# 用法 (仓库根目录):
#   agda --library-file=<libs> -i src -i probes --html --html-highlight=all --html-dir=<H> probes/OCF/Align/LadderLabAccept.lagda.md
#   ORDLAB_HTML=<H> python3 probes/Survey/scripts/ordlab/mk_rebase.py [输出目录]   # 默认写回 probes/OCF/Align/
import sys,re,os,io,collections,json
HERE=os.path.dirname(os.path.abspath(__file__))
R0=os.path.abspath(os.path.join(HERE,'..','..','..','..'))
OUT=(sys.argv[1].rstrip('/')+'/') if len(sys.argv)>1 else R0+'/probes/OCF/Align/'
H=os.environ['ORDLAB_HTML']
DS=R0+'/probes/Survey/scripts/depslice.py'
sys.argv=['depslice',H]
exec(open(DS,encoding='utf-8').read().replace('os.path.abspath(__file__)','"%s"'%DS))
A='OCF.Align.'
Z=A+'LadderLabZ'
LABM='Base Class Rel Psi Eval Inst NFOmega NFTop Forget Top'.split()
# ---- 模块对应 ----
SHIM={Z+'NFWForce':'OCF.Free.Force',Z+'NFWEq':'OCF.Free.Eq',Z+'NFWFloor':'OCF.Free.Floor',Z+'NFWAux':'OCF.Free.Aux',
      Z+'NFWFT':'OCF.Free.Tree',Z+'NFWPrefix':'OCF.Free.Prefix',Z+'NFWBase':'OCF.Free.Base',Z+'NFWTree':A+'LadderNFTree',Z+'Uniform4Two':'OCF.Free.Tree'}
def main_of(m):
    if m in SHIM: return SHIM[m]
    if m.startswith(Z+'InfW'): return A+'LadderInf'+m[len(Z+'InfW'):]
    return None
NEUTRAL={'OCF.BTBO','OCF.Barrier',A+'EBO',A+'LadderInfBase'}
def boundary(m):
    return m.startswith('OCF.Free') or m in NEUTRAL or main_of(m) is not None or m.startswith(A+'LadderInf') or m==A+'LadderNFTree'
def short(m):
    return m[len(Z):] if m.startswith(Z) else m[len(A):]
# 与主线重合的模块: 丢掉逐字相同的块, 转出 (同 freeextract 的 RE 表)
RE={'Level':[('Level',None)],'Prefix':[('Prefix',None)],'Uniform3Base':[('Floor',None)],'Uniform4Two':[('Tree',None)],
    'Symbolic':[('Aux','Fs Fst Mlev')],'UniformS':[('Aux','kd kd-≅ ≅ᴵ→⊑ᴵ ⊑ᴵ-≅ˡ ⊑ᴵ-≅ʳ tf'),('Prefix','_≅ᶻ_ zᶻ sᶻ lᶻ ĉᶻ ≅ᶻ-sym ≅ᶻ-trans 𝟎ˢ')],
    'OmegaExpBase':[('Aux','σ⊥')],'Stage2Label':[('Aux','one⁰ two⁰')],'Uniform4Base':[('Tree','Fl asl asr swp dupr2')]}
SP={'<root>','<open>','<mutual>','<private>','<abstract>','<instance>','<interleaved>'}
def hdr(nm): return nm.startswith('module ') or nm in SP
def norm(ls): return tuple(l.rstrip() for l in ls if l.strip() and not l.strip().startswith('--'))
fidx={}
def free_blocks(x):
    if x in fidx: return fidx[x]
    f=chunk('OCF.Free.'+x); s=set()
    for c in f.chunks:
        if not hdr(c['name']): s.add(norm(c['text']))
    fidx[x]=s; return s
def matches_free(m,c):
    s=short(m)
    if s not in RE: return False
    t=norm(chunk(m).chunks[c]['text'])
    return any(t in free_blocks(x) for x,_ in RE[s])
# ---- 切片 ----
roots=[(A+'LadderLab'+m,i) for m in LABM for i in range(len(chunk(A+'LadderLab'+m).chunks))]
par={r:None for r in roots}; q=collections.deque(roots); drop=collections.defaultdict(set); bedge=collections.defaultdict(set); rev=collections.defaultdict(set)
def run_q():
    while q:
        n=q.popleft()
        for t in succ(n):
            tm,tc=t
            if boundary(tm):
                if tm not in NEUTRAL: bedge[n].add(tm)
                continue
            rev[t].add(n)
            if t in par: continue
            par[t]=n
            if not hdr(chunk(tm).chunks[tc]['name']) and matches_free(tm,tc):
                drop[tm].add(tc); continue
            q.append(t)
run_q()
# depslice 的盲点: `module D = Diagonal Uniform` 的引用 D.x 链到 Diagonal 内部, 看不见 D 这一块和它的实参 (同 freeextract 的 fix_alias)
while True:
    more=[]
    for (m,c) in list(par):
        f=chunk(m); txt='\n'.join(f.chunks[c]['text'])
        for i,ch in enumerate(f.chunks):
            if ch['name'].startswith('module ') and (m,i) not in par and ' = ' in (ch['text'][0] if ch['text'] else ''):
                nm=ch['name'].split()[1]
                if re.search(r'(?<![\w′])'+re.escape(nm)+r'\.',txt) or re.search(r'open\s+'+re.escape(nm)+r'\b',txt):
                    more.append(((m,i),(m,c)))
    if not more: break
    for x,src_ in more:
        if x not in par: par[x]=src_; q.append(x)
        rev[x].add(src_)
    run_q()
LM={A+'LadderLab'+m for m in LABM}
reached=collections.defaultdict(set)
for (m,c) in par:
    if c not in drop.get(m,()): reached[m].add(c)
# ---- 纯记号 ----
imp=set(); st=[]
def seed(n):
    if n not in imp: imp.add(n); st.append(n)
for n in par:
    m,c=n
    nm=chunk(m).chunks[c]['name']
    if m==A+'Level' or m in LM or n in bedge or c in drop.get(m,()):
        if not hdr(nm): seed(n)
while st:
    n=st.pop()
    for p in rev[n]: seed(p)
def is_pure(m,c):
    f=chunk(m); ch=f.chunks[c]
    if hdr(ch['name']) or ch['hdrs']: return False   # 嵌套块一律复制
    return (m,c) not in imp
def names_of(ch):
    out=[]; ls=ch['text']
    if not ls: return out
    st0=ls[0].strip(); t=st0.split()
    if t[0] in('data','record'):
        for l in ch['text']:
            s=l.strip().split()
            if not s: continue
            if s[0] in('data','record'): out.append(s[1]); continue
            if s[0]=='constructor': out.append(s[1]); continue
            if s[0]=='field':
                continue
            if ':' in s:
                k=s.index(':')
                if len(l)-len(l.lstrip())<=4 and k>0: out+=s[:k]
    elif t[0]=='pattern': out.append(t[1])
    else:
        k=t.index(':') if ':' in t else None
        out+= t[:k] if k else [ch['name']]
    return out
pure=collections.defaultdict(set); clone=collections.defaultdict(set)
for m in reached:
    if m in LM: continue
    for c in reached[m]:
        (pure if is_pure(m,c) else clone)[m].add(c)
def realc(m,cs): return {c for c in cs if not hdr(chunk(m).chunks[c]['name'])}
CL={m for m in reached if m not in LM and (realc(m,clone[m]) or drop.get(m))}
def tgt(mod):
    "导入目标; None 表示这一行去掉"
    if mod in NEUTRAL or mod.startswith('OCF.Free') or mod.startswith(A+'LadderInf') or mod==A+'LadderNFTree': return mod
    mm=main_of(mod)
    if mm: return mm
    if mod in LM: return A+'OrdLab'+mod[len(A+'LadderLab'):]
    if mod in CL: return A+'OrdLabZ'+short(mod)
    if mod in reached and realc(mod,pure[mod]): return mod
    return None
# ---- 输出选择 (同 freeextract.select) ----
def src_path(m):
    for base in ('probes','src'):
        for ext in ('.lagda.md','.agda'):
            p=os.path.join(R0,base,*m.split('.'))+ext
            if os.path.exists(p): return p
def select(m,keep):
    f=chunk(m); out=[]; imps=[]
    lit=src_path(m).endswith('.md')
    off=0; incode=not lit; lastimp=None
    live=set()
    for c in keep:
        nm=f.chunks[c]['name']
        if not hdr(nm):
            live.add(c); live.update(f.chunks[c]['hdrs'])
        elif nm.startswith('module ') and ' = ' in '\n'.join(f.chunks[c]['text']): live.add(c)
    for line in f.text.split('\n'):
        ln=len(line)+1; st0=line.strip(); k=at(f,off)
        if st0.startswith('```'):
            incode=st0.startswith('```agda')
            if incode: out.append(None)
            off+=ln; continue
        if not incode:
            if st0.startswith('## '): out.append('\x01'+st0)
            off+=ln; continue
        if st0.startswith('{-# OPTIONS') or re.match(r'module OCF\.',st0):
            off+=ln; continue
        if k is None:
            if st0=='': out.append('')
            off+=ln; continue
        c=f.chunks[k]; name=c['name']; hd=c['hdrs']
        if name=='<root>': ok=True
        elif name=='<open>': ok=all(h in live for h in hd)
        elif hdr(name): ok=k in live
        else: ok=k in keep
        if ok:
            if re.match(r'(open\s+)?import\b',st0): imps.append(st0); lastimp=k
            elif name=='<open>' and k==lastimp: imps[-1]+=' '+st0
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
            m_=re.match(r'\s*(\S+(?: \S+)*)\s*:',l)
            if m_: deftok.update(m_.group(1).split())
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
STDOPEN={'Ord-Ord','Trich','Nat-Lt','Restr','Restrˢ','RestrO','Top','E'}
# 导出表
body={}; exports={}; bmods=set()
for m in CL:
    keep=clone[m]
    b,i=select(m,keep); body[m]=(b,i)
    e=tokens([l for l in b if l is not None])
    for fm,names in RE.get(short(m),[]):
        e|= tokens(open_lines) if False else set()
    exports[A+'OrdLabZ'+short(m)]=e
    bmods|=modnames([l for l in b if l is not None])
def free_exports(x):
    f=chunk('OCF.Free.'+x); e=set()
    for c in f.chunks: e|=tokens(c['text'])
    return e
reexp={}
for m in CL:
    s=short(m); lines=[]
    for fm,names in RE.get(s,[]):
        if names is None:
            lines.append('open import OCF.Free.%s public'%fm)
            exports[A+'OrdLabZ'+s]|=free_exports(fm)
        else:
            lines.append('open import OCF.Free.%s public using (%s)'%(fm,'; '.join(names.split())))
            exports[A+'OrdLabZ'+s]|=set(names.split())
    ps=[]
    for c in sorted(realc(m,pure[m])):
        ps+=names_of(chunk(m).chunks[c])
    ps=sorted(set(ps))
    if ps:
        lines.append('open import %s public using (%s)'%(m,'; '.join(ps)))
        exports[A+'OrdLabZ'+s]|=set(ps)
    reexp[m]=lines
def rw(st0,me):
    m=re.match(r'(open\s+)?import\s+(\S+)(.*)$',st0,re.S)
    mod=m.group(2)
    if not mod.startswith('OCF.'): return st0
    t=tgt(mod)
    if t is None or t==me: return None
    rest=m.group(3)
    u=re.search(r'using\s*\((.*?)\)',rest,re.S)
    if u and t in exports:
        names=[x.strip() for x in u.group(1).split(';') if x.strip()]
        names=[x for x in names if x.split()[-1] in exports[t]]
        if not names and 'renaming' not in rest and 'hiding' not in rest: return None
        rest=rest[:u.start()]+'using ('+'; '.join(names)+')'+rest[u.end():]
    if 'hiding' in rest and t in exports:
        hh=re.search(r'hiding\s*\((.*?)\)',rest,re.S)
        names=[x.strip() for x in hh.group(1).split(';') if x.strip() and x.strip() in exports[t]]
        rest=rest[:hh.start()]+('hiding ('+'; '.join(names)+')' if names else '')+rest[hh.end():]
    rn=re.search(r'renaming\s*\((.*?)\)',rest,re.S)
    if rn and t in exports and 'public' not in rest:
        names=[x.strip() for x in rn.group(1).split(';') if x.strip() and x.split()[0].strip() in exports[t]]
        rest=rest[:rn.start()]+('renaming ('+'; '.join(names)+')' if names else '')+rest[rn.end():]
    return (m.group(1) or '')+'import '+t+rest
known=bmods|STDOPEN
PATCHZ={'Uniform3Rel':[('open import OCF.Align.OrdLabZUniform3Depth1 using (_≈₁_; GA1)\n','')],'Uniform3Depth2Fold':[('; GA1ʰ','')]}
wrote=[]
for m in sorted(CL):
    b,il=body[m]; s=short(m); me=A+'OrdLabZ'+s
    imports=[];seen=set();aliases=set()
    for l in il:
        r=rw(l,me)
        if r and r not in seen:
            seen.add(r); imports.append(r)
            a=re.search(r'\bas\s+(\S+)',r)
            if a: aliases.add(a.group(1))
    imports+=reexp[m]
    srcname=m[len(A):]
    t=render(me,'%s (主线上的切片)'%s,['**验收用, 不在证书的闭包内.** 由 `Survey/scripts/ordlab/mk_rebase.py` 从 [%s](%s.lagda.md) 切出: 只留 `LadderLab*` 标签链的定义级切片里碰到树的块, 代码行逐字, 导入改指主线 `OCF.Free.*`, 与主线重合的块和纯记号块转出. 讲解见原文件. 结论写在 [OrdLab](OrdLab.lagda.md).'%(srcname,srcname)],imports,[b],known|aliases)
    for a,bb in PATCHZ.get(s,[]):
        if a not in t: print('PATCH MISS',s,a[:60])
        t=t.replace(a,bb)
    io.open(OUT+'OrdLabZ%s.lagda.md'%s,'w',encoding='utf-8').write(t.rstrip('\n')+'\n')
    wrote.append(s)
# ---- 标签类: 全文保留, 只改导入与模块名 ----
for x in LABM:
    p=R0+'/probes/OCF/Align/LadderLab%s.lagda.md'%x
    t=open(p,encoding='utf-8').read()
    me=A+'OrdLab'+x
    def imp_sub(mt):
        st1=re.sub(r'\s*\n\s*',' ',mt.group(0))
        ind=''
        r=rw(st1,me)
        return r if r else ''
    t=re.sub(r'(?m)^(?:open )?import OCF\.[^\n]*(?:\n[ ]+[^\n]*)*',imp_sub,t)
    t=re.sub(r'(?m)^module OCF\.Align\.LadderLab'+x+r'\b','module '+me,t)
    t=re.sub(r'\[LadderLab\]\(LadderLab\.lagda\.md\)','[OrdLab](OrdLab.lagda.md)',t)
    note='> **机械改写, 验收用.** 由 [LadderLab%s](LadderLab%s.lagda.md) 经 `Survey/scripts/ordlab/mk_rebase.py` 生成: 只改模块名与导入, 克隆的证书 `LadderLabZInfW*` 换成主线 `LadderInf*`. 见 [OrdLab](OrdLab.lagda.md). 下面的文字是原文.\n\n'%(x,x)
    io.open(OUT+'OrdLab%s.lagda.md'%x,'w',encoding='utf-8').write(note+t)
# ---- 报告 ----
tot=0
print('clones:')
for s,m in sorted((short(m),m) for m in CL):
    n=sum(len(chunk(m).chunks[c]['text']) for c in realc(m,clone[m]))
    tot+=n
    print('  %-24s clone %5d lines, pure %3d chunks, dropped %3d'%(s,n,len(realc(m,pure[m])),len(drop.get(m,()))))
print('total clone lines',tot)
print('pure originals:',sorted(short(m) for m in reached if m not in LM and m not in CL and realc(m,pure[m])))
