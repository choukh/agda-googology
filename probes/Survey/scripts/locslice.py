# -*- coding: utf-8 -*-
# 四层行数表 EBO 列的统计: 定义级切片, 按到达的块计 agda 非空非注释行, 排除 BTBO 层与记号模块.
# 用法: agda --html --html-highlight=all --html-dir=<H> 编译 UniformNF5Accept, Uniform5Top, Uniform5Label, Uniform4Label, 再 python3 locslice.py <H>.
import re,os,sys,io,collections
R=os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)),'..','..','..')); H=sys.argv[1]
def src(mod):
    for base in ('probes','src'):
        for ext in ('.lagda.md','.agda'):
            p=os.path.join(R,base,*mod.split('.'))+ext
            if os.path.exists(p): return p
    return None
ANY=re.compile(r'<a id="(\d+)" href="([^"#]*)(?:#(\d+))?" class="([^"]*)">')
class F: pass
files={}
def chunk(mod):
    if mod in files: return files[mod]
    p=src(mod)
    if p is None: files[mod]=None; return None
    f=F(); f.mod=mod; f.text=io.open(p,encoding='utf-8').read()
    f.starts=[]; f.ids=[]; f.names=[]   # chunk start offsets (0-based), id per line span
    f.line_chunk=[]; chunks=[]
    lit=p.endswith('.md'); incode=not lit
    off=0; stack=[]  # (hdr_indent, body_indent, hdr_chunk, names)
    root={}; cur=None; last=None; pend_hdr=None
    def new(name):
        chunks.append({'name':name,'hdrs':[s[2] for s in stack if s[2] is not None],'text':[]})
        return len(chunks)-1
    rootc=new('<root>'); 
    for line in f.text.split('\n'):
        ln=len(line)+1; c=cur
        st=line.strip()
        if lit and st.startswith('```'):
            incode= st.startswith('```agda'); cur=None; last=None if incode else last
            f.line_chunk.append((off,off+ln,None)); off+=ln; continue
        if not incode or not st or st.startswith('--') :
            f.line_chunk.append((off,off+ln,cur if incode else None)); off+=ln; continue
        i=len(line)-len(line.lstrip(' '))
        while stack and i<=stack[-1][0]: stack.pop()
        scope=stack[-1] if stack else None
        names=scope[3] if scope else root
        body=scope[1] if scope else 0
        if scope and scope[1] is None: scope[1]=i; body=i
        if pend_hdr is not None:
            c=pend_hdr
            if st.endswith('where'):
                stack.append([pend_hdr_i,None,pend_hdr,{}]); pend_hdr=None
            chunks[c]['text'].append(line); f.line_chunk.append((off,off+ln,c)); off+=ln; cur=c; continue
        if i>body:
            c=cur if cur is not None else rootc
        else:
            t=st.split()[0]
            if t in ('open','import','infix','infixl','infixr','variable','{-#'):
                c=new('<open>'); 
                _tk=st.split()
                _app=(t=='open' and _tk[1]!='import' and len(_tk)>2 and _tk[2] not in ('using','hiding','renaming','public'))
                if _app:
                    if scope and scope[2] is not None: chunks[scope[2]].setdefault('opens',[]).append(c)
                    else: chunks[rootc].setdefault('opens',[]).append(c)
            elif t=='module':
                nm=st.split()[1]; c=new('module '+nm); names[nm]=c
                if st.endswith('where'): stack.append([i,None,c,{}])
                elif ' = ' not in st: pend_hdr=c; pend_hdr_i=i
            elif t in ('mutual','private','abstract','instance','interleaved'):
                c=new('<'+t+'>'); stack.append([i,None,c,{}])
            elif t in ('data','record','pattern'):
                nm=st.split()[1]
                c=names.get(nm)
                if c is None: c=new(nm); names[nm]=c
            else:
                toks=st.split(); colon=None
                for k,tk in enumerate(toks):
                    if tk==':': colon=k;break
                    if tk=='=': break
                if t in names and t!='_': c=names[t]
                elif colon is not None:
                    c=new(t)
                    for tk in toks[:colon]: names[tk]=c
                elif last is not None: c=last
                else: c=new(t); names[t]=c
            if t not in ('open','import','infix','infixl','infixr','variable','{-#','mutual','private','abstract','instance','interleaved'): last=c
        chunks[c]['text'].append(line); f.line_chunk.append((off,off+ln,c)); off+=ln; cur=c
    f.chunks=chunks; f.rootc=rootc
    import bisect
    f.bis=[a for a,b,c in f.line_chunk]
    # edges
    hp=os.path.join(H,mod+'.html'); edges=collections.defaultdict(set)
    if os.path.exists(hp):
        h=io.open(hp,encoding='utf-8').read()
        for m in ANY.finditer(h):
            a,hf,fr,cl=m.groups()
            if cl in('Bound','Comment','Keyword','Symbol','Number','String') or fr is None or not hf: continue
            s=f.at(int(a)-1) if False else at(f,int(a)-1)
            if s is None: continue
            edges[s].add((hf[:-5],int(fr)-1))
    f.edges=edges
    files[mod]=f
    return f
import bisect
def at(f,o):
    k=bisect.bisect_right(f.bis,o)-1
    return f.line_chunk[k][2] if k>=0 else None
def succ(node):
    mod,c=node; f=chunk(mod); out=[]
    ch=f.chunks[c]
    for h in ch['hdrs']: out.append((mod,h))
    out.append((mod,f.rootc))
    for o in ch.get('opens',[]): out.append((mod,o))
    for (tm,to) in f.edges.get(c,()):
        g=chunk(tm)
        if g is None: continue
        t=at(g,to)
        if t is not None: out.append((tm,t))
    return out
def find(mod,name):
    f=chunk(mod)
    return [(mod,i) for i,c in enumerate(f.chunks) if c['name']==name]
NOT={'OCF.Align.EBO','OCF.Align.Correspond','OCF.Align.StandardOmega','OCF.Align.SystemOmega','OCF.Align.Translate','OCF.Notation.EBO'}
PAT=re.compile(r'(?<![\w′])(Lab|LabL|Lab₀|LabS|NF₁|cmpᵀ|_<ᵀ_|fsn|γ′ᴱ|Idx|natT)(?![\w′ᴸ])')
def bfs(starts):
    par={s:None for s in starts}; q=collections.deque(starts)
    while q:
        n=q.popleft()
        for t in succ(n):
            if t not in par: par[t]=n; q.append(t)
    return par
def path(par,n):
    r=[]
    while n is not None:
        r.append(n[0].replace('OCF.Align.','')+':'+chunk(n[0]).chunks[n[1]]['name']); n=par[n]
    return ' <- '.join(r)

def rep(label,mod,name,show=False):
    st=find(mod,name)
    if not st:
        print(label,'start not found'); return None
    par=bfs(st); ct=collections.Counter(n[0] for n in par)
    bad=[n for n in par if n[0] in NOT]
    tb=[n for n in par if n[0] not in NOT and PAT.search('\n'.join(chunk(n[0]).chunks[n[1]]['text']))]
    print('==',label,'reached',len(par),'| notation-module chunks',len(bad),'| token hits elsewhere',len(tb))
    for n in bad[:4]: print('    ',path(par,n))
    for n in tb[:4]: print('    ',path(par,n))
    return par

def lines(n):
    t=chunk(n[0]).chunks[n[1]]['text']
    return sum(1 for l in t if l.strip() and not l.strip().startswith('--'))
def closure(roots):
    st=[]
    for m,n in roots:
        st+=find(m,n)
    return set(bfs(st))

B4='OCF.Align.Uniform4Base'; T2='OCF.Align.Uniform4Two'; NF='OCF.Align.NotFree'; M='OCF.Align.UniformNF5Main'
BASE={'OCF.BTBO','OCF.Align.Level','OCF.Align.NoCumsum','OCF.Align.Uniform','OCF.Align.Label','OCF.Align.Standard','OCF.Align.StandardOmega','OCF.Align.SystemOmega','OCF.Align.EBO','OCF.Align.Correspond','OCF.Align.Closure','OCF.Align.Bachmann','OCF.Align.Diagonal','OCF.Align.Finite','OCF.Align.Translate'}
def RT(ms):
    for m,n in ms:
        if not find(m,n): print('MISSING',m,n)
    return closure(ms)
L1=RT([(B4,'O'),(B4,'Fl')])
Gt=RT([(NF,'Goodᴺ')])
Gf=RT([(NF,'Goodᴺ'),(NF,'forceᴺ'),(NF,'forceᴺ-HS')])
L2=RT([(B4,'ψ̄'),(B4,'ψᵒ'),(B4,'Ω̇'),(B4,'ι'),(T2,'TΩ·2')])
L3=RT([(M,'GᴺΩ̇'),(M,'GoodTΩ·2'),(M,'GᴺT'),(M,'GoodT')])
def show(name,par,minus=()):
    ms=set()
    for p in minus: ms|=p
    q=[n for n in par if n not in ms and n[0] not in BASE]
    t=collections.Counter()
    for n in q: t[n[0].replace('OCF.Align.','')]+=lines(n)
    print(name,'TOTAL=',sum(t.values()),sorted(t.items(),key=lambda x:-x[1])[:9])
show('L1 type+cert',L1|Gt)
show('L2 cum',L1|L2|Gf)
show('L3 cum',L1|L2|Gf|L3)
f=chunk('OCF.Align.Uniform5Top'); print([c['name'] for c in f.chunks if 'label' in c['name']][:12])
f=chunk('OCF.Align.UniformNF5Accept'); print([c['name'] for c in f.chunks if 'label' in c['name'] or c['name'].startswith('module')][:12])
LB=[]
for m,n in [('OCF.Align.UniformNF5Accept','label-TΩ·2'),('OCF.Align.UniformNF5Accept','module ATΩ·2'),('OCF.Align.Uniform5Top','TΩ·2-label'),('OCF.Align.Uniform5Top','label-TΩ·2'),('OCF.Align.Uniform5Label','TΩ-label'),('OCF.Align.Uniform5Label','label-Ω̇'),('OCF.Align.Uniform4Label','TΩ-label'),('OCF.Align.Uniform4Label','TΩ+1-label'),('OCF.Align.Uniform4Label','TΩ·2-label')]:
    if find(m,n): LB.append((m,n)); print('root',m,n)
L4=closure(LB)
show('L4 new',L4,[L1,L2,Gf,L3])
show('L4 cum',L1|L2|Gf|L3|L4)
print('reached bad notation in L3:',sum(1 for n in (L1|L2|Gf|L3) if n[0] in NOT))

f=chunk(M); print('chunks with G in Main:',[c['name'] for c in f.chunks if 'G' in c['name']][:14]); print('Main in L3 lines:',sum(lines(n) for n in L3 if n[0]==M), 'of', sum(lines((M,i)) for i in range(len(f.chunks))))
