import re,sys
import os; AL=os.path.join(os.path.dirname(os.path.abspath(__file__)),'..','..','..','OCF','Align')+'/'
def rd(n): return open(AL+n+'.lagda.md',encoding='utf8').read()
def wr(n,s): open(AL+n+'.lagda.md','w',encoding='utf8').write(s)
# functions whose path-argument is a height strict path: duplicate zero/(suc j) lines
PATHFN=['outL','inL','out-inL','addL','ψL','ELl','ELr','EqW','Ll→','→Ll','Lr→','→Lr','W→','→W','≈owS','≈ow⁻S','≈oeS','≈oe⁻S','≈oLS','≈oL⁻S','addLl','addLr','ψLl','ψLr','z⊴L','addL⊴','mRL','mLL','tRL','tLL','WFL','L→W','W→L','aL','ψWL']
def dup_paths(src):
    out=[]
    for line in src.split('\n'):
        out.append(line)
        m=re.match(r'^(\s*)(\S+)(.*)$',line)
        if not m: continue
        ind,name,rest=m.groups()
        if name not in PATHFN: continue
        if '=' not in rest or rest.lstrip().startswith(':'): continue
        lhs,rhs=rest.split('=',1)
        if re.search(r'(^| )zero( |$)',lhs):
            l2=re.sub(r'(^| )zero( |$)',r'\1(self n₉)\2',lhs,count=1)
            out.append(ind+name+l2+'='+rhs)
        elif re.search(r'\(suc (j\w*|i|j′)\)',lhs):
            l2=re.sub(r'\(suc (j\w*|i|j′)\)',r'(lim n₉ \1)',lhs,count=1)
            out.append(ind+name+l2+'='+rhs)
    return '\n'.join(out)
def common(s):
    s=s.replace('<ᴺ','◁').replace('<tr','◁-tr')
    s=s.replace("open Trich renaming (_<_ to _◁_; <-dec to ◁-dec) using (zero; suc)\n","")
    s=s.replace("open Trich renaming (_<_ to _◁_) using (zero; suc)\n","")
    s=s.replace('open import OCF.BTBO using (injᵃ; injᵇ; injᶜ; module Trich)\n','')
    s=s.replace('open import OCF.BTBO using (module Trich)\n','')
    for f in ['W','Eq','Psi','Le','Main','Pre','Force']:
        s=s.replace('NoCum'+f,'TLOps'+f)
    return s
