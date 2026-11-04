import re
AL='/Users/alsg/Agentic/agda-googology/probes/OCF/Align/'
def rd(n): return open(AL+n+'.lagda.md',encoding='utf8').read()
def wr(n,s): open(AL+n+'.lagda.md','w',encoding='utf8').write(s)
PATHFN=['outL','inL','out-inL','addL','ψL','ELl','ELr','EqW','Ll→','→Ll','Lr→','→Lr','W→','→W','≈owS','≈ow⁻S','≈oeS','≈oe⁻S','≈oLS','≈oL⁻S','addLl','addLr','ψLl','ψLr','z⊴L','addL⊴','mRL','mLL','tRL','tLL','WFL','L→W','W→L','aL','ψWL']
BASE=[('zero','rz'),('(self n₉)','(rself n₉)'),('zero','cz'),('(self n₉)','(cself n₉)')]
def repath(src):
    """TLOps 的路径四句 → 八句: zero/self→rz,rself,cz,cself; suc/lim→rs,rlim,cs,clim"""
    out=[]
    for line in src.split('\n'):
        m=re.match(r'^(\s*)(\S+)(.*)$',line)
        if not m or m.group(2) not in PATHFN or '=' not in m.group(3) or m.group(3).lstrip().startswith(':'):
            out.append(line);continue
        ind,name,rest=m.groups()
        lhs,rhs=rest.split('=',1)
        if re.search(r'(^| )\(self n₉\)( |$)',lhs):
            out.append(ind+name+re.sub(r'(^| )\(self n₉\)( |$)',r'\1(rself n₉)\2',lhs,count=1)+'='+rhs)
            out.append(ind+name+re.sub(r'(^| )\(self n₉\)( |$)',r'\1(cself n₉)\2',lhs,count=1)+'='+rhs)
        elif re.search(r'(^| )zero( |$)',lhs):
            out.append(ind+name+re.sub(r'(^| )zero( |$)',r'\1rz\2',lhs,count=1)+'='+rhs)
            out.append(ind+name+re.sub(r'(^| )zero( |$)',r'\1cz\2',lhs,count=1)+'='+rhs)
        elif re.search(r'\(lim n₉ (\S+)\)',lhs):
            out.append(ind+name+re.sub(r'\(lim n₉ (\S+)\)',r'(rlim n₉ \1)',lhs,count=1)+'='+rhs)
            out.append(ind+name+re.sub(r'\(lim n₉ (\S+)\)',r'(clim n₉ \1)',lhs,count=1)+'='+rhs)
        elif re.search(r'\(suc (j\S*|i)\)',lhs):
            out.append(ind+name+re.sub(r'\(suc (j\S*|i)\)',r'(rs \1)',lhs,count=1)+'='+rhs)
            out.append(ind+name+re.sub(r'\(suc (j\S*|i)\)',r'(cs \1)',lhs,count=1)+'='+rhs)
        else:
            out.append(line)
    return '\n'.join(out)
def mods(s):
    for f in ['W','Eq','Psi','Le','Main','Pre','Force','Clo','Sim']:
        s=re.sub(r'\bTLOps'+f+r'\b','TLOpsD'+f,s)
    return s
