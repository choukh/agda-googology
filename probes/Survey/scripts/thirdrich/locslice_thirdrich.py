# 中文：复用既有定义块/HTML依赖算法；不编译、不改数学源码。
# 用法 python3 本文件 HTML目录
import pathlib, collections
base = pathlib.Path(__file__).resolve().parents[1] / 'locslice.py'
__file__ = str(base)
exec(base.read_text().split("\nB4=")[0])
P = 'OCF.Lean.'
def roots(mod, names):
    out = [(P + mod, n) for n in names.split()]
    for m,n in out:
        if not find(m,n): raise RuntimeError('缺根 '+m+':'+n)
    return out
# 模块应用盲区：Complete(allS/allT)、At=Frames(Actual.D.world)与
# Actual.D=Defaults(bounds,bounds-legal)的参数作为显式根。
leg = roots('ThirdRichLeg', 'normalise normalise-legal tower-normalise tower-legal normalised-floor floor-legal')
leg += roots('ThirdRichLegBuild', 'allS allT leg legal-leg partial legal-partial')
world = roots('ThirdRichLeg', 'closed-world closed-world-legal default-world-extends')
world += roots('ThirdRichLegNegWorld', 'bounds bounds-legal world world-legal')
world += roots('ThirdRichWorldSections', 'advanced-world advanced-legal from-default initial floors')
world += roots('ThirdRichLegBuild', 'allS allT leg legal-leg partial legal-partial')
# 整族世界的公开构造/合法/扩张/准入；值covers不计在此组。
family = roots('ThirdRichWorldSections', 'world world-legal feedback feedback-legal next grow full full-legal full-grow admitted full-admitted from-default')
family += roots('ThirdRichLegBuild', 'allS allT leg legal-leg partial legal-partial')
value = roots('ThirdRichLeg', 'normalise-covers tower-covers floor-covers')
value += roots('ThirdRichWorldSections', 'covers floors-covered')
# value实例另补合法坐标族，实际证明由HTML递归到inflate等。
value += roots('ThirdRichLegValueRun', 'LegalS LegalT')

def report(label, rs, prior=set()):
    ns = closure(rs)
    counts = collections.Counter()
    for n in ns: counts[n[0]] += lines(n)
    extra = ns - prior
    print('\n'+label)
    print('总行数',sum(counts.values()),'定义块',len(ns),'新增于前组',sum(lines(n) for n in extra))
    print('逐模块',dict(sorted(counts.items())))
    print('记号块',sum(n[0] in NOT for n in ns))
    missing=[m for m in counts if not pathlib.Path(H,m+'.html').exists()]
    if missing: raise RuntimeError('缺HTML '+str(missing))
    print('第三方库不计（与既有locslice口径相同）；无仓库模块按名称排除。')
    if '--details' in sys.argv:
        for m,c in sorted(ns):
            print(m,chunk(m).chunks[c]['name'],lines((m,c)))
    return ns
normal_only = [r for r in leg if r[1] not in ('normalised-floor', 'floor-legal')]
N=report('A0 全族合法化+合法性（无floor实例）',normal_only)
L=report('A 全族合法化+原floor合法实例',leg,N)
W=report('B 实际closed-world+合法+rich指标界默认组件world扩张',world)
C=report('A∪B',leg+world,L)
family_nodes=report('A∪B∪整族世界/合法/扩张/准入',leg+world+family,C)
V=report('上述全部+值Cover',leg+world+family+value,family_nodes)

legal_sound = roots('ThirdRichLegValueLegal', 'zero-sound')
report('合法Cover含第零层标准值桥',leg+world+family+value+legal_sound,V)
raw_value = roots('ThirdRichLegValueRun', 'inflateS inflateT zero-inflate')
report('合法Cover与rawCover及标准值桥全部',leg+world+family+value+legal_sound+raw_value,V)
