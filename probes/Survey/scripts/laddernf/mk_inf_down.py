# 由 LadderMonoRel, LadderMonoDown 生成 LadderInfDn: 跨高度的关系, 从 Q m 到 Q m′, 对任意 d : m <ᴸ m′.
import re,os
R=os.environ.get('REPO') or os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)),'..','..','..','..'))
A=R+'/probes/OCF/Align/'
def code(p):
    t=open(p,encoding='utf-8').read()
    return re.findall(r'^```agda[ \t]*\n(.*?)^```',t,re.S|re.M)
rel=code(A+'LadderMonoRel.lagda.md')
dn=code(A+'LadderMonoDown.lagda.md')
head=rel[0]
head=head.replace('module OCF.Align.LadderMonoRel where','open import OCF.Align.LadderInfBase\nmodule OCF.Align.LadderInfDn (𝕊 : HtS) where')
head=re.sub(r'open import OCF\.Align\.LadderNF(\w+)',lambda m:'open import OCF.Align.LadderInf'+m.group(1)+' 𝕊',head)
head=head.replace('open RestrQ','open RestrQ\nopen import OCF.Free.Eq using (_≅ˢ_)')
body=rel[1]+rel[2]+rel[3] if len(rel)>3 else ''.join(rel[1:])
body=body.replace('module _ (m : ℕ) (a b : Ordᴵ) where','module _ {m m′ : Ht} (δ : m <ᴸ m′) (a b : Ordᴵ) where')
body=body.replace('Q (suc m) b','Q m′ b').replace('Vs (suc m) (suc q)','Vs m′ (tr< q δ)').replace('Sub (suc m)','Sub m′')
body=body.replace('(qcl (suc q) κ₂','(qcl (tr< q δ) κ₂').replace('(qΩ↓ (suc q) fe′','(qΩ↓ (tr< q δ) fe′')
body=body.replace('(h′ ξ′ ζ′ (intoV q z′))','(h′ ξ′ ζ′ (intoV (tr< q δ) z′))')
body=body.replace('Eh zero','Eh h₀').replace('Eh H (suc m)','Eh H m′').replace('Eh n (suc m)','Eh n m′')
body=body.replace('D-Ψ : ∀ {H m a b t','D-Ψ : ∀ {H m m′ a b t').replace('(qH : H <ᴸ m) (ok : Ok w)','(δ : m <ᴸ m′) (qH : H <ᴸ m) (ok : Ok w)')
body=body.replace('Dn m a b','Dn δ a b').replace('Ψ (suc qH)','Ψ (tr< qH δ)').replace('Ψ (suc q)','Ψ (tr< q δ)')
body=body.replace('chD : ∀ {m a b n','chD : ∀ {m m′ a b n').replace('(q : n <ᴸ m) (ok : Ok w)','(δ : m <ᴸ m′) (q : n <ᴸ m) (ok : Ok w)')
body=body.replace('(h′ ξ′ (Z* ρ) (intoV q z))','(h′ ξ′ (Z* ρ) (intoV (tr< q δ) z))')
body=body.replace('(e′ n (inj₁ refl) (suc q))','(e′ n (inj₁ refl) (tr< q δ))')
body=body.replace('(h′ ξ′ ζ′ (intoV q v))','(h′ ξ′ ζ′ (intoV (tr< q δ) v))').replace('(h′ ξ′ ζ′ (intoV q (tr⁻Q d₂ v)))','(h′ ξ′ ζ′ (intoV (tr< q δ) (tr⁻Q d₂ v)))')
body=body.replace('(e-lo ζ′ (inj₂ l) e′)','(e-lo ζ′ (inj₂ l) e′)')
body=re.sub(r'D-Ψ qH ','D-Ψ δ qH ',body)
body=re.sub(r'D-Ψ \{H\} qH ','D-Ψ {H} δ qH ',body)
body=re.sub(r'D-Ψ q ok','D-Ψ δ q ok',body)
body=re.sub(r'chD q ok','chD δ q ok',body)
body=re.sub(r'chD \{n = n\} q ok','chD {n = n} δ q ok',body)
body=body.replace('D-Ψ δ qH ok','D-Ψ δ qH ok')
body=body.replace('D-Ψ {H} {t = t} {t′} qH','D-Ψ {H} {t = t} {t′} δ qH')
body=body.replace('chD {χ = χ} {ρ = ρ} {ξ = ξ} {ξ′} q ok','chD {χ = χ} {ρ = ρ} {ξ = ξ} {ξ′} δ q ok')
body=body.replace('D→≈ᵠ : ∀ {m a b φ χ ψ ρ w w′} {x : Q m a φ χ} {x′ : Q m′ b ψ ρ} → Dn δ a b x x′','D→≈ᵠ : ∀ {m m′ a b φ χ ψ ρ w w′} {δ : m <ᴸ m′} {x : Q m a φ χ} {x′ : Q m′ b ψ ρ} → Dn δ a b x x′')
body=body.replace('(ok′ : Ok w′) (e′ : Eh h₀ (suc m) w′ ρ)','(ok′ : Ok w′) (e′ : Eh h₀ m′ w′ ρ)')
body=body.replace('R→≈ᵠ','R→≈ᵠ')
# 求值行
body=body.replace('(inj₁ refl) (suc q))','(inj₁ refl) (tr< q δ))')
body=body.replace('D→≈ᵠ {χ = χ} {ρ = ρ} {w = w} {w′ = w′} (dcl','D→≈ᵠ {χ = χ} {ρ = ρ} {w = w} {w′ = w′} {δ = δ} (dcl')
body=body.replace('D→≈ᵠ (dΩ↓','D→≈ᵠ {δ = δ} (dΩ↓')
body=body.replace('(s₂ (e′ n (Hi-0 n) (suc q)))','(s₂ (e′ n (Hi-0 n) (tr< q δ)))')
body=body.replace('(ac′ (e↓ e′ n (inj₁ refl) (suc q)))','(ac′ (e↓ e′ n (inj₁ refl) (tr< q δ)))')
body=body.replace('{n} {k = k} {k′} {q} {ac = ac} {ac′ = ac′} {h} {h′} ek s c f) with tri n H','{n} {k = k} {k′} {q} {ac = ac} {ac′ = ac′} {h} {h′} ek s c f) with tri n H')
body=re.sub(r' \{q′ = [^}]*\}','',body)
out='''# 高度抽象: 跨高度的关系 `Dn`

> **判决: HOLDS** (编译过, 无条件). 结论写在 [LadderInf](LadderInf.lagda.md). 由 `Survey/scripts/laddernf/mk_inf_down.py` 从 [LadderMonoRel](LadderMonoRel.lagda.md), [LadderMonoDown](LadderMonoDown.lagda.md) 改写, $m+1$ 换成任意 `δ : m <ᴸ m′`, 节点的 `suc q` 换成 `tr< q δ`.

```agda
'''+head+'''```

## §1 关系

```agda
'''+body
open(A+'LadderInfDn.lagda.md','w',encoding='utf-8').write(out+'```\n')
