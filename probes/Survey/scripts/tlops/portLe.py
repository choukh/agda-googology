from common import *
s=rd('NoCumLe'); s=common(s)
s=s.replace('''# 不累加的世界: 第一位置

> 不含记号. 结论写在 [NoCum](NoCum.lagda.md). `⊴`, `add⊴`: 与 [CumUpLe](CumUpLe.lagda.md) 同形.''','''# 树的算子语言 (四): 第一位置

> 不含记号. 入口 [TLOps](TLOps.lagda.md). 由 [NoCumLe](NoCumLe.lagda.md) 改写. 新增 `Ωh⊴`: 高度单调, $p\\triangleleft p'$ 则 $\\dot\\Omega_{p,0}\\trianglelefteq\\dot\\Omega_{p',0}$. 这是回灌作高度 (`T⊤` 的类比) 的唯一前提, 不分情况读规则.''')
s=s.replace('''z⊴ : ∀ {p₀ a₀ u₀ p a u}''','''-- 高度单调
Ωh⊴ : ∀ {p p′} → p ⊲ p′ → Ω̇ p azero ⊴ Ω̇ p′ azero
Ωh⊴ {p} C.self = rf (Ω≈ p z≈)
Ωh⊴ {p} {asuc p′} (C.suc P) = fc (rL {j = zero} (ni (λ q g → eR {stp = es} (rw (Ωh⊴ P)))))
Ωh⊴ {p} {alim f} (C.lim n P) = l n (rL {j = self n} (Ωh⊴ P))

z⊴ : ∀ {p₀ a₀ u₀ p a u}''')
s=dup_paths(s)
wr('TLOpsLe',s)
