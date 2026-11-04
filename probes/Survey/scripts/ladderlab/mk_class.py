# -*- coding: utf-8 -*-
# 生成 LadderLabRel, LadderLabClass, LadderLabPsi, LadderLabEval:
#   Rel  从 LadderInfWRel (已对 HtS 抽象) 改: ≅ˢ 换成 ≅ᴬ, rwk 改回成对的构造子 (反演要), R-tl 取自 ScafLadderQRel.
#   Class, Psi, Eval 从 ScafLadderQClass, ScafLadderQPsi, ScafLadderQEval 改: 对 HtS 抽象, Ωᵉ (suc m) ν 换成 P m ν.
# 用法: python3 mk_class.py [输出目录]. 逐字节可重复.
import re,os,sys
HERE=os.path.dirname(os.path.abspath(__file__))
A=os.path.abspath(os.path.join(HERE,'..','..','..','OCF','Align'))+'/'
OUT=(sys.argv[1].rstrip('/')+'/') if len(sys.argv)>1 else A
def rd(m): return open(A+m+'.lagda.md',encoding='utf-8').read()
def wr(m,s): open(OUT+m+'.lagda.md','w',encoding='utf-8').write(s)
def sub1(s,a,b):
    assert s.count(a)==1,('sub1',a[:80],s.count(a))
    return s.replace(a,b)
def cut(s,a,b,new=''):
    i=s.index(a); j=s.index(b,i)
    return s[:i]+new+s[j:]
def zworld(s):
    s=re.sub(r'OCF\.Align\.ScafLadderZ(?=[A-Z])','OCF.Align.LadderLabZ',s)
    return s

HEAD='''> **机械改写, 验收用.** 由 `%s` 经 `Survey/scripts/ladderlab/mk_class.py` 生成: 对高度结构 `HtS` 抽象, 记号前缀换成 `PxS` 的 `P`; 见 [LadderLab](LadderLab.lagda.md). 下面的文字来自原文件.

'''
MOD='''{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderInfBase
open import OCF.Align.LadderLabBase
module OCF.Align.%s (𝕊 : HtS) (𝕏 : PxS 𝕊) where

open PxS 𝕏
'''

# ------------------------------------------------- Rel
def mk_rel():
    q=rd('ScafLadderQRel'); s=rd('LadderInfWRel')
    # 头: 取 QRel 的导入
    imp=zworld(q[q.index('open import Data.Nat'):q.index('```\n\n## §1 关系')])
    imp=imp.replace('open import OCF.Align.LadderLabZUniform3Base hiding (_⊕_; Ψ) renaming (FW to FW₀)','open import OCF.Align.LadderLabZUniform3Base hiding (_⊕_; Ψ; evη) renaming (FW to FW₀)')
    imp=imp.replace('using (Fl; asl; asr; swp; dupr; dupr2; _<ᴸ_; zero; suc; tr<)','using (Fl; asl; asr; swp; dupr; dupr2)')
    imp=imp.replace('open import OCF.Align.ScafLadderQ\n','open import OCF.Align.LadderLabZInfWTree 𝕊\n')
    imp=imp.replace('open import OCF.Align.ScafLadderQClass using (out-intoU)\n','')
    imp=imp.replace('open import OCF.Align.ScafLadderQPsi using (out-intoV)\n','')
    imp+='open import Relation.Binary.Definitions using (DecidableEquality)\nopen import Relation.Nullary using (yes; no)\nopen import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)\n'
    b=s[s.index('out-intoU : ∀'):]
    # rwk 成对
    b=sub1(b,"    rwkˡ : ∀ {φ φ′ χ χ′ ψ ρ} {le : ∀ {L} → Ev L φ′ → Ev L φ} {lc : Sub m χ′ χ} {x : Q m a φ χ} {x′ : Q m b ψ ρ} → R₊ x x′ → R₊ (qwk le lc x) x′\n    rwkʳ : ∀ {φ χ ψ ψ′ ρ ρ′} {le′ : ∀ {L} → Ev L ψ′ → Ev L ψ} {lc′ : Sub m ρ′ ρ} {x : Q m a φ χ} {x′ : Q m b ψ ρ} → R₊ x x′ → R₊ x (qwk le′ lc′ x′)\n",
           "    rwk : ∀ {φ φ′ χ χ′ ψ ψ′ ρ ρ′} {le : ∀ {L} → Ev L φ′ → Ev L φ} {lc : Sub m χ′ χ} {le′ : ∀ {L} → Ev L ψ′ → Ev L ψ} {lc′ : Sub m ρ′ ρ}\n          {x : Q m a φ χ} {x′ : Q m b ψ ρ} → R₊ x x′ → R₊ (qwk le lc x) (qwk le′ lc′ x′)\n")
    b=cut(b,"rwk : ∀ {m a b φ φ′ χ χ′ ψ ψ′ ρ ρ′}","Z∼ : ∀")
    # R-tl
    t=q[q.index('R-tl : ∀'):q.index('Fl∼ : ∀')]
    t=t.replace('Rq 0 c c′','Rq h₀ c c′').replace('(λ i ())','(λ i q₀ → ⊥-elim (no< q₀))')
    b=cut(b,"R-tl : ∀","Fl∼ : ∀",t)
    b=sub1(b,"""R-row _ I base = rclo (∼ᶠ-refl fz)
  (R-tlΩ (≅ᴵ-refl (suc zero)) (⊔∼ (∼ᶠ-refl fz) (fk∼ z≅)))
  (λ η η′ eη → R-tlΩ eη (⊔∼ (∼ᶠ-refl fz) (fk∼ eη)))
""","""R-row _ I base = rclo (∼ᶠ-refl fz)
  (R-tl (≅ᴵ-refl (suc zero)) (⊔∼ (∼ᶠ-refl fz) (fk∼ z≅)) (Ωˢ-≅ᴬ (≅ᴵ-refl (suc zero))))
  (λ η η′ eη → R-tl eη (⊔∼ (∼ᶠ-refl fz) (fk∼ eη)) (Ωˢ-≅ᴬ eη))
""")
    # 去掉 R→≈ᵠ (它读 ≈ᴿ; 这里要的是 Rd, 在 LadderLabEval)
    i=b.index('## §6 求值')
    b=b[:i].rstrip()+'\n'
    b=b.replace('x ≅ˢ y','x ≅ᴬ y')
    # rcl, rΩ↓ 两边的高度分开 (否则对 Rq x x 反演要 K), 假设写成 Hy
    b=sub1(b,"""record SameQ : Set where
  constructor same
""","""data SameQ {m n : Ht} (q : n <ᴸ m) : ∀ {n′} → n′ <ᴸ m → Set where
  same : SameQ q q

-- 高度不同的两棵树之间的假设: 只有高度相等时有内容. 反演 `Rq x x` 不必消去 n ≡ n
module _ {m : Ht} (Lv : ∀ {n} → n <ᴸ m → ∀ {k k′ ξ ζ ξ′ ζ′} → Q n k ξ ζ → Q n k′ ξ′ ζ′ → Set) where
  HyE : ∀ {n n′} → n <ᴸ m → n ≡ n′ → ∀ {k k′ ξ ζ ξ′ ζ′} → Q n k ξ ζ → Q n′ k′ ξ′ ζ′ → Set
  HyE q refl z z′ = Lv q z z′

  Hy : ∀ {n n′} → n <ᴸ m → ∀ {k k′ ξ ζ ξ′ ζ′} → Q n k ξ ζ → Q n′ k′ ξ′ ζ′ → Set
  Hy {n} {n′} q z z′ = Σ (n ≡ n′) λ e → HyE q e z z′

  mkH : ∀ {n} (q : n <ᴸ m) {k k′ ξ ζ ξ′ ζ′} {z : Q n k ξ ζ} {z′ : Q n k′ ξ′ ζ′} → Lv q z z′ → Hy q z z′
  mkH q l = refl , l

  -- Ht 有可判定相等 (由 tri, irr), 所以是集合
  _≟H_ : DecidableEquality Ht
  a ≟H b with tri a b
  ... | tlt r = no (λ { refl → irr r })
  ... | teq e = yes e
  ... | tgt r = no (λ { refl → irr r })

  unH : ∀ {n} (q : n <ᴸ m) {k k′ ξ ζ ξ′ ζ′} {z : Q n k ξ ζ} {z′ : Q n k′ ξ′ ζ′} → Hy q z z′ → Lv q z z′
  unH q {z = z} {z′ = z′} (e , l) = subst (λ e′ → HyE q e′ z z′) (Decidable⇒UIP.≡-irrelevant _≟H_ e refl) l
""")
    b=sub1(b,"""    rcl : ∀ {φ χ ψ ρ n κ₁ κ₂} {q : n <ᴸ m} {s : ∀ {ℓ} → Ev ℓ (χ n) → Ev ℓ (κ₁ ⊔ fk zero)} {s′ : ∀ {ℓ} → Ev ℓ (ρ n) → Ev ℓ (κ₂ ⊔ fk zero)}
         {t : Q m a φ χ} {t′ : Q m b ψ ρ} {g : (η : Ordᴵ) → Q m a φ (upd χ n (κ₁ ⊔ fk η))} {g′ : (η : Ordᴵ) → Q m b ψ (upd ρ n (κ₂ ⊔ fk η))} →
         SameQ → κ₁ ∼ᶠ κ₂ → R₊ t t′ → (∀ η η′ → η ≅ᴵ η′ → R₊ (g η) (g′ η′)) → R₊ (qcl q κ₁ s t g) (qcl q κ₂ s′ t′ g′)
""","""    rcl : ∀ {φ χ ψ ρ n n′ κ₁ κ₂} {q : n <ᴸ m} {q′ : n′ <ᴸ m} {s : ∀ {ℓ} → Ev ℓ (χ n) → Ev ℓ (κ₁ ⊔ fk zero)} {s′ : ∀ {ℓ} → Ev ℓ (ρ n′) → Ev ℓ (κ₂ ⊔ fk zero)}
         {t : Q m a φ χ} {t′ : Q m b ψ ρ} {g : (η : Ordᴵ) → Q m a φ (upd χ n (κ₁ ⊔ fk η))} {g′ : (η : Ordᴵ) → Q m b ψ (upd ρ n′ (κ₂ ⊔ fk η))} →
         SameQ q q′ → κ₁ ∼ᶠ κ₂ → R₊ t t′ → (∀ η η′ → η ≅ᴵ η′ → R₊ (g η) (g′ η′)) → R₊ (qcl q κ₁ s t g) (qcl q′ κ₂ s′ t′ g′)
""")
    b=sub1(b,"""    rΩ↓ : ∀ {φ χ ψ ρ n k k′} {q : n <ᴸ m} {fe : ∀ {L} → Ev L φ → Ev L Fl} {fe′ : ∀ {L} → Ev L ψ → Ev L Fl} {ac : ∀ {L} → Ev L (χ n) → k <ᴵ L} {ac′ : ∀ {L} → Ev L (ρ n) → k′ <ᴵ L}
          {h : ∀ ξ ζ → Vs m q k ξ ζ → Q m a (ξ ⊔ φ) (lo n ζ ∪ χ)} {h′ : ∀ ξ ζ → Vs m q k′ ξ ζ → Q m b (ξ ⊔ ψ) (lo n ζ ∪ ρ)} → SameQ → k ≅ᴵ k′ → φ ∼ᶠ ψ → Sim∼ m χ ρ →
          (∀ ξ ξ′ ζ ζ′ → ξ ∼ᶠ ξ′ → Sim∼ n ζ ζ′ → Sim∼ n ζ ζ′ → (z : Q n k ξ ζ) (z′ : Q n k′ ξ′ ζ′) → Lv q z z′ → R₊ (h ξ ζ (intoV q z)) (h′ ξ′ ζ′ (intoV q z′))) → R₊ (qΩ↓ q fe ac h) (qΩ↓ q fe′ ac′ h′)
""","""    rΩ↓ : ∀ {φ χ ψ ρ n n′ k k′} {q : n <ᴸ m} {q′ : n′ <ᴸ m} {fe : ∀ {L} → Ev L φ → Ev L Fl} {fe′ : ∀ {L} → Ev L ψ → Ev L Fl} {ac : ∀ {L} → Ev L (χ n) → k <ᴵ L} {ac′ : ∀ {L} → Ev L (ρ n′) → k′ <ᴵ L}
          {h : ∀ ξ ζ → Vs m q k ξ ζ → Q m a (ξ ⊔ φ) (lo n ζ ∪ χ)} {h′ : ∀ ξ ζ → Vs m q′ k′ ξ ζ → Q m b (ξ ⊔ ψ) (lo n′ ζ ∪ ρ)} → SameQ q q′ → k ≅ᴵ k′ → φ ∼ᶠ ψ → Sim∼ m χ ρ →
          (∀ ξ ξ′ ζ ζ′ → ξ ∼ᶠ ξ′ → Sim∼ n ζ ζ′ → Sim∼ n′ ζ ζ′ → (z : Q n k ξ ζ) (z′ : Q n′ k′ ξ′ ζ′) → Hy Lv q z z′ → R₊ (h ξ ζ (intoV q z)) (h′ ξ′ ζ′ (intoV q′ z′))) → R₊ (qΩ↓ q fe ac h) (qΩ↓ q′ fe′ ac′ h′)
""")
    b=sub1(b,"Z∼ : ∀ {m χ ρ}","""intoVH : ∀ {m n} (q : n <ᴸ m) {k k′ ξ ζ ξ′ ζ′} {z : Q n k ξ ζ} {z′ : Q n k′ ξ′ ζ′} → Rq n k k′ z z′ → Hy (LVq m) q z z′
intoVH q l = mkH _ q (intoVq q l)

Z∼ : ∀ {m χ ρ}""")
    b=b.replace("(intoVq q (outVq (tr< q dq) l))","(intoVH q (outVq (tr< q dq) (unH _ (tr< q dq) l)))")
    b=b.replace("(intoRq (<→◃ r) (outVq dq l))","(intoRq (<→◃ r) (outVq dq (unH _ dq l)))")
    b=b.replace("(intoVq q (outVq l lz))","(intoVH q (outVq l (unH _ l lz)))")
    b=b.replace("(intoVq q (R-tr⁻ˡ","(intoVH q (R-tr⁻ˡ")
    b=b.replace("(intoVq q (chRΨ","(intoVH q (chRΨ")
    b=b.replace("(z : Q n k ξ ζ) (z′ : Q n k′ ξ′ ζ′) → LVq m q z z′ → Rq m a b","(z : Q n k ξ ζ) (z′ : Q n k′ ξ′ ζ′) → Hy (LVq m) q z z′ → Rq m a b")
    # 成对的 rwk 子句
    lines=b.split('\n'); out=[]
    for l in lines:
        if re.match(r'^R-Ψ .*\(rwkˡ \{lc = lc\} r\)',l):
            out.append("R-Ψ qH ok e p ok′ e′ p′ et (rwk {lc = lc} {lc′ = lc′} r) = rwk (R-Ψ qH ok (λ i h r₁ → lc i r₁ (e i h r₁)) p ok′ (λ i h r₁ → lc′ i r₁ (e′ i h r₁)) p′ et r)")
            continue
        if re.match(r'^R-Ψ .*\(rwkʳ',l): continue
        if '(rwkʳ r) = rwkʳ' in l: continue
        if '(rwkˡ r) = rwkˡ' in l:
            l=l.replace('rwkˡ','rwk')
        out.append(l)
    b='\n'.join(out)
    return HEAD%'LadderInfWRel'+'# 高度抽象: 塔上的互模拟 (标签路线)\n\n```agda\n'+MOD%'LadderLabRel'+imp+'open RestrQ\n\n'+b

# ------------------------------------------------- 共用替换
def px(s):
    s=re.sub(r'Ωᵉ \(suc \(suc m\)\) \[\]','P (suc m) []',s)
    s=re.sub(r'Ωᵉ \(suc ([mnH])\) (\(w ∷ ws\)|\[\]|[ντθ])',r'P \1 \2',s)
    s=re.sub(r'ltμ \(Ωᵉ ([mnH]) τ\) (I0|I)\b',r'P-lt \1 τ \2',s)
    return s

def header(src,name,extra=''):
    s=rd(src)
    imp=zworld(s[s.index('open import Data.Nat'):s.index('```',s.index('open import Data.Nat'))])
    imp=imp.replace('open import OCF.Align.LadderLabZUniform3Base hiding (_⊕_; Ψ) renaming (FW to FW₀)','open import OCF.Align.LadderLabZUniform3Base hiding (_⊕_; Ψ; evη) renaming (FW to FW₀)')
    imp=imp.replace('using (Fl; asl; asr; swp; dupr; dupr2; _<ᴸ_; zero; suc; tr<)','using (Fl; asl; asr; swp; dupr; dupr2)')
    imp=imp.replace('open import OCF.Align.ScafLadderQ\n','open import OCF.Align.LadderLabZInfWTree 𝕊\n')
    imp=imp.replace('open import OCF.Align.ScafLadderQClass\n','open import OCF.Align.LadderLabClass 𝕊 𝕏\n')
    imp=imp.replace('open import OCF.Align.ScafLadderQPsi\n','open import OCF.Align.LadderLabPsi 𝕊 𝕏\n')
    imp=imp.replace('open import OCF.Align.ScafLadderQRel\n','open import OCF.Align.LadderLabRel 𝕊 𝕏\n')
    title=s[:s.index('```agda')]
    title=title[title.index('# '):]
    body=s[s.index('```',s.index('open import Data.Nat')):]
    return HEAD%src+title+'```agda\n'+MOD%name+imp+extra+body

# ------------------------------------------------- Class
def mk_class():
    s=header('ScafLadderQClass','LadderLabClass')
    s=s.replace('open import OCF.Align.LadderLabZStandardOmega using (Ωᵐ)\n','open import OCF.Align.LadderLabZStandardOmega using (n[])\n')
    # §0 记号
    s=cut(s,"## §0 记号: 列表","## §1 `Lq`","""## §0 记号: 叶子 $\\Omega_u$ 的共尾度与基本列

```agda
cofΩt-c1 : ∀ u → cof u ≡ c1 → cof (Ωt u) ≡ cΩ (pred u)
cofΩt-c1 (w ∷ ws) e = cong (E.cofψ0 (w ∷ ws)) e

cofΩt-ω : ∀ u → cof u ≡ cω → cof (Ωt u) ≡ cω
cofΩt-ω (w ∷ ws) e = cong (E.cofψ0 (w ∷ ws)) e

cofΩt-Ω : ∀ u → cof u ≡ cΩ [] → cof (Ωt u) ≡ cΩ []
cofΩt-Ω (w ∷ ws) e = cong (E.cofψ0 (w ∷ ws)) e

fsn-Ωt : ∀ u → cof u ≡ cω → ∀ n → fsn (Ωt u) n ≡ Ωt (fsn u n)
fsn-Ωt (w ∷ ws) e n = E.fsn0-eq w ws n e

fsT-Ωt1 : ∀ u → cof u ≡ c1 → ∀ θ → fsT (Ωt u) θ ≡ θ
fsT-Ωt1 (w ∷ ws) e θ = fsT-c1 (w ∷ ws) _ e θ

fsT0-cΩ : ∀ u c θ → c ≡ cΩ [] → E.fsT0 u c θ ≡ ψᵗ (fsT u θ) [] ∷ []
fsT0-cΩ u .(cΩ []) θ refl = refl

fsT-ΩtΩ : ∀ u → cof u ≡ cΩ [] → ∀ θ → fsT (Ωt u) θ ≡ Ωt (fsT u θ)
fsT-ΩtΩ (w ∷ ws) e θ = fsT0-cΩ (w ∷ ws) _ θ e
```

""")
    s=sub1(s,"module _ (m : ℕ) (c : Ordᴵ)","module _ (m : Ht) (c : Ordᴵ)")
    s=s.replace("cΩ (Ωᵉ (suc n) ν)","cΩ (P n ν)").replace("cΩ (Ωᵉ (suc m) ν)","cΩ (P m ν)")
    # Lq, LL, LV
    s=cut(s,"Lq : ∀ m c → Bool → Mode","outL : ∀","""XL : Ht → Set₁
XL n = Mode → ∀ {k ξ ζ} → Q n k ξ ζ → T → Set

LqV : ∀ m (v : ∀ {n} → n <ᴸ m → XL n) c → Bool → Mode → ∀ {φ χ} → Q m c φ χ → T → Set
LLV : ∀ m (v : ∀ {n} → n <ᴸ m → XL n) c {k} → k ◃ c → Mode → ∀ {ξ ζ} → Q m k ξ ζ → T → Set
LqV m v c b mo x u = Lq₊ m c (LLV m v c) v b mo x u
LLV m v (suc c)   zero      mo x u = LqV m v c true mo x u
LLV m v (suc c)   (suc r)   mo x u = LLV m v c r mo x u
LLV m v (lim f s) (self n)  mo x u = LqV m v (f n) true mo x u
LLV m v (lim f s) (lim n r) mo x u = LLV m v (f n) r mo x u

FLv : ∀ m → (∀ {n} → n <ᴸ m → XL n) → XL m
FLv m v mo {k} x u = LqV m v k true mo x u

LV : ∀ m {n} → n <ᴸ m → XL n
LV = Rec XL FLv

Lq : ∀ m c → Bool → Mode → ∀ {φ χ} → Q m c φ χ → T → Set
Lq m = LqV m (LV m)

LL : ∀ m c {k} → k ◃ c → Mode → ∀ {ξ ζ} → Q m k ξ ζ → T → Set
LL m = LLV m (LV m)

""")
    s=cut(s,"outLV : ∀","Lq-cv : ∀","""outLV : ∀ {m n} (q : n <ᴸ m) {mo k ξ ζ} {z : Q n k ξ ζ} {θ} → LV m q mo z θ → Lq n k true mo z θ
outLV {m} q {mo} {z = z} {θ} l = subst (λ X → X mo z θ) (Rec-β XL FLv m q) l

intoLV : ∀ {m n} (q : n <ᴸ m) {mo k ξ ζ} {z : Q n k ξ ζ} {θ} → Lq n k true mo z θ → LV m q mo z θ
intoLV {m} q {mo} {z = z} {θ} l = subst (λ X → X mo z θ) (sym (Rec-β XL FLv m q)) l

""")
    s=s.replace("FWχ-⊞ : ∀ {χ ρ x ps y ys} →","FWχ-⊞ : ∀ {χ ρ x ps y ys} →")
    # 嵌入 ι↓
    s=cut(s,"FlF : ∀","FC-lift : ∀","""FlC : ∀ {χ : Fv} {x u} n {m} → FlrLab x u → (∀ i → i <ᴸ n → FlrLab (χ i) u) → ∀ i → i <ᴸ m → FlrLab (cap χ n x i) u
FlC n F G i q with tri i n
... | tlt r = G i r
... | teq _ = F
... | tgt _ = λ ()

""")
    s=cut(s,"Lq-ι↓ : ∀","```\n\n## §2 尾巴","""Lq-ι↓ : ∀ {n m k b mo φ χ} (d : n <ᴸ m) {x : Q n k φ χ} {u} → Lq n k true mo x u → Lq m zero b mo (ι↓ {α = zero} d x) u
Lq-ι↓ d lz = lz
Lq-ι↓ {n = n} {χ = χ} d (ls cc F Fχ Fc l) = ls cc F (FlC {χ} n Fc Fχ) (FC-lift Fc) (Lq-ι↓ d l)
Lq-ι↓ d (ll cc h) = ll cc (λ n → Lq-ι↓ d (h n))
Lq-ι↓ d (li cc I e hP hI) = li cc I e (λ η x l s v → Lq-ι↓ d (hP η x l s v)) (λ η x i → Lq-ι↓ d (hI η x i))
Lq-ι↓ d (lĉ cc K h₀′ hk) = lĉ cc K (Lq-ι↓ d h₀′) (λ k → Lq-ι↓ d (hk k))
Lq-ι↓ d (lŝ cc I b o h₀′ hg) = lŝ cc I b o (Lq-ι↓ d h₀′) (λ θ Y hY lY nθ lt e → Lq-ι↓ d (hg θ Y hY lY nθ lt e))
Lq-ι↓ d (lclo F cc h₀′ hg) = lclo F cc (Lq-ι↓ d h₀′) (λ θ Y hY lY nθ lt → Lq-ι↓ d (hg θ Y hY lY nθ lt))
Lq-ι↓ d (lcl F cc I₀ z₀ o h₀′ hg) = lcl F cc I₀ z₀ o (Lq-ι↓ d h₀′) (λ θ Y hY lY nθ lt → lwk (Lq-ι↓ d (hg θ Y hY lY nθ lt)))
Lq-ι↓ d (lwk l) = lwk (Lq-ι↓ d l)
Lq-ι↓ {m = m} {b = b} d (lΩ↓ {ps = ps} {y} {ys} {q = q} {h = h} cc I e f) =
  lΩ↓ {q = tr< q d} cc I e (λ {mo′} v ξ ζ z θ l → lwk
    (subst (λ w → Lq m zero b mo′ (ι↓ d (h ξ ζ (intoV q w))) (ps ++ fsT (y ∷ ys) θ)) (sym (out-intoV (tr< q d) z))
       (Lq-ι↓ d (f v ξ ζ _ θ (intoLV q (outLV (tr< q d) l))))))
Lq-ι↓ {m = m} {b = b} d (lΩ {ps = ps} {y} {ys} {r = r} {h = h} cc I e f) =
  lΩ↓ {q = d} cc I e (λ {mo′} v ξ ζ z θ l → lwk
    (subst (λ w → Lq m zero b mo′ (ι↓ d (h ξ ζ (intoU (<→◃ r) w))) (ps ++ fsT (y ∷ ys) θ)) (sym (out-intoV d z))
       (Lq-ι↓ d (f v ξ ζ _ θ (intoL (<→◃ r) (outLV d l))))))
Lq-ι↓ {k = suc a} d (lob {r = zero} l x) = lwk (Lq-ι↓ d l)
Lq-ι↓ {k = lim f s} d (lob {r = self n} l x) = lwk (Lq-ι↓ d l)
""")
    # Tl
    s=s.replace("Lq 0 c false","Lq h₀ c false")
    s=s.replace("(λ i ()) tt","(λ i q₀ → ⊥-elim (no< q₀)) tt")
    s=s.replace("tlA {y = y ∷ ys} fp (lŝ₀ cc K h₀ hk) = lĉ {ps = []} cc K (tlA fp h₀) (λ k → tlA fp (hk k))","tlA {y = y ∷ ys} fp (lŝ₀ cc K h₀′ hk) = lĉ {ps = []} cc K (tlA fp h₀′) (λ k → tlA fp (hk k))")
    # §5 Ω̇
    s=cut(s,"Lq-up : ∀ {mo φ χ}","ZuK : ∀","""Lq-up : ∀ {mo φ χ} {x : Q h₀ zero φ χ} {u} → Lq h₀ zero false mo x u → Lq h₀ zero true mo x u
Lq-up lz = lz
Lq-up (ls cc F Fχ _ l) = ls cc F Fχ (λ ()) (Lq-up l)
Lq-up (ll cc h) = ll cc (λ n → Lq-up (h n))
Lq-up (li cc I e hP hI) = li cc I e (λ η x l s v → Lq-up (hP η x l s v)) (λ η x i → Lq-up (hI η x i))
Lq-up (lĉ cc K h₀′ hk) = lĉ cc K (Lq-up h₀′) (λ k → Lq-up (hk k))
Lq-up (lŝ cc I b o h₀′ hg) = lŝ cc I b o (Lq-up h₀′) (λ θ Y hY lY nθ lt e → Lq-up (hg θ Y hY lY nθ lt e))
Lq-up (lclo F cc h₀′ hg) = lclo F cc (Lq-up h₀′) (λ θ Y hY lY nθ lt → Lq-up (hg θ Y hY lY nθ lt))
Lq-up (lcl {q = q} F cc I₀ z₀ o h₀′ hg) = ⊥-elim (no< q)
Lq-up (lwk l) = lwk (Lq-up l)
Lq-up (lΩ↓ {q = q} cc I e f) = ⊥-elim (no< q)

""")
    s=cut(s,"tail-Ω : ∀ m τ","LqΩ̇ᴵ : ∀ m","""XLq : Ht → Set
XLq m = ∀ {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → ∀ {α} → α ≅ᴵ toLevel Y hY → ∀ mo → Lq m α true mo (Ω̇ m α) (Ωt (P m θ))

-- 第 0 行
rowLq : ∀ m (I : ∀ {n} → n <ᴸ m → XLq n) (v : View _<ᴸ_ h₀ m) → Row₀ 𝕊 P m v → ∀ mo → Lq m zero true mo (rowV m (ΩI m) v) (Ωt (P m []))
rowLq _ I base (rb e) mo =
  rq (cong Ωt (sym e)) (Lq-up (lclo {ps = []} {y = ΩΩ} {ys = []} (Fw-Ω̂ mo) refl
       (Tl.tlΩ one⁰ (hs hz) lab1 nf1 (≅ᴵ-refl _) {fz ⊔ fk zero} {proj₂} tt)
       (λ θ Y hY lY nθ lt → Tl.tlΩ Y hY lY nθ (≅ᴵ-refl _) {fz ⊔ fk (toLevel Y hY)} {λ e q → proj₂ e (suc q)} (ZuK mo (toLevel Y hY)))))
rowLq m I (clos {n = n} q) (rc .q cc fs) mo =
  subst (λ X → Lq m zero true mo (rowC q X) (Ωt (P m []))) (sym (ΩI≡ q))
  (lcl {ps = []} {y = ψᵗ (P m []) []} {ys = []} {q = q} Fw-cl (cofΩt-Ω (P m []) cc) I₁ᵖ z≼1
      (λ θ → subst (Occ _) (sym (fsTe θ)) (os (P-occ n θ)))
      (lwk (rq (sym (fsTe (natT 1))) (Lq-ι↓ q (I q one⁰ (hs hz) lab1 nf1 (s≅ z≅) mo))))
      (λ θ Y hY lY nθ lt → lwk (rq (sym (fsTe θ)) (Lq-ι↓ q (I q Y hY lY nθ (≅ᴵ-refl _) mo)))))
  where
  fsTe : ∀ θ → fsT (Ωt (P m [])) θ ≡ Ωt (P n θ)
  fsTe θ = trans (fsT-ΩtΩ (P m []) cc θ) (cong Ωt (fs θ))
rowLq m I (chain F qs₁) (rl .F .qs₁ cc f0 fs) mo =
  ll {ps = []} {y = ψᵗ (P m []) []} {ys = []} (cofΩt-ω (P m []) cc)
     (λ { zero → rq (sym (trans (fsn-Ωt (P m []) cc 0) (cong Ωt f0))) (𝟏-lab mo)
        ; (suc i) → rq (sym (trans (fsn-Ωt (P m []) cc (suc i)) (cong Ωt (fs i))))
             (subst (λ X → Lq m zero true mo (stepL (qs₁ i) X) (Ωt (P (F i) []))) (sym (ΩI≡ (qs₁ i)))
                (lwk (Lq-ι↓ (qs₁ i) (I (qs₁ i) Ord₊.zero hz (l0 refl z≅) n[] z≅ mo)))) })
  where
  𝟏-lab : ∀ mo → Lq m zero true mo (𝟏L {m}) (Ωt [])
  𝟏-lab mo = lwk (ls {ps = []} {y = 𝟏} {ys = []} refl (fl mo) (λ i q ()) (λ ()) lz)
    where
    fl : ∀ mo → FlU mo fz []
    fl hon ()
    fl (wkm c) ()

FLq : ∀ m → (∀ {n} → n <ᴸ m → XLq n) → XLq m
FLq m I {θ = []} Ord₊.zero hY l nθ z≅ mo = rowLq m I (view m) (P-row m) mo
FLq m I {θ = w ∷ ws} Ord₊.zero hY l nθ z≅ mo with Lab0[] l
... | ()
FLq m I (Ord₊.suc Y) hY (l0 cc ()) nθ (s≅ e) mo
FLq m I (Ord₊.suc Y) hY (lω cc () h) nθ (s≅ e) mo
FLq m I {θ = []} (Ord₊.suc Y) hY (l1 () (s≅ e′) l) nθ (s≅ e) mo
FLq m I {θ = w ∷ ws} (Ord₊.suc Y) hY (l1 c₁ (s≅ e′) l) nθ {suc j} (s≅ e) mo =
  lΩ {ps = []} {y = ψᵗ (P m (w ∷ ws)) []} {ys = []}
     (trans (cofΩt-c1 (P m (w ∷ ws)) (trans (P-cof m w ws) c₁)) (cong cΩ (P-pred m w ws)))
     (Y , hs⁻ hY , Lab-≅ e′ l , NF₁-pred nθ c₁) e
     (λ v ξ ζ z θ l′ → lwk (rq (sym (fsT-Ωt1 (P m (w ∷ ws)) (trans (P-cof m w ws) c₁) θ)) (lob l′ (Lq-ι zero l′))))
FLq m I (Ord₊.lim F′) hY (l0 c₁ ()) nθ (l≅ k) mo
FLq m I (Ord₊.lim F′) hY (l1 c₁ () l) nθ (l≅ k) mo
FLq m I {θ = []} (Ord₊.lim F′) hY (lω () (l≅ k′) h) nθ (l≅ k) mo
FLq m I {θ = w ∷ ws} (Ord₊.lim F′) hY (lω c₁ (l≅ k′) h) nθ {lim f s} (l≅ ee) mo =
  ll {ps = []} {y = ψᵗ (P m (w ∷ ws)) []} {ys = []} (cofΩt-ω (P m (w ∷ ws)) (trans (P-cof m w ws) c₁))
     (λ n → rq (sym (trans (fsn-Ωt (P m (w ∷ ws)) (trans (P-cof m w ws) c₁) n) (cong Ωt (P-fsn m w ws n))))
               (lob (FLq m I (F′ n) (hl₁ hY n) (Lab-≅ (k′ n) (h n)) (NF₁-fsn nθ c₁ n) (ee n) mo) (Lq-ι (self n) (FLq m I (F′ n) (hl₁ hY n) (Lab-≅ (k′ n) (h n)) (NF₁-fsn nθ c₁ n) (ee n) mo))))

LqΩ̇ : ∀ m → XLq m
LqΩ̇ m = FLq m (Rec XLq FLq m)

""")
    s=px(s)
    return s

# ------------------------------------------------- Psi
def mk_psi():
    s=header('ScafLadderQPsi','LadderLabPsi','''open import OCF.Align.LadderLabZUniform5Psi using (I₁)
''')
    s=s.replace("open RestrQ\n","open RestrQ\n\nprivate\n  I0′ : Idx []\n  I0′ = I0\n",1) if False else s
    s=cut(s,"cmp≡ : ∀ n ν τ","FC-Ω : ∀")
    s=sub1(s,"""FC-Ω : ∀ {t τ u} H (Iτ : Idx τ) → t ≅ᴵ lvI Iτ → FC true t (ψᵗ (Ωᵉ (suc H) τ) u ∷ [])
FC-Ω {suc t} H Iτ e ink = inj₂ (_ , Iτ , inj₁ (≺ᴵ-respʳ (via (≅ᴵ-refl t) zero) e) , oτ (tail-Ω H _))
FC-Ω {lim f s} H Iτ e inb = inj₂ (_ , Iτ , inj₂ e , oτ (tail-Ω H _))
""","""FC-Ω : ∀ {t τ u} H (Iτ : Idx τ) → t ≅ᴵ lvI Iτ → FC true t (ψᵗ (P H τ) u ∷ [])
FC-Ω {suc t} H Iτ e ink = inj₂ (_ , Iτ , inj₁ (≺ᴵ-respʳ (via (≅ᴵ-refl t) zero) e) , oτ (P-tail H _))
FC-Ω {lim f s} H Iτ e inb = inj₂ (_ , Iτ , inj₂ e , oτ (P-tail H _))

FlU→P : ∀ {m φ b W} → Occ (natT 1) (ψᵗ W b ∷ []) → FlU m φ b → FlM m (Fl ⊔ φ) (ψᵗ W b ∷ [])
FlU→P {m = hon} oc F (inl (inr ink)) = inj₁ z≅
FlU→P {m = hon} oc F (inr k) with F k
... | inj₁ e = inj₁ e
... | inj₂ (inj₁ e) = inj₂ (natT 1 , I₁ , inj₂ e , oc)
... | inj₂ (inj₂ (w , Iw , kw , o)) = inj₂ (w , Iw , kw , od o)
FlU→P {m = wkm c} oc F (inl (inr ink)) = inj₁ (inj₁ (inj₁ z≅))
FlU→P {m = wkm c} oc F (inr k) with F k
... | inj₁ e = inj₁ e
... | inj₂ (inj₁ e) = inj₂ (natT 1 , I₁ , inj₂ e , oc)
... | inj₂ (inj₂ (w , Iw , kw , o)) = inj₂ (w , Iw , kw , od o)

Fw-ψP : ∀ {m φ ps y ys W} → cmpᵀ (sucT []) W ≡ lt → cof (y ∷ ys) ≡ cΩ [] → Fw m (φ ⊔ fk zero) ps y ys →
        Fw m ((Fl ⊔ φ) ⊔ fk zero) [] (ψᵗ W (ps ++ (y ∷ ys))) []
Fw-ψP {m = hon} ℓ cc G (inr ink) = inj₁ z≅
Fw-ψP {m = hon} ℓ cc G (inl (inl (inr ink))) = inj₁ z≅
Fw-ψP {m = hon} {ps = ps} {y} {ys} {W} ℓ cc G (inl (inr k)) with G (inl k)
... | inj₁ e = inj₁ e
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , λ θ → subst (Occ w) (sym (HeadRules.penh W {ps} {y} {ys} cc (inj₁ ℓ) θ)) (od (o θ)))
Fw-ψP {m = wkm c} ℓ cc G (inr ink) = inj₁ (inj₁ (inj₁ z≅))
Fw-ψP {m = wkm c} ℓ cc G (inl (inl (inr ink))) = inj₁ (inj₁ (inj₁ z≅))
Fw-ψP {m = wkm c} {ps = ps} {y} {ys} {W} ℓ cc G (inl (inr k)) with G (inl k)
... | inj₁ e = inj₁ e
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , λ θ → subst (Occ w) (sym (HeadRules.penh W {ps} {y} {ys} cc (inj₁ ℓ) θ)) (od (o θ)))
""")
    s=cut(s,"out-intoV : ∀ {m n}","Lq-tr  : ∀")
    s=px(s)
    s=re.sub(r'FlU→μ \(Ωᵉ ([mH]) τ\) F',r'FlU→P (os (P-occ \1 τ)) F',s)
    s=re.sub(r'Fw-ψ \{m = hon\} \(Ωᵉ ([mH]) τ\) cc G',r'Fw-ψP {m = hon} (P-lt \1 τ I0) cc G',s)
    s=re.sub(r'Fw-ψ \(Ωᵉ ([mH]) τ\) cc G',r'Fw-ψP (P-lt \1 τ I0) cc G',s)
    s=re.sub(r'cmp≡ \(suc ([mH])\) ν τ',r'P-cmp≡ \1 ν τ',s)
    s=re.sub(r'\bcmp-lt τ\b','P-cmp-lt τ',s)
    s=re.sub(r'\bcmp-gt ν\b','P-cmp-gt ν',s)
    s=s.replace('tail-Ω H τ','P-tail H τ')
    # 不再有 Lq-ψ 的 h₀ 歧义: 模式变量 h₀ 改名
    s=re.sub(r'\bh₀\b','h₀′',s)
    assert 'Ωᵉ' not in s, [l for l in s.split('\n') if 'Ωᵉ' in l][:5]
    return s

# ------------------------------------------------- Eval
def mk_eval():
    s=header('ScafLadderQEval','LadderLabEval')
    s=s.replace("using (OkW; Cv-of; Fw→[]; module LimRow; inp₀)","using (OkW; Cv-of; Fw→[]; inp₀)")
    s=sub1(s,"## §1 互模拟求值\n","""## §0 极限行

`LimRow` 对 $W$ 一致: 只要共尾度 $\\Omega_{W+1}$ 的 $W$ 对可数项恒 `gt`.

```agda
module LimRowP {W : T} {ps : T} {y : PT} {ys : T} (cc : cof (y ∷ ys) ≡ cΩ W) (gtᵂ : ∀ {w} → Idx w → cmpᵀ (sucT W) w ≡ gt) where
  limμW : ∀ {c′ φ} {F : ℕ → Run φ} → (∀ n → LWʰ[ c′ ] (F n) (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) W n))) → LWʰ[ c′ ] (limA 0 F) (ps ++ (y ∷ ys))
  limμW {F = F} h {w = w} ev p Iw ei ki u =
    gl (trans (cofW w ps y ys) (trans (cong (E.cofA w) cc) (cong (E.cofψ₊ w W) (gtᵂ Iw))))
       (λ n → subst (LabL₊ _ Ll _) (sym (gtW w ps y ys W cc (gtᵂ Iw) n)) (proj₁ (h n ev p Iw ei ki u))) ,
    hl (NB-sum ps) (λ n → subst (Hn _) (sym (gtW w ps y ys W cc (gtᵂ Iw) n)) (proj₂ (h n ev p Iw ei ki u)))

  limμO : ∀ {φ} {F : ℕ → Run φ} → (∀ n → L0 (F n) (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) W n))) → L0 (limA 0 F) (ps ++ (y ∷ ys))
  limμO {F = F} h ev p nu =
    let cω′ = trans (cofW [] ps y ys) (trans (cong (E.cofA []) cc) (cong (E.cofψ₊ [] W) (gtᵂ I0))) in
    let Rn = λ n → h n ev p (subst NF₁ (gtW [] ps y ys W cc (gtᵂ I0) n) (NF₁-fsn nu cω′ n)) in
    limᴸ nu cω′ (λ n → proj₁ (Rn n)) (λ n → subst (Lab _) (sym (gtW [] ps y ys W cc (gtᵂ I0) n)) (proj₂ (Rn n)))
```

## §1 互模拟求值
""")
    s=re.sub(r'LimRow\.(limμ[WO]) \{ν = Ωᵉ ([nm]) ν\} \{ps\} \{y\} \{ys\} cc',r'LimRowP.\1 {W = P \2 ν} {ps} {y} {ys} cc (P-gt \2 ν)',s)
    s=re.sub(r'\bh₀\b','h₀′',s)
    s=s.replace('Eh zero ','Eh h₀ ')
    s=s.replace('(intoVq q (chRΨ','(intoVH q (chRΨ')
    assert 'Ωᵉ' not in s[s.index('```agda'):]
    return s

wr('LadderLabRel',mk_rel())
wr('LadderLabClass',mk_class())
wr('LadderLabPsi',mk_psi())
wr('LadderLabEval',mk_eval())

# ------------------------------------------------- NF (Ω 版): ScafLadderNF 加 sψ 的情形
def mk_nf():
    s=rd('ScafLadderNF')
    s=zworld(s)
    s=s.replace('module OCF.Align.ScafLadderNF where','module OCF.Align.LadderLabNFOmega where')
    s=sub1(s,"using (NF₁; NFᴾ₁; n[]; n∷; nψ; Sb; sC; sΩ; sΩ²; bnd[];","using (NF₁; NFᴾ₁; n[]; n∷; nψ; Sb; sC; sΩ; sΩ²; sψ; ψ¹; bnd[];")
    s=sub1(s,"inv-ψ : ∀ {u x ys U}","""no-ψ¹ : ∀ {e z} → (ψ¹ ∷ e) <ᵗ (Ω₁ ∷ z) → ⊥
no-ψ¹ (E.hd< (E.lv< q)) = <ᵀ-irrefl q
no-ψ¹ (E.hd< (E.ar< ()))

inv-ψ : ∀ {u x ys U}""")
    s=sub1(s,"  key n[] b l = E.[]<\n","""  key n[] b l = E.[]<
  key (n∷ {x = ψᵗ (_ ∷ _) x} (nψ nu (sψ k ce) na bx) nys hd) b l = ⊥-elim (no-ψ¹ (inv-ψ (arg< l)))
""")
    return HEAD%'ScafLadderNF'+s

wr('LadderLabNFOmega',mk_nf())

# ------------------------------------------------- 遗忘标签: LadderNFAccept §1
def mk_forget():
    s=rd('LadderNFAccept')
    i=s.index('## §1 遗忘标签'); j=s.index('## §2 标签贴在证书的计值上')
    b=s[i:j]
    hdr='''# 高度上的标签: 遗忘标签

> **机械复制.** 由 `LadderNFAccept` §1 经 `Survey/scripts/ladderlab/mk_class.py` 复制, 落在 `LadderLabZ*` 世界. 见 [LadderLab](LadderLab.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderLabForget where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Align.Level
open import OCF.Align.LadderLabZPrefix using (Z; ĉᴸ; toZ)
import OCF.Align.LadderLabZGoodLBase as GL
open GL using (Goodᴸ; forceᴸ; forceᴸ-HS; Ptᴸ; ptsᴸ; lvᴸ)
open import OCF.Align.LadderLabZNFWForce
open import OCF.Align.LadderLabZNFWEq using (_≅ᶻ_)
```

'''
    return hdr+b

wr('LadderLabForget',mk_forget())
