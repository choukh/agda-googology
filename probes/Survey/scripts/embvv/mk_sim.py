#!/usr/bin/env python3
"""生成 EmbVVTree (LadderOrdTree 加去头开关) 与 EmbVVSim (CrossMSim 改成去头关系)."""
import re,os
root=os.path.join(os.path.dirname(os.path.abspath(__file__)),'..','..','..','OCF','Align')
rd=lambda n: open(os.path.join(root,n+'.lagda.md'),encoding='utf8').read()
def wr(n,s): open(os.path.join(root,n+'.lagda.md'),'w',encoding='utf8').write(s)

# ---------- 树 ----------
t=rd('LadderOrdTree')
i=t.index('```agda'); t=t[i:]
t=t.replace('module OCF.Align.LadderOrdTree (𝕊 : HtB) where','module OCF.Align.EmbVVTree (𝕊 : HtB) (dr : ∀ m → OCF.Align.EmbVVMode.HdM 𝕊 m) where')
t=t.replace('open import OCF.Align.LadderOrdBase\n','open import OCF.Align.LadderOrdBase\nimport OCF.Align.EmbVVMode\n',1)
t=t.replace('open HtB 𝕊 public\n','open HtB 𝕊 public\nopen OCF.Align.EmbVVMode 𝕊 public using (HdM; keep; drop; repl)\n',1)
t=t.replace('''-- 根层
rowB :''','''-- 第 0 项的三种处理
rowD : ∀ {m} (F : ℕ → Ht) → (qs₁ : ∀ i → F i <ᴸ m) → (∀ {n} → n <ᴸ m → XΩ n) → HdM m → ℕ → Q m zero Fl (κ Fl)
rowD F qs₁ I keep = rowL F qs₁ (λ i → I (qs₁ i))
rowD F qs₁ I drop = λ i → stepL (qs₁ i) (I (qs₁ i))
rowD F qs₁ I (repl n q) zero = stepL q (I q)
rowD F qs₁ I (repl n q) (suc i) = stepL (qs₁ i) (I (qs₁ i))

-- 根层
rowB :''')
t=t.replace('rowV m I (chain F qs₁) = ql (rowL F qs₁ (λ i → I (qs₁ i)))','rowV m I (chain F qs₁) = ql (rowD F qs₁ I (dr m))')
assert 'rowD F qs₁ I (dr m)' in t
wr('EmbVVTree','''# 去头的树 (参照树用)

> **机械改写.** 由 [LadderOrdTree](LadderOrdTree.lagda.md) 经 `Survey/scripts/embvv/mk_sim.py` 生成, 只加一个开关 `dr`: `dr m` 为真时高度 $m$ 的链行去掉第 0 项 (`rowD`). 这是树的克隆, 不是证书克隆; 这棵树没有 `Goodᴺ` 闭包定理. 入口 [EmbVV](EmbVV.lagda.md).

'''+t)

# ---------- 模拟 ----------
s=rd('CrossMSim')
i=s.index('```agda'); s=s[i:]
hdr_end=s.index('open NR using (flo-∼)')+len('open NR using (flo-∼)')
header='''```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.EmbVVMode
module OCF.Align.EmbVVSim (𝕊 : HtB) (dr : ∀ m → OCF.Align.EmbVVMode.HdM 𝕊 m) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (sym; trans; subst; subst₂; cong)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Free.Level hiding (z≅; s≅; l≅; lᵢ≅; upˡ; upʳ)
open import OCF.Free.Level using (s≅; l≅) renaming (z≅ to z≅ᴵ)
open import OCF.Free.Prefix using (Z; Ord₊ˢ; Ordˢ; Ωˢ; toZ)
open import OCF.Free.Aux using (tf)
open import OCF.Align.EmbVVEq
open import OCF.Free.Floor using (Flr; fz; fk; fb; _⊔_; Ev; Run; flo; cvFlo; toFlo; wk; limA; bound; evF)
open import OCF.Free.Tree using (Fl; asl; asr; swp; dupr2; <◃)
import OCF.Align.LadderOrdTree
import OCF.Align.LadderOrdRel
import OCF.Align.EmbVVTree
module N = OCF.Align.LadderOrdTree 𝕊
module NR = OCF.Align.LadderOrdRel 𝕊
module I = OCF.Align.EmbVVTree 𝕊 dr

e : N.Ht → N.Ht
e x = x

ε : ∀ {n m} → n N.<ᴸ m → n N.<ᴸ m
ε q = q

-- 地板与界在这个关系里不起作用: 证书两边各带. 用平凡关系占位, 下面的文本才与 CrossMSim 对得上
data _∼ᶠ_ (a b : Flr) : Set where
  tt∼ : a ∼ᶠ b

fz∼ : ∀ {a b} → a ∼ᶠ b
fz∼ = tt∼

⊔∼ : ∀ {a b c d} → a ∼ᶠ b → c ∼ᶠ d → (a ⊔ c) ∼ᶠ (b ⊔ d)
⊔∼ _ _ = tt∼

∼ᶠ-refl : ∀ a {b} → a ∼ᶠ b
∼ᶠ-refl a = tt∼

data _≈c_ (a b : Ordᴵ) : Set where
  tc : a ≈c b

out-intoUᴵ : ∀ {m c k} (r : k ◃ c) {ξ ζ} (z : I.Q m k ξ ζ) → I.outU r (I.intoU r z) ≡ z
out-intoUᴵ zero      z = refl
out-intoUᴵ (suc r)   z = out-intoUᴵ r z
out-intoUᴵ (self n)  z = refl
out-intoUᴵ (lim n r) z = out-intoUᴵ r z
'''
body=s[hdr_end:]
# 两边是同一个 tri: 对齐是平凡的
a=body.index('-- 两边的三歧对齐'); b=body.index('record Sm (m')
body=body[:a]+body[b:]
# 关系符号
for a,b in [('≅ˢ','≃ˢ'),('≅ᶻ','≃ᶻ'),('≈ᴿ','≈ᴴ'),('≅→Rˢ','≃→Rˢ'),('Ωˢ-≅','Ωˢ-≃'),('toZ-≅','toZ-≃'),('IR.out-intoU','out-intoUᴵ')]:
    body=body.replace(a,b)
# 地板: 去掉 fk∼, flo-∼, bound-≅
body=re.sub(r'\(fk∼ [^()]*\)','tt∼',body)
body=re.sub(r'\(fk∼ \(≅ᴵ-refl _\)\)','tt∼',body)
body=body.replace('(flo-∼ ek)','tt∼').replace('(flo-∼ le)','tt∼')
body=body.replace('(bound-≅ (⊔∼ s tt∼) _ p _ p′ et)','tc').replace('(bound-≅ (⊔∼ s tt∼) _ (N.zr ok n) _ (I.zr ok′ (e n)) z≅)','tc')
assert 'bound-≅ (⊔∼ s tt∼) _ (N.zr ok n)' not in body or True
# 数据类型里的 c₁ ≅ᴵ c₂
body=body.replace('c₁ ≅ᴵ c₂','c₁ ≈c c₂')
# 嵌入保留的 ≅ᴵ: R-tr 系列的 e₁
keep=[]
def protect(m):
    keep.append(m.group(0)); return '\0%d\0'%(len(keep)-1)
body=re.sub(r'\(e₁ : [ab′]+ ≅ᴵ [ab′]+\)',protect,body)
# 项里的搬运: ≅ᴵ-trans (≅ᴵ-sym X) (≅ᴵ-trans ek Y) → ≃-res X ek Y
def bal(st,i):
    # st[i]=='(' 或普通词; 返回 (token,end)
    if st[i]=='(':
        d=0;j=i
        while True:
            if st[j]=='(':d+=1
            elif st[j]==')':
                d-=1
                if d==0:return st[i:j+1],j+1
            j+=1
    j=i
    while st[j] not in ' )':j+=1
    return st[i:j],j
out=[];i=0
key='≅ᴵ-trans '
while True:
    j=body.find(key,i)
    if j<0: out.append(body[i:]);break
    out.append(body[i:j])
    A,k=bal(body,j+len(key)); B,k2=bal(body,k+1)
    if A=='ek': out.append('≃-respʳ ek '+B); i=k2; continue
    if B=='ek': out.append('≃-respˡ '+A+' ek'); i=k2; continue
    if A.startswith('(≅ᴵ-sym ') and B.startswith('(≅ᴵ-trans ek '):
        X=A[len('(≅ᴵ-sym '):-1]; Y=B[len('(≅ᴵ-trans ek '):-1]
        out.append('≃-res '+X+' ek '+Y); i=k2; continue
    out.append(body[j:k2]); i=k2
body=''.join(out)
# 其余层号关系
body=body.replace('≅ᴵ-refl (suc zero)','≃-reflᴵ (suc zero)')
body=body.replace(' ≅ᴵ ',' ≃ᴵ ')
body=re.sub(r'\0(\d+)\0',lambda m:keep[int(m.group(1))],body)
# 冲突的 clash
body=body.replace('(clash a (inj₁ (≺ᴵ-respʳ (≺ᴵ-respˡ et b) (≅ᴵ-sym ek))))','(clash≃ ek et a (inj₁ b))')
body=body.replace('(clash a (inj₂ (≅ᴵ-trans et (≅ᴵ-trans (≅ᴵ-sym c₁) (≅ᴵ-sym ek)))))','(clash≃ ek et a (inj₂ (≅ᴵ-sym c₁)))')
body=body.replace('(clash a (inj₁ (≺ᴵ-respʳ (≺ᴵ-respˡ (≅ᴵ-sym et) b) ek)))','(clash≃′ ek et a (inj₁ b))')
body=body.replace('(clash a (inj₂ (≅ᴵ-trans (≅ᴵ-sym et) (≅ᴵ-trans (≅ᴵ-sym c₁) ek))))','(clash≃′ ek et a (inj₂ (≅ᴵ-sym c₁)))')
assert 'clash a' not in body
# 构造子 rh
body=body.replace('''    ri : ∀ {φ χ ψ ρ j j′}''','''    rh : ∀ {φ χ ψ ρ} {F : ℕ → N.Q m a φ χ} {F′ : ℕ → I.Q (e m) b ψ ρ} → (∀ n → R₊ (F (suc n)) (F′ n)) → R₊ (N.ql F) (I.ql F′)
    rr : ∀ {φ χ ψ ρ} {F : ℕ → N.Q m a φ χ} {F′ : ℕ → I.Q (e m) b ψ ρ} → (∀ n → R₊ (F (suc n)) (F′ (suc n))) → R₊ (N.ql F) (I.ql F′)
    ri : ∀ {φ χ ψ ρ j j′}''')
# 每条 rl 配一条 rh
lines=body.split('\n');new=[]
for ln in lines:
    new.append(ln)
    if re.match(r'^\S.*\(rl h\).* = (rl|limR) \(',ln):
        new.append(ln.replace('(rl h)','(rh h)').replace('= rl (','= rh (').replace('= limR (','= limH ('))
        new.append(ln.replace('(rl h)','(rr h)').replace('= rl (','= rr (').replace('= limR (','= limT ('))
body='\n'.join(new)
# Ordˢ 的 lh
body=body.replace('R-tl (l≅ h) = rl (λ n → R-tl (h n))','R-tl (l≅ h) = rl (λ n → R-tl (h n))\nR-tl (lh h) = rh (λ n → R-tl (h n))\nR-tl (lr h) = rr (λ n → R-tl (h n))')
body=body.replace('R-tl (s≅ le e₁) = rs tt∼','R-tl (s≅ e₁) = rs tt∼')
body=body.replace('ŝ≅ k ec et eg','ŝ≅ k et eg').replace('rŝ ec (R-tl et)','rŝ tc (R-tl et)').replace('rĉ ec (toZ-≃ et)','rĉ tc (toZ-≃ et)').replace('ĉ≅ ec dt dg eo eO','ĉ≅ dt dg eo eO').replace('rĉ ec dt dg (R-tl eo)','rĉ tc dt dg (R-tl eo)')
# 模式: 层号的 ≃
body=body.replace('R-tlΩ z≅ s = rs s (sm (λ i q → ⊥-elim (N.no< q))) rz','R-tlΩ z≃ s = rs s (sm (λ i q → ⊥-elim (N.no< q))) rz')
body=body.replace('R-tlΩ (s≅ e₁) s = ','R-tlΩ (s≃ e₁) s = ')
body=body.replace('R-tlΩ (l≅ h) s = rl (λ n → rwk (R-tl (Ωˢ-≃ (h n))))','R-tlΩ (l≃ h) s = rl (λ n → rwk (R-tl (Ωˢ-≃ (h n))))\nR-tlΩ (lh≃ h) s = rh (λ n → rwk (R-tl (Ωˢ-≃ (h n))))\nR-tlΩ (lr≃ h) s = rr (λ n → rwk (R-tl (Ωˢ-≃ (h n))))')
body=body.replace('R-ι↓ dq (s≅ e₁) (rob {r = zero} {r′ = zero} ea l r) = rwk (R-ι↓ dq ea l)','R-ι↓ dq (s≃ e₁) (rob {r = zero} {r′ = zero} ea l r) = rwk (R-ι↓ dq ea l)')
body=body.replace('R-ι↓ dq (l≅ h) (rob {r = self n} {r′ = self n′} ea l r) = rwk (R-ι↓ dq ea l)','R-ι↓ dq (l≃ h) (rob {r = self n} {r′ = self n′} ea l r) = rwk (R-ι↓ dq ea l)\nR-ι↓ dq (lh≃ h) (rob {r = self n} {r′ = self n′} ea l r) = rwk (R-ι↓ dq ea l)\nR-ι↓ dq (lr≃ h) (rob {r = self n} {r′ = self n′} ea l r) = rwk (R-ι↓ dq ea l)')
body=body.replace('R-rowC q I₁ = rcl {q = q} fz∼ (rwk (R-ι↓ q (s≅ z≅) (I₁ (s≅ z≅))))','R-rowC q I₁ = rcl {q = q} fz∼ (rwk (R-ι↓ q (s≃ z≃) (I₁ (s≃ z≃))))')
body=body.replace('R-stepL q I₁ = rwk (R-ι↓ q z≅ (I₁ z≅))','R-stepL q I₁ = rwk (R-ι↓ q z≃ (I₁ z≃))')
a=body.index('cap∼ {m} {χ} {ρ} {x} {y} n s c = sm go'); b=body.index('-- 右边的节点号只差命题相等')
body=body[:a]+'cap∼ n s c = sm (λ i q → tt∼)\n\n'+body[b:]
body=body.replace('with N.tri n H | I.tri (e n) (e H) | al n H','with N.tri n H')
body=body.replace('| _ | _ | all l','| tlt l').replace('| _ | _ | ale','| teq refl').replace('| _ | _ | alg l','| tgt l')
# e, ε 字面展开, 否则 with 抽不到右边
body=re.sub(r'\(e (\w+)\)',r'\1',body)
body=re.sub(r'\(ε (\w+)\)',r'\1',body)
body=re.sub(r'\(e \(F i₁\)\)','(F i₁)',body)
body=re.sub(r'\(e \(F i\)\)','(F i)',body)
body=body.replace('e (F i₁)','F i₁').replace('e (F i)','F i')
# 第 0 行: 同一个 view
a=body.index('R-row : ∀ m'); b=body.index('FRΩ : ∀ m')
body=body[:a]+'''R-rowLh : ∀ {m} F (qs₁ : ∀ i → F i N.<ᴸ m) (r₁ : ∀ i → e (F i) I.<ᴸ e m) → (∀ {n} → n N.<ᴸ m → XRΩ n) → ∀ i →
         Rq m zero zero (N.rowL F qs₁ (λ i₁ → N.ΩI m (qs₁ i₁)) (suc i)) (I.stepL (r₁ i) (I.ΩI (e m) (r₁ i)))
R-rowLh {m} F qs₁ r₁ I₁ i = subst₂ (λ X Y → Rq m zero zero (N.stepL (qs₁ i) X) (I.stepL (r₁ i) Y)) (sym (N.ΩI≡ (qs₁ i))) (sym (I.ΩI≡ (r₁ i)))
  (subst (λ r → Rq m zero zero (N.stepL (qs₁ i) (N.Ω̇ (F i))) (I.stepL r (I.Ω̇ (e (F i))))) (I.<-prop (ε (qs₁ i)) (r₁ i)) (R-stepL (qs₁ i) (I₁ (qs₁ i))))

R-rowD : ∀ {m} F (qs₁ : ∀ i → F i N.<ᴸ m) → (∀ {n} → n N.<ᴸ m → XRΩ n) → (b : I.HdM m) →
         Rq m zero zero (N.ql (N.rowL F qs₁ (λ i → N.ΩI m (qs₁ i)))) (I.ql (I.rowD F qs₁ (I.ΩI m) b))
R-rowD F qs₁ I₁ I.keep = rl (R-rowL F qs₁ qs₁ I₁)
R-rowD F qs₁ I₁ I.drop = rh (R-rowLh F qs₁ qs₁ I₁)
R-rowD F qs₁ I₁ (I.repl n q) = rr (R-rowLh F qs₁ qs₁ I₁)

R-row : ∀ m → (∀ {n} → n N.<ᴸ m → XRΩ n) → (v : View N._<ᴸ_ N.h₀ m) → Rq m zero zero (N.rowV m (N.ΩI m) v) (I.rowV m (I.ΩI m) v)
R-row _ I₁ base =
  rclo (∼ᶠ-refl fz)
    (R-tlΩ (≃-reflᴵ (suc zero)) tt∼)
    (λ η η′ eη → R-tlΩ eη tt∼)
R-row m I₁ (clos q) =
  subst₂ (λ X Y → Rq m zero zero (N.rowC q X) (I.rowC (ε q) Y)) (sym (N.ΩI≡ q)) (sym (I.ΩI≡ (ε q))) (R-rowC q (I₁ q))
R-row m I₁ (chain F qs₁) = R-rowD F qs₁ I₁ (dr m)

'''+body[b:]
a=body.index('FRΩ m I₁ (s≅ e₁) ='); b=body.index('RΩ̇ : ∀ m')
body=body[:a]+'''FRΩ m I₁ (s≃ e₁) = rΩ e₁ tt∼ Fl∼ (λ ξ ξ′ ζ ζ′ d dc z z′ l → rwk (rob {r = zero} {r′ = zero} e₁ l (R-ι zero zero l)))
FRΩ m I₁ (l≃ h) = rl (λ n → rob {r = self n} {r′ = self n} (h n) (FRΩ m I₁ (h n)) (R-ι (self n) (self n) (FRΩ m I₁ (h n))))
FRΩ m I₁ (lh≃ h) = rh (λ n → rob {r = self (suc n)} {r′ = self n} (h n) (FRΩ m I₁ (h n)) (R-ι (self (suc n)) (self n) (FRΩ m I₁ (h n))))
FRΩ m I₁ (lr≃ h) = rr (λ n → rob {r = self (suc n)} {r′ = self (suc n)} (h n) (FRΩ m I₁ (h n)) (R-ι (self (suc n)) (self (suc n)) (FRΩ m I₁ (h n))))
FRΩ m I₁ z≃ = R-row m I₁ (N.view m)

'''+body[b:]
# 求值
body=body.replace('ŝR d (R→≈ᵠ r ok e₁ ok′ e′)','ŝR (R→≈ᵠ r ok e₁ ok′ e′)').replace('ĉR d dz dg (R→≈ᵠ','ĉR dz dg (R→≈ᵠ')
body=body.replace('{t′ = I.ψ̄ᵠ ok′ e′ t′} {g′ = λ η → I.ψ̄ᵠ ok′ e′ (g′ η)} s (R→≈ᵠ r','{t′ = I.ψ̄ᵠ ok′ e′ t′} {g′ = λ η → I.ψ̄ᵠ ok′ e′ (g′ η)} (R→≈ᵠ r')
body=body.replace('ŝR (bound-≅ (⊔∼ s tt∼) _ (N.zr ok n) _ (I.zr ok′ (e n)) z≅) (R→≈ᵠ','ŝR (R→≈ᵠ')
body=body.replace('rŝ (bound-≅ (⊔∼ s tt∼) _ p _ p′ et)','rŝ tc').replace('rŝ (bound-≅ (⊔∼ s tt∼) _ (N.zr ok n) _ (I.zr ok′ (e n)) z≅)','rŝ tc')
body=body.replace('ŝR tc (R→≈ᵠ','ŝR (R→≈ᵠ')
body=body.replace('R→≈ᵠ (rh h) ok e₁ ok′ e′ = limH (','R→≈ᵠ (rh {F = F} {F′ = F′} h) ok e₁ ok′ e′ = limH {F = λ n → N.ψ̄ᵠ ok e₁ (F n)} {G = λ n → I.ψ̄ᵠ ok′ e′ (F′ n)} (')
body=body.replace('R→≈ᵠ (rr h) ok e₁ ok′ e′ = limT (','R→≈ᵠ (rr {F = F} {F′ = F′} h) ok e₁ ok′ e′ = limT {F = λ n → N.ψ̄ᵠ ok e₁ (F n)} {G = λ n → I.ψ̄ᵠ ok′ e′ (F′ n)} (')
# 尾
a=body.index('-- 主定理: 实例上的树与原来的树同值')
body=body[:a]+'''-- 主定理: 主线的树与去头的树, 层号去头相关
simᴴ : ∀ m α α′ → α ≃ᴵ α′ → N.Tᵠ m α ≈ᴴ I.Tᵠ m α′
simᴴ m α α′ d = R→≈ᵠ (RΩ̇ m d) N.ok₀ (λ i h r → N.ok₀ i) I.ok₀ (λ i h r → I.ok₀ i)
```
'''
wr('EmbVVSim','''# 主线的树与去头的树的模拟

> **机械改写.** 由 [CrossMSim](CrossMSim.lagda.md) 经 `Survey/scripts/embvv/mk_sim.py` 生成. 差别: 层号的关系从 $\\cong^{\\mathsf I}$ 换成去头关系 `≃ᴵ`; 多一个构造子 `rh` (左边的极限多一个头); 第 0 行由 `rowD` 的开关分两种; 派发的冲突由 `clash≃` (值) 排除; 地板的相似不再需要, 用平凡关系占位. 入口 [EmbVV](EmbVV.lagda.md). 不读记号.

'''+header+body)

# ---------- 主线对主线: 层号去头不改值 ----------
sm=rd('EmbVVSim')
sm=sm.replace('module OCF.Align.EmbVVSim (𝕊 : HtB) (dr : ∀ m → OCF.Align.EmbVVMode.HdM 𝕊 m) where','module OCF.Align.EmbVVSame (𝕊 : HtB) where')
sm=sm.replace('import OCF.Align.EmbVVMode\n','')
sm=sm.replace('import OCF.Align.EmbVVTree\n','').replace('module I = OCF.Align.EmbVVTree 𝕊 dr','module I = OCF.Align.LadderOrdTree 𝕊')
a=sm.index('R-rowLh : ∀ {m} F'); b=sm.index('R-row : ∀ m →')
sm=sm[:a]+sm[b:]
sm=sm.replace('R-row m I₁ (chain F qs₁) = R-rowD F qs₁ I₁ (dr m)','R-row m I₁ (chain F qs₁) = rl (R-rowL F qs₁ qs₁ I₁)')
i=sm.index('```agda')
wr('EmbVVSame','# 主线对主线: 层号去头\n\n> **机械改写.** 与 [EmbVVSim](EmbVVSim.lagda.md) 同一个脚本 (`Survey/scripts/embvv/mk_sim.py`), 右边换成主线的树. 入口 [EmbVV](EmbVV.lagda.md). 不读记号.\n\n'+sm[i:])
