# 记号参照: ψ₀(Ω_Ω+…) 一段的具体比较

> 验收文件 (读记号). 编译定理, 无前提, 对任意 `HC` 推导: 参照 ψ₀(Ω_Ω) ≺ ψ₀(Ω_Ω+ψ₁(Ω₂)) ≺ ψ₀(Ω_Ω+Ω₂) ≺ ψ₀(Ω_Ω·2) ≺ ψ₀(ψ_Ω(Ω₂)) ≺ ψ₀(Ω_{Ω+1}) (`≺` 指 `L.suc X ≼ Y`), 其中三对的反向 `≼` 不成立 (`B⋠A`, `C⋠B`, `E⋠C`); 非标准形 ψ₀(Ω_Ω+ψ₁(Ω_Ω+Ω₂)) 有 `HC` 推导, 参照与 ψ₀(Ω_Ω+Ω₂) 的互相 `≼` (`D≼B`, `B≼D`).
> 由 [YiNFO](YiNFO.lagda.md) 的 `mono<` 代入; 每个项给两种标准形证明 (`NF₁` 供 `cofin₁`, `EboLeanBase.NF` 供 `hc`). 推导放 `opaque`, 只作前提可满足的实例.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNFOCase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.List using ([]; _∷_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import OCF.Align.EboLeanDef using (T; PT; ψ; natT; Ωt; γT; EBOψ; HC; h0; h1; hω; fsn;
  _<ᵀ_; []<; hd<; tl<; lv<; ar<)
import OCF.Align.EboLeanBase as B
open import OCF.Align.EboLeanTree using (hc; hc-tower)
open import OCF.Align.Standard using (c[]; c∷)
open import OCF.Align.StandardOmega using (NF₁; NFᴾ₁; n[]; n∷; nψ; sC; Bnd₁; vh; vd; vs; vt; bnd[];
  sΩ; Flat; f[]; f∷; flatVis; flatBnd; f1; fΩ; nf1; nfΩ; nfβ; nfβᴱ; t2-NF; tO-NF; NF₁-fsn)
open import OCF.Align.Stage2 using (t2; tO)
open import OCF.Align.Bachmann using (<ᵀ-asym)
open import OCF.Lean.YiRefTw2 using (Rt; tree-≼; hω-inv; fs≼; t₊; h₊)
open import OCF.Lean.YiNFO using (mono<; mono≤; mono<-strict; fsn≡)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; s≼s; l≼; ≼-trans)
```

## 记号项

`tA` = ψ₀(Ω_Ω+ψ₁(Ω₂)), `tB` = ψ₀(Ω_Ω+Ω₂), `tC` = ψ₀(Ω_Ω·2) (即 Stage2 的 `t2`), `tD` = ψ₀(Ω_Ω+ψ₁(Ω_Ω+Ω₂)), `tE` = ψ₀(ψ_Ω(Ω₂)) (读作 ψ₀(Ω_Ω·Ω₂), 读法是判断), `t₊` = ψ₀(Ω_{Ω+1}). EBO 里 Ω_μ = ψ_μ(0), Ω = Ω₁.

```agda
ω₁ : T
ω₁ = Ωt (natT 1)

ΩΩ : PT
ΩΩ = ψ ω₁ []

Ω₂ : PT
Ω₂ = ψ (natT 2) []

ψ₁Ω₂ : PT
ψ₁Ω₂ = ψ (natT 1) (Ω₂ ∷ [])

ψ₁ΩΩΩ₂ : PT
ψ₁ΩΩΩ₂ = ψ (natT 1) (ΩΩ ∷ Ω₂ ∷ [])

ψΩΩ₂ : PT
ψΩΩ₂ = ψ ω₁ (Ω₂ ∷ [])

argA argB argC : T
argA = ΩΩ ∷ ψ₁Ω₂ ∷ []
argB = ΩΩ ∷ Ω₂ ∷ []
argC = ΩΩ ∷ ΩΩ ∷ []

tA tB tC tD tE : T
tA = ψ [] argA ∷ []
tB = ψ [] argB ∷ []
tC = ψ [] argC ∷ []
tD = ψ [] (ΩΩ ∷ ψ₁ΩΩΩ₂ ∷ []) ∷ []
tE = ψ [] (ψΩΩ₂ ∷ []) ∷ []

_ : tC ≡ t2
_ = refl

_ : t₊ ≡ tO
_ = refl

_ : ∀ n → fsn tD n ≡ fsn tB (suc n)
_ = λ n → refl
```

## 标准形: `NF₁`

```agda
z< : ∀ {z x xs} → z ≡ [] → z <ᵀ (x ∷ xs)
z< refl = []<

f2 : Flat (natT 2)
f2 = f∷ f[] f1

fΩ₂ : Flat (Ω₂ ∷ [])
fΩ₂ = f∷ f2 f[]

nf2₁ : NF₁ (natT 2)
nf2₁ = n∷ (nψ n[] (sC c[]) n[] bnd[]) nf1 (inj₂ refl)

nΩ₂₁ : NF₁ (Ω₂ ∷ [])
nΩ₂₁ = n∷ (nψ nf2₁ (sC (c∷ (c∷ c[]))) n[] bnd[]) n[] tt

bndA : Bnd₁ [] argA
bndA (vh _)        = []<
bndA (vd _ ())
bndA (vs _ v)      = z< (flatVis fΩ v)
bndA (vt (vh _))   = hd< (lv< (hd< (lv< []<)))
bndA (vt (vd _ v)) = z< (flatVis fΩ₂ v)
bndA (vt (vs _ v)) = z< (flatVis f1 v)
bndA (vt (vt ()))

nA₁ : NF₁ tA
nA₁ = n∷ (nψ n[] (sC c[]) (n∷ nfβ (n∷ (nψ nf1 (sC (c∷ c[])) nΩ₂₁ (flatBnd fΩ₂)) n[] tt) (inj₁ refl)) bndA) n[] tt

nB₁ : NF₁ tB
nB₁ = n∷ (nψ n[] (sC c[]) (n∷ nfβ nΩ₂₁ (inj₁ refl)) (flatBnd (f∷ fΩ fΩ₂))) n[] tt

nC₁ : NF₁ tC
nC₁ = t2-NF

bndE : Bnd₁ [] (ψΩΩ₂ ∷ [])
bndE (vh _)   = hd< (lv< (hd< (lv< []<)))
bndE (vd _ v) = z< (flatVis fΩ₂ v)
bndE (vs _ v) = z< (flatVis fΩ v)
bndE (vt ())

nE₁ : NF₁ tE
nE₁ = n∷ (nψ n[] (sC c[]) (n∷ (nψ nfΩ (sΩ c[]) nΩ₂₁ (flatBnd fΩ₂)) n[] tt) bndE) n[] tt

nbtbo₁ : NF₁ (EBOψ 2)
nbtbo₁ = n∷ (nψ n[] (sC c[]) nfβᴱ (flatBnd (f∷ fΩ f[]))) n[] tt
```

范围的边界: 塔第 3 行 ψ₀(Ω_{Ω_Ω}) 不在 `NF₁` 里 (下标 Ω_Ω 既不可数, 也不是 Ω+可数), `mono<` 用不到它.

```agda
row3-out : ¬ NF₁ (EBOψ 3)
row3-out (n∷ (nψ _ _ (n∷ (nψ _ (sC ()) _ _) _ _) _) _ _)
```

## 标准形: `EboLeanBase.NF` 与推导

```agda
flatG : ∀ {u z t} → Flat t → B.InG u z t → z ≡ []
flatG (f∷ fu fx) (B.gp (B.gh _))   = refl
flatG (f∷ fu fx) (B.gp (B.gw _ i)) = flatG fu i
flatG (f∷ fu fx) (B.gp (B.gc _ ()))
flatG (f∷ fu fx) (B.gtl i)         = flatG fx i

flatGB : ∀ {u x xs} → Flat (x ∷ xs) → B.GB u (x ∷ xs) (x ∷ xs)
flatGB f i = z< (flatG f i)

n1ᴮ : B.NF (natT 1)
n1ᴮ = B.n∷ (B.nψ B.n[] B.n[] B.GB[]) tt B.n[]

n2ᴮ : B.NF (natT 2)
n2ᴮ = B.n∷ (B.nψ B.n[] B.n[] B.GB[]) (inj₂ refl) n1ᴮ

nω₁ᴮ : B.NF ω₁
nω₁ᴮ = B.n∷ (B.nψ n1ᴮ B.n[] B.GB[]) tt B.n[]

nΩΩᴮ : B.NFP ΩΩ
nΩΩᴮ = B.nψ nω₁ᴮ B.n[] B.GB[]

nΩ₂ᴮ : B.NFP Ω₂
nΩ₂ᴮ = B.nψ n2ᴮ B.n[] B.GB[]

gA : B.GB [] argA argA
gA (B.gp (B.gh _))         = []<
gA (B.gp (B.gw _ i))       = z< (flatG fΩ i)
gA (B.gp (B.gc _ ()))
gA (B.gtl (B.gp (B.gh _)))   = hd< (lv< (hd< (lv< []<)))
gA (B.gtl (B.gp (B.gw _ i))) = z< (flatG f1 i)
gA (B.gtl (B.gp (B.gc _ i))) = z< (flatG fΩ₂ i)
gA (B.gtl (B.gtl ()))

nAᴮ : B.NF tA
nAᴮ = B.n∷ (B.nψ B.n[] (B.n∷ nΩΩᴮ (inj₁ (lv< (hd< (lv< []<))))
                         (B.n∷ (B.nψ n1ᴮ (B.n∷ nΩ₂ᴮ tt B.n[]) (flatGB fΩ₂)) tt B.n[])) gA) tt B.n[]

nBᴮ : B.NF tB
nBᴮ = B.n∷ (B.nψ B.n[] (B.n∷ nΩΩᴮ (inj₁ (lv< (hd< (lv< []<)))) (B.n∷ nΩ₂ᴮ tt B.n[]))
                 (flatGB (f∷ fΩ fΩ₂))) tt B.n[]

nCᴮ : B.NF tC
nCᴮ = B.n∷ (B.nψ B.n[] (B.n∷ nΩΩᴮ (inj₂ refl) (B.n∷ nΩΩᴮ tt B.n[])) (flatGB (f∷ fΩ (f∷ fΩ f[])))) tt B.n[]

gE : B.GB [] (ψΩΩ₂ ∷ []) (ψΩΩ₂ ∷ [])
gE (B.gp (B.gh _))   = hd< (lv< (hd< (lv< []<)))
gE (B.gp (B.gw _ i)) = z< (flatG fΩ i)
gE (B.gp (B.gc _ i)) = z< (flatG fΩ₂ i)
gE (B.gtl ())

nEᴮ : B.NF tE
nEᴮ = B.n∷ (B.nψ B.n[] (B.n∷ (B.nψ nω₁ᴮ (B.n∷ nΩ₂ᴮ tt B.n[]) (flatGB fΩ₂)) tt B.n[]) gE) tt B.n[]

opaque
  hA : HC tA
  hA = hc nAᴮ (B.c∷ B.c[])

  hB : HC tB
  hB = hc nBᴮ (B.c∷ B.c[])

  hC : HC tC
  hC = hc nCᴮ (B.c∷ B.c[])

  hE : HC tE
  hE = hc nEᴮ (B.c∷ B.c[])
```

## 项序

```agda
btbo<A : EBOψ 2 <ᵀ tA
btbo<A = hd< (ar< (tl< []<))

A<B : tA <ᵀ tB
A<B = hd< (ar< (tl< (hd< (lv< (tl< []<)))))

B<C : tB <ᵀ tC
B<C = hd< (ar< (tl< (hd< (lv< (hd< (lv< []<))))))

C<E : tC <ᵀ tE
C<E = hd< (ar< (hd< (ar< []<)))

E<O : tE <ᵀ t₊
E<O = hd< (ar< (hd< (lv< (tl< []<))))
```

## 值序: 严格比较与反向的否定

```agda
btbo≺A : (h : HC (EBOψ 2)) (h′ : HC tA) → L.suc (Rt h) ≼ Rt h′
btbo≺A h h′ = mono< nbtbo₁ nA₁ h h′ btbo<A

A≺B : (h : HC tA) (h′ : HC tB) → L.suc (Rt h) ≼ Rt h′
A≺B h h′ = mono< nA₁ nB₁ h h′ A<B

B⋠A : (h : HC tA) (h′ : HC tB) → ¬ (Rt h′ ≼ Rt h)
B⋠A h h′ = mono<-strict nA₁ nB₁ h h′ A<B

B≺C : (h : HC tB) (h′ : HC tC) → L.suc (Rt h) ≼ Rt h′
B≺C h h′ = mono< nB₁ nC₁ h h′ B<C

C⋠B : (h : HC tB) (h′ : HC tC) → ¬ (Rt h′ ≼ Rt h)
C⋠B h h′ = mono<-strict nB₁ nC₁ h h′ B<C

C≺E : (h : HC tC) (h′ : HC tE) → L.suc (Rt h) ≼ Rt h′
C≺E h h′ = mono< nC₁ nE₁ h h′ C<E

E⋠C : (h : HC tC) (h′ : HC tE) → ¬ (Rt h′ ≼ Rt h)
E⋠C h h′ = mono<-strict nC₁ nE₁ h h′ C<E

E≺O : (h : HC tE) (h′ : HC t₊) → L.suc (Rt h) ≼ Rt h′
E≺O h h′ = mono< nE₁ tO-NF h h′ E<O
```

定值的用法: 不高于 A 的参照的值, 到不了 B 的参照.

```agda
below-A : (h : HC tA) (h′ : HC tB) {X : L.Ordᶜ L.zero} → X ≼ Rt h → ¬ (Rt h′ ≼ X)
below-A h h′ p q = B⋠A h h′ (≼-trans q p)
```

## ψ₀(Ω_Ω+ψ₁(Ω_Ω+Ω₂)): 不是标准形, 参照与 ψ₀(Ω_Ω+Ω₂) 的互相 `≼`

它的可见参数 Ω_Ω+Ω₂ 不低于参数 Ω_Ω+ψ₁(Ω_Ω+Ω₂), 两种标准形都不成立. 它的第 n 个基本列项就是 `tB` 的第 n+1 项 (上面的 `refl`), 所以有 `HC` 推导, 参照与 `tB` 的互相 `≼`.

```agda
noD : ¬ ((ΩΩ ∷ Ω₂ ∷ []) <ᵀ (ΩΩ ∷ ψ₁ΩΩΩ₂ ∷ []))
noD (hd< p) = B.<ᴾ-irrefl p
noD (tl< q) = <ᵀ-asym q (hd< (lv< (tl< []<)))

D-notNF₁ : ¬ NF₁ tD
D-notNF₁ (n∷ (nψ _ _ _ bnd) _ _) = noD (bnd (vt (vh (inj₁ []<))))

D-notNFᴮ : ¬ B.NF tD
D-notNFᴮ (B.n∷ (B.nψ _ _ g) _ _) = noD (g (B.gtl (B.gp (B.gh (inj₁ []<)))))

hD : HC tD
hD = hω refl (λ n → hω-inv hB refl (suc n))

γ< : ∀ k → γT argB (natT 1) k <ᵀ γT argB (natT 1) (suc k)
γ< zero    = hd< (ar< []<)
γ< (suc k) = hd< (ar< (tl< (γ< k)))

nfB : ∀ n → NF₁ (fsn tB n)
nfB n = subst NF₁ (sym (fsn≡ tB n)) (NF₁-fsn nB₁ refl n)

D≼B : (h : HC tB) (h′ : HC tD) → Rt h′ ≼ Rt h
D≼B h (h0 ())
D≼B h (h1 () _)
D≼B h (hω _ hs) = l≼ (λ n → ≼-trans (tree-≼ refl (hs n) (hω-inv h refl (suc n))) (fs≼ h refl (suc n)))

B≼D : (h : HC tB) (h′ : HC tD) → Rt h ≼ Rt h′
B≼D (h0 ()) h′
B≼D (h1 () _) h′
B≼D (hω _ hs) h′ = l≼ (λ n →
  ≼-trans (mono≤ (nfB n) (nfB (suc n)) (hs n) (hs (suc n)) (inj₁ (hd< (ar< (tl< (γ< n))))))
          (≼-trans (tree-≼ refl (hs (suc n)) (hω-inv h′ refl n)) (fs≼ h′ refl n)))

A≺D : (h : HC tA) (h′ : HC tD) → L.suc (Rt h) ≼ Rt h′
A≺D h h′ = ≼-trans (A≺B h hB) (B≼D hB h′)

D≺C : (h : HC tD) (h′ : HC tC) → L.suc (Rt h) ≼ Rt h′
D≺C h h′ = ≼-trans (s≼s (D≼B hB h)) (B≺C hB h′)
```

## 实例 (前提可满足)

```agda
inst-AB : L.suc (Rt hA) ≼ Rt hB
inst-AB = A≺B hA hB

inst-BC : L.suc (Rt hB) ≼ Rt hC
inst-BC = B≺C hB hC

inst-CE : L.suc (Rt hC) ≼ Rt hE
inst-CE = C≺E hC hE

inst-EO : L.suc (Rt hE) ≼ Rt h₊
inst-EO = E≺O hE h₊

inst-btbo : L.suc (Rt (hc-tower 2)) ≼ Rt hA
inst-btbo = btbo≺A (hc-tower 2) hA

inst-DB : Rt hD ≼ Rt hB
inst-DB = D≼B hB hD
```
