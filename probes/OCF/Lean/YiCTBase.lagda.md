# `up` 行的底参数清空来源表的影响

> 编译定理与有限测试; 不改树、折叠、合法性. 不读记号 (`At` 用 `YiCTCall` 里的逐字副本). "带祖先表" 只指把一次底折叠调用里的 `org-no` 换成该层主折叠此刻带的表, 不是新的折叠.
> (i) 经两层 `ink` 的孩子 (tw 3 朝 tw 1 经 `ink (ink self)`, 进孩子 0 即 tw 2, 再在 tw 2 上走 `ink` 行): 祖先表 `otₜ` 的两部分都是空表, 底折叠的每个槽位、每条路径上 `kpᶜ` 与 `org-no` 下相同 (`same`).
> (ii) 一层 `ink` 之后 (`outᶜ 1` 第 1 个部分和第 2 个链点, X₀ 的孩子 0, 底的前缀是 Ωt X₀; `link₁`, `link₂`): X₀ 的顶槽位朝 h₁ 2 经 `inc 0 u`, 带 `ot₂` 时保留在 `qᵍ 1`, 带 `org-no` 时走链 (`anc`, `clr`, `pxᵃ`, `hx`).
> `YiCTCall` 那一支在 tw 1 上的主表也是空表 (`OT-empty`). 不否定什么; (ii) 的底在 (h₁ 2, `inc 0 u`) 处是否被实际查询没有追踪. 入口: `same`, `clr`, `anc`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCTBase where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)

open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀; Keep)
open import OCF.Lean.YiMTTab using (rbᶻ)
open import OCF.Lean.YiDXFold using (alt; flr)
open import OCF.Lean.YiDXTest using (h₁; n1; n3; IsNothing; IsJust; el; HeadΩ; HeadLim)
open import OCF.Lean.YiKFKeep
open import OCF.Lean.YiKFFold
open import OCF.Lean.YiKFTest using (outᶜ; qᵍ)
open import OCF.Lean.YiCTCall using (module At; brΩ; posΩ; L₁; o₁; r₁; pv₁; ws₁; ot₁; OT)
```

## (i) 两层 `ink`: 祖先表是空表

```agda
noOrg : (j b : L) (t : Pos⁼ b) → org-at j b (org-no j b) t ≡ nothing
noOrg j b              (inj₁ _)              = refl
noOrg j (nd (sΩ k″) h) (inj₂ (inj₁ t))       = refl
noOrg j (nd sS h)      (inj₂ (inj₂ (c , t))) = noOrg j (h c) t
noOrg j (nd sL h)      (inj₂ (inj₂ (c , t))) = noOrg j (h c) t
noOrg j (nd (sΩ k″) h) (inj₂ (inj₂ (c , t))) = noOrg j (h c) t

emptyOrg : (k j b : L) (F : (p′ : Pos k) → Keep j (Br k p′) (fromBr k p′ zero)) (t : Pos⁼ b)
         → org-at j b (altOrg j b (org-no j b) (mapOrg k j F b (org-no k b))) t ≡ nothing
emptyOrg k j b              F (inj₁ _)              = refl
emptyOrg k j (nd (sΩ k″) h) F (inj₂ (inj₁ t))       = refl
emptyOrg k j (nd sS h)      F (inj₂ (inj₂ (c , t))) = emptyOrg k j (h c) F t
emptyOrg k j (nd sL h)      F (inj₂ (inj₂ (c , t))) = emptyOrg k j (h c) F t
emptyOrg k j (nd (sΩ k″) h) F (inj₂ (inj₂ (c , t))) = emptyOrg k j (h c) F t

kpᶜ-org : ∀ ℓ o pv p {j} (w : j ≤ ℓ) (T T′ : Org j ℓ) → org-at j ℓ T (inj₂ p) ≡ org-at j ℓ T′ (inj₂ p)
        → kpᶜ ℓ o pv p w T ≡ kpᶜ ℓ o pv p w T′
kpᶜ-org ℓ o pv p {j} w T T′ e = cong (λ m → alt (kpʳ ℓ o pv p w) (alt m (flr (at ℓ p) (fromBr ℓ p) j))) e
```

tw 3 的孩子 0 就是 tw 2, 路径仍是 `ink self`, 所以 tw 2 上走的又是 `ink` 行; 祖先表由 `dlg` 生成, 继承部分来自起点的 `org-no`, 新增部分来自 `pvT 3` 在前缀上的 `org-no`.

```agda
h₃ : Tr (tw 2) → L
h₃ c = tw 2 ⊕ ↑ (tw 2) c

wₜ : tw 1 ≤ tw 2
wₜ = ink self ∙ proj₂ (proj₁ (Ok-tw 3)) zero

wₜ-form : wₜ ≡ ink self
wₜ-form = refl

otₜ : Org (tw 1) (tw 2)
otₜ = dlg (tw 2) h₃ (Ok-tw 3) (pvT 3) (ink self) (org-no (tw 1) (tw 3)) zero

oₜ : Ok (tw 2)
oₜ = proj₂ (Ok-tw 3) zero

pvₜ : Pv (tw 2)
pvₜ = proj₂ (pvT 3) zero

Fₜ : (p′ : Pos (tw 2)) → Keep (tw 1) (Br (tw 2) p′) (fromBr (tw 2) p′ zero)
Fₜ p′ = kpʳ (tw 2) (proj₁ (proj₁ (Ok-tw 3))) (proj₁ (proj₁ (pvT 3))) p′ (ink self)

otₜ-form : otₜ ≡ altOrg (tw 1) (tw 2) (org-no (tw 1) (tw 2)) (mapOrg (tw 2) (tw 1) Fₜ (tw 2) (org-no (tw 2) (tw 2)))
otₜ-form = refl

same : ∀ (p : Pos (tw 2)) (w : tw 1 ≤ tw 2) → kpᶜ (tw 2) oₜ pvₜ p w otₜ ≡ kpᶜ (tw 2) oₜ pvₜ p w (org-no (tw 1) (tw 2))
same p w = kpᶜ-org (tw 2) oₜ pvₜ p w otₜ (org-no (tw 1) (tw 2))
  (trans (emptyOrg (tw 2) (tw 1) (tw 2) Fₜ (inj₂ p)) (sym (noOrg (tw 1) (tw 2) (inj₂ p))))
```

## (ii) 一层 `ink` 之后: X₀ 的顶槽位

```agda
open At n1

link₁ : brΩ (el (el (el (outᶜ n1) 1) 0) 1) tt zero ≡ proj₁ (next⁺ β) + proj₁ (G (proj₁ (Ωt X₀) + brΩ (proj₁ (Ωt X₀)) tt zero))
link₁ = refl

B₁ˣ : Base L₁
B₁ˣ i u = FC.ψ X₀ o₂ (rbᶻ X₀) pv₂ (B₀ X₀) i (inc zero u) (org-no i X₀) (B₀ X₀ i (inc zero u)) (proj₁ (Ωt X₀))

β₁ˣ : Tr⁺ j
β₁ˣ = FC.ψ X₀ o₂ (rbᶻ X₀) pv₂ (B₀ X₀) j w₂ ot₂ β (proj₁ (Ωt X₀))

link₂ : G (proj₁ (Ωt X₀) + brΩ (proj₁ (Ωt X₀)) tt zero) ≡ FC.ψ L₁ o₁ r₁ pv₁ B₁ˣ j ws₁ ot₁ β₁ˣ (proj₁ (Ωt L₁))
link₂ = refl

u : j ≤ L₁
u = inc tt (inc n3 (inc tt self))

top : Pos X₀
top = inj₁ (inj₁ tt)

clr : IsNothing (kpᶜ X₀ o₂ pv₂ top (inc zero u) (org-no j X₀))
clr = tt

anc : IsJust (kpᶜ X₀ o₂ pv₂ top (inc zero u) ot₂)
anc = tt

Bxᵃ : Tr⁺ j
Bxᵃ = FC.ψ X₀ o₂ (rbᶻ X₀) pv₂ (B₀ X₀) j (inc zero u) ot₂ (B₀ X₀ j (inc zero u)) (proj₁ (Ωt X₀))

hx : HeadLim (proj₁ (B₁ˣ j u))
hx = tt

hxᵃ : HeadΩ (proj₁ Bxᵃ)
hxᵃ = tt

pxᵃ : posΩ (proj₁ Bxᵃ) tt ≡ qᵍ n1
pxᵃ = refl
```

`YiCTCall` 那一支在 tw 1 (X₀ 的前缀叶子) 上的主表 `OT` 也是空表, 所以 P₃ 回灌 (目标与路径同主折叠) 处换成带祖先表也不变.

```agda
OT-empty : ∀ t → org-at j (tw 1) OT t ≡ nothing
OT-empty t = emptyOrg (h₁ (suc n1)) j (tw 1) _ t
```
