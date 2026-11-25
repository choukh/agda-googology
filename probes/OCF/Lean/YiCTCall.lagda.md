# 审核那一格在实际折叠路径上: `cand₂` 的 c = 0 支

> 有限测试 (具体闭项上的 `refl`) 与对证据、来源表的编译定理; 不读记号, 不改树、折叠、合法性. `YiKFValue` 的 `At`、`brᵍ` 等逐字复制 (该文件第 77–143 行), 以免导入其含记号的闭包.
> `cand₂` (d = 1, 目标 h₁ 2) 的分支 `brᵍ 1 0` 沿 `E0`–`E10` 展开到 `kpᶜ (tw 1) O PV P₁ (inc 3 (inc tt self)) OT`: P₁ 在塔第 1 项孩子 3 里、层号 h₁ 1, 目标 h₁ 2 自己有同层号、同分支类型的槽位 q′; 这次调用对一切证据与来源表给 `nothing` (`cell`), 输出在那里是 ℕ 极限 (`probe-call`, `hd₃`).
> 只把比较表证据换成在孩子 (3,3) 给 `self` 的表, 同一探针就是保留在 q′ 的 Ω 结点 (`cf-pos`); d = 0 的同形格由 (A) 的地板保留 (`d0-cell`).
> 不否定什么. 只追踪了 c = 0 一支里的一条路; `AuditDCand` 原格 (目标 h₁ 3, 路径 `inc 3 self`) 不在这条路上 (路上的目标只有 h₁ 2 与回灌目标 tw 1). 入口: `E10`, `cell`, `cf-pos`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCTCall where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀; Keep; kp; node⁺)
open import OCF.Lean.YiTBRow using (Rb)
open import OCF.Lean.YiMTTab using (rbᶻ; tbᶻ)
open import OCF.Lean.YiDXTest using (h₁; a₁; hh; oᵈ; n1; n2; n3; IsNothing; IsJust; el; HeadΩ; HeadLim)
open import OCF.Lean.YiKFKeep
open import OCF.Lean.YiKFFold
open import OCF.Lean.YiKFTest using (pr; outᶜ; pvᵈ; zᵍ)
```

## `YiKFValue` 的对象 (逐字副本)

```agda
posΩ : ∀ {S} (t : T S) → HeadΩ t → P S
posΩ (Ω p g) _ = p

brΩ : ∀ {S} (t : T S) (hd : HeadΩ t) → B S (posΩ t hd) → T S
brΩ (Ω p g) _ = g

hdᵍ : ∀ d → HeadΩ (pr (outᶜ d))
hdᵍ d = tt

brᵍ : (d : Tr zero) → Tr (h₁ d) → Tr (h₁ (suc d))
brᵍ d = brΩ (pr (outᶜ d)) (hdᵍ d)

IsInu : ∀ {b j ℓ} → Pth b j ℓ → Set
IsInu (inu _) = ⊤
IsInu _       = ⊥

unU : ∀ {b j s h} (w : Pth b j (nd s h)) → IsInu w → (c : Ch s) → Pth b j (h c)
unU (inu vs) _ c = vs c

module At (d : Tr zero) where
  ℓ j X₀ : L
  ℓ  = a₁ (suc (suc d))
  j  = h₁ (suc d)
  X₀ = tw 1 ⊕ (zero ⊕ (zero ⊕ ↑ (h₁ (suc d)) (zᵍ d)))

  o : Ok ℓ
  o = proj₂ oᵈ (suc (suc d))

  pv : Pv ℓ
  pv = proj₂ pvᵈ (suc (suc d))

  o₂ : Ok X₀
  o₂ = proj₂ (proj₂ o (zᵍ d)) tt

  pv₂ : Pv X₀
  pv₂ = proj₂ (proj₂ pv (zᵍ d)) tt

  ot₂ : Org j X₀
  ot₂ = proj₂ (dlg (h₁ (suc d)) (hh (suc d)) o pv self (org-no j ℓ) (zᵍ d)) tt

  w₂ : j ≤ X₀
  w₂ = unU (self ∙ proj₂ (proj₁ o) (zᵍ d)) tt tt

  β : Tr⁺ j
  β = Ωt j

  G : Tr X₀ → Tr⁺ j
  G = FC.ψ X₀ o₂ (rbᶻ X₀) pv₂ (B₀ X₀) j w₂ ot₂ β

  br-form : ∀ c → brᵍ d c ≡ proj₁ (next⁺ β) + proj₁ (G (brΩ (proj₁ (Ωt X₀)) tt c))
  br-form c = refl
```

## 槽位

P₃: 孩子 3 的层号 h₁ 3 里的 h₁ 2 (与目标同层); P₁: 再下一层 h₁ 1 (低于目标). q′: 目标 h₁ 2 自己的槽位, 层号 h₁ 1. qf: 目标的地板槽位 (层号 zero).

```agda
P₁ P₃ : Pos (tw 1)
P₁ = inj₂ (n3 , inj₂ (inj₂ (tt , inj₂ (inj₂ (tt , inj₁ tt)))))
P₃ = inj₂ (n3 , inj₂ (inj₂ (tt , inj₁ tt)))

q′ qf : Pos (h₁ n2)
q′ = inj₂ (tt , inj₁ tt)
qf = inj₂ (tt , inj₂ (inj₂ (tt , inj₁ tt)))

at-P₁ : at (tw 1) P₁ ≡ h₁ n1
at-P₁ = refl

at-q′ : at (h₁ n2) q′ ≡ at (tw 1) P₁
at-q′ = refl

br-q′ : Br (h₁ n2) q′ ≡ Br (tw 1) P₁
br-q′ = refl

own-q′ : kp (h₁ n2) (proj₂ (Ok-tw 1) n2) q′ self ≡ just (q′ , (λ z → z) , refl)
own-q′ = refl
```

这一格对一切证据、一切来源表、孩子 3 里的一切路径都走链: `kpʳ` 落在 `(inj₂ _) (inc _ _)` 一行, 来源表只给 Ω 形状结点的下标槽位记条目, `org-at` 在 P₁ 上终于 `inj₁` (`org-P₁`), 层号非零, 地板不适用.

```agda
cell : ∀ o pv {j} (v : j ≤ h₁ n3) ot → IsNothing (kpᶜ (tw 1) o pv P₁ (inc n3 v) ot)
cell o pv v ot = tt

cell₃ : ∀ o pv {j} (v : j ≤ h₁ n3) ot → IsNothing (kpᶜ (tw 1) o pv P₃ (inc n3 v) ot)
cell₃ o pv v ot = tt

org-P₁ : ∀ {j} (T : Org j (tw 1)) → org-at j (tw 1) T (inj₂ P₁) ≡ nothing
org-P₁ T = refl

d0-cell : ∀ o pv (v₀ : h₁ n1 ≤ h₁ n2) ot
  → IsJust (kpᶜ (tw 1) o pv (inj₂ (n2 , inj₂ (inj₂ (tt , inj₂ (inj₂ (tt , inj₁ tt)))))) (inc n2 v₀) ot)
d0-cell o pv v₀ ot = tt
```

## 展开: `brᵍ 1 0` 到那次调用

名字同 `YiKFValue.At 1`. 每一步右边的参数逐字取自 `YiKFFold.ψ` 相应的行; L₁ 是 X₀ 的孩子 0 (`nd sS (λ _ → tw 1)`).

```agda
open At n1

t₀ : Tr (h₁ n2)
t₀ = proj₁ (G (brΩ (proj₁ (Ωt X₀)) tt zero))

E0 : brᵍ n1 zero ≡ proj₁ (next⁺ β) + t₀
E0 = br-form zero

L₁ : L
L₁ = nd sS (λ _ → tw 1)

o₁ : Ok L₁
o₁ = proj₂ o₂ zero
r₁ : Rb L₁
r₁ = proj₂ (rbᶻ X₀) zero
pv₁ : Pv L₁
pv₁ = proj₂ pv₂ zero
B₁ : Base L₁
B₁ i u = FC.ψ X₀ o₂ (rbᶻ X₀) pv₂ (B₀ X₀) i (inc zero u) (org-no i X₀) (B₀ X₀ i (inc zero u)) zero
ws₁ : j ≤ L₁
ws₁ = unU w₂ tt zero
ot₁ : Org j L₁
ot₁ = proj₂ ot₂ zero
β₁ : Tr⁺ j
β₁ = FC.ψ X₀ o₂ (rbᶻ X₀) pv₂ (B₀ X₀) j w₂ ot₂ β zero

E1 : G (brΩ (proj₁ (Ωt X₀)) tt zero) ≡ FC.ψ L₁ o₁ r₁ pv₁ B₁ j ws₁ ot₁ β₁ (proj₁ (Ωt L₁))
E1 = refl
```

L₁ 的结点 (槽位层号 tw 1, 高于目标) 走链; 链点进 tw 1, 路径 `inc 3 (inc tt self)`.

```agda
kp-L₁ : IsNothing (kpᶜ L₁ o₁ pv₁ (inj₂ (tt , inj₁ tt)) ws₁ ot₁)
kp-L₁ = tt

g₁ : Tr (tw 1) → Tr L₁
g₁ c = proj₁ (upz {s = sS} {h = λ _ → tw 1} tt (suc c , z◃ c ◃s))

s₁ : Tr (tw 1) → Tr (tw 1)
s₁ z = proj₁ (FC.ψ L₁ o₁ r₁ pv₁ B₁ (tw 1) (inc tt self) (org-no (tw 1) L₁) (B₁ (tw 1) (inc tt self)) (g₁ z))

Fch : ℕ → Tr⁺ j
Fch n = FC.ψ L₁ o₁ r₁ pv₁ B₁ j ws₁ ot₁ β₁ (g₁ (iter s₁ zero n))

E2 : FC.ψ L₁ o₁ r₁ pv₁ B₁ j ws₁ ot₁ β₁ (proj₁ (Ωt L₁)) ≡ limc⁺ Fch
E2 = refl

O : Ok (tw 1)
O = proj₂ o₁ tt
R : Rb (tw 1)
R = proj₂ r₁ tt
PV : Pv (tw 1)
PV = proj₂ pv₁ tt
Bt : Base (tw 1)
Bt i u = FC.ψ L₁ o₁ r₁ pv₁ B₁ i (inc tt u) (org-no i L₁) (B₁ i (inc tt u)) zero
v : j ≤ tw 1
v = unU ws₁ tt tt
OT : Org j (tw 1)
OT = proj₂ ot₁ tt
βt : Tr⁺ j
βt = FC.ψ L₁ o₁ r₁ pv₁ B₁ j ws₁ ot₁ β₁ zero

v-form : v ≡ inc n3 (inc tt self)
v-form = refl

E3 : ∀ z → FC.ψ L₁ o₁ r₁ pv₁ B₁ j ws₁ ot₁ β₁ (g₁ z) ≡ next⁺ (FC.ψ (tw 1) O R PV Bt j v OT βt z)
E3 z = refl

E4 : s₁ zero ≡ proj₁ (next⁺ (Ωt (tw 1)))
E4 = refl

E4′ : el (proj₁ (FC.ψ (tw 1) O R PV Bt j v OT βt (s₁ zero))) 0 ≡ proj₁ (FC.ψ (tw 1) O R PV Bt j v OT βt (proj₁ (Ωt (tw 1))))
E4′ = refl
```

tw 1 的顶结点 (层号 zero) 保留在地板 qf; 分支 3 在最小表里没有 (3,3) 的条目, 走上折回退 `ψˡ`.

```agda
kp-top : kpᶜ (tw 1) O PV (inj₁ (inj₁ tt)) v OT ≡ just (qf , (λ z → z) , refl)
kp-top = refl

E5 : FC.ψ (tw 1) O R PV Bt j v OT βt (proj₁ (Ωt (tw 1)))
   ≡ Ω⁺ qf (λ z → FC.ψ (tw 1) O R PV Bt j v OT βt (proj₁ (upz {s = sΩ zero} {h = h₁} z (Ωt (h₁ z)))))
E5 = refl

Xt : Base (tw 1)
Xt i u = FC.ψ (tw 1) O R PV Bt i u (org-no i (tw 1)) (Bt i u) zero

βt′ : Tr⁺ j
βt′ = FC.ψ (tw 1) O R PV Bt j v OT βt zero

tb33 : proj₁ R n3 n3 ≡ nothing
tb33 = refl

y₃ : Tr (tw 1)
y₃ = proj₁ (upz {s = sΩ zero} {h = h₁} n3 (Ωt (h₁ n3)))

E6 : FC.ψ (tw 1) O R PV Bt j v OT βt y₃ ≡ FC.ψˡ (tw 1) O PV Xt j v OT βt′ (h₁ n3) (down stop n3) (proj₁ (Ωt (h₁ n3)))
E6 = refl
```

Ωt (h₁ 3) 的结点搬到 P₃ (与目标同层) 走链, 回灌的目标与路径就是原目标与原路径; 链点下到 h₁ 2.

```agda
at-P₃ : at (tw 1) P₃ ≡ h₁ n2
at-P₃ = refl

posW-P₃ : posW (tw 1) P₃ ≡ inc n3 (inc tt self)
posW-P₃ = refl

kp-P₃ : kpᶜ (tw 1) O PV P₃ v OT ≡ nothing
kp-P₃ = refl

g₃ : Tr (h₁ n2) → Tr (h₁ n3)
g₃ c = proj₁ (upz {s = sS} {h = λ _ → h₁ n2} tt (suc c , z◃ c ◃s))

s₃ : Tr (h₁ n2) → Tr (h₁ n2)
s₃ z = proj₁ (FC.ψˡ (tw 1) O PV Xt (h₁ n2) (inc n3 (inc tt self)) (org-no (h₁ n2) (tw 1)) (Xt (h₁ n2) (inc n3 (inc tt self))) (h₁ n3) (down stop n3) (g₃ z))

F₃ : ℕ → Tr⁺ j
F₃ n = FC.ψˡ (tw 1) O PV Xt j v OT βt′ (h₁ n3) (down stop n3) (g₃ (iter s₃ zero n))

E7 : FC.ψˡ (tw 1) O PV Xt j v OT βt′ (h₁ n3) (down stop n3) (proj₁ (Ωt (h₁ n3))) ≡ limc⁺ F₃
E7 = refl

X₃ : Base (tw 1)
X₃ i u = FC.ψˡ (tw 1) O PV Xt i u (org-no i (tw 1)) (Xt i u) (h₁ n3) (down stop n3) zero

βt″ : Tr⁺ j
βt″ = FC.ψˡ (tw 1) O PV Xt j v OT βt′ (h₁ n3) (down stop n3) zero

E8 : ∀ z → FC.ψˡ (tw 1) O PV Xt j v OT βt′ (h₁ n3) (down stop n3) (g₃ z)
        ≡ next⁺ (FC.ψˡ (tw 1) O PV X₃ j v OT βt″ (h₁ n2) (down (down stop n3) tt) z)
E8 z = refl

E9 : s₃ zero ≡ proj₁ (next⁺ (Ωt (h₁ n2)))
E9 = refl

E9′ : el (proj₁ (FC.ψˡ (tw 1) O PV X₃ j v OT βt″ (h₁ n2) (down (down stop n3) tt) (s₃ zero))) 0
    ≡ proj₁ (FC.ψˡ (tw 1) O PV X₃ j v OT βt″ (h₁ n2) (down (down stop n3) tt) (proj₁ (Ωt (h₁ n2))))
E9′ = refl
```

Ωt (h₁ 2) 的结点搬到 P₁: 那次调用.

```agda
mv-P₁ : mv (down (down stop n3) tt) (inj₂ (tt , inj₁ tt)) ≡ P₁
mv-P₁ = refl

E10 : FC.ψˡ (tw 1) O PV X₃ j v OT βt″ (h₁ n2) (down (down stop n3) tt) (proj₁ (Ωt (h₁ n2)))
    ≡ node⁺ (kpᶜ (tw 1) O PV P₁ v OT)
        (λ z → FC.ψˡ (tw 1) O PV X₃ j v OT βt″ (h₁ n2) (down (down stop n3) tt) (proj₁ (upz {s = sS} {h = λ _ → h₁ n1} tt (suc z , z◃ z ◃s))))
        (λ z → proj₁ (FC.ψˡ (tw 1) O PV X₃ (h₁ n1) (posW (tw 1) P₁) (org-no (h₁ n1) (tw 1)) (X₃ (h₁ n1) (posW (tw 1) P₁))
                        (h₁ n2) (down (down stop n3) tt) (proj₁ (upz {s = sS} {h = λ _ → h₁ n1} tt (suc z , z◃ z ◃s)))))
E10 = refl

kp-P₁ : kpᶜ (tw 1) O PV P₁ v OT ≡ nothing
kp-P₁ = refl
```

## 输出上的探针

`pr t₀` 是保留在 qf 的结点; 它的分支 3 (`t₂`) 是 P₃ 的链; `pr t₂` 就是 `E10` 那次调用 (加前面的部分和), 是 ℕ 极限.

```agda
pos₀ : posΩ (pr t₀) tt ≡ qf
pos₀ = refl

t₂ : Tr (h₁ n2)
t₂ = brΩ (pr t₀) tt n3

old₃ : Tr (h₁ n2)
old₃ = proj₁ (FC.ψ (tw 1) O R PV Bt j v OT βt y₃)

t₂-call : t₂ ≡ proj₁ (Fch 0) + old₃
t₂-call = refl

probe-call : pr t₂ ≡ proj₁ (Fch 0) + (proj₁ (F₃ 0) + proj₁ (FC.ψˡ (tw 1) O PV X₃ j v OT βt″ (h₁ n2) (down (down stop n3) tt) (proj₁ (Ωt (h₁ n2)))))
probe-call = refl

hd₂ : HeadLim t₂
hd₂ = tt

hd₃ : HeadLim (pr t₂)
hd₃ = tt
```

## 只换比较表证据的对照

表 `R′` 只在孩子 (3,3) 多一个条目 `self`, 其余同最小表; 折叠与保留判定不变. 同一次折叠进孩子 3 如实折, 同一位置的探针保留在目标自己的槽位 q′.

```agda
tb′ : (c c′ : Tr zero) → Maybe ((h₁ c′ ≤ h₁ c) ⊎ (h₁ c ≤ h₁ c′))
tb′ (suc (suc (suc zero))) (suc (suc (suc zero))) = just (inj₁ self)
tb′ c c′ = tbᶻ zero h₁ c c′

R′ : Rb (tw 1)
R′ = tb′ , λ c → rbᶻ (h₁ c)

new₃ : Tr (h₁ n2)
new₃ = proj₁ (FC.ψ (tw 1) O R′ PV Bt j v OT βt y₃)

cf-old : HeadLim (pr old₃)
cf-old = tt

cf-new : HeadΩ (pr new₃)
cf-new = tt

cf-pos : posΩ (pr new₃) tt ≡ q′
cf-pos = refl
```
