# `YiCTCall` 那一格在 d = ωᵉ: 分支在 (z, ωᵉ+2) 上查表

> 判决: 编译定理 (形状档, `refl`) 与一条有限测试, 不读记号, 不改树、折叠、合法性. `YiCTCall` 的展开对一切孩子 d 成立, 路径恒经孩子 d+2 (`CellD.v-form`); d = ωᵉ 时被保留的顶结点的分支 z 在 (z, ωᵉ+2) 上查表 (`br-ω`, `row-ω`), 最小表在对角上没有条目 (`min-ω`); 塔第 1 项的任何表在这一对角上有条目就弱判等 (`cell→wdecα`), 加函数外延得 WLPO (`cell→wlpo`, 条件); 目标沿结构带着逐孩子的可缺路径时同样 (`cellP→wdecα`, `cellP→wlpo`; 有判定时前提可满足, `dec→pth`).
> d = 1 时现成的闭项表 `YiTBRow.tb` (两端都是字面数字才比较) 在这一格保留在 q′ (`tb-pos`, 有限测试), 与 `YiCTCall.cf-pos` 同.
> 不否定什么: 数字孩子上的整列填表, 换基, 别的保留判定. 来源: `CellD` 的定义与 `E0`–`E4` 取自 `YiCTCall` 第 137–205 行, `Y` 即第 230 行的 `y₃`, `n1` 换成变量 d, 名字加上标 ᵈ. 否定本身在 [YiDGDiag](YiDGDiag.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiDGCell where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiTBRow using (Rb; dW; tb)
open import OCF.Lean.YiTBTab using (ωᵉ)
open import OCF.Lean.YiMTTab using (rbᶻ; tbᶻ)
open import OCF.Lean.YiDXTest using (h₁; n2; HeadΩ)
open import OCF.Lean.YiAbsObs using (Dec′; IsJust; AllF; WLPO)
open import OCF.Lean.YiKFKeep
open import OCF.Lean.YiKFFold
open import OCF.Lean.YiKFTest using (pr)
open import OCF.Lean.YiCTCall using (module At; unU; brΩ; posΩ; brᵍ; O; PV; Bt; v; OT; βt; y₃; q′)
open import OCF.Lean.YiDGDiag using (cα; module Diag; FunextB; wlpo; back; pathA; peel)
```

## 对一切 d 的展开

```agda
module CellD (d : Tr zero) where
  open At d

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

  t₀ : Tr j
  t₀ = proj₁ (G (brΩ (proj₁ (Ωt X₀)) tt zero))

  E0 : brᵍ d zero ≡ proj₁ (next⁺ β) + t₀
  E0 = br-form zero

  E1 : G (brΩ (proj₁ (Ωt X₀)) tt zero) ≡ FC.ψ L₁ o₁ r₁ pv₁ B₁ j ws₁ ot₁ β₁ (proj₁ (Ωt L₁))
  E1 = refl

  Oᵈ : Ok (tw 1)
  Oᵈ = proj₂ o₁ tt
  Rᵈ : Rb (tw 1)
  Rᵈ = proj₂ r₁ tt
  PVᵈ : Pv (tw 1)
  PVᵈ = proj₂ pv₁ tt
  Btᵈ : Base (tw 1)
  Btᵈ i u = FC.ψ L₁ o₁ r₁ pv₁ B₁ i (inc tt u) (org-no i L₁) (B₁ i (inc tt u)) zero
  vᵈ : j ≤ tw 1
  vᵈ = unU ws₁ tt tt
  OTᵈ : Org j (tw 1)
  OTᵈ = proj₂ ot₁ tt
  βtᵈ : Tr⁺ j
  βtᵈ = FC.ψ L₁ o₁ r₁ pv₁ B₁ j ws₁ ot₁ β₁ zero

  v-form : vᵈ ≡ inc (suc (suc d)) (inc tt self)
  v-form = refl

  R-form : proj₁ Rᵈ ≡ tbᶻ zero h₁
  R-form = refl

  kp-top : IsJust (kpᶜ (tw 1) Oᵈ PVᵈ (inj₁ (inj₁ tt)) vᵈ OTᵈ)
  kp-top = tt

  g₁ : Tr (tw 1) → Tr L₁
  g₁ c = proj₁ (upz {s = sS} {h = λ _ → tw 1} tt (suc c , z◃ c ◃s))

  s₁ : Tr (tw 1) → Tr (tw 1)
  s₁ z = proj₁ (FC.ψ L₁ o₁ r₁ pv₁ B₁ (tw 1) (inc tt self) (org-no (tw 1) L₁) (B₁ (tw 1) (inc tt self)) (g₁ z))

  Fch : ℕ → Tr⁺ j
  Fch n = FC.ψ L₁ o₁ r₁ pv₁ B₁ j ws₁ ot₁ β₁ (g₁ (iter s₁ zero n))

  E2 : FC.ψ L₁ o₁ r₁ pv₁ B₁ j ws₁ ot₁ β₁ (proj₁ (Ωt L₁)) ≡ limc⁺ Fch
  E2 = refl

  E3 : ∀ z → FC.ψ L₁ o₁ r₁ pv₁ B₁ j ws₁ ot₁ β₁ (g₁ z) ≡ next⁺ (FC.ψ (tw 1) Oᵈ Rᵈ PVᵈ Btᵈ j vᵈ OTᵈ βtᵈ z)
  E3 z = refl

  E4 : s₁ zero ≡ proj₁ (next⁺ (Ωt (tw 1)))
  E4 = refl

  Y : Tr zero → Tr (tw 1)
  Y z = proj₁ (upz {s = sΩ zero} {h = h₁} z (Ωt (h₁ z)))

  hd₀ : HeadΩ (pr t₀)
  hd₀ = tt
```

## d = ωᵉ

保留结点的分支类型在 d = ωᵉ 时字面是 `Tr zero` (保留的槽位是 ωᵉ 层孩子 0 里层号 zero 的那一个); 分支 z 是那次 tw 1 上的折叠, 它在 (z, ωᵉ+2) 上查表. 换成任意表 `Rv`, 同一次调用查的是 `proj₁ Rv z (ωᵉ+2)`.

```agda
module Cω = CellD ωᵉ

br-ω : ∀ z → brΩ (pr Cω.t₀) Cω.hd₀ z
     ≡ proj₁ (Cω.Fch 0) + proj₁ (FC.ψ (tw 1) Cω.Oᵈ Cω.Rᵈ Cω.PVᵈ Cω.Btᵈ (h₁ (suc ωᵉ)) Cω.vᵈ Cω.OTᵈ Cω.βtᵈ (Cω.Y z))
br-ω z = refl

row-ω : ∀ (Rv : Rb (tw 1)) z → Σ _ λ F → Σ _ λ G → Σ _ λ H →
  FC.ψ (tw 1) Cω.Oᵈ Rv Cω.PVᵈ Cω.Btᵈ (h₁ (suc ωᵉ)) Cω.vᵈ Cω.OTᵈ Cω.βtᵈ (Cω.Y z) ≡ dW (proj₁ Rv z (suc (suc ωᵉ))) F G H
row-ω Rv z = _ , _ , _ , refl

min-ω : proj₁ Cω.Rᵈ (suc (suc ωᵉ)) (suc (suc ωᵉ)) ≡ nothing
min-ω = refl

cell→wdecα : (Rv : Rb (tw 1)) → IsJust (proj₁ Rv (suc (suc ωᵉ)) (suc (suc ωᵉ)))
  → ∀ α → AllF α ⊎ (_≡_ {A = Tr zero} (suc (suc ωᵉ)) (suc (suc (cα α))) → ⊥)
cell→wdecα Rv = Diag.wdecα (proj₁ Rv) 2

cell→wlpo : FunextB → (Rv : Rb (tw 1)) → IsJust (proj₁ Rv (suc (suc ωᵉ)) (suc (suc ωᵉ))) → WLPO
cell→wlpo fe Rv = wlpo fe (proj₁ Rv) 2
```

不经表: 目标 h₁ (ωᵉ+1) 若沿结构带着 "每个孩子一条可缺的路径" `o` (一致目标 `inu` 的可缺版本, 行就用 `o z`, 不比较下标), 要在对角孩子 ωᵉ+2 保留就要 `o (ωᵉ+2)` 有条目; 同样弱判等.

```agda
clash : ∀ {x} → h₁ ωᵉ ≡ h₁ (suc x) → ⊥
clash ()

unS : ∀ {b} (x : Tr zero) {j ℓ} → Pth b j ℓ → j ≡ h₁ ωᵉ → ℓ ≡ h₁ (suc x) → Pth b (h₁ ωᵉ) (h₁ x)
unS x self      e₁   e₂   = ⊥-elim (clash (trans (sym e₁) e₂))
unS x (inc c v) refl refl = v
unS x (inu vs)  refl refl = vs tt
unS x (ink v)   e₁   ()

cellP→wdecα : (o : (c : Tr zero) → Maybe (h₁ (suc ωᵉ) ≤ h₁ c)) → IsJust (o (suc (suc ωᵉ)))
  → ∀ α → AllF α ⊎ (_≡_ {A = Tr zero} (suc (suc ωᵉ)) (suc (suc (cα α))) → ⊥)
cellP→wdecα o j α = go (o (suc (suc (cα α)))) refl
  where
  go : (u : Maybe (h₁ (suc ωᵉ) ≤ h₁ (suc (suc (cα α))))) → o (suc (suc (cα α))) ≡ u
     → AllF α ⊎ (_≡_ {A = Tr zero} (suc (suc ωᵉ)) (suc (suc (cα α))) → ⊥)
  go (just p) q = inj₁ (pathA α (unS (cα α) (peel (suc (cα α)) ωᵉ p refl refl) refl refl) refl refl)
  go nothing  q = inj₂ (λ e → subst IsJust q (subst (λ c → IsJust (o c)) e j))

cellP→wlpo : FunextB → (o : (c : Tr zero) → Maybe (h₁ (suc ωᵉ) ≤ h₁ c)) → IsJust (o (suc (suc ωᵉ))) → WLPO
cellP→wlpo fe o j α with cellP→wdecα o j α
... | inj₁ af = inj₁ af
... | inj₂ ne = inj₂ (λ af → ne (back fe 2 α af))
```

前提可满足 (相对判定): 能判定 "孩子字面是 ωᵉ+2", 就有在对角上有条目的 `o`.

```agda
module _ (D : (c : Tr zero) → Dec′ (_≡_ {A = Tr zero} (suc (suc ωᵉ)) c)) where
  mkP : ∀ {c} → Dec′ (_≡_ {A = Tr zero} (suc (suc ωᵉ)) c) → Maybe (h₁ (suc ωᵉ) ≤ h₁ c)
  mkP (inj₁ e) = just (subst (λ z → h₁ (suc ωᵉ) ≤ h₁ z) e (inc tt self))
  mkP (inj₂ _) = nothing

  oD : (c : Tr zero) → Maybe (h₁ (suc ωᵉ) ≤ h₁ c)
  oD c = mkP (D c)

  isjP : (u : Dec′ (_≡_ {A = Tr zero} (suc (suc ωᵉ)) (suc (suc ωᵉ)))) → IsJust (mkP u)
  isjP (inj₁ e)  = tt
  isjP (inj₂ ne) = ⊥-elim (ne refl)

  dec→pth : IsJust (oD (suc (suc ωᵉ)))
  dec→pth = isjP (D (suc (suc ωᵉ)))
```

## d = 1: 现成的数字表 (有限测试)

```agda
Rᵗ : Rb (tw 1)
Rᵗ = tb , λ c → rbᶻ (h₁ c)

newᵗ : Tr (h₁ n2)
newᵗ = proj₁ (FC.ψ (tw 1) O Rᵗ PV Bt (h₁ n2) v OT βt y₃)

tb-hd : HeadΩ (pr newᵗ)
tb-hd = tt

tb-pos : posΩ (pr newᵗ) tt ≡ q′
tb-pos = refl
```
