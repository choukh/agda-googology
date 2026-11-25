# 限在读回域推导上的链步: 陈述, 与宽量化接口的关系, d = 1 归到 `Cand`
验收文件 (读记号); 编译定理: `StepDom` 只对 `Dom` 的 `dN` 推导量化, 分支取 Ω 树的实际分支, 源关系由推导给出 (`src`); `dom-a₁` (前缀 tw 1 读空, a₁ (d+1) 读作 Ω_{κ+1}); `wide→dom` (`TightStep d` 加 `OK`、`PrefixU … []` 推出限制版); `dom→cand : TightDom 1 → YiKTSlot.Cand` (n = 0 的实例就是 `Cand`); `kp*ᵍ`、`kp₀ᵍ` (对一切 d ≥ 1, 把 YiKT 的有限测试升为定理: 实际证据下 ↑z 顶结点的下标槽位走链, 同一孩子里前缀 tw 1 的下标槽位保留); `start-form` (对一切 d, 链步折叠的起点是 `h₁ d` 的 Ω 树加两段可数尾巴).
判决: 第 0 步完成, 第 1 步未走通. 判断 (未编译): `Cand` 不成立; d ≥ 2 时 n = 0 的实例按大小不成立. 本件不否定 `StepDom`, `refute` 只把否定归到一棵树的读法上界.
入口: `TightDom`, `dom→cand`, `refute`, `kp*ᵍ`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiRQDom where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; kp)
open import OCF.Lean.YiTBRow using (Rb; ψ; ψ₀ʳ)
open import OCF.Lean.YiMTTab using (rbᶻ)
open import OCF.Lean.YiLKIface using (OK) renaming (feed to feedᴸ)
open import OCF.Lean.YiSUIface using (PrefixU)
open import OCF.Lean.YiSYReduce using (a₁; h₁; oᴱ; Bᴱ)
open import OCF.Lean.YiTLReduce using (TightStep; hh)
open import OCF.Lean.YiGLDom using (Dom; dz; dC; dN; dom-top; dom-rd)
open import OCF.Lean.YiNLCtx using (prefix)
open import OCF.Lean.YiNLRaise using (ΩΩ; fsΩΩ)
open import OCF.Lean.YiGTGen using (weakᴿ)
open import OCF.Lean.YiKTSlot using (IsNothing; IsJust)
open import OCF.Align.JiaAuditClosure using (cof-regular; fs-regular)
open import OCF.Align.EboLeanBase using (<ᵀ-irrefl)
import OCF.Lean.YiKTSlot as KT
import OCF.Lean.YiTFTight as TF
import OCF.Lean.YiTFTw1 as TW
import OCF.Lean.YiSYDesc as D
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiGIRel as GR
import OCF.Align.EboLeanDef as E
```

## 陈述

Ω 形状层号 `nd (sΩ k) h` 由 `dN` 进入读回域: 下标层读作 κ, 层号读作 ν (`cof ν ≡ cΩ κ`), 每个带关系证据的孩子 c 读作 ν[η]. 分支固定为 Ω 树的实际分支 `gΩ`, 它的源关系由孩子的推导给出 (`src`), 所以不作前提. 前缀 t 取空 (`deriv-at`、`FromPres` 用的也是空前缀), 链的参照是 `γT (Ωt ν) κ`.

```agda
module Step (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h)) (r : Rb (nd (sΩ k) h)) (B : Base (nd (sΩ k) h)) where
  gΩ : Tr k → Tr (nd (sΩ k) h)
  gΩ c = proj₁ (upz {s = sΩ k} {h = h} c (Ωt (h c)))

  fd : Tr k → Tr k
  fd = feedᴸ (nd (sΩ k) h) o r B (inj₁ (inj₁ tt)) gΩ

  src : ∀ {μ c} → Dom (h c) μ → GR.R (nd (sΩ k) h) (E.Ωt μ) (gΩ c)
  src D = H.mU {t = []} H.mz (dom-top D)

  StepDom : Set
  StepDom = ∀ {κ ν} → Dom k κ → E.cof ν ≡ E.cΩ κ → (∀ η c → GR.R k η c → Dom (h c) (E.fsT ν η))
    → (n : ℕ) (z : Tr k) → GR.R k (E.γT (E.Ωt ν) κ n) z → GR.R k (E.γT (E.Ωt ν) κ (suc n)) (fd z)

module Sᵈ (d : Tr zero) = Step (h₁ d) (hh d) (proj₂ oᴱ (suc d)) (rbᶻ (a₁ (suc d))) (D.dn Bᴱ (suc d))

TightDom : Tr zero → Set
TightDom d = Sᵈ.StepDom d
```

宽量化的 `TightStep d` 对任意分支 g 与 g 上任意的关系证据量化; 限制版是它在实际分支上的实例 (`wide→dom`). `YiTFTw1.no-stepU′-tw1` 与 `YiTFTight.no-tight′` 用的分支 `g₁`、`gT` 是把孩子树直接嵌进 tw 1 叶子的孩子, 不是 Ω 树的分支 (`not-gT`); `TightDom` 也没有 `PrefixU` 前提, `YiTFTight.vacuous` 的空真机制不适用.

```agda
wide→dom : ∀ d → TightStep d → OK (D.dn Bᴱ (suc d)) → PrefixU (D.dn Bᴱ (suc d)) [] → TightDom d
wide→dom d ts gb pf {κ} {ν} Dk e f n z rz =
  ts gb [] pf (E.Ωt ν) κ (dom-rd Dk) (ΩΩ ν e) (Sᵈ.gΩ d) n z rz
    (subst (λ t → GR.R (a₁ (suc d)) t (Sᵈ.gΩ d z)) (sym (fsΩΩ ν _ e)) (Sᵈ.src d (f _ z rz)))

isΩ : ∀ {S} → T S → Set
isΩ (Ω _ _) = ⊤
isΩ _ = ⊥

inner : ∀ {s h} → Tr (nd s h) → Set
inner (up _ _ y _) = isΩ y
inner _ = ⊥

not-gT : TF.gT TW.cΩ₁ ≡ Sᵈ.gΩ (suc zero) TW.cΩ₁ → ⊥
not-gT e = subst inner (sym e) tt
```

## 读回域里的推导与可满足

前缀 tw 1 取空读法 `dz`; 孩子 `hh d c` 的读法全由 ↑c 一侧承载 (`dom-hh`), 写法照 `YiKTSlot.top-hh`. a₁ (d+1) 由 `dN` 读作 Ω_{κ+1} (`dom-a₁`).

```agda
dom-h₁ : ∀ {κ d} → GR.R zero κ d → Dom (h₁ d) κ
dom-h₁ {κ} {d} r = dC (prefix zero) zero {t = []} {ν = κ} {y = d} (dz zero) r

dom-hh : ∀ d {η c} → GR.R (h₁ d) η c → Dom (hh d c) η
dom-hh d {η} {c} r = dC (prefix (tw 1)) (tw 1) {t = []} {ν = η}
  {y = proj₁ (upz {s = sΩ zero} {h = h₁} (suc d) (upz {s = sS} {h = λ _ → h₁ d} tt (suc c , z◃ c ◃s)))} (dz (tw 1))
  (H.mU {t = []} H.mz (H.mU {t = []} H.mz (weakᴿ (h₁ d) r ◃s)))

dom-f : ∀ d κ η c → GR.R (h₁ d) η c → Dom (hh d c) (E.fsT (E.Ωs κ) η)
dom-f d κ η c r = subst (Dom (hh d c)) (sym (fs-regular κ η)) (dom-hh d r)

dom-a₁ : ∀ {κ d} → GR.R zero κ d → Dom (a₁ (suc d)) (E.Ωs κ)
dom-a₁ {κ} {d} r = dN (hh d) (dom-h₁ r) (cof-regular κ) (dom-f d κ)
```

n = 0、z 取下标层的 Ω 树: 对一切 d 前提都实填 (`dom→top`). d = 1、κ = 1 时结论逐字是 `YiKTSlot.Cand` (`top→cand` 是恒等).

```agda
Top₁ : (d : Tr zero) → E.T → Set
Top₁ d κ = GR.R (h₁ d) (E.γT (E.Ωt (E.Ωs κ)) κ 1) (Sᵈ.fd d (proj₁ (Ωt (h₁ d))))

dom→top : ∀ d {κ} → GR.R zero κ d → TightDom d → Top₁ d κ
dom→top d {κ} r td = td (dom-h₁ r) (cof-regular κ) (dom-f d κ) 0 (proj₁ (Ωt (h₁ d))) (dom-top (dom-h₁ r))

r₁ : GR.R zero KT.κ* (suc zero)
r₁ = H.m1 refl H.mz

top→cand : Top₁ (suc zero) KT.κ* → KT.Cand
top→cand c = c

dom→cand : TightDom (suc zero) → KT.Cand
dom→cand td = td (dom-h₁ r₁) (cof-regular KT.κ*) (dom-f (suc zero) KT.κ*) 0 KT.z* KT.hyp₁
```

## 否定归到一棵树的读法上界

`Refute d κ`: 上面那一棵树的每个下界读法都低于链的第 1 项. 它成立则 `TightDom d` 不成立. 前提可满足与否是判断 (见回报), 本件不证.

```agda
Refute : (d : Tr zero) → E.T → Set
Refute d κ = ∀ {t} → GR.R (h₁ d) t (Sᵈ.fd d (proj₁ (Ωt (h₁ d)))) → t E.<ᵀ E.γT (E.Ωt (E.Ωs κ)) κ 1

refute : ∀ d {κ} → GR.R zero κ d → Refute d κ → TightDom d → ⊥
refute d r ub td = <ᵀ-irrefl (ub (dom→top d r td))
```

## 机制: 一切 d ≥ 1 上的两个槽位

孩子 z = Ω_{h₁(d+1)} 里, ↑z 的顶结点是下标层 `h₁ d` 的 Ω 形状; 它的下标槽位经层号证据推进前缀 tw 1 叶子的孩子 d+2, 朝 `h₁ (d+1)` 折时落在 `kp` 的 "Ω 形状、槽位在孩子里、路径经 `inc`" 一行 (`kp*ᵍ`); 同一孩子里前缀 tw 1 自己的下标槽位保留 (`kp₀ᵍ`). d = 0 即 `YiKTSlot.kp*`、`kp₀`. 按定义计算, 对变量 d 成立.

```agda
zᵍ : (d : Tr zero) → Tr (h₁ (suc d))
zᵍ d = proj₁ (Ωt (h₁ (suc d)))

p*ᵍ p₀ᵍ : (d : Tr zero) → Pos (a₁ (suc (suc d)))
p*ᵍ d = inj₂ (zᵍ d , inj₂ (inj₂ (tt , inj₂ (inj₁ (inj₁ tt)))))
p₀ᵍ d = inj₂ (zᵍ d , inj₂ (inj₂ (tt , inj₂ (inj₂ (zero , inj₂ (inj₂ (tt , inj₂ (inj₁ (inj₁ tt)))))))))

kp*ᵍ : ∀ d → IsNothing (kp (a₁ (suc (suc d))) (proj₂ oᴱ (suc (suc d))) (p*ᵍ d) (ink self))
kp*ᵍ d = tt

kp₀ᵍ : ∀ d → IsJust (kp (a₁ (suc (suc d))) (proj₂ oᴱ (suc (suc d))) (p₀ᵍ d) (ink self))
kp₀ᵍ d = tt
```

`fd` 里折到 `h₁ d` 的起点 (继承底在 `h₁ d` 处的值) 对一切 d 是 `h₁ d` 的 Ω 树加两段可数尾巴; `TF.Y₂` 就是 `twᶻ 1` (`YiTFTight.Y₂-tw`). d = 1 即 `YiTFTight.β-form`.

```agda
start-form : ∀ d → proj₁ (D.dn Bᴱ (suc d) (h₁ d) (ink self)) ≡ proj₁ ((Ωt (h₁ d) ⊞ TF.Y₁) ⊞ TF.Y₂)
start-form d = refl
```

YiTF 的补偿要经前缀 tw 1 下标槽位结点的分支 c, 那里装的是孩子 c 的内容. 朝 tw 1 的孩子 c′ 折时, 孩子 c 里的槽位一律走链 (`drop`, c = c′ 也是); c ≠ 0 的嵌入在最小表下只留可数尾巴 (`fall`, c = c′ 也是). 两条都是按定义的行.

```agda
drop : ∀ (o : Ok (tw 1)) c t c′ {j} (v : j ≤ h₁ c′) → IsNothing (kp (tw 1) o (inj₂ (c , t)) (inc c′ v))
drop o c t c′ v = tt

fall : ∀ (o : Ok (tw 1)) (B : Base (tw 1)) c′ c {j} (v : j ≤ h₁ (suc c′)) β x (y : Tr (h₁ (suc c))) e
  → ψ (tw 1) o (rbᶻ (tw 1)) B j (inc (suc c′) v) β (up x (suc c) y e)
  ≡ ψ (tw 1) o (rbᶻ (tw 1)) B j (inc (suc c′) v) β x ⊞ ψ₀ʳ (h₁ (suc c)) (proj₂ o (suc c)) (rbᶻ (h₁ (suc c))) y
fall o B c′ c v β x y e = refl
```
