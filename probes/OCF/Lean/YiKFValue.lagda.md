# 候选折叠 (A)+(B)+(C) 的值: 一点上的定理与链步第 1 项的归约

> 验收文件 (读记号), 不进成品; 树、折叠、合法性不改. 编译定理: `YiTFTw1` 那一点上候选的输出承载 ψ₁(Ω₁) (`out-abc`, 证明用 `YiDXValue.node-ab`); 对一切 d, 同步对象孩子 `a₁ (d+2)` 顶槽位回灌 Ω 树分支的输出 `outᶜ d` 里有一个保留在 `qᵍ d` 上的 Ω 结点, 分支的形状是 `br-form`.
> 条件定理 (`top`, 对一切 d 与一切参照 t): `cof t ≡ cΩ κ`, `h₁ d` 读作 κ, 且每个分支承载 `t[η]` (`Branch`), 则 `outᶜ d` 承载 t. 实例 `cand₁` (d = 0, t = ψ₁(Ω_{Ω₁}), 即 `YiKTSlot.Cand` 的参照) 与 `cand₂` (d = 1, t = ψ₂(Ω_{Ω₂})). `Branch` 未判定.
> 不否定什么. 底是标准底 `B₀`, 不是 `YiKTSlot.Cand` 用的继承底; 对象取自 `YiDXTest` (与 `YiSYReduce` 的同名对象逐字相同). 入口: `top`, `br-form`, `out-abc`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiKFValue where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiTBRow using (Rb)
open import OCF.Lean.YiMTTab using (rbᶻ)
open import OCF.Lean.YiDXTest using (h₁; a₁; hh; oᵈ; n1; c₂; p₁; el; HeadΩ; HeadLim)
open import OCF.Lean.YiDXValue using (lv1; γ₁; q₁; node-ab)
open import OCF.Lean.YiKFKeep
open import OCF.Lean.YiKFFold
open import OCF.Lean.YiKFTest
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiGIRel as GR
import OCF.Align.EboLeanDef as E
```

## `YiTFTw1` 那一点

与 `YiDXValue.Inst` 同形: 退路把孩子 2 的树上折后, 结点在第 1 层的地板槽位保留, 第 c 个分支是 `next⁺ (Φ c)`.

```agda
module Inst where
  o₁ : Ok (tw 1)
  o₁ = Ok-tw 1

  j₁ : L
  j₁ = at (tw 1) p₁

  w₁ : j₁ ≤ tw 1
  w₁ = posW (tw 1) p₁

  β₁ : Tr⁺ j₁
  β₁ = B₀ (tw 1) j₁ w₁

  d₁ : Dn (tw 1) (h₁ n1)
  d₁ = down (down stop c₂) tt

  X X₁ X₂ : Base (tw 1)
  X  i u = FC.ψ (tw 1) o₁ (rbᶻ (tw 1)) (pvT 1) (B₀ (tw 1)) i u (org-no i (tw 1)) (B₀ (tw 1) i u) zero
  X₁ i u = FC.ψˡ (tw 1) o₁ (pvT 1) X i u (org-no i (tw 1)) (X i u) (h₁ c₂) (down stop c₂) zero
  X₂ i u = FC.ψˡ (tw 1) o₁ (pvT 1) X₁ i u (org-no i (tw 1)) (X₁ i u) (h₁ n1) d₁ zero

  Φ : Tr zero → Tr⁺ lv1
  Φ c = FC.ψˡ (tw 1) o₁ (pvT 1) X₂ j₁ w₁ (org-no j₁ (tw 1)) β₁ zero (down d₁ tt) c

  shape : out₁ᶜ ≡ proj₁ (next⁺ (Ω⁺ {S = Sig lv1} q₁ (λ c → next⁺ (Φ c))))
  shape = refl

out-abc : GR.R lv1 γ₁ out₁ᶜ
out-abc = subst (GR.R lv1 γ₁) (sym Inst.shape)
  (node-ab Inst.Φ refl (λ c → refl)
    (FC.monoˡ (tw 1) Inst.o₁ (pvT 1) Inst.X₂ Inst.j₁ Inst.w₁ (org-no Inst.j₁ (tw 1)) Inst.β₁ zero (down Inst.d₁ tt)))
```

## 链步第 1 项里保留的结点

`pr (outᶜ d)` (第 1 个部分和里第 1 个链点的折叠) 对变量 d 起头是 Ω 结点, 槽位是 `qᵍ d`; `pr t ◃ t` 沿三层 ℕ 极限.

```agda
posΩ : ∀ {S} (t : T S) → HeadΩ t → P S
posΩ (Ω p g) _ = p

brΩ : ∀ {S} (t : T S) (hd : HeadΩ t) → B S (posΩ t hd) → T S
brΩ (Ω p g) _ = g

eqΩ : ∀ {S} (t : T S) (hd : HeadΩ t) → Ω (posΩ t hd) (brΩ t hd) ≡ t
eqΩ (Ω p g) _ = refl

el◃ : ∀ {S} (t : T S) → HeadLim t → ∀ n → Lt S (el t n) t
el◃ (lim f a) _ n = ◃l n

hdᵍ : ∀ d → HeadΩ (pr (outᶜ d))
hdᵍ d = tt

posᵍ : ∀ d → posΩ (pr (outᶜ d)) (hdᵍ d) ≡ qᵍ d
posᵍ d = refl

brᵍ : (d : Tr zero) → Tr (h₁ d) → Tr (h₁ (suc d))
brᵍ d = brΩ (pr (outᶜ d)) (hdᵍ d)

pr◃ : ∀ d → h₁ (suc d) ⊢ pr (outᶜ d) ◃ outᶜ d
pr◃ d = ◃t (el◃ (el (el (outᶜ d) 1) 0) tt 0) (◃t (el◃ (el (outᶜ d) 1) tt 0) (el◃ (outᶜ d) tt 1))
```

分支的形状: 第 0 个链点的折叠 `next⁺ β` 加上孩子层 `X₀` (下标层为 `h₁ d` 的 Ω 形状, 即 `tw 1 ⊕ ↑ z`) 上朝 `h₁ (d+1)` 的折叠, 折的是 `X₀` 的 Ω 树的第 c 个分支. 来源表 `ot₂` 是 `ink` 行生成的那一张在孩子里的分量.

```agda
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

## 条件定理

`Branch d t`: 下标层 `h₁ d` 的树 c 承载 η 时, 第 c 个分支承载 `t[η]`. 结论只用 `mΩ` 一条与 `pr◃`.

```agda
Branch : (d : Tr zero) → E.T → Set
Branch d t = ∀ η c → GR.R (h₁ d) η c → GR.R (h₁ (suc d)) (E.fsT t η) (brᵍ d c)

top : ∀ d {t κ} → E.cof t ≡ E.cΩ κ → GR.Rd (h₁ d) κ → Branch d t → GR.R (h₁ (suc d)) t (outᶜ d)
top d e rd bh = H.mw (subst (GR.R (h₁ (suc d)) _) (eqΩ (pr (outᶜ d)) (hdᵍ d)) (H.mΩ e rd bh)) (pr◃ d)
```

实例. d = 0: κ = 0, t = ψ₁(Ω_{Ω₁}) (`YiKTSlot.Cand` 的参照, 共尾度 Ω₁). d = 1: κ = 1, t = ψ₂(Ω_{Ω₂}).

```agda
κ₁ κ₂ t₁ t₂ : E.T
κ₁ = E.𝟏 ∷ []
κ₂ = E.sucT κ₁
t₁ = E.ψ κ₁ (E.Ωt (E.Ωt κ₁)) ∷ []
t₂ = E.ψ κ₂ (E.Ωt (E.Ωt κ₂)) ∷ []

cand₁ : Branch zero t₁ → GR.R (h₁ n1) t₁ (outᶜ zero)
cand₁ = top zero {t = t₁} {κ = []} refl (GR.c0 refl)

cand₂ : Branch n1 t₂ → GR.R (h₁ (suc n1)) t₂ (outᶜ n1)
cand₂ = top n1 {t = t₂} {κ = κ₁} refl (GR.ca (inj₂ (refl , GR.c0 refl)))
```
