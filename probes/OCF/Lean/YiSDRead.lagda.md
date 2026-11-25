# 替身支配原材料在 EBO 参照上的读回形式

> 验收文件 (读记号). 判决: 编译定理, 无前提 (`lowΩᵗ` 是条件定理). 对一切层号 k, j 与孩子 c: c 的每个读法 η 给出替身层号 `j ⊕ ↑ k c` 的 Ω 树的参照 Ω_η (`sub-read`), j 有域内读法 t 时给出 Ω_{t++η} (`top-read`); 于是塔每一项上带盖的支配 `cap-domᵗ` 与 `Hand₁` (`hand₁ᵗ`) 成立, 不按站分.
> 可疑的一格 (c = ω, 目标 `h₁ 1`): 读回形式成立 (`cell-read`, `cell-cap`); 第 0 个孩子上一般参照的抬高成立 (`raise₀`); 一般参照的陈述 `CellRaise` 没有证也没有否定.
> 不给出什么: `SubDom` 对一般参照未走通; `lowΩᵗ` 的前提 (辅助系统上的保持, 上下文保持余尾 Ω 并与代入交换, 槽位允许余尾) 没有实填. 来源: `sub-read` 是 `YiNLRaise.raiseR` 取前缀上下文的实例 (同 `YiNLCanonical.reg-top` 的写法). 接口见 [YiSDIface](YiSDIface.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSDRead where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import OCF.Lean.YiRWBlock hiding (R)
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
open import OCF.Lean.YiRWFold using (Base)
open import OCF.Lean.YiBSBase using (route)
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiKVRel as KV
import OCF.Align.EboLeanDef as E
open import OCF.Align.EboLeanBase using (_≤ᵀ_)
open import OCF.Align.JiaAuditClosure using (cof-regular; fs-regular)
open import OCF.Lean.YiAbsSimInst using (𝕍)
open import OCF.Lean.YiAbsGEbo using (refᴱ)
open import OCF.Lean.YiAbsGIface
open import OCF.Lean.YiGIBlock using (blkᵍ)
open import OCF.Lean.YiFIGen using (low→)
open import OCF.Lean.YiNLCtx using (Top; prefix; app≤)
open import OCF.Lean.YiNLRaise using (raiseR; fsΩΩ)
open import OCF.Lean.YiNLCanonical using (one-top)
open import OCF.Lean.YiBLFold using (foldᴮ; rowsᴮ; Bsᴮ; Sₙ; rcₙ; route-tw1; module Aux; module Main)
open import OCF.Lean.YiQDFold using (kept-tw1)
open import OCF.Lean.YiVALeaf using (nzs)
open import OCF.Lean.YiTBRow using (h₁; nat)
open import OCF.Lean.YiGLDom using (Dom; dom-rd; dom-top; dom-fin)
open import OCF.Lean.YiSDIface
```

## 换基折叠上的分级结构

各字段照 `YiFIGen.gradedᴷ` (关系是主线的 `YiGIRel.R`), 只把折叠换成 `foldᴮ`; `Bdˢ` 照 `YiGIInst.Bdᵍ`. 下面只用到关系, `Weak`, `Node`.

```agda
Bdˢ : ∀ {ℓ j} → Bsᴮ ℓ → j P.≤ ℓ → O.Tr⁺ j → E.T → Set
Bdˢ {ℓ} {j} (o , r , b) w β t₀ = GR.R j (E.ψ [] t₀ ∷ []) (proj₁ β) × (∀ i u → proj₁ (O.Ωt i) KV.⊴ proj₁ (b i u))

gradedˢ : Graded blkᵍ foldᴮ rowsᴮ refᴱ 𝕍
gradedˢ = record
  { ℓ₀ = zero ; v = KV.readRW ; R = GR.R ; Rd = GR.Rd ; Nu = GR.Nu ; bt = proj₁
  ; cl = λ _ t → E.ψ [] t ∷ [] ; Cx = λ _ _ → E.T ; app = λ t₀ a → E.ψ [] (t₀ ++ a) ∷ [] ; Bd = Bdˢ }

domsˢ : Doms blkᵍ foldᴮ
domsˢ = record { Gx = λ ℓ x → x ≡ proj₁ (O.Ωt ℓ) ; Gb = λ _ _ → ⊤ ; Wl = λ _ → ⊤ ; Gl = λ k x → x ≡ proj₁ (O.Ωt k) }

weakˢ : Laws.Weak gradedˢ domsˢ
weakˢ {ℓ = zero}   = H.mw
weakˢ {ℓ = nd s h} = H.mw

nodeˢ : Laws.Node gradedˢ domsˢ
nodeˢ {ℓ = nd s h} p g e nu hyp = H.mΩ e nu (λ η c l → hyp η c (low→ (nd s h) p l))
```

## 读回形式: 对一切层号

`sub-read` 不用地板 ≤ j, 也不看 c 的形状; 给出的参照是 Ω_η (把 j 读成空). `top-read` 用 j 的一个读法 t 给出 Ω_{t++η}. `fs-top`: 正则的 Ω_{μ+1} 套一层 Ω 之后, 代入 η 得 Ω_η.

```agda
sub-read : ∀ k j (c : Tr k) {η} → GR.R k η c → Top (j ⊕ ↑ k c) η
sub-read k j c r = raiseR k (prefix j) [] (GR.c0 refl) (one-top j) r

top-read : ∀ k j {t} → GR.Rd j t → Top j t → (c : Tr k) → ∀ {η} → GR.R k η c → Top (j ⊕ ↑ k c) (t ++ η)
top-read k j {t} qa lf c r = raiseR k (prefix j) t qa lf r

fs-top : ∀ μ η → E.fsT (E.Ωt (E.Ωs μ)) η ≡ E.Ωt η
fs-top μ η = trans (fsΩΩ (E.Ωs μ) η (cof-regular μ)) (cong E.Ωt (fs-regular μ η))
```

## 塔各项

参数同 `YiBLFold.Tower`. 上下文取前缀上下文 `(ν , P) ↦ ψ_ν(P ++ t)`, Le 取项序 `≤ᵀ`. 孩子 c 的读法: `R (tw n) η c`.

```agda
module Tw (n : ℕ) (B : Base (tw (suc n))) (j : L) (c′ : Tr (tw n)) (v : j P.≤ tw n ⊕ ↑ (tw n) c′) (u : tw n P.≤ j)
    (eq : route (Sₙ n) j c′ v ≡ inj₂ u) where
  open Prefix gradedˢ domsˢ (tw n) (λ c → tw n ⊕ ↑ (tw n) c) (P.Ok-tw (suc n)) (Sₙ n) (rcₙ n) B j c′ v u eq
    E.T (λ ν s → E.ψ ν s ∷ []) ++-assoc public
  open Split _≤ᵀ_ weakˢ public
  open SubstDom _≤ᵀ_ weakˢ public using (Hand₁; SubDom)
  open Aux j
  open Main (tw n) (λ c → tw n ⊕ ↑ (tw n) c) (P.Ok-tw (suc n)) (Sₙ n) (rcₙ n) B j c′ v u eq

  ρ : Tr (tw n) → E.T → Set
  ρ c η = GR.R (tw n) η c

  sub-readᵗ : SubRead ρ E.Ωt
  sub-readᵗ c r = sub-read (tw n) j c r

  sub-read⁺ : ∀ {t} → Dom j t → SubRead ρ (λ η → E.Ωt (t ++ η))
  sub-read⁺ D c r = top-read (tw n) j (dom-rd D) (dom-top D) c r

  cap-domᵗ : CapDom ρ E.Ωt
  cap-domᵗ = read→cap app≤ sub-readᵗ

  hand₁ᵗ : Hand₁
  hand₁ᵗ = hand₁ _≤ᵀ_ weakˢ
```

Ω 树上的保持: 参照取 Ω_{Ω_{μ+1}} (μ 任意, 塔的读法是 μ = κ n). 前提是辅助系统上的保持与顶槽位的三项 (上下文保持余尾 Ω, 与代入交换, 槽位允许 κ); 嵌入一行只用 `sub-readᵗ`.

```agda
  module _ (auxK : ∀ {b} (s′ : Stᴬ b) K″ → Bdᴬᵖ s′ K″ → ∀ {t x} → GR.R b t x → GR.R j (apᵖ K″ t) (proj₁ (Φᴬ s′ x))) where
    lowΩᵗ : ∀ μ (β : O.Tr⁺ j) (K : Cxtᵖ) → Bdᴮᵖ (rt β) K → (ev : Kept (inj₁ (inj₁ tt))) {κ : E.T}
      → E.cof (apᵖ K (E.Ωt (E.Ωs μ))) ≡ E.cΩ κ → GR.Nu j (proj₁ ev) κ
      → (∀ η → E.fsT (apᵖ K (E.Ωt (E.Ωs μ))) η ≡ apᵖ K (E.fsT (E.Ωt (E.Ωs μ)) η))
      → GR.R j (apᵖ K (E.Ωt (E.Ωs μ))) (proj₁ (Φᴮ (rt β) (proj₁ (O.Ωt (tw (suc n))))))
    lowΩᵗ μ β K bd ev cΩ nu fs = lowΩᵖ _≤ᵀ_ weakˢ nodeˢ auxK sub-readᵗ β K bd ev cΩ nu
      (λ η → trans (cong (apᵖ K) (sym (fs-top μ η))) (sym (fs η)))
```

## 可疑的一格: c = ω, 目标 `h₁ 1`

孩子层号 `h₁ ω` 与替身层号 `h₁ 1 ⊕ ↑ω` 结构不同. `CellRaise` 是 `YiQDFold.raise→SubDom` 的前提在这一格上的陈述 (一般参照 s).

```agda
ω⁰ : Tr zero
ω⁰ = lim nat (λ _ → ◃s)

CellRaise : Set
CellRaise = ∀ {s} → GR.R (h₁ ω⁰) s (proj₁ (O.Ωt (h₁ ω⁰)))
  → GR.R (h₁ (nat 1) ⊕ ↑ zero ω⁰) s (proj₁ (O.Ωt (h₁ (nat 1) ⊕ ↑ zero ω⁰)))

module Cell (B : Base (tw 1)) where
  open Tw 0 B (h₁ (nat 1)) (nat 1) P.self (P.lift zero (↑ zero (nat 1))) (route-tw1 (nzs zero)) public

  cell-read : ∀ {η} → GR.R zero η ω⁰ → Top (h₁ (nat 1) ⊕ ↑ zero ω⁰) (E.natT 1 ++ η)
  cell-read r = sub-read⁺ (dom-fin 1) ω⁰ r

  cell-cap : ∀ {t s η} → GR.R zero η ω⁰ → s ≤ᵀ E.Ωt η → SubAt ω⁰ t s
  cell-cap = cap-domᵗ ω⁰

  cell-same : CellRaise → ∀ {t s} → GR.R (h₁ ω⁰) s (proj₁ (O.Ωt (h₁ ω⁰))) → SubAt ω⁰ t s
  cell-same cr r = same (inj₂ refl) ω⁰ (cr r)

  kept₁ : Kept (inj₁ (inj₁ tt))
  kept₁ = kept-tw1 (nzs zero)
```

第 0 个孩子 (层号 zero 抬到 `h₁ 1`) 上一般参照的抬高成立: 第 0 层的 Ω 树是 1, 它嵌在 `h₁ 1` 的 Ω 树第一分支下面. 第 1 个孩子起 (后继形状的层号, Ω 树的顶槽位在被抬高的那一层) 这个证法不适用.

```agda
raise₀ : ∀ {s} → GR.R zero s (proj₁ (O.Ωt zero)) → GR.R (h₁ (nat 1)) s (proj₁ (O.Ωt (h₁ (nat 1))))
raise₀ r = H.mw (H.mU H.mz r) ◃w
```
