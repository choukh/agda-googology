# Refute 归到一个项、继承底在每一层的形状、第 1 层的统一上界
验收文件（读记号）；编译定理：`single`、`single⁻`（`YiRQDom.Refute d κ` 当且仅当链的第 1 项 γ₁ 不是那棵树的下界读法，对一切 d、κ）；`base-form`（继承底在每一层、每条路径上都是 Ω 树加两段可数尾巴，对一切 d）；`leaf-node₂`（朝 `h₁ 2` 时 tw 1 叶子的下标槽位保留成 Ω₁ 槽位的结点）；`bL1`（第 `h₁ 1` 层每棵树的读法都低于 Ω₂）。
不否定 `Refute`、`TightDom`、`Cand`：`γ₁*<Ω₂` 说 `bL1` 的界高于 d = 1 的 γ₁；`no-uniform-γ₂`、`no-uniform-γ₁*` 是 `YiUSUni` 在这两个 γ₁ 上的实例。入口 `single`、`bL1`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiUSBound where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base)
open import OCF.Lean.YiTBRow using (ψ)
open import OCF.Lean.YiMTTab using (rbᶻ)
open import OCF.Lean.YiSYReduce using (h₁; a₁; Bᴱ)
open import OCF.Lean.YiTFBound using (rd-zero; bZ; c2; r2)
open import OCF.Lean.YiUSUni using (Ω₂; Ω₁<Ω₂; sucΩ₂; ++Ω₂; mLΩ₂; LΩ₂; ReqL; Req₀; Req₁; no-uniform₂; no-uniform₁)
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiRQDom as RQ
import OCF.Lean.YiKTSlot as KT
import OCF.Lean.YiTFTight as TF
import OCF.Lean.YiSYDesc as D
import OCF.Align.EboLeanDef as E
open E using (_<ᵀ_; []<; hd<; tl<; lv<)
open import OCF.Align.EboLeanBase using (_≤ᵀ_; tri; <ᵀ-irrefl; <ᵀ-trans; ≤-<)
open import OCF.Align.EBO using (pred-suc)
open import OCF.Align.EboLeanView using (vΩ; fΩ-eq)
```

## Refute 归到一个项

`R` 对项序向下封闭，项序三歧，所以 `Refute d κ` 等价于 γ₁ 不是读法。

```agda
R-mc : ∀ ℓ {s t x} → s ≤ᵀ t → GR.R ℓ t x → GR.R ℓ s x
R-mc zero = H.mc
R-mc (nd _ _) = H.mc

γ₁ : E.T → E.T
γ₁ κ = E.γT (E.Ωt (E.Ωs κ)) κ 1

-- perf: E-2/C-9。对真目标 `with tri` 在 6G 撞墙 (251)，改成在变量谓词上消费三歧。
below : (P : E.T → Set) → (∀ {s t} → s ≤ᵀ t → P t → P s) → (g : E.T) → (P g → ⊥)
  → ∀ t → (t <ᵀ g) ⊎ (t ≡ g) ⊎ (g <ᵀ t) → P t → t <ᵀ g
below P mc g no t (inj₁ lt) r = lt
below P mc g no t (inj₂ (inj₁ refl)) r = ⊥-elim (no r)
below P mc g no t (inj₂ (inj₂ gt)) r = ⊥-elim (no (mc (inj₁ gt) r))

single : ∀ d κ → (GR.R (h₁ d) (γ₁ κ) (RQ.Sᵈ.fd d (proj₁ (Ωt (h₁ d)))) → ⊥) → RQ.Refute d κ
single d κ no {t} r = below (λ s → GR.R (h₁ d) s (RQ.Sᵈ.fd d (proj₁ (Ωt (h₁ d))))) (R-mc (h₁ d)) (γ₁ κ) no t (tri t (γ₁ κ)) r

single⁻ : ∀ d κ → RQ.Refute d κ → GR.R (h₁ d) (γ₁ κ) (RQ.Sᵈ.fd d (proj₁ (Ωt (h₁ d)))) → ⊥
single⁻ d κ ref r = <ᵀ-irrefl (ref r)
```

## 继承底

`YiRQDom.start-form` 只对 `h₁ d` 与 `ink self`；这里对任意层 i、任意路径 u（变量上 `refl`，C-9）。所以链步折叠里出现的每个底都是 "该层的 Ω 树 ⊞ 两段可数"。

```agda
base-form : ∀ d i (u : i ≤ a₁ (suc d)) → proj₁ (D.dn Bᴱ (suc d) i u) ≡ proj₁ ((Ωt i ⊞ TF.Y₁) ⊞ TF.Y₂)
base-form d i u = refl
```

## 目标 `h₁ 2` 上保留的结点是 Ω₁ 槽位

同 `YiVALeaf.leaf-node`，目标换成 `h₁ 2`、路径经孩子 3（`fd` 在 d = 2 时到达 tw 1 叶子的路径就是这一条，`YiRQDom.kp₀ᵍ`）：tw 1 的下标槽位落到 `h₁ 2` 的 Ω₁ 槽位 `q₁₂`（分支是可数树），不是它自己的 Ω₂ 槽位。

```agda
three : Tr zero
three = suc (suc (suc zero))

q₁₂ : Pos (h₁ (suc (suc zero)))
q₁₂ = inj₂ (tt , inj₂ (inj₂ (tt , inj₁ tt)))

leaf-node₂ : (B : Base (tw 1)) (β : Tr⁺ (h₁ (suc (suc zero))))
  → ψ (tw 1) (Ok-tw 1) (rbᶻ (tw 1)) B (h₁ (suc (suc zero))) (inc three (inc tt self)) β (proj₁ (Ωt (tw 1)))
  ≡ Ω⁺ q₁₂ (λ z → ψ (tw 1) (Ok-tw 1) (rbᶻ (tw 1)) B (h₁ (suc (suc zero))) (inc three (inc tt self)) β
      (proj₁ (upz {s = sΩ zero} {h = h₁} z (Ωt (h₁ z)))))
leaf-node₂ B β = refl
```

## 第 1 层：一切树的读法低于 Ω₂

不要树类：第 1 层只有一个槽位，分支是可数树，`Nu` 只容 0（`rd-zero`）；孩子是第 0 层（`bZ`）。

```agda
L1 : L
L1 = h₁ (suc zero)

bL1 : ∀ {t x} → GR.R L1 t x → t <ᵀ Ω₂
bL1 H.mz = []<
bL1 (H.m1 {t = t} e r) = subst (_<ᵀ Ω₂) (pred-suc t e) (sucΩ₂ (bL1 r))
bL1 (H.mL {t = t} e h) = mLΩ₂ t e (bL1 (h 2))
bL1 (H.mΩ {t = t} {p = inj₂ (tt , inj₁ tt)} e nu h) =
  LΩ₂ (vΩ t e) (rd-zero nu) (subst (_<ᵀ Ω₂) (fΩ-eq (vΩ t e) (E.natT 2)) (bL1 (h (E.natT 2) c2 r2)))
bL1 (H.mΩ {p = inj₂ (tt , inj₂ ())} e nu h)
bL1 (H.mU m ch) = ++Ω₂ (bL1 m) (<ᵀ-trans (bZ ch) Ω₁<Ω₂)
bL1 (H.mw m d) = bL1 m
bL1 (H.mc le m) = ≤-< le (bL1 m)
```

## 与两个 γ₁ 的关系

d = 1 的 γ₁（`Cand` 的参照 ψ₁(Ω_{Ω₁})）低于 Ω₂，`bL1` 不判定它。两个 γ₁ 都落在 `YiUSUni` 的区间里。

```agda
γ₁*<Ω₂ : γ₁ KT.κ* <ᵀ Ω₂
γ₁*<Ω₂ = hd< (lv< (tl< []<))

no-uniform-γ₂ : ReqL (γ₁ (E.natT 2)) → Req₀ (γ₁ (E.natT 2)) → Req₁ (γ₁ (E.natT 2)) → ⊥
no-uniform-γ₂ = no-uniform₂ _

no-uniform-γ₁* : ReqL (γ₁ KT.κ*) → Req₀ (γ₁ KT.κ*) → ⊥
no-uniform-γ₁* = no-uniform₁ _
```
