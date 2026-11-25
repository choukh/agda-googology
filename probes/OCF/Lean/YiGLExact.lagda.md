# 精确标签的关系族与其上的 Leaf, LowKeep 的陈述

> 验收文件 (读记号)。编译定理: 把 `YiGIRel.R` 的槽位余尾从下界读法换成精确标签得关系族 `Rˣ`; `topˣ` 是 `Rˣ` 上的 Leaf, 对一切带精确标签的层号 (含 ℕ 极限层号, 用向下封闭吸收部分和的余量); ω 孩子上的实例 `topˣ-ω`, `topˣ-source`。
> `LowKeepˣ` 只是陈述 (层号、路径、表、底、底值、前缀、目标下标都是变量, 参照为记号项), 没有居民; 它不是 `YiAbsGIface.LowKeep` 的实例 (那里的 `cl`, `app` 只看层号, 这里目标下标来自标签证据)。
> 第 0 层 `Rˣ zero` 与 `YiGIRel.R zero` 是同一个关系, 出口不变。不否定什么。入口: [YiGLFrame](YiGLFrame.lagda.md), [YiGLOmega](YiGLOmega.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiGLExact where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Lean.YiRWBlock hiding (R)
import OCF.Lean.YiRWOps as O
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiTBRow using (Rb; ψ)
open import OCF.Lean.YiLKIface using (OK)
open import OCF.Lean.YiKVInst using (Ωω; fsnΩω)
open import OCF.Lean.YiCLPhi using (ωᵀ)
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiBVSmall as S
import OCF.Lean.YiSQOmega as W
import OCF.Align.EboLeanDef as E
open import OCF.Align.EboLean3Base using (Ωt-mono)
open import OCF.Align.EBO using (pred-suc)
open import OCF.Align.JiaAuditClosure using (cof-regular; fs-regular)
open import OCF.Lean.YiGLFrame
open import OCF.Lean.YiGLOmega using (Lω; lbl-ω; lbl-source)
```

## 关系族

与 `YiGIRel.R` 逐字同形, 只有槽位余尾一项不同: `Lbl (at ℓ p)`。

```agda
mutual
  Rˣ : (ℓ : L) → E.T → Tr ℓ → Set
  Rˣ zero = H.M⁰
  Rˣ (nd s h) = H.Mᴴ (Sig (nd s h)) (Lowˣ (nd s h)) (λ c → Rˣ (h c)) (λ p → Lbl (at (nd s h) p))

  Lowˣ : (ℓ : L) (p : Pos ℓ) → E.T → Br ℓ p → Set
  Lowˣ (nd s h) (inj₂ (c , t)) = Low⁼ˣ (h c) t
  Lowˣ (nd (sΩ k) h) (inj₁ t) = Low⁼ˣ k t

  Low⁼ˣ : (a : L) (t : Pos⁼ a) → E.T → Br⁼ a t → Set
  Low⁼ˣ a (inj₁ _) = Rˣ a
  Low⁼ˣ a (inj₂ p) = Lowˣ a p

zero-same : Rˣ zero ≡ GR.R zero
zero-same = refl

wkˣ : ∀ ℓ {t x y} → Rˣ ℓ t x → ℓ ⊢ x ◃ y → Rˣ ℓ t y
wkˣ zero = H.mw
wkˣ (nd s h) = H.mw

module Gˣ (s : Sh) (h : Ch s → L) =
  H.Gen {Sig (nd s h)} {Lowˣ (nd s h)} {λ c → Rˣ (h c)} {λ p → Lbl (at (nd s h) p)}
```

## Leaf

后继形状: 结点的余尾下标就是孩子的精确标签。ℕ 极限形状: Ω 树是部分和, 第 n 个孩子的 Ω 树对着孩子自己的标签, 再用向下封闭降到基本列第 n 项。

```agda
topˣ : ∀ a {ν} → Lbl a ν → Rˣ a (E.Ωt ν) (proj₁ (O.Ωt a))
topˣ zero refl = H.m1 refl H.mz
topˣ (nd sS h) {ν} (e , q) =
  subst (λ t → Rˣ (nd sS h) (E.Ωt t) (proj₁ (O.Ωt (nd sS h)))) (pred-suc ν e)
    (H.mΩ (cof-regular (E.pred ν)) q
      (λ η c r → subst (λ t → Rˣ (nd sS h) t (up zero tt (suc c) (O.z◃ c ◃s)))
        (sym (fs-regular (E.pred ν) η)) (H.mU H.mz (wkˣ (h tt) r ◃s))))
topˣ (nd sL g) {ν} (e , nf , la , f) = H.mL (Ωω ν e)
  (λ n → subst (λ t → Rˣ (nd sL g) t (proj₁ (O.Ωt (nd sL g)))) (sym (fsnΩω ν n e))
    (H.mc (Ωt-mono (proj₁ (proj₂ (proj₂ (f n)))))
      (Gˣ.m-cum sL g (λ m → O.upz {s = sL} {h = g} m (O.Ωt (g m))) n
        (H.mU H.mz (topˣ (g n) (proj₁ (proj₂ (f n))))))))
topˣ (nd (sΩ k) h) ()

topˣ-ω : Rˣ Lω (E.Ωt ωᵀ) (proj₁ (O.Ωt Lω))
topˣ-ω = topˣ Lω lbl-ω

topˣ-source : Rˣ (S.child W.ω) (E.Ωt (E.sucT ωᵀ)) (proj₁ (O.Ωt (S.child W.ω)))
topˣ-source = topˣ (S.child W.ω) lbl-source
```

## LowKeep 的陈述

目标 j 带精确标签 ν; 底在每个槽位层、对该层每个精确标签对着前缀 (`Prefixˣ`); 结论在目标层的 `Rˣ` 里。

```agda
Prefixˣ : ∀ {ℓ} → Base ℓ → E.T → Set
Prefixˣ {ℓ} B t = (p : Pos ℓ) (κ : E.T) → Lbl (at ℓ p) κ
  → Rˣ (at ℓ p) (E.ψ κ t ∷ []) (proj₁ (B (at ℓ p) (posW ℓ p)))

LowKeepAtˣ : L → Set
LowKeepAtˣ ℓ = ∀ {j} (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) (w : j ≤ ℓ) (β : O.Tr⁺ j) (ν t : E.T)
  → Lbl j ν → OK B → Prefixˣ B t → Rˣ j (E.ψ ν t ∷ []) (proj₁ β)
  → ∀ {a x} → Rˣ ℓ a x → Rˣ j (E.ψ ν (t ++ a) ∷ []) (proj₁ (ψ ℓ o r B j w β x))

LowKeepˣ : Set
LowKeepˣ = ∀ ℓ {λ′} → Lbl ℓ λ′ → LowKeepAtˣ ℓ
```

前提可满足: 标准底对空前缀满足 `Prefixˣ`, 目标层的 Ω 树对着 ψ_ν(0)。

```agda
prefixˣ-B₀ : ∀ ℓ → Prefixˣ (B₀ ℓ) []
prefixˣ-B₀ ℓ p κ l = topˣ (at ℓ p) l

betaˣ : ∀ j {ν} → Lbl j ν → Rˣ j (E.ψ ν [] ∷ []) (proj₁ (O.Ωt j))
betaˣ = topˣ
```
