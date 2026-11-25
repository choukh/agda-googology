# 分级结构的一份参数化实例

> 验收文件 (读记号). 判决: 编译定理, 无前提. `gradedᴹ`: 关系取主线的 `YiGIRel.R`, 对折叠 (连同 `bt`, 槽位读法 `Nu`)、上下文 (类型 X, 头 `hd`, 前缀 `pf`, 作用 ψ_{hd K}(pf K ++ a))、读法域 `Rd` 与底的条件 `Bd` 参数化; 五份旧实例 (`YiGIInst.gradedᵍ`, `YiFIGen.gradedᴷ`, `YiWREnd.gradedᴮ`, `YiBAEbo.gradedᴱ`, `YiSDRead.gradedˢ`) 都是它的取值, 逐字 `refl` (`ᵍ≡` 等).
> 底的条件: 四份是 "底值对着上下文的某个参照 × 各层底不低于 Ω 树" (`BdΩ`), `gradedᴮ` 只有前一半 (`BdR`); 前一半的参照 ψ₀(t₀) 与 ψ_ν(K ++ []) 互推 (`bnd⇔`). 三份 `Rows` 是 `rowsᴹ` 的取值; 其上生成原理与 `Weak`/`Lim`/`Node` 一次给出 (`Gen.genᴹ` 等, 证明照 `YiFIGen.genᴷ`), 三份旧的 (`genᴷ`, `genᴮ`, `genᴱ` 与同组三条) 是取值.
> 不给出什么: 保持律 (`LowKeep` 等) 与出口不在内.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiMIGraded where

open import Data.Bool using (Bool)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)

open import OCF.Lean.YiRWBlock using (L; Tr; zero)
open import OCF.Lean.YiRWFold using (Base)
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiBSBase as BB
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiKVRel as KV
import OCF.Align.EboLeanDef as E
open import OCF.Lean.YiAbsFrame using (Block; Fold)
open import OCF.Lean.YiAbsSimInst using (𝕍)
open import OCF.Lean.YiAbsGEbo using (refᴱ)
open import OCF.Lean.YiAbsGIface using (Graded; Rows; Doms; module Laws)
open import OCF.Lean.YiAbsGRow using (module Row)
open import OCF.Lean.YiFIIface using (module FI)
open import OCF.Align.EboLeanBase using (_≤ᵀ_)
open import OCF.Lean.YiRWBlock using (Sh; Ch; nd; sS; sΩ; Pos; Br; at; Ω; suc; ↑)
import OCF.Lean.YiHCRel as H
open import OCF.Lean.YiGIBlock using (slTᵍ)
open import OCF.Lean.YiGIBlock using (blkᵍ; foldᵍ; rowsᵍ)
open import OCF.Lean.YiBLFold using (foldᴮ; rowsᴮ)
open import OCF.Lean.YiFIFold using (foldᴷ; rowsᴷ)
open import OCF.Lean.YiDXFold using (KeepFn)
open import OCF.Lean.YiGLDom using (Dom)
open import OCF.Lean.YiGIInst using (gradedᵍ; Bdᵍ)
open import OCF.Lean.YiFIGen using (gradedᴷ; domsᴷ; genᴷ; weakᴷ; limᴷ; nodeᴷ; module Ind; →low; low→)
open import OCF.Lean.YiWREnd using (gradedᴮ; Bdᴮ; domsᴮ; genᴮ; weakᴮ; limᴮ; nodeᴮ)
open import OCF.Lean.YiBAEbo using (gradedᴱ; Bdᴱ; apE; domsᴱ; genᴱ; weakᴱ; limᴱ; nodeᴱ)
open import OCF.Lean.YiSDRead using (gradedˢ; Bdˢ)
```

## 实例

```agda
module _ (𝔽 : Fold blkᵍ) (ℜ : Rows blkᵍ 𝔽) (bt : ∀ {j} → Fold.Bt 𝔽 j → Tr j)
         (Nu : (ℓ : L) → Rows.Sl ℜ ℓ → E.T → Set) (Rd : L → E.T → Set)
         (X : Set) (hd pf : X → E.T) (Bd : ∀ {ℓ j} → Fold.Bs 𝔽 ℓ → j P.≤ ℓ → Fold.Bt 𝔽 j → X → Set) where
  apᴹ : X → E.T → E.T
  apᴹ K a = E.ψ (hd K) (pf K ++ a) ∷ []

  gradedᴹ : Graded blkᵍ 𝔽 ℜ refᴱ 𝕍
  gradedᴹ = record
    { ℓ₀ = zero ; v = KV.readRW ; R = GR.R ; Rd = Rd ; Nu = Nu ; bt = bt
    ; cl = λ _ t → E.ψ [] t ∷ [] ; Cx = λ _ _ → X ; app = apᴹ ; Bd = Bd }
```

## 五份旧实例是它的取值

```agda
idT : E.T → E.T
idT t = t

zeroT : E.T → E.T
zeroT _ = []

ᵍ≡ : gradedᵍ ≡ gradedᴹ foldᵍ rowsᵍ proj₁ GR.Nu GR.Rd E.T zeroT idT Bdᵍ
ᵍ≡ = refl

ᴷ≡ : (K : KeepFn) (lifted : Bool) → gradedᴷ K lifted ≡ gradedᴹ (foldᴷ K lifted) (rowsᴷ K lifted) proj₁ GR.Nu GR.Rd E.T zeroT idT Bdᵍ
ᴷ≡ K lifted = refl

ᴮ≡ : gradedᴮ ≡ gradedᴹ foldᴮ rowsᴮ proj₁ GR.Nu Dom E.T zeroT idT Bdᴮ
ᴮ≡ = refl

ᴱ≡ : gradedᴱ ≡ gradedᴹ foldᴮ rowsᴮ proj₁ GR.Nu GR.Rd (E.T × E.T) proj₁ proj₂ Bdᴱ
ᴱ≡ = refl

ˢ≡ : gradedˢ ≡ gradedᴹ foldᴮ rowsᴮ proj₁ GR.Nu GR.Rd E.T zeroT idT Bdˢ
ˢ≡ = refl
```

## 底的条件

`BdR bnd`: 底值不低于上下文的参照 `bnd K`. `BdΩ bnd`: 再加各层的底不低于 Ω 树. 四份旧的 Bd 是取值; `bnd` 的两种写法 (ψ₀(t₀) 与 `apE K []`) 经 `++-identityʳ` 互推.

```agda
module _ {Rb : L → Set} (X : Set) (bnd : X → E.T) where
  BdR BdΩ : ∀ {ℓ j} → P.Ok ℓ × Rb ℓ × Base ℓ → j P.≤ ℓ → O.Tr⁺ j → X → Set
  BdR {ℓ} {j} b w β K = GR.R j (bnd K) (proj₁ β)
  BdΩ {ℓ} {j} b w β K = GR.R j (bnd K) (proj₁ β) × (∀ i u → proj₁ (O.Ωt i) KV.⊴ proj₁ (proj₂ (proj₂ b) i u))

ψ₀ : E.T → E.T
ψ₀ t = E.ψ [] t ∷ []

ᵍBd : ∀ {ℓ j} → Bdᵍ {ℓ} {j} ≡ BdΩ {Rb = TB.Rb} E.T ψ₀
ᵍBd = refl

ˢBd : ∀ {ℓ j} → Bdˢ {ℓ} {j} ≡ BdΩ {Rb = BB.Rb} E.T ψ₀
ˢBd = refl

ᴱBd : ∀ {ℓ j} → Bdᴱ {ℓ} {j} ≡ BdΩ {Rb = BB.Rb} (E.T × E.T) (λ K → apE K [])
ᴱBd = refl

ᴮBd : ∀ {ℓ j} → Bdᴮ {ℓ} {j} ≡ BdR {Rb = BB.Rb} E.T ψ₀
ᴮBd = refl

bnd⇔ : ∀ {j} (ν K : E.T) (β : Tr j) → (GR.R j (E.ψ ν K ∷ []) β → GR.R j (apE (ν , K) []) β)
                                      × (GR.R j (apE (ν , K) []) β → GR.R j (E.ψ ν K ∷ []) β)
bnd⇔ {j} ν K β = subst (λ z → GR.R j (E.ψ ν z ∷ []) β) (sym (++-identityʳ K))
               , subst (λ z → GR.R j (E.ψ ν z ∷ []) β) (++-identityʳ K)
```

## 行与生成原理

`rowsᴹ 𝔽 bt⁺`: 三份旧的 `Rows` (`rowsᵍ`, `rowsᴮ`, `rowsᴷ`) 的公共形状, 只差底值类型到 `Tr⁺` 的映射 (`rows≡`). 在它上面, 关系的生成原理与 `Weak`, `Lim`, `Node` 对一切折叠、上下文、读法域、底的条件一次给出 (`genᴹ` 等; 证明逐字照 `YiFIGen.genᴷ`). `genᴷ`, `genᴮ`, `genᴱ` 与三组 `Weak`/`Lim`/`Node` 是取值: 同一个项填进旧的类型 (`genᴷ′` 等).

```agda
rowsᴹ : (𝔽 : Fold blkᵍ) → (∀ {j} → Fold.Bt 𝔽 j → O.Tr⁺ j) → Rows blkᵍ 𝔽
rowsᴹ 𝔽 bt⁺ = record
  { sc = suc ; Sl = Pos ; slL = at ; SlT = Br ; slT = slTᵍ ; nd = Ω
  ; Ωt = λ ℓ → proj₁ (O.Ωt ℓ) ; Dn = O.Dn ; upf = λ {ℓ} {j} d β y → proj₁ (O.Up j d (bt⁺ β) y)
  ; sucL = λ ℓ → nd sS (λ _ → ℓ) ; ΩL = λ k h → nd (sΩ k) h ; lift = ↑ }

idβ : ∀ {j} → O.Tr⁺ j → O.Tr⁺ j
idβ β = β

rows≡ᵍ : rowsᵍ ≡ rowsᴹ foldᵍ idβ
rows≡ᵍ = refl

rows≡ᴮ : rowsᴮ ≡ rowsᴹ foldᴮ idβ
rows≡ᴮ = refl

rows≡ᴷ : (K : KeepFn) (lifted : Bool) → rowsᴷ K lifted ≡ rowsᴹ (foldᴷ K lifted) idβ
rows≡ᴷ K lifted = refl

module Gen (𝔽 : Fold blkᵍ) (bt⁺ : ∀ {j} → Fold.Bt 𝔽 j → O.Tr⁺ j) (Rd : L → E.T → Set) (X : Set) (hd pf : X → E.T)
           (Bd : ∀ {ℓ j} → Fold.Bs 𝔽 ℓ → j P.≤ ℓ → Fold.Bt 𝔽 j → X → Set) (𝔻 : Doms blkᵍ 𝔽) where
  𝔾ᴹ : Graded blkᵍ 𝔽 (rowsᴹ 𝔽 bt⁺) refᴱ 𝕍
  𝔾ᴹ = gradedᴹ 𝔽 (rowsᴹ 𝔽 bt⁺) (λ β → proj₁ (bt⁺ β)) GR.Nu Rd X hd pf Bd
  open FI 𝔾ᴹ 𝔻 using (Gen⁺)
  open Laws 𝔾ᴹ 𝔻 using (Weak; Lim; Node)
  open Row 𝔾ᴹ 𝔻 using (Rules)

  genᴹ : ∀ ℓ → Gen⁺ _≤ᵀ_ ℓ
  genᴹ zero Q rs qc = Ind.ind Q (qz refl) q1 qL (λ ()) (λ ()) qw qc
    where open Rules rs
  genᴹ (nd s h) Q rs qc = Ind.ind Q (qz refl) q1 qL
    (λ p g e nu hR hQ → qΩ p g e nu (λ η c l → hR η c (→low (nd s h) p l)) (λ η c l → hQ η c (→low (nd s h) p l)))
    (λ c y e m q ch → qU c (y , e) m q ch) qw qc
    where open Rules rs

  weakᴹ : Weak
  weakᴹ {ℓ = zero}   = H.mw
  weakᴹ {ℓ = nd s h} = H.mw

  limᴹ : Lim
  limᴹ {ℓ = zero}   = H.mL
  limᴹ {ℓ = nd s h} = H.mL

  nodeᴹ : Node
  nodeᴹ {ℓ = nd s h} p g e nu hyp = H.mΩ e nu (λ η c l → hyp η c (low→ (nd s h) p l))

module _ (K : KeepFn) (lifted : Bool) where
  open Gen (foldᴷ K lifted) idβ GR.Rd E.T zeroT idT Bdᵍ (domsᴷ K lifted)
  genᴷ′ : ∀ ℓ → FI.Gen⁺ (gradedᴷ K lifted) (domsᴷ K lifted) _≤ᵀ_ ℓ
  genᴷ′ = genᴹ
  weakᴷ′ : Laws.Weak (gradedᴷ K lifted) (domsᴷ K lifted)
  weakᴷ′ = weakᴹ
  limᴷ′ : Laws.Lim (gradedᴷ K lifted) (domsᴷ K lifted)
  limᴷ′ = limᴹ
  nodeᴷ′ : Laws.Node (gradedᴷ K lifted) (domsᴷ K lifted)
  nodeᴷ′ = nodeᴹ

module _ where
  open Gen foldᴮ idβ Dom E.T zeroT idT Bdᴮ domsᴮ
  genᴮ′ : ∀ ℓ → FI.Gen⁺ gradedᴮ domsᴮ _≤ᵀ_ ℓ
  genᴮ′ = genᴹ
  weakᴮ′ : Laws.Weak gradedᴮ domsᴮ
  weakᴮ′ = weakᴹ
  limᴮ′ : Laws.Lim gradedᴮ domsᴮ
  limᴮ′ = limᴹ
  nodeᴮ′ : Laws.Node gradedᴮ domsᴮ
  nodeᴮ′ = nodeᴹ

module _ where
  open Gen foldᴮ idβ GR.Rd (E.T × E.T) proj₁ proj₂ Bdᴱ domsᴱ
  genᴱ′ : ∀ ℓ → FI.Gen⁺ gradedᴱ domsᴱ _≤ᵀ_ ℓ
  genᴱ′ = genᴹ
  weakᴱ′ : Laws.Weak gradedᴱ domsᴱ
  weakᴱ′ = weakᴹ
  limᴱ′ : Laws.Lim gradedᴱ domsᴱ
  limᴱ′ = limᴹ
  nodeᴱ′ : Laws.Node gradedᴱ domsᴱ
  nodeᴱ′ = nodeᴹ
```
