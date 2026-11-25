# 换基律的配对否定: 现行回退与上折回退各违反哪一条

> 判决: 编译定理, 不读记号. 现行回退 (`YiDXFold.Fold K false`, 主线 `YiTBRow.ψ`) 违反 `reb`: 前缀为零, 底值不含结点时嵌入的输出不含结点 (`YiFINeg.fb-nf`, `main-nf`), 所以任何换基行的替身像都不含结点 (`cur-¬RebAt`); `YiBSFold` 的替身在塔第 1 项上含结点 (`sub-ω`), 两个折叠在同一格上都不能以它为替身 (`fb-¬rebᴮ`, `main-¬rebᴮ`).
> 上折回退违反 `lw` 与 `cpE`: 换基层号取原材料的孩子层号时, 目标 `h₁ ω` 到孩子 ωᵉ 的层号没有字面路径 (`up-¬lw`, 用 `YiRKCell.no-ωᵉ`); K = `kp` 时它自己的孩子状态对一切槽位都没有保留证据 (`lf-noEv`), 所以目标层槽位的副本不能带证据 (`up-¬cpE`).
> 不否定什么: 不否定值; `up-¬cpE` 只对 K = `kp`, 其余 K 由 `up-¬lw` 管.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBLNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; kp)
import OCF.Lean.YiDXFold as DX
open DX using (KeepFn)
open import OCF.Lean.YiTBRow using (h₁; nat) renaming (ψ to ψ₁; Rb to Rbᵀ)
open import OCF.Lean.YiMTTab using (rbᶻ)
open import OCF.Lean.YiVALeaf using (NZ; nzs; nzl)
open import OCF.Lean.YiTBTab using (ωᶜ; ωᵉ)
open import OCF.Lean.YiFINeg using (NF; nz; ns; nl; nf-down; fb-nf; main-nf)
open import OCF.Lean.YiRKCell using (no-ωᵉ; IsChild; mv-child)
open import OCF.Lean.YiGIBlock using (blkᵍ; ChTᵍ; upᵍ)
open import OCF.Lean.YiAbsFrame using (Fold)
open import OCF.Lean.YiAbsSim using (Val)
open import OCF.Lean.YiAbsGIface
open import OCF.Lean.YiFIIface
open import OCF.Lean.YiFIFold using (foldᴷ; rowsᴷ; module Tree)
open import OCF.Lean.YiBLIface
open import OCF.Lean.YiBLFold using (module Aux; _⊴ᵗ_)
```

## 现行回退: `reb`

不含结点的树沿 `⊴` 向下封闭; 所以输出不含结点的嵌入行不能不低于含结点的替身像.

```agda
nf-⊴ : ∀ {j} {τ t : Tr j} → τ ⊴ᵗ t → NF t → NF τ
nf-⊴ (inj₁ refl) n = n
nf-⊴ (inj₂ d)    n = nf-down d n

module _ {𝔽 : Fold blkᵍ} {ℜ : Rows blkᵍ 𝔽} {𝕋 : Ref} {𝕍 : Val} (𝔾 : Graded blkᵍ 𝔽 ℜ 𝕋 𝕍) (𝔻 : Doms blkᵍ 𝔽) where
  open FI 𝔾 𝔻 using (Sys; module Sys)
  open BL 𝔾 𝔻 using (RebAt)

  cur-¬RebAt : ∀ {j} (𝒮 𝒜 : Sys j) (𝓀ᴬ : Sys.KeepLaw 𝒜) {a} (s : Sys.St 𝒮 a) (r : RebAt 𝒮 𝒜 𝓀ᴬ s) (c : CH a) (y : ChTᵍ a c)
    → NF (Sys.Φ 𝒮 s (upᵍ zero c y)) → (NF (Sys.Φ 𝒜 (RebAt.Sr r c zero) (RebAt.sub r c zero)) → ⊥) → ⊥
  cur-¬RebAt 𝒮 𝒜 𝓀ᴬ s r c y ny no = no (nf-⊴ (RebAt.reb r c zero y) ny)
```

两个现行折叠在这一格: 前缀为零, 底值不含结点.

```agda
fb-¬reb : ∀ (K : KeepFn) k h (o : Ok (nd (sΩ k) h)) (rc : (c : Tr k) → Rbᵀ (h c)) (B : Base (nd (sΩ k) h)) j c′ (v : j ≤ h c′)
  (β : Tr⁺ j) c y e → NF (proj₁ β) → (τ : Tr j) → (NF τ → ⊥)
  → τ ⊴ᵗ proj₁ (DX.Fold.ψ K false (nd (sΩ k) h) o ((λ _ _ → nothing) , rc) B j (inc c′ v) β (up zero c y e)) → ⊥
fb-¬reb K k h o rc B j c′ v β c y e nβ τ no le = no (nf-⊴ le (fb-nf K k h o rc B j c′ v β c y e nβ))

main-¬reb : ∀ {c c′} → NZ c → NZ c′ → (o : Ok (tw 1)) (B : Base (tw 1)) (j : L) (v : j ≤ h₁ c′) (β : Tr⁺ j)
  (y : Tr (h₁ c)) (e : h₁ c ⊢ zero ◃ y) → NF (proj₁ β) → (τ : Tr j) → (NF τ → ⊥)
  → τ ⊴ᵗ proj₁ (ψ₁ (tw 1) o (rbᶻ (tw 1)) B j (inc c′ v) β (up zero c y e)) → ⊥
main-¬reb nc nc′ o B j v β y e nβ τ no le = no (nf-⊴ le (main-nf nc nc′ o B j v β y e nβ))
```

`YiBSFold` 在塔第 1 项, 目标 `h₁ 1` (经孩子 1), 孩子 ω 处的替身: 换基层号 `h₁ 1 ⊕ ↑ω` 的 Ω 树是部分和极限, 第 0 项进到 `h₁ 1` 自身, 那里的 Ω 结点保留. 对一切合法证据, 底, 底值成立; x = 0 时 `YiBLFold.Main.Srᴮ` 的底值就是 β.

```agda
j₁ : L
j₁ = h₁ (nat 1)

sub-ω : (o′ : Ok (j₁ ⊕ ↑ zero ωᶜ)) (B′ : Base (j₁ ⊕ ↑ zero ωᶜ)) (β : Tr⁺ j₁)
  → NF (proj₁ (Aux.Φᴬ j₁ (Aux.rbs (↑ zero ωᶜ) o′ B′ β) (proj₁ (Ωt (j₁ ⊕ ↑ zero ωᶜ))))) → ⊥
sub-ω o′ B′ β (nl f) with f 0
... | ()

fb-¬rebᴮ : ∀ (K : KeepFn) (o : Ok (tw 1)) (rc : (c : Tr zero) → Rbᵀ (h₁ c)) (B : Base (tw 1)) (β : Tr⁺ j₁) y e
  (o′ : Ok (j₁ ⊕ ↑ zero ωᶜ)) (B′ : Base (j₁ ⊕ ↑ zero ωᶜ)) → NF (proj₁ β)
  → proj₁ (Aux.Φᴬ j₁ (Aux.rbs (↑ zero ωᶜ) o′ B′ β) (proj₁ (Ωt (j₁ ⊕ ↑ zero ωᶜ))))
    ⊴ᵗ proj₁ (DX.Fold.ψ K false (tw 1) o ((λ _ _ → nothing) , rc) B j₁ (inc (nat 1) self) β (up zero ωᶜ y e)) → ⊥
fb-¬rebᴮ K o rc B β y e o′ B′ nβ = fb-¬reb K zero h₁ o rc B j₁ (nat 1) self β ωᶜ y e nβ _ (sub-ω o′ B′ β)

main-¬rebᴮ : (o : Ok (tw 1)) (B : Base (tw 1)) (β : Tr⁺ j₁) (y : Tr (h₁ ωᶜ)) (e : h₁ ωᶜ ⊢ zero ◃ y)
  (o′ : Ok (j₁ ⊕ ↑ zero ωᶜ)) (B′ : Base (j₁ ⊕ ↑ zero ωᶜ)) → NF (proj₁ β)
  → proj₁ (Aux.Φᴬ j₁ (Aux.rbs (↑ zero ωᶜ) o′ B′ β) (proj₁ (Ωt (j₁ ⊕ ↑ zero ωᶜ))))
    ⊴ᵗ proj₁ (ψ₁ (tw 1) o (rbᶻ (tw 1)) B j₁ (inc (nat 1) self) β (up zero ωᶜ y e)) → ⊥
main-¬rebᴮ o B β y e o′ B′ nβ = main-¬reb (nzl _ _) (nzs _) o B j₁ self β y e nβ _ (sub-ω o′ B′ β)
```

## 上折回退: `lw` 与 `cpE`

上折回退把孩子材料留在它自己的孩子层号上. 把它读成换基行 (换基层号 = 孩子层号), 字面公共上界 `lw` 在 (ω, ωᵉ) 一格不存在; 对任何系统与任何 K.

```agda
module _ {𝔽 : Fold blkᵍ} {ℜ : Rows blkᵍ 𝔽} {𝕋 : Ref} {𝕍 : Val} (𝔾 : Graded blkᵍ 𝔽 ℜ 𝕋 𝕍) (𝔻 : Doms blkᵍ 𝔽) where
  open FI 𝔾 𝔻 using (Sys; module Sys)
  open BL 𝔾 𝔻 using (RebAt)

  up-¬lw : (𝒮 𝒜 : Sys (h₁ ωᶜ)) (𝓀ᴬ : Sys.KeepLaw 𝒜) (s : Sys.St 𝒮 (tw 1)) (r : RebAt 𝒮 𝒜 𝓀ᴬ s)
    → (∀ c x → RebAt.Lr r c x ≡ h₁ c) → ⊥
  up-¬lw 𝒮 𝒜 𝓀ᴬ s r eq = no-ωᵉ (inj₂ (subst (λ b → h₁ ωᶜ ≤ b) (eq ωᵉ zero) (RebAt.lw r ωᵉ zero)))
```

K = `kp` 时上折回退的孩子状态 (`lf`, 下行链非空) 在 Ω 形状层号上经指定孩子的路径下对一切槽位都不保留; 以这些状态作换基状态, 副本证据 `cpE` 为空 (目标层有槽位即可).

```agda
module UpNeg {𝕋 : Ref} {𝕍 : Val}
    (𝔾 : Graded blkᵍ (foldᴷ kp true) (rowsᴷ kp true) 𝕋 𝕍) (𝔻 : Doms blkᵍ (foldᴷ kp true))
    (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h)) (rc : (c : Tr k) → Rbᵀ (h c)) (B : Base (nd (sΩ k) h))
    (j : L) (c′ : Tr k) (v : j ≤ h c′) where
  open Tree kp 𝔾 𝔻 k h o rc B j c′ v
  open FI 𝔾 𝔻 using (Sys; module Sys)
  open BL 𝔾 𝔻 using (RebAt)

  kp-child : (p : Pos (nd (sΩ k) h)) → IsChild (nd (sΩ k) h) p → kp (nd (sΩ k) h) o p (inc c′ v) ≡ nothing
  kp-child (inj₁ _) ()
  kp-child (inj₂ _) _ = refl

  IsLfD : ∀ {a} → Stᴷ a → Set
  IsLfD (rt β)              = ⊥
  IsLfD (lf stop X β)       = ⊥
  IsLfD (lf (down d c) X β) = ⊤

  lf-noEv : ∀ {a} (s : Stᴷ a) → IsLfD s → (p : Pos a) → Evᴷ s p → ⊥
  lf-noEv (lf (down d c) X β) _ p (q , cv , e , eq) with trans (sym (kp-child (mv (down d c) p) (mv-child d (inj₂ (c , inj₂ p)) tt))) eq
  ... | ()

  module _ (Cxtᴷ : Set) (apᴷ : Cxtᴷ → Ref.T 𝕋 → Ref.T 𝕋) (Bdᴷ : ∀ {a} → Stᴷ a → Cxtᴷ → Set) where
    step-lf : (β : Tr⁺ j) (c : Tr k) (x : Tr (nd (sΩ k) h)) → IsLfD (stepᴷ Cxtᴷ apᴷ Bdᴷ (rt β) c x)
    step-lf β c x = tt

    up-¬cpE : (𝒮 : Sys j) → ∀ {a} (s : Sys.St 𝒮 a) (r : RebAt 𝒮 (sysᴷ Cxtᴷ apᴷ Bdᴷ) (keepᴷ Cxtᴷ apᴷ Bdᴷ) s) (c : CH a) (x : Tr a)
      → IsLfD (RebAt.Sr r c x) → Pos j → ⊥
    up-¬cpE 𝒮 s r c x isl q = lf-noEv (RebAt.Sr r c x) isl _ (RebAt.cpE r c x q)
```
