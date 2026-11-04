# 主线直接标: 链行的读法 (一般定理)

> **验收文件, 读记号.** 结论写在 [OrdLab](OrdLab.lagda.md), 实例在 [OrdLabReadTop](OrdLabReadTop.lagda.md). 全部是主线的定理, 没有克隆的证书.
>
> `chain-needs-zero`: 对一切 `HtB`, 一切链行 $m$, 一切 $\omega$-共尾的 $u$: 若第 0 行的计值带字面标签 $\psi_0(\Omega_u)$, 则 $u[0]=0$. 原因: 链行的第 0 项字面是 $\omega$ (`rowL` 的 `𝟏L`, `ω-lab`), 而 $\psi_0(\Omega_v)$ ($v\ne0$) 的第 1 项不是后继, $\omega$ 的第 1 项是后继 (`two`, `pick`).
>
> `GenRow`: 链行上的一般操作, $X$, $Y$ 都是变量, 不计算证书.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.OrdLabRead where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; _∷_; []; replicate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; toZ)
open import OCF.Free.Eq using (_≅ᶻ_; toZ-≅; sucR; wkR; lᶻ)
open import OCF.Free.Base using (r∅)
open import OCF.Free.Floor using (Ev; fz; ∅ᴿ)
open import OCF.Free.Force using (Goodᴺ; forceᴺ; forceᴺ-≅)
open import OCF.Free.Tree using (Fl)
open import OCF.Align.OrdLabZCorrespond using (Lab; l0; l1; lω; Lab-≅; fs-rep)
import OCF.Align.EBO as E
open E using (T; PT; natT; Ωt; cof; fsn; fsT; pred; c0; c1; cω; cΩ; cmpᵀ; lt; eq; gt; sucT) renaming (ψ to ψᵗ; _<ᵀ_ to _<ᵗ_)
open import OCF.Align.Bachmann using (cofA≢c1)
open import OCF.Align.Standard using (fsT-ne)
open import OCF.Align.Correspond using (cmp-suc[]; cof-ne)
open import OCF.Align.LadderLabZStandardOmega using (n[]; Ω₁; Ωᵐ; ψ¹; fsn-ψ¹)
open import OCF.Align.OrdLabZUniform3Base using (ψ₀ᵗ)
open import OCF.Align.OrdLabZStage2 using (≺→⊑)
open import OCF.Align.LadderInfTop2 using (top) renaming (fin to fin₂)
open import OCF.Align.LadderOrdBase using (HtB; View; chain)
open import OCF.Align.LadderOrdPos
open import OCF.Align.LadderOrdCode using (ωᶜ; ω²ᶜ)
open import OCF.Align.LadderOrdInst using (M₂; e₂; e²)
open import OCF.Align.LadderOrdAgree using (agree₂; agree²)
import OCF.Align.LadderOrdGrow
import OCF.Align.OrdLabChain
open import OCF.Align.OrdLabAccept using (ord-top₂; ord-top²; ord-∞; module G₂; module G²; module Gω)
module C₂ = OCF.Align.OrdLabChain (HB M₂)
module C² = OCF.Align.OrdLabChain (HB ω²ᶜ)
module Cω = OCF.Align.OrdLabChain (HB ωᶜ)
```

## §1 记号一侧

`ψ₁(1)·2`, `ψ₁(2)` 与它们上的 $\psi_0(\Omega_\cdot)$. 这里的 `refl` 都是有限检查.

```agda
tω·2 : T
tω·2 = ψ₀ᵗ (Ωt (ψ¹ ∷ ψ¹ ∷ []))

ψ²ᵗ : PT
ψ²ᵗ = ψᵗ (natT 1) (natT 2)

tω² : T
tω² = ψ₀ᵗ (Ωt (ψ²ᵗ ∷ []))

fsn-ω·2 : ∀ n → fsn tω·2 n ≡ ψ₀ᵗ (Ωt (ψ¹ ∷ Ωᵐ n []))
fsn-ω·2 n = cong (λ z → ψ₀ᵗ (Ωt (ψ¹ ∷ z))) (fsn-ψ¹ n)

-- 有限检查: 基本列的头几项
_ : fsn tω·2 0 ≡ ψ₀ᵗ (Ωt (ψ¹ ∷ []))
_ = refl

_ : fsn tω² 0 ≡ ψ₀ᵗ (natT 1)
_ = refl

_ : fsn tω² 1 ≡ ψ₀ᵗ (Ωt (ψ¹ ∷ []))
_ = refl

_ : fsn tω² 2 ≡ tω·2
_ = refl

_ : cmpᵀ tω·2 tω² ≡ lt
_ = refl
```

## §2 第 0 项的标签

`ωZ` 的计值带标签 $\psi_0(1)$. 经 `ord-∞`: 码 `ωᶜ` 的顶, 那里第 0 项确实是 $\psi_0(\Omega_{\psi_1(1)})[0]=\psi_0(1)$.

```agda
lab-lim : ∀ {X t} {h : ℕ → Ordᶜ zero} → Lab X t → cof t ≡ cω → X ≅ lim h → ∀ n → Lab (h n) (fsn t n)
lab-lim (l0 c e) c′ eh with trans (sym c) c′
... | ()
lab-lim (l1 c e l) c′ eh with trans (sym c) c′
... | ()
lab-lim {h = h} (lω {F = F} c e H) c′ eh n = Lab-≅ (lp (≅-trans (≅-sym eh) e) n) (H n)
  where
  lp : ∀ {f g : ℕ → Ordᶜ zero} → lim f ≅ lim g → ∀ n → f n ≅ g n
  lp (l≅ k) = k

ev₀ : Ev (suc zero) Fl
ev₀ = tt , (λ q → q)

Y-self : Cω.ωZ ≅ᶻ Cω.ωZ
Y-self = toZ-≅ (sucR {φ = fz} {ψ = fz} {R = ∅ᴿ} {R′ = ∅ᴿ} r∅ {zero} {zero} {suc zero} {suc zero} tt zero tt zero z≅)

ω-lab : (G : Goodᴺ Cω.ωZ) → Lab (forceᴺ Cω.ωZ G) (ψ₀ᵗ (natT 1))
ω-lab G = Lab-≅ (forceᴺ-≅ Y-self G (Cω.ChainRow.G₀ Rw)) (subst (λ X → Lab X (ψ₀ᵗ (natT 1))) (Cω.ChainRow.first Rw) (lab-lim L refl (Cω.ChainRow.eq Rw) 0))
  where
  Rw = Cω.chain-row {end} {λ i → low (blk i end)} {λ i → tt} refl ev₀ zero
  L = ord-∞ Ord₊.zero hz (l0 refl z≅) n[] E.[]< z≅ ev₀ zero
```

## §3 链行要 $u[0]=0$

`ψ₀(Ω_v)` ($v\ne0$) 的第 1 项不是后继, 而 $\omega$ 的第 1 项是后继. 所以 $\omega$ 不带这个标签.

```agda
cof-ψ₀ : ∀ b → [] <ᵗ b → cof (ψᵗ [] b ∷ []) ≡ c1 → ⊥
cof-ψ₀ (y ∷ ys) E.[]< e = cofA≢c1 [] (cof (y ∷ ys)) e

-- 第 1 项的形状
pick : ∀ w ws → Σ T λ b → ([] <ᵗ b) × (fsn (ψ₀ᵗ (Ωt (w ∷ ws))) 1 ≡ ψᵗ [] b ∷ [])
pick w ws = go (cof (w ∷ ws)) refl
  where
  v = w ∷ ws
  y = ψᵗ v []
  viaΩ : ∀ {μ} (be : cof (y ∷ []) ≡ cΩ μ) → Σ T λ b → ([] <ᵗ b) × (fsn (ψ₀ᵗ (Ωt v)) 1 ≡ ψᵗ [] b ∷ [])
  viaΩ {μ} be = fsT (y ∷ []) η , fsT-ne be E.[]< , trans (E.fsn₊-eq [] y [] 1 be) (aux (cmpᵀ (sucT μ) []) (cmp-suc[] μ))
    where
    η = ψᵗ μ (fsT (y ∷ []) (E.Ωt μ)) ∷ []
    aux : ∀ m → m ≡ gt → E.trm (E.fsn↓c [] y [] μ be m 1) ≡ ψᵗ [] (fsT (y ∷ []) η) ∷ []
    aux .gt refl = cong (λ z → ψᵗ [] z ∷ []) (trans (E.fsT↓-trm (y ∷ []) be _) (cong (fsT (y ∷ [])) (E.γ↓-trm (y ∷ []) μ be 1)))
  go : ∀ c → cof v ≡ c → Σ T λ b → ([] <ᵗ b) × (fsn (ψ₀ᵗ (Ωt v)) 1 ≡ ψᵗ [] b ∷ [])
  go c0 e = ⊥-elim (cof-ne w ws e)
  go c1 e = viaΩ (cong (E.cofψ0 v) e)
  go (cΩ ν) e = viaΩ (cong (E.cofψ0 v) e)
  go cω e = fsn (y ∷ []) 1 , subst ([] <ᵗ_) (sym (E.fsn0-eq w ws 1 e)) E.[]< , E.fsn₊-eq [] y [] 1 (cong (E.cofψ0 v) e)

-- 带后继树的标签
tr⁰ : {a b c : Ordᶜ zero} → a ≅ b → a ≅ c → b ≅ c
tr⁰ e e′ = ≅-trans (≅-sym e) e′

s≇z : {Y : Ordᶜ zero} → suc Y ≅ zero {ℓ = zero} → ⊥
s≇z ()

s≇l : {Y : Ordᶜ zero} {f : ℕ → Ordᶜ zero} → suc Y ≅ lim f → ⊥
s≇l ()

l≇z : {f : ℕ → Ordᶜ zero} → lim f ≅ zero {ℓ = zero} → ⊥
l≇z ()

l≇s : {Y : Ordᶜ zero} {f : ℕ → Ordᶜ zero} → lim f ≅ suc Y → ⊥
l≇s ()

lab-suc : ∀ {X Y t} → Lab X t → X ≅ suc Y → cof t ≡ c1
lab-suc (l0 c e) es = ⊥-elim (s≇z (tr⁰ es e))
lab-suc (l1 c e l) es = c
lab-suc (lω c e h) es = ⊥-elim (s≇l (tr⁰ es e))

nat1 : ∀ {X} → Lab X (natT 1) → Σ (Ordᶜ zero) λ Y → X ≅ suc Y
nat1 (l1 c e l) = _ , e

l-part : ∀ {f g : ℕ → Ordᶜ zero} → lim f ≅ lim g → ∀ n → f n ≅ g n
l-part (l≅ k) = k

two : ∀ {x t} → Lab x (ψ₀ᵗ (natT 1)) → Lab x t → cof (fsn t 1) ≡ c1
two (lω c e H) (l0 c′ e′) = ⊥-elim (l≇z (tr⁰ e e′))
two (lω c e H) (l1 c′ e′ l) = ⊥-elim (l≇s (tr⁰ e e′))
two (lω c e H) (lω c′ e′ H′) = lab-suc (H′ 1) (tr⁰ (l-part (tr⁰ e e′) 1) (proj₂ (nat1 (H 1))))

zero-or : ∀ v (G : Goodᴺ Cω.ωZ) → Lab (forceᴺ Cω.ωZ G) (ψ₀ᵗ (Ωt v)) → v ≡ []
zero-or [] G L = refl
zero-or (w ∷ ws) G L = ⊥-elim (cof-ψ₀ (proj₁ P) (proj₁ (proj₂ P)) (trans (cong cof (sym (proj₂ (proj₂ P)))) (two (ω-lab G) L)))
  where P = pick w ws

fsn-ψ₀Ω : ∀ u → cof u ≡ cω → ∀ n → fsn (ψ₀ᵗ (Ωt u)) n ≡ ψ₀ᵗ (Ωt (fsn u n))
fsn-ψ₀Ω [] () n
fsn-ψ₀Ω (w ∷ ws) e n = trans (E.fsn₊-eq [] (ψᵗ (w ∷ ws) []) [] n (cong (E.cofψ0 (w ∷ ws)) e)) (cong (λ z → ψᵗ [] z ∷ []) (E.fsn0-eq w ws n e))

cof-ψ₀Ω : ∀ u → cof u ≡ cω → cof (ψ₀ᵗ (Ωt u)) ≡ cω
cof-ψ₀Ω [] ()
cof-ψ₀Ω (w ∷ ws) e = cong (λ c → E.cofA [] (E.cofψ0 (w ∷ ws) c)) e

-- 定理: 对一切高度结构, 一切链行, 一切 u
module NoChain (𝕊 : HtB) where
  open import OCF.Align.LadderOrdMain 𝕊 using (GᴺTᵠ)
  private module C = OCF.Align.OrdLabChain 𝕊
  open HtB 𝕊 using (view)

  chain-needs-zero : ∀ {m F qf} → view m ≡ chain F qf → ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → ∀ u → cof u ≡ cω →
                     Lab (forceᴺ _ (GᴺTᵠ m zero ev z)) (ψ₀ᵗ (Ωt u)) → fsn u 0 ≡ []
  chain-needs-zero c ev z u cu L =
    zero-or (fsn u 0) (C.ChainRow.G₀ Rw)
      (subst (λ X → Lab X (ψ₀ᵗ (Ωt (fsn u 0)))) (C.ChainRow.first Rw)
        (subst (Lab (C.ChainRow.h Rw 0)) (fsn-ψ₀Ω u cu 0) (lab-lim L (cof-ψ₀Ω u cu) (C.ChainRow.eq Rw) 0)))
    where Rw = C.chain-row c ev z

-- 链行上的一般操作. X, Y 都是变量: 不计算证书
module GenRow (𝕊 : HtB) where
  private module C = OCF.Align.OrdLabChain 𝕊
  open C using (ChainRow; mkCR)

  tail-gen : ∀ {X Y} (Rw : ChainRow X Y) {s : ℕ → T} → (∀ n → Lab (Y n) (s n)) → ∀ n → Lab (ChainRow.h Rw (suc n)) (s n)
  tail-gen Rw L n = Lab-≅ (ChainRow.rest Rw n) (L n)

  fgh-gen : ∀ {X Y} (Rw : ChainRow X Y) n → FGH X (suc n) ≡ FGH (Y n) (suc n)
  fgh-gen Rw n = trans (FGH-≅ (ChainRow.eq Rw) (suc n)) (FGH-≅ (ChainRow.rest Rw n) (suc n))

  to-X : ∀ {X Y} (Rw : ChainRow X Y) n → ChainRow.h Rw n ⊑⁰ X
  to-X Rw n = ⊑-trans (⊑-lim n (≅→⊑ (≅-refl⁰ _))) (≅→⊑ (≅-sym (ChainRow.eq Rw)))

  -- 错开一位: X 与 lim Y 同值
  same-shift : ∀ {X Y} (Rw : ChainRow X Y) → (X ⊑⁰ lim Y) × (lim Y ⊑⁰ X)
  same-shift {X} {Y} Rw = ⊑-trans (≅→⊑ (ChainRow.eq Rw)) (lim-⊑ up′) , lim-⊑ (λ n → ⊑-trans (≅→⊑ (≅-sym (ChainRow.rest Rw n))) (to-X Rw (suc n)))
    where
    up′ : ∀ n → ChainRow.h Rw n ⊑⁰ lim Y
    up′ zero = ⊑-trans (ChainRow.step Rw 0) (⊑-trans (≅→⊑ (ChainRow.rest Rw 0)) (⊑-lim 0 (≅→⊑ (≅-refl⁰ _))))
    up′ (suc n) = ⊑-trans (≅→⊑ (ChainRow.rest Rw n)) (⊑-lim n (≅→⊑ (≅-refl⁰ _)))

  -- 只差第 0 项: h (n+1) ≅ Z (n+1), 且 Z 0 ⊑ Z 1
  same-head : ∀ {X Y} {Z : ℕ → Ordᶜ zero} (Rw : ChainRow X Y) → (∀ n → Y n ≅ Z (suc n)) → Z 0 ⊑⁰ Z 1 → (X ⊑⁰ lim Z) × (lim Z ⊑⁰ X)
  same-head {X} {Y} {Z} Rw e s₀ = ⊑-trans (≅→⊑ (ChainRow.eq Rw)) (lim-⊑ up′) , lim-⊑ dn′
    where
    sh : ∀ n → ChainRow.h Rw (suc n) ≅ Z (suc n)
    sh n = ≅-trans (ChainRow.rest Rw n) (e n)
    up′ : ∀ n → ChainRow.h Rw n ⊑⁰ lim Z
    up′ zero = ⊑-trans (ChainRow.step Rw 0) (⊑-trans (≅→⊑ (sh 0)) (⊑-lim 1 (≅→⊑ (≅-refl⁰ _))))
    up′ (suc n) = ⊑-trans (≅→⊑ (sh n)) (⊑-lim (suc n) (≅→⊑ (≅-refl⁰ _)))
    dn′ : ∀ n → Z n ⊑⁰ X
    dn′ zero = ⊑-trans s₀ (⊑-trans (≅→⊑ (≅-sym (sh 0))) (to-X Rw 1))
    dn′ (suc n) = ⊑-trans (≅→⊑ (≅-sym (sh n))) (to-X Rw (suc n))

  fgh-head : ∀ {X Y} {Z : ℕ → Ordᶜ zero} (Rw : ChainRow X Y) → (∀ n → Y n ≅ Z (suc n)) → ∀ n → FGH X (suc n) ≡ FGH (lim Z) (suc n)
  fgh-head Rw e n = trans (fgh-gen Rw n) (FGH-≅ (e n) (suc n))
```
