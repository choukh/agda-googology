# 完整候选折叠满足换基接口的树一侧律

> 判决: 编译定理, 不读记号. 主系统是候选 `YiUFFold.ψ (suc d)` 在 Ω 形状层号上, 目标经孩子 c′ 且 `route` 落在地板之上的根状态; 辅助系统是候选 `ψ d` 在换基层号 `j ⊕ b` 上沿 `lift j b` 的折叠 (带证据) 连同上折. 保留律 (`keepᴮ`, `keepᴬ`), 回退律 (`fallᴬ`), 换基律 (`rebᴮ`), 单调都成立, 接上 `YiBLIface` 得 `lowᴮ`.
> 与 `YiBLFold` 的差别: 辅助系统是同一个折叠低一档并带证据 (那里是 `YiRBSib.ψ` 配 `rb-no`); 主系统下标侧槽位有保留证据 (那里塔第 2 项起没有).
> 不给出什么: 出口 `OutR` 与辅助系统的 `Out` 是前提, 没有实填; 不处理 `route` 落在地板之下的行. 来源: 逐段改自 `YiBLFold` (`Lf`, `cp`, `_⊴ᵗ_`, `dn₁`, `cW-eq` 原样导入). 域与 `lowᴰ` 在 [YiUFDom](YiUFDom.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiUFLaw where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀; node⁺)
open import OCF.Lean.YiBSBase using (Schema; schema; floor; offsets; ok-floor; index-floor; ok-offsets; shape; route; back; raiseO; downOk)
open import OCF.Lean.YiGIBlock using (blkᵍ; chLᵍ; ChTᵍ; chTᵍ; upᵍ; slTᵍ)
open import OCF.Lean.YiAbsFrame using (Block; Fold)
open import OCF.Lean.YiAbsSim using (Val)
open import OCF.Lean.YiAbsGIface
open import OCF.Lean.YiFIIface
open import OCF.Lean.YiFIFold using (node-eq)
open import OCF.Lean.YiBLIface
open import OCF.Lean.YiBLFold using (_⊴ᵗ_; dn₁; cW-eq)
import OCF.Lean.YiBLFold as BLF
open import OCF.Lean.YiUFBase
import OCF.Lean.YiUFFold as C
open C using (kp; kp⁼)
```

## 填进 `Fold`, `Rows`

底是 (合法证据, 候选的证据 `YiUFBase.Rb`, 原底); 折叠是第 D 个候选.

```agda
Bsᶜ : L → Set
Bsᶜ ℓ = Ok ℓ × Rb ℓ × Base ℓ

dnᶜ : ℕ → (ℓ : L) → Bsᶜ ℓ → (c : CH ℓ) → Tr ℓ → Bsᶜ (chLᵍ ℓ c)
dnᶜ D (nd s h) (o , r , b) c x = proj₂ o c , proj₂ r c , λ j w → C.ψ D (nd s h) o r b j (inc c w) (b j (inc c w)) x

foldᶜ : ℕ → Fold blkᵍ
foldᶜ D = record
  { Bs = Bsᶜ ; LegB = λ _ _ → ⊤ ; Bt = Tr⁺ ; LegT = λ _ _ → ⊤
  ; ψ  = λ ℓ b j w β x → proj₁ (C.ψ D ℓ (proj₁ b) (proj₁ (proj₂ b)) (proj₂ (proj₂ b)) j w β x)
  ; ψβ = λ ℓ b j w β x → C.ψ D ℓ (proj₁ b) (proj₁ (proj₂ b)) (proj₂ (proj₂ b)) j w β x
  ; dn = dnᶜ D }

rowsᶜ : (D : ℕ) → Rows blkᵍ (foldᶜ D)
rowsᶜ D = record
  { sc = suc ; Sl = Pos ; slL = at ; SlT = Br ; slT = slTᵍ ; nd = Ω
  ; Ωt = λ ℓ → proj₁ (Ωt ℓ) ; Dn = Dn ; upf = λ {ℓ} {j} d β y → proj₁ (Up j d β y)
  ; sucL = λ ℓ → nd sS (λ _ → ℓ) ; ΩL = λ k h → nd (sΩ k) h ; lift = ↑ }

fall-self : ∀ d (j : L) (o : Ok j) (r : Rb j) (B : Base j) (β : Tr⁺ j) (x : Tr j) (c : CH j) (y : ChTᵍ j c)
  → Up (chLᵍ j c) (dn₁ j c) (C.ψ d j o r B j self β x) (chTᵍ j c y) ≡ C.ψ d j o r B j self β (upᵍ x c y)
fall-self d (nd s h) o r B β x c (y , e) = refl
```

## 辅助系统: 换基层号上沿 `lift` 的候选折叠 (第 d 个, 带证据)

```agda
module Aux (d : ℕ) (j : L) where
  open BLF.Aux j using (Lf; here; there; lf; cp) public

  data Stᴬ : L → Set where
    rbs : (b : L) → Ok (j ⊕ b) → Rb (j ⊕ b) → Base (j ⊕ b) → Tr⁺ j → Stᴬ (j ⊕ b)
    us  : ∀ {a} → Dn j a → Tr⁺ j → Stᴬ a

  Φᴬ : ∀ {a} → Stᴬ a → Tr a → Tr⁺ j
  Φᴬ (rbs b o r B β) x = C.ψ d (j ⊕ b) o r B j (lift j b) β x
  Φᴬ (us {a} dn β) x   = Up a dn β x

  Evᴬ : ∀ {a} → Stᴬ a → Pos a → Set
  Evᴬ (rbs b o r B β) p = Σ (Pos j) λ q → Σ (Br j q → Br (j ⊕ b) p) λ cv → Σ (cv (fromBr j q zero) ≡ fromBr (j ⊕ b) p zero) λ e
    → kp (j ⊕ b) o r p (lift j b) ≡ just (q , cv , e)
  Evᴬ (us dn β) p = ⊤

  slotᴬ : ∀ {a} (s : Stᴬ a) (p : Pos a) → Evᴬ s p → Pos j
  slotᴬ (rbs b o r B β) p e = proj₁ e
  slotᴬ (us dn β) p e = mv dn p

  mvcᴬ : ∀ {a} (s : Stᴬ a) (p : Pos a) (e : Evᴬ s p) → Br j (slotᴬ s p e) → Br a p
  mvcᴬ (rbs b o r B β) p e z = proj₁ (proj₂ e) z
  mvcᴬ (us dn β) p e z = mvBr dn p z

  keepᴬ′ : ∀ {a} (s : Stᴬ a) (p : Pos a) (e : Evᴬ s p) (g : Br a p → Tr a)
    → Ω (slotᴬ s p e) (λ c → proj₁ (Φᴬ s (g (mvcᴬ s p e c)))) ⊴ᵗ proj₁ (Φᴬ s (Ω p g))
  keepᴬ′ (rbs b o r B β) p (q , cv , e , eq) g = inj₁ (node-eq (kp (j ⊕ b) o r p (lift j b)) q cv e _ _ eq)
  keepᴬ′ (us dn β) p e g = inj₁ refl

  dnD : ∀ {a} → Dn j a → (c : CH a) → Dn j (chLᵍ a c)
  dnD {a = zero} dn ()
  dnD {nd s h} dn c = down dn c

  stepᴬ : ∀ {a} → Stᴬ a → (c : CH a) → Tr a → Stᴬ (chLᵍ a c)
  stepᴬ (rbs zero o r B β) c x = us (dn₁ j c) (Φᴬ (rbs zero o r B β) x)
  stepᴬ (rbs (nd s h) o r B β) c x =
    rbs (h c) (proj₂ o c) (proj₂ r c) (λ i u → C.ψ d (j ⊕ nd s h) o r B i (inc c u) (B i (inc c u)) x) (Φᴬ (rbs (nd s h) o r B β) x)
  stepᴬ (us {a} dn β) c x = us (dnD dn c) (Up a dn β x)

  fallᴬ′ : ∀ {a} (s : Stᴬ a) (c : CH a) (x : Tr a) (y : ChTᵍ a c)
    → proj₁ (Φᴬ (stepᴬ s c x) (chTᵍ a c y)) ⊴ᵗ proj₁ (Φᴬ s (upᵍ x c y))
  fallᴬ′ (rbs zero o r B β) c x y = inj₁ (cong proj₁ (fall-self d j o r B β x c y))
  fallᴬ′ (rbs (nd s h) o r B β) c x (y , e) = inj₁ refl
  fallᴬ′ (us {a = zero} dn β) () x y
  fallᴬ′ (us {nd s h} dn β) c x (y , e) = inj₁ refl

  monoᴬ′ : ∀ {a} (s : Stᴬ a) {x y : Tr a} → a ⊢ x ◃ y → j ⊢ proj₁ (Φᴬ s x) ◃ proj₁ (Φᴬ s y)
  monoᴬ′ (rbs b o r B β) q = C.mono d (j ⊕ b) o r B j (lift j b) β q
  monoᴬ′ (us {a} dn β) q   = Upm a dn β q
```

目标层槽位的副本在 `lift j b` 下保留, 落回原槽位 (同 `YiBLFold.Aux.ev-cp`, 对候选的 `kp` 与任意证据).

```agda
  ev-cp : (b : L) (l : Lf b) (o : Ok (j ⊕ b)) (r : Rb (j ⊕ b)) (q : Pos j)
    → Σ (Br j q → Br (j ⊕ b) (cp b l q)) λ cv → Σ (cv (fromBr j q zero) ≡ fromBr (j ⊕ b) (cp b l q) zero) λ e
      → kp (j ⊕ b) o r (cp b l q) (lift j b) ≡ just (q , cv , e)
  ev-cp .zero     here                o r q = (λ z → z) , refl , refl
  ev-cp .(nd _ _) (there {h = h} c l) o r q = ev-cp (h c) l (proj₂ o c) (proj₂ r c) q

  evᴬ-cp : (b : L) (l : Lf b) (o : Ok (j ⊕ b)) (r : Rb (j ⊕ b)) (B : Base (j ⊕ b)) (β : Tr⁺ j) (q : Pos j)
    → Evᴬ (rbs b o r B β) (cp b l q)
  evᴬ-cp b l o r B β q = q , ev-cp b l o r q
```

## 主系统: 换基行的根状态

```agda
module Main (d : ℕ) (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h)) (rk : Rb k) (S : Schema k h) (rc : (c : Tr k) → Rb (h c))
            (B : Base (nd (sΩ k) h)) (j : L) (c′ : Tr k) (v : j ≤ h c′) (u : floor S ≤ j)
            (eq : route S j c′ v ≡ inj₂ u) where
  open Aux d j
  ℓ : L
  ℓ = nd (sΩ k) h
  r : Rb ℓ
  r = (rk , just S) , rc
  w : j ≤ ℓ
  w = inc c′ v
  oj : Ok j
  oj = downOk (h c′) (proj₂ o c′) j v
  rj : Rb j
  rj = rb≤ (h c′) (rc c′) v

  data Stᴮ : L → Set where
    rt : Tr⁺ j → Stᴮ (nd (sΩ k) h)

  Φᴮ : ∀ {a} → Stᴮ a → Tr a → Tr⁺ j
  Φᴮ (rt β) x = C.ψ (suc d) ℓ o r B j w β x

  Evᴮ : ∀ {a} → Stᴮ a → Pos a → Set
  Evᴮ (rt β) p = Σ (Pos j) λ q → Σ (Br j q → Br ℓ p) λ cv → Σ (cv (fromBr j q zero) ≡ fromBr ℓ p zero) λ e
    → kp ℓ o r p w ≡ just (q , cv , e)

  slotᴮ : ∀ {a} (s : Stᴮ a) (p : Pos a) → Evᴮ s p → Pos j
  slotᴮ (rt β) p e = proj₁ e

  mvcᴮ : ∀ {a} (s : Stᴮ a) (p : Pos a) (e : Evᴮ s p) → Br j (slotᴮ s p e) → Br a p
  mvcᴮ (rt β) p e z = proj₁ (proj₂ e) z

  keepᴮ′ : ∀ {a} (s : Stᴮ a) (p : Pos a) (e : Evᴮ s p) (g : Br a p → Tr a)
    → Ω (slotᴮ s p e) (λ c → proj₁ (Φᴮ s (g (mvcᴮ s p e c)))) ⊴ᵗ proj₁ (Φᴮ s (Ω p g))
  keepᴮ′ (rt β) p (q , cv , e , eq′) g = inj₁ (node-eq (kp ℓ o r p w) q cv e _ _ eq′)

  main-noEv : ∀ β (c : Tr k) (t : Pos⁼ (h c)) → Evᴮ (rt β) (inj₂ (c , t)) → ⊥
  main-noEv β c t (q , cv , e , ())

  monoᴮ′ : ∀ {a} (s : Stᴮ a) {x y : Tr a} → a ⊢ x ◃ y → j ⊢ proj₁ (Φᴮ s x) ◃ proj₁ (Φᴮ s y)
  monoᴮ′ (rt β) q = C.mono (suc d) ℓ o r B j w β q

  row-reb : ∀ β x c y e → C.ψ (suc d) ℓ o r B j w β (up x c y e)
    ≡ C.seen d S j oj rj u (C.ψ (suc d) ℓ o r B j w β x) c
      ⊞ C.ψ (suc d) (h c) (proj₂ o c) (rc c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y
  row-reb β x c y e = cW-eq (route S j c′ v) eq

  oᴮ : (c : Tr k) → Ok (j ⊕ offsets S c)
  oᴮ c = Ok⊕ j (offsets S c) oj (raiseO (floor S) j (offsets S c) u (ok-offsets S c))

  Srᴮ : Tr⁺ j → (c : Tr k) → Tr ℓ → Stᴬ (j ⊕ offsets S c)
  Srᴮ β c x = rbs (offsets S c) (oᴮ c) (rb-row S j oj rj u c) (B₀ _) (C.ψ (suc d) ℓ o r B j w β x)

  subᴮ : (c : Tr k) → Tr ℓ → Tr (j ⊕ offsets S c)
  subᴮ c x = proj₁ (Ωt (j ⊕ offsets S c))

  rebᴮ′ : ∀ β c x (y : ChTᵍ ℓ c) → proj₁ (Φᴬ (Srᴮ β c x) (subᴮ c x)) ⊴ᵗ proj₁ (Φᴮ (rt β) (upᵍ x c y))
  rebᴮ′ β c x (y , e) = inj₂ (subst (λ Z → j ⊢ proj₁ (C.seen d S j oj rj u (C.ψ (suc d) ℓ o r B j w β x) c) ◃ proj₁ Z)
    (sym (row-reb β x c y e))
    (+-mono _ (ι-mono j (proj₂ (C.ψ (suc d) (h c) (proj₂ o c) (rc c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y)))))
```

## 接上整体接口

```agda
wfL : ∀ {D} {𝕋 : Ref} {𝕍 : Val} (𝔾 : Graded blkᵍ (foldᶜ D) (rowsᶜ D) 𝕋 𝕍) (𝔻 : Doms blkᵍ (foldᶜ D)) (a : L) → FI.WfL 𝔾 𝔻 a
wfL 𝔾 𝔻 zero      = FI.wf (λ ())
wfL 𝔾 𝔻 (nd s h′) = FI.wf (λ c → wfL 𝔾 𝔻 (h′ c))

module Pack (d : ℕ) {𝕋 : Ref} {𝕍 : Val} (𝔾 : Graded blkᵍ (foldᶜ (suc d)) (rowsᶜ (suc d)) 𝕋 𝕍) (𝔻 : Doms blkᵍ (foldᶜ (suc d)))
    (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h)) (rk : Rb k) (S : Schema k h) (rc : (c : Tr k) → Rb (h c))
    (B : Base (nd (sΩ k) h)) (j : L) (c′ : Tr k) (v : j ≤ h c′) (u : floor S ≤ j) (eq : route S j c′ v ≡ inj₂ u)
    (Cxtᴬ : Set) (apᴬ : Cxtᴬ → Ref.T 𝕋 → Ref.T 𝕋) (Bdᴬ : ∀ {a} → Aux.Stᴬ d j a → Cxtᴬ → Set)
    (Cxtᴮ : Set) (apᴮ : Cxtᴮ → Ref.T 𝕋 → Ref.T 𝕋) (Bdᴮ : ∀ {a} → Main.Stᴮ d k h o rk S rc B j c′ v u eq a → Cxtᴮ → Set) where
  open FI 𝔾 𝔻
  open BL 𝔾 𝔻
  open Laws 𝔾 𝔻 using (Weak; Lim; Node; app; Cx) renaming (R to Rᵍ)
  open Aux d j
  open Main d k h o rk S rc B j c′ v u eq

  sysᴬ : Sys j
  sysᴬ = record { St = Stᴬ ; Φ = λ s x → proj₁ (Φᴬ s x) ; Ev = Evᴬ ; Cxt = Cxtᴬ ; ap = apᴬ ; Bdˢ = Bdᴬ }
  keepᴬ : Sys.KeepLaw sysᴬ
  keepᴬ = record { slot = slotᴬ ; mvc = mvcᴬ ; keep = keepᴬ′ }
  fallᴬ : Sys.FallLaw sysᴬ
  fallᴬ = record { step = stepᴬ ; fall = fallᴬ′ }
  monoᴬ : Sys.Monoˢ sysᴬ
  monoᴬ = monoᴬ′

  sysᴮ : Sys j
  sysᴮ = record { St = Stᴮ ; Φ = λ s x → proj₁ (Φᴮ s x) ; Ev = Evᴮ ; Cxt = Cxtᴮ ; ap = apᴮ ; Bdˢ = Bdᴮ }
  keepᴮ : Sys.KeepLaw sysᴮ
  keepᴮ = record { slot = slotᴮ ; mvc = mvcᴮ ; keep = keepᴮ′ }
  monoᴮ : Sys.Monoˢ sysᴮ
  monoᴮ = monoᴮ′

  rebᴮ : ∀ {a} (s : Stᴮ a) → RebAt sysᴮ sysᴬ keepᴬ s
  rebᴮ (rt β) = record
    { Lr  = λ c x → j ⊕ offsets S c
    ; Sr  = Srᴮ β
    ; sub = subᴮ
    ; reb = rebᴮ′ β
    ; lw  = λ c x → lift j (offsets S c)
    ; cp  = λ c x q → cp (offsets S c) (lf (offsets S c)) q
    ; cpE = λ c x q → evᴬ-cp (offsets S c) (lf (offsets S c)) (oᴮ c) (rb-row S j oj rj u c) (B₀ _) (C.ψ (suc d) ℓ o r B j w β x) q
    ; cpS = λ c x q → refl }

  embᴮ : EmbLaw sysᴮ sysᴬ keepᴬ
  embᴮ = record { row = λ s → inj₂ (rebᴮ s) }

  lowᴮ : (Le : Ref.T 𝕋 → Ref.T 𝕋 → Set) (wk : Weak) (lm : Lim) (nod : Node)
    → OutR sysᴮ sysᴬ keepᴬ embᴮ Le keepᴮ → Sys.Out sysᴬ Le keepᴬ fallᴬ → (∀ a → Gen⁺ Le a)
    → (β : Tr⁺ j) (K₀ : Cxtᴮ) → Bdᴮ (rt β) K₀ → (Kc : Cx ℓ j) → (∀ t → apᴮ K₀ t ≡ app Kc t)
    → ∀ {a x} → Rᵍ ℓ a x → Rᵍ j (app Kc a) (proj₁ (C.ψ (suc d) ℓ o r B j w β x))
  lowᴮ Le wk lm nod ex exᴬ gen β K₀ bd Kc ec =
    SuffRA.sys→low sysᴮ sysᴬ keepᴬ embᴮ Le wk lm nod monoᴮ keepᴮ ex monoᴬ fallᴬ exᴬ (wfL 𝔾 𝔻) gen
      (wfL 𝔾 𝔻 ℓ) (rt β) K₀ bd (o , r , B) w β Kc (λ x → refl) ec
```

## 塔各项

```agda
Sₙ : (n : ℕ) → Schema (tw n) (λ c → tw n ⊕ ↑ (tw n) c)
Sₙ n = schema (tw n) (↑ (tw n)) (Ok-tw n) self (OkO↑ (tw n) (tw n) (Ok-tw n) self) (λ c → refl)

rcₙ : (n : ℕ) (c : Tr (tw n)) → Rb (tw n ⊕ ↑ (tw n) c)
rcₙ n c = rbO (tw n) (↑ (tw n) c) (rb-tw n) (Ok-tw n) (OkO↑ (tw n) (tw n) (Ok-tw n) self c)

rb-tw≡ : (n : ℕ) → rb-tw (suc n) ≡ ((rb-tw n , just (Sₙ n)) , rcₙ n)
rb-tw≡ n = refl
```
