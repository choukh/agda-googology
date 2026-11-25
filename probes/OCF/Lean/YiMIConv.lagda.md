# 换基折叠上的五个旧名字落到五参数接口

> 判决: 编译定理, 无前提, 不读记号. 换基折叠 `YiBSFold.ψ` 上的五个旧定理 (另加候选折叠 `Fold K true` 上的 `lowᴷ`), 结论逐字是 [YiMIIface](YiMIIface.lagda.md) 的 `LowAt` 或 `Hold` 在一组参数上的取值: `lowᴮ`/`lowᵗ` (域全体), `lowᴰ`/`lowˣ` (域 `KD`), `low-tw1` (域只含 Ω 树, 由 `lowᴰ` 经 `hold-dom` 重新得到), `lowᶻ` (目标第 0 层, 全部状态, 即 `KeepSys`), `lowΩ` (域只含 Ω 树, 每个参照 a 另带参照一侧的条件, 不用 `R ℓ a x`).
> 不给出什么: 前提各不相同, 本文只给出 `low-tw1 ← lowᴰ` 一条旧定理之间的推导; 不证任何前提.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiMIConv where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base)
open import OCF.Lean.YiBSBase
import OCF.Lean.YiBSFold as BS
open import OCF.Lean.YiGIBlock using (blkᵍ)
open import OCF.Lean.YiAbsFrame using (Block; Fold)
open import OCF.Lean.YiAbsSim using (Val)
open import OCF.Lean.YiAbsGIface
open import OCF.Lean.YiFIIface
open import OCF.Lean.YiBLIface
open import OCF.Lean.YiBLFold
open import OCF.Lean.YiQDIface
open import OCF.Lean.YiQDFold
open import OCF.Lean.YiXTIface
open import OCF.Lean.YiXTReb using (module XReb)
open import OCF.Lean.YiSDIface using (module SD)
open import OCF.Lean.YiWRZero
open import OCF.Lean.YiVALeaf using (NZ)
open import OCF.Lean.YiTBRow using (h₁)
open import OCF.Lean.YiFIFold using (foldᴷ; rowsᴷ; module Tree)
open import OCF.Lean.YiDXFold using (KeepFn)
import OCF.Lean.YiTBRow as TB
open import Data.Bool using (true)
open import Data.Maybe using (nothing)
open import OCF.Lean.YiMIIface
```

## 根状态的换基行

参数同 `YiBLFold.Pack`. 五个参数的取值: 目标 j (经孩子 c′, `route` 落在地板之上), 路径 `w = inc c′ v`, 底 `(o , r , B)`, 上下文 Kc (系统的上下文 K₀ 经 `ec` 对上), 域见各条; 不变式 `Bdᴮ (rt β) K₀`.

```agda
module Root {𝕋 : Ref} {𝕍 : Val} (𝔾 : Graded blkᵍ foldᴮ rowsᴮ 𝕋 𝕍) (𝔻 : Doms blkᵍ foldᴮ)
    (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h)) (S : Schema k h) (rc : (c : Tr k) → Rb (h c))
    (B : Base (nd (sΩ k) h)) (j : L) (c′ : Tr k) (v : j ≤ h c′) (u : floor S ≤ j) (eq : route S j c′ v ≡ inj₂ u)
    (Cxtᴬ : Set) (apᴬ : Cxtᴬ → Ref.T 𝕋 → Ref.T 𝕋) (Bdᴬ : ∀ {a} → Aux.Stᴬ j a → Cxtᴬ → Set)
    (Cxtᴮ : Set) (apᴮ : Cxtᴮ → Ref.T 𝕋 → Ref.T 𝕋) (Bdᴮ : ∀ {a} → Main.Stᴮ k h o S rc B j c′ v u eq a → Cxtᴮ → Set)
    (Le : Ref.T 𝕋 → Ref.T 𝕋 → Set) (wk : Laws.Weak 𝔾 𝔻) (lm : Laws.Lim 𝔾 𝔻) (nod : Laws.Node 𝔾 𝔻)
    (gen : ∀ a → FI.Gen⁺ 𝔾 𝔻 Le a) where
  open Laws 𝔾 𝔻 using (Cx; Zero; Succ; Emb) renaming (R to Rᵍ)
  open FI 𝔾 𝔻 using (Sys)
  open BL 𝔾 𝔻 using (OutR)
  open QD 𝔾 𝔻 using (OutRDT; OutDT)
  open XT 𝔾 𝔻 using (Below; AboveL)
  open Rest 𝔾 𝔻 using (OutDN; OutRDN)
  open MI 𝔾 𝔻
  open Main k h o S rc B j c′ v u eq using (ℓ; r; w; rt)
  open QDPack 𝔾 𝔻 k h o S rc B j c′ v u eq Cxtᴬ apᴬ Bdᴬ Cxtᴮ apᴮ Bdᴮ

  lowᴮ→ : OutR sysᴮ sysᴬ keepᴬ embᴮ Le keepᴮ → Sys.Out sysᴬ Le keepᴬ fallᴬ
    → (β : Tr⁺ j) (K₀ : Cxtᴮ) → Bdᴮ (rt β) K₀ → (Kc : Cx ℓ j) → (∀ t → apᴮ K₀ t ≡ Laws.app 𝔾 𝔻 Kc t)
    → LowAt (o , r , B) w β Kc ⊤ᴰ
  lowᴮ→ ex exᴬ β K₀ bd Kc ec _ rr = lowᴮ Le wk lm nod ex exᴬ gen β K₀ bd Kc ec rr

  module _ (zr : Zero) (sr : Succ) (em : Emb) (leR : ∀ {s t o} → Le s t → Rᵍ j t o → Rᵍ j s o) where
    open WithRules Le wk lm nod zr sr em leR gen using (lowᴰ; ntᴬ)

    lowᴰ→ : OutRDT sysᴮ sysᴬ keepᴬ embᴮ Le keepᴮ Dᴮ ntᴮ → OutDT sysᴬ Le keepᴬ fallᴬ Dᴬ ntᴬ
      → (β : Tr⁺ j) (K₀ : Cxtᴮ) → Bdᴮ (rt β) K₀ → (Kc : Cx ℓ j) → (∀ t → apᴮ K₀ t ≡ Laws.app 𝔾 𝔻 Kc t)
      → LowAt (o , r , B) w β Kc KD
    lowᴰ→ exᴮ exᴬ β K₀ bd Kc ec = lowᴰ exᴮ exᴬ β K₀ bd Kc ec

    open XReb 𝔾 𝔻 k h o S rc B j c′ v u eq Cxtᴬ apᴬ Bdᴬ Cxtᴮ apᴮ Bdᴮ using (module WithR)
    open WithR Le wk lm nod zr sr em leR gen using (lowˣ; xtᴬ)

    lowˣ→ : OutRDN sysᴮ sysᴬ keepᴬ embᴮ Le Dᴮ → OutDN sysᴬ Le fallᴬ
      → Below sysᴮ → Below sysᴬ → AboveL sysᴬ keepᴬ Dᴬ xtᴬ
      → (β : Tr⁺ j) (K₀ : Cxtᴮ) → Bdᴮ (rt β) K₀ → (Kc : Cx ℓ j) → (∀ t → apᴮ K₀ t ≡ Laws.app 𝔾 𝔻 Kc t)
      → LowAt (o , r , B) w β Kc KD
    lowˣ→ rᴮ rᴬ blᴮ blᴬ ab β K₀ bd Kc ec = lowˣ rᴮ rᴬ blᴮ blᴬ ab β K₀ bd Kc ec
```

## 塔的项

`lowᵗ`: `Root` 在 `tw (suc n)` 上 (同 `YiBLFold.Tower`). `low-tw1`: 第 1 项, 域只含 Ω 树; 它由 `lowᴰ→` 沿 `KD ⊇ {Ω 树}` (`Ωt-tw1`) 经 `hold-dom` 得到, 与旧定义 `low-tw1 = lowᴰ … Ωt-tw1` 同一条推导.

```agda
module Tw {𝕋 : Ref} {𝕍 : Val} (𝔾 : Graded blkᵍ foldᴮ rowsᴮ 𝕋 𝕍) (𝔻 : Doms blkᵍ foldᴮ) where
  open Laws 𝔾 𝔻 using (Cx; Weak; Lim; Node; Zero; Succ; Emb) renaming (R to Rᵍ)
  open FI 𝔾 𝔻 using (Sys; Gen⁺)
  open BL 𝔾 𝔻 using (OutR)
  open QD 𝔾 𝔻 using (OutRDT; OutDT)
  open MI 𝔾 𝔻

  module _ (n : ℕ) (B : Base (tw (suc n))) (j : L) (c′ : Tr (tw n)) (v : j ≤ tw n ⊕ ↑ (tw n) c′) (u : tw n ≤ j)
      (eq : route (Sₙ n) j c′ v ≡ inj₂ u)
      (Cxtᴬ : Set) (apᴬ : Cxtᴬ → Ref.T 𝕋 → Ref.T 𝕋) (Bdᴬ : ∀ {a} → Aux.Stᴬ j a → Cxtᴬ → Set)
      (Cxtᴮ : Set) (apᴮ : Cxtᴮ → Ref.T 𝕋 → Ref.T 𝕋)
      (Bdᴮ : ∀ {a} → Main.Stᴮ (tw n) (λ c → tw n ⊕ ↑ (tw n) c) (Ok-tw (suc n)) (Sₙ n) (rcₙ n) B j c′ v u eq a → Cxtᴮ → Set)
      (Le : Ref.T 𝕋 → Ref.T 𝕋 → Set) (wk : Weak) (lm : Lim) (nod : Node) (gen : ∀ a → Gen⁺ Le a) where
    open Tower 𝔾 𝔻 n B j c′ v u eq Cxtᴬ apᴬ Bdᴬ Cxtᴮ apᴮ Bdᴮ using (lowᵗ; sysᴮ; sysᴬ; keepᴬ; embᴮ; keepᴮ; fallᴬ)

    lowᵗ→ : OutR sysᴮ sysᴬ keepᴬ embᴮ Le keepᴮ → Sys.Out sysᴬ Le keepᴬ fallᴬ
      → (β : Tr⁺ j) (K₀ : Cxtᴮ) → Bdᴮ (Main.rt β) K₀ → (Kc : Cx (tw (suc n)) j) → (∀ t → apᴮ K₀ t ≡ Laws.app 𝔾 𝔻 Kc t)
      → LowAt (Ok-tw (suc n) , rb-tw (suc n) , B) (inc c′ v) β Kc ⊤ᴰ
    lowᵗ→ ex exᴬ β K₀ bd Kc ec _ rr = lowᵗ Le wk lm nod ex exᴬ gen β K₀ bd Kc ec rr

  module _ (B : Base (tw 1)) {d : Tr zero} (nz : NZ d)
      (Cxtᴬ : Set) (apᴬ : Cxtᴬ → Ref.T 𝕋 → Ref.T 𝕋) (Bdᴬ : ∀ {a} → Aux.Stᴬ (h₁ d) a → Cxtᴬ → Set)
      (Cxtᴮ : Set) (apᴮ : Cxtᴮ → Ref.T 𝕋 → Ref.T 𝕋)
      (Bdᴮ : ∀ {a} → Main.Stᴮ zero h₁ (Ok-tw 1) (Sₙ 0) (rcₙ 0) B (h₁ d) d self (lift zero (↑ zero d)) (route-tw1 nz) a → Cxtᴮ → Set)
      (Le : Ref.T 𝕋 → Ref.T 𝕋 → Set) (wk : Weak) (lm : Lim) (nod : Node) (zr : Zero) (sr : Succ) (em : Emb)
      (leR : ∀ {s t o} → Le s t → Rᵍ (h₁ d) t o → Rᵍ (h₁ d) s o) (gen : ∀ a → Gen⁺ Le a) where
    open QDTw1 𝔾 𝔻 B nz Cxtᴬ apᴬ Bdᴬ Cxtᴮ apᴮ Bdᴮ
    open WithRules Le wk lm nod zr sr em leR gen using (lowᴰ; ntᴬ)

    Ωᴰ : Tr (tw 1) → Set
    Ωᴰ x = x ≡ proj₁ (Ωt (tw 1))

    low-tw1→ : OutRDT sysᴮ sysᴬ keepᴬ embᴮ Le keepᴮ Dᴮ ntᴮ → OutDT sysᴬ Le keepᴬ fallᴬ Dᴬ ntᴬ
      → (β : Tr⁺ (h₁ d)) (K₀ : Cxtᴮ) → Bdᴮ (Main.rt β) K₀ → (Kc : Cx (tw 1) (h₁ d)) → (∀ t → apᴮ K₀ t ≡ Laws.app 𝔾 𝔻 Kc t)
      → LowAt (Ok-tw 1 , rb-tw 1 , B) (inc d self) β Kc Ωᴰ
    low-tw1→ exᴮ exᴬ β K₀ bd Kc ec refl rr = low-tw1 Le wk lm nod zr sr em leR gen exᴮ exᴬ β K₀ bd Kc ec rr

    low-tw1′ : OutRDT sysᴮ sysᴬ keepᴬ embᴮ Le keepᴮ Dᴮ ntᴮ → OutDT sysᴬ Le keepᴬ fallᴬ Dᴬ ntᴬ
      → (β : Tr⁺ (h₁ d)) (K₀ : Cxtᴮ) → Bdᴮ (Main.rt β) K₀ → (Kc : Cx (tw 1) (h₁ d)) → (∀ t → apᴮ K₀ t ≡ Laws.app 𝔾 𝔻 Kc t)
      → LowAt (Ok-tw 1 , rb-tw 1 , B) (inc d self) β Kc Ωᴰ
    low-tw1′ exᴮ exᴬ β K₀ bd Kc ec = hold-dom {D = KD} {D′ = Ωᴰ} (λ e → subst KD (sym e) Ωt-tw1) (lowᴰ exᴮ exᴬ β K₀ bd Kc ec)
```

## 朝第 0 层

参数同 `YiWRZero.Zero`. 目标第 0 层, 路径 `z≤`, 一切状态 (底与底值任意); 即 `KeepSys sysᶻ`, 域全体, 不变式 `Bdᶻ`. 落到一点用 `sys→LowAt`.

```agda
module ToZero {𝕋 : Ref} {𝕍 : Val} (𝔾 : Graded blkᵍ foldᴮ rowsᴮ 𝕋 𝕍) (𝔻 : Doms blkᵍ foldᴮ)
    (Cxtᶻ : Set) (apᶻ : Cxtᶻ → Ref.T 𝕋 → Ref.T 𝕋) (Bdᶻ : ∀ {a} → Stᶻ a → Cxtᶻ → Set)
    (Le : Ref.T 𝕋 → Ref.T 𝕋 → Set) (wk : Laws.Weak 𝔾 𝔻) (lm : Laws.Lim 𝔾 𝔻) (nod : Laws.Node 𝔾 𝔻)
    (zr : Laws.Zero 𝔾 𝔻) (sr : Laws.Succ 𝔾 𝔻) (em : Laws.Emb 𝔾 𝔻)
    (leR : ∀ {s t o} → Le s t → Graded.R 𝔾 zero t o → Graded.R 𝔾 zero s o) (gen : ∀ a → FI.Gen⁺ 𝔾 𝔻 Le a) where
  open Laws 𝔾 𝔻 using (Cx; app)
  open XT 𝔾 𝔻 using (AboveL)
  open Rest 𝔾 𝔻 using (OutDN)
  open MI 𝔾 𝔻
  open Zero 𝔾 𝔻 Cxtᶻ apᶻ Bdᶻ
  open WithRules Le wk lm nod zr sr em leR gen using (lowᶻ; xtᶻ)

  lowᶻ→ : OutDN sysᶻ Le fallᶻ → AboveL sysᶻ keepᶻ Dᶻ xtᶻ → KeepSys sysᶻ (λ _ → ⊤ᴰ)
  lowᶻ→ rest ab s K bd _ rr = lowᶻ rest ab s K bd rr

  lowᶻ-pt : OutDN sysᶻ Le fallᶻ → AboveL sysᶻ keepᶻ Dᶻ xtᶻ
    → ∀ {ℓ} (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) (β : Tr⁺ zero) (K : Cxtᶻ) → Bdᶻ (o , r , B , β) K
    → (Kc : Cx ℓ zero) → (∀ t → apᶻ K t ≡ app Kc t) → LowAt (o , r , B) (z≤ ℓ) β Kc ⊤ᴰ
  lowᶻ-pt rest ab o r B β K bd Kc ec =
    sys→LowAt sysᶻ (lowᶻ→ rest ab) (o , r , B , β) K bd (o , r , B) (z≤ _) β Kc (λ _ → refl) ec
```

## Ω 树上的直接保持

参数同 `YiSDIface.SD`, `AtΩ`. `lowΩ` 只对 Ω 树, 不用 `R ℓ a x`: 每个参照 a 另要顶槽位允许的余尾与分支上的 `RefBr` (`CondΩ a`). 所以它是 `Hold` 在域 {Ω 树} 上的取值, 条件是 "每个 `R ℓ a (Ω 树)` 的 a 都有 `CondΩ a`"; 上下文是系统自己的 `apᴮ K`.

```agda
module OmegaTop {𝕋 : Ref} {𝕍 : Val} (𝔾 : Graded blkᵍ foldᴮ rowsᴮ 𝕋 𝕍) (𝔻 : Doms blkᵍ foldᴮ)
    (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h)) (S : Schema k h) (rc : (c : Tr k) → Rb (h c))
    (B : Base (nd (sΩ k) h)) (j : L) (c′ : Tr k) (v : j ≤ h c′) (u : floor S ≤ j) (eq : route S j c′ v ≡ inj₂ u)
    (Cxtᴬ : Set) (apᴬ : Cxtᴬ → Ref.T 𝕋 → Ref.T 𝕋) (Bdᴬ : ∀ {a} → Aux.Stᴬ j a → Cxtᴬ → Set)
    (Cxtᴮ : Set) (apᴮ : Cxtᴮ → Ref.T 𝕋 → Ref.T 𝕋) (Bdᴮ : ∀ {a} → Main.Stᴮ k h o S rc B j c′ v u eq a → Cxtᴮ → Set)
    (wk : Laws.Weak 𝔾 𝔻) (nod : Laws.Node 𝔾 𝔻)
    (auxK : ∀ {b} (s′ : Aux.Stᴬ j b) K″ → Bdᴬ s′ K″ → ∀ {t x} → Graded.R 𝔾 b t x
          → Graded.R 𝔾 j (apᴬ K″ t) (proj₁ (Aux.Φᴬ j s′ x))) where
  open Laws 𝔾 𝔻 using (Cx; app) renaming (R to Rᵍ)
  open MI 𝔾 𝔻
  open Main k h o S rc B j c′ v u eq using (ℓ; r; w; rt; Φᴮ)
  open SD 𝔾 𝔻 k h o S rc B j c′ v u eq Cxtᴬ apᴬ Bdᴬ Cxtᴮ apᴮ Bdᴮ using (Kept; module AtΩ)
  open AtΩ wk nod auxK using (lowΩ; RefBr)

  Ωᴰ : Tr ℓ → Set
  Ωᴰ x = x ≡ proj₁ (Ωt ℓ)

  CondΩ : Tr⁺ j → Cxtᴮ → Kept (inj₁ (inj₁ tt)) → Ref.T 𝕋 → Set
  CondΩ β K ev a = Σ (Ref.T 𝕋) λ κ → Ref.CΩ 𝕋 (apᴮ K a) κ × Graded.Nu 𝔾 j (proj₁ ev) κ
    × (∀ η c → Rᵍ k η c → RefBr β c (Ref.fsT 𝕋 (apᴮ K a) η))

  lowΩ→ : (β : Tr⁺ j) (K : Cxtᴮ) (ev : Kept (inj₁ (inj₁ tt)))
    → (∀ {a} → Rᵍ ℓ a (proj₁ (Ωt ℓ)) → CondΩ β K ev a)
    → Hold (λ x → proj₁ (Φᴮ (rt β) x)) (apᴮ K) Ωᴰ
  lowΩ→ β K ev cd refl rr with cd rr
  ... | κ , cΩ , nu , rf = lowΩ β K ev cΩ nu rf

  lowΩ-pt : (β : Tr⁺ j) (K : Cxtᴮ) (ev : Kept (inj₁ (inj₁ tt)))
    → (∀ {a} → Rᵍ ℓ a (proj₁ (Ωt ℓ)) → CondΩ β K ev a)
    → (Kc : Cx ℓ j) → (∀ t → apᴮ K t ≡ app Kc t) → LowAt (o , r , B) w β Kc Ωᴰ
  lowΩ-pt β K ev cd Kc ec {a} {x} d rr =
    subst (λ t → Rᵍ j t (proj₁ (Φᴮ (rt β) x))) (ec a) (lowΩ→ β K ev cd d rr)
```

## 上折回退的候选折叠

参数同 `YiFIFold.Tree`. `lowᴷ`: 折叠 `Fold K true`, 目标 j 经孩子 c′, 表整行缺项 (`r` 的第一分量处处 `nothing`), 域全体, 不变式 `Bdᴷ (rt β) K₀`.

```agda
module OnK (K : KeepFn) {𝕋 : Ref} {𝕍 : Val}
    (𝔾 : Graded blkᵍ (foldᴷ K true) (rowsᴷ K true) 𝕋 𝕍) (𝔻 : Doms blkᵍ (foldᴷ K true))
    (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h)) (rc : (c : Tr k) → TB.Rb (h c)) (B : Base (nd (sΩ k) h))
    (j : L) (c′ : Tr k) (v : j ≤ h c′)
    (Cxtᴷ : Set) (apᴷ : Cxtᴷ → Ref.T 𝕋 → Ref.T 𝕋) (Bdᴷ : ∀ {a} → Tree.Stᴷ K 𝔾 𝔻 k h o rc B j c′ v a → Cxtᴷ → Set)
    (Le : Ref.T 𝕋 → Ref.T 𝕋 → Set) (wk : Laws.Weak 𝔾 𝔻) (lm : Laws.Lim 𝔾 𝔻) (nod : Laws.Node 𝔾 𝔻)
    (gen : ∀ a → FI.Gen⁺ 𝔾 𝔻 Le a) where
  open Laws 𝔾 𝔻 using (Cx; app)
  open FI 𝔾 𝔻 using (module Sys)
  open MI 𝔾 𝔻
  open Tree K 𝔾 𝔻 k h o rc B j c′ v using (rt; sysᴷ; keepᴷ; fallᴷ; lowᴷ)

  lowᴷ→ : Sys.Out (sysᴷ Cxtᴷ apᴷ Bdᴷ) Le (keepᴷ Cxtᴷ apᴷ Bdᴷ) (fallᴷ Cxtᴷ apᴷ Bdᴷ)
    → (β : Tr⁺ j) (K₀ : Cxtᴷ) → Bdᴷ (rt β) K₀ → (Kc : Cx (nd (sΩ k) h) j) → (∀ t → apᴷ K₀ t ≡ app Kc t)
    → LowAt (o , ((λ _ _ → nothing) , rc) , B) (inc c′ v) β Kc ⊤ᴰ
  lowᴷ→ ex β K₀ bd Kc ec _ rr = lowᴷ Cxtᴷ apᴷ Bdᴷ Le wk lm nod ex gen β K₀ bd Kc ec rr
```
