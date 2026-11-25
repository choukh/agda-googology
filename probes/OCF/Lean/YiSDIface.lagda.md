# 换基行嵌入出口的分解: 逐点的三种情形, 读回形式, Ω 树上的直接保持

> 判决: 接口与编译定理, 无前提, 不读记号. 嵌入出口第二分量 ("替身支配原材料", `Dominate`) 与两棵 Ω 树之间的形式 (`SubDomᴷ`) 互推 (`need`, `give`); 逐点的义务 `SubAt` 在三种字面条件下: 参照已对着替身 (`same`), 参照 Le 不高于替身的某个参照 (`cap`), 参照高于替身的一切参照时无解 (`stuck`).
> 读回形式 `SubRead` (孩子 c 的每个读法 η 给出替身的参照 `top η`) 推出带盖的支配 `CapDom`; Ω 树上换基折叠的保持 (`lowΩ`) 只要顶槽位保留, 上下文保持余尾 Ω, 每个分支上一份 `RefBr`, 不要一般的 `SubDom`, `Hand₁`. 前缀上下文下 `Hand₁` 成立 (`Prefix.hand₁`), `RefBr` 由 `SubRead` 给出 (`Prefix.refBr`).
> 不给出什么: 一般参照上的 `SubDom` 没有证也没有否定; `stuck` 的前提没有实例. 记号一侧的实例在 [YiSDRead](YiSDRead.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSDIface where

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiBSBase
open import OCF.Lean.YiGIBlock using (blkᵍ; ChTᵍ; chTᵍ; upᵍ)
open import OCF.Lean.YiAbsSim using (Val)
open import OCF.Lean.YiAbsGIface
open import OCF.Lean.YiAbsGRow
open import OCF.Lean.YiFIIface
open import OCF.Lean.YiBLIface
open import OCF.Lean.YiBLFold
open import OCF.Lean.YiQDIface
open import OCF.Lean.YiQDFold
```

## 出口的分解

参数同 `YiQDFold.QDPack`. `SubAt c t s`: 孩子 c, 左参照 t, 孩子参照 s 这一点上的义务 (替身层号 `j ⊕ offsets S c` 的 Ω 树上找一个参照 s″, 使 t ⊕ s 沿 Le 不高于 t ⊕ s″).

```agda
module SD {𝕋 : Ref} {𝕍 : Val} (𝔾 : Graded blkᵍ foldᴮ rowsᴮ 𝕋 𝕍) (𝔻 : Doms blkᵍ foldᴮ)
    (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h)) (S : Schema k h) (rc : (c : Tr k) → Rb (h c))
    (B : Base (nd (sΩ k) h)) (j : L) (c′ : Tr k) (v : j ≤ h c′) (u : floor S ≤ j) (eq : route S j c′ v ≡ inj₂ u)
    (Cxtᴬ : Set) (apᴬ : Cxtᴬ → Ref.T 𝕋 → Ref.T 𝕋) (Bdᴬ : ∀ {a} → Aux.Stᴬ j a → Cxtᴬ → Set)
    (Cxtᴮ : Set) (apᴮ : Cxtᴮ → Ref.T 𝕋 → Ref.T 𝕋) (Bdᴮ : ∀ {a} → Main.Stᴮ k h o S rc B j c′ v u eq a → Cxtᴮ → Set) where
  open QD 𝔾 𝔻
  open Laws 𝔾 𝔻 using (Weak; Lim; Node; Zero; Succ; Emb) renaming (R to Rᵍ)
  open Aux j
  open Main k h o S rc B j c′ v u eq
  open QDPack 𝔾 𝔻 k h o S rc B j c′ v u eq Cxtᴬ apᴬ Bdᴬ Cxtᴮ apᴮ Bdᴮ public

  Tᵣ : Set
  Tᵣ = Ref.T 𝕋

  Lrᶜ : Tr k → L
  Lrᶜ c = j ⊕ offsets S c

  Ωˢ : (c : Tr k) → Tr (Lrᶜ c)
  Ωˢ c = proj₁ (Ωt (Lrᶜ c))

  module Split (Le : Tᵣ → Tᵣ → Set) (wk : Weak) where
    open SubstDom Le wk

    SubAt : Tr k → Tᵣ → Tᵣ → Set
    SubAt c t s = Σ Tᵣ λ s″ → Rᵍ (Lrᶜ c) s″ (Ωˢ c) × Le (Ref._⊕_ 𝕋 t s) (Ref._⊕_ 𝕋 t s″)

    Dominate : Set
    Dominate = (c : Tr k) → ∀ {t s x} (y : ChTᵍ ℓ c) → KD (upᵍ x c y) → Rᵍ ℓ t x → Rᵍ (h c) s (chTᵍ ℓ c y) → SubAt c t s

    SubDomᴷ : Set
    SubDomᴷ = ∀ (c : Tr k) {t s : Tᵣ} {x : Tr ℓ} → KD x → Rᵍ ℓ t x → Rᵍ (h c) s (proj₁ (Ωt (h c))) → SubAt c t s
```

域里的嵌入的原材料 `⊴` 孩子层号的 Ω 树, Ω 树自己也在域里: 所以 `Dominate` 恰是两棵 Ω 树之间的形式. `SubDomᴷ` 比 `YiQDFold` 的 `SubDom` 多一个前提 `KD x`.

```agda
    need : Dominate → SubDomᴷ
    need dm c kd r rs = dm c (Ωt (h c)) (kd , inj₁ refl) r rs

    give : SubDomᴷ → Dominate
    give sd c (y , e) (kd , le) r ry = sd c kd r (Row.wk⊴ 𝔾 𝔻 wk ry le)

    weaken : SubDom → SubDomᴷ
    weaken sd c _ r rs = sd c r rs

    toOut : Hand₁ → Dominate → ∀ {a} (s : Stᴮ a) K → Bdᴮ s K → EmbOutD sysᴮ sysᴬ keepᴬ embᴮ Le Dᴮ s K (inj₂ (rebᴮ s))
    toOut e₁ dm (rt β) K bd = e₁ β K bd , dm

    fromOut : (β : Tr⁺ j) (K : Cxtᴮ) → EmbOutD sysᴮ sysᴬ keepᴬ embᴮ Le Dᴮ (rt β) K (inj₂ (rebᴮ (rt β))) → Dominate
    fromOut β K E = proj₂ E
```

逐点的三种情形. `stuck` 的 H 是替身的一切参照都满足的性质; 这一点的参照沿 Le 越过它时无解.

```agda
    same : (∀ {t} → Le t t) → ∀ c {t s} → Rᵍ (Lrᶜ c) s (Ωˢ c) → SubAt c t s
    same rf c {s = s} r = s , r , rf

    cap : (∀ t {s s″} → Le s s″ → Le (Ref._⊕_ 𝕋 t s) (Ref._⊕_ 𝕋 t s″))
      → ∀ c {t s s″} → Le s s″ → Rᵍ (Lrᶜ c) s″ (Ωˢ c) → SubAt c t s
    cap cg c {t} {s″ = s″} le r = s″ , r , cg t le

    stuck : ∀ c {t s} (H : Tᵣ → Set) → (∀ {s″} → Rᵍ (Lrᶜ c) s″ (Ωˢ c) → H s″)
      → (∀ {s″} → H s″ → Le (Ref._⊕_ 𝕋 t s) (Ref._⊕_ 𝕋 t s″) → ⊥) → SubAt c t s → ⊥
    stuck c H al no (s″ , r , le) = no (al r) le
```

读回形式. `ρ c η`: η 是孩子 c 的一个读法; `top η`: 由它给出的替身层号的参照. `CapDom`: 孩子参照沿 Le 不高于某个 `top η` 的点上义务成立.

```agda
    SubRead : (Tr k → Tᵣ → Set) → (Tᵣ → Tᵣ) → Set
    SubRead ρ top = ∀ c {η} → ρ c η → Rᵍ (Lrᶜ c) (top η) (Ωˢ c)

    CapDom : (Tr k → Tᵣ → Set) → (Tᵣ → Tᵣ) → Set
    CapDom ρ top = ∀ c {t s η} → ρ c η → Le s (top η) → SubAt c t s

    read→cap : (∀ t {s s″} → Le s s″ → Le (Ref._⊕_ 𝕋 t s) (Ref._⊕_ 𝕋 t s″))
      → ∀ {ρ top} → SubRead ρ top → CapDom ρ top
    read→cap cg sr c q le = cap cg c le (sr c q)
```

## Ω 树上的直接保持

`Ωt ℓ` 只有顶结点与每个分支上一个嵌入 `up zero c (Ωt (h c))`. 顶槽位保留时, 换基折叠在它上面的保持不经过主系统的生成原理: 分支 c 上只要一份 `RefBr` (辅助系统的上下文与替身的参照, 合起来是要证的参照), 再用辅助系统上的保持 `auxK`.

```agda
  module AtΩ (wk : Weak) (nod : Node)
      (auxK : ∀ {b} (s′ : Stᴬ b) K″ → Bdᴬ s′ K″ → ∀ {t x} → Rᵍ b t x → Rᵍ j (apᴬ K″ t) (proj₁ (Φᴬ s′ x))) where

    RefBr : Tr⁺ j → Tr k → Tᵣ → Set
    RefBr β c a′ = Σ Cxtᴬ λ K″ → Σ Tᵣ λ s″ → Bdᴬ (Srᴮ β c zero) K″ × Rᵍ (Lrᶜ c) s″ (Ωˢ c) × (apᴬ K″ s″ ≡ a′)

    low-branch : (β : Tr⁺ j) (c : Tr k) {a′ : Tᵣ} → RefBr β c a′
      → Rᵍ j a′ (proj₁ (Φᴮ (rt β) (proj₁ (upz c (Ωt (h c))))))
    low-branch β c (K″ , s″ , bd″ , rs , e) = Row.wk⊴ 𝔾 𝔻 wk
      (subst (λ z → Rᵍ j z (proj₁ (Φᴬ (Srᴮ β c zero) (subᴮ c zero)))) e (auxK (Srᴮ β c zero) K″ bd″ rs))
      (rebᴮ′ β c zero (Ωt (h c)))

    lowΩ : (β : Tr⁺ j) (K : Cxtᴮ) (ev : Kept (inj₁ (inj₁ tt))) {a κ : Tᵣ}
      → Ref.CΩ 𝕋 (apᴮ K a) κ → Graded.Nu 𝔾 j (proj₁ ev) κ
      → (∀ η c → Rᵍ k η c → RefBr β c (Ref.fsT 𝕋 (apᴮ K a) η))
      → Rᵍ j (apᴮ K a) (proj₁ (Φᴮ (rt β) (proj₁ (Ωt ℓ))))
    lowΩ β K ev cΩ nu rf = Row.wk⊴ 𝔾 𝔻 wk
      (nod (proj₁ ev) (λ z → proj₁ (Φᴮ (rt β) (proj₁ (upz (mvcᴮ (rt β) (inj₁ (inj₁ tt)) ev z) (Ωt (h (mvcᴮ (rt β) (inj₁ (inj₁ tt)) ev z)))))))
        cΩ nu
        (λ η z l → low-branch β (mvcᴮ (rt β) (inj₁ (inj₁ tt)) ev z) (rf η _ (mvRᴮ (rt β) (inj₁ (inj₁ tt)) ev η z l))))
      (keepᴮ′ (rt β) (inj₁ (inj₁ tt)) ev (λ c → proj₁ (upz c (Ωt (h c)))))
```

`auxK` 由辅助系统的出口 `OutDT` 给出 (`YiQDIface.SuffD.keepAllᴰ`, 域取全体).

```agda
  module FromAux (Le : Tᵣ → Tᵣ → Set) (wk : Weak) (lm : Lim) (nod : Node) (zr : Zero) (sr : Succ) (em : Emb)
      (leR : ∀ {s t o} → Le s t → Rᵍ j t o → Rᵍ j s o) (gen : ∀ a → FI.Gen⁺ 𝔾 𝔻 Le a) where
    open WithRules Le wk lm nod zr sr em leR gen

    module _ (exᴬ : OutDT sysᴬ Le keepᴬ fallᴬ Dᴬ ntᴬ) where
      auxKᴬ : ∀ {b} (s′ : Stᴬ b) K″ → Bdᴬ s′ K″ → ∀ {t x} → Rᵍ b t x → Rᵍ j (apᴬ K″ t) (proj₁ (Φᴬ s′ x))
      auxKᴬ {b} s′ K″ bd″ r = SuffD.keepAllᴰ sysᴬ Le wk lm nod monoᴬ keepᴬ fallᴬ domᴬ (λ _ _ _ _ _ → tt)
        (outDT→outD sysᴬ exᴬ) gen (wfL 𝔾 𝔻 b) s′ K″ bd″ r tt

      open AtΩ wk nod auxKᴬ public
```

## 前缀上下文

上下文取 (标签 x, 前缀 P), 作用 `F x (P ⊕ t)`; 状态对着上下文的条件取 "底值对着 `F x P`". 则 `Hand₁` 对一切 t, x 成立 (只用 ⊕ 的结合律), 分支上的 `RefBr` 由读回形式与 "作用与代入交换到 `top η`" 给出.

```agda
module Prefix {𝕋 : Ref} {𝕍 : Val} (𝔾 : Graded blkᵍ foldᴮ rowsᴮ 𝕋 𝕍) (𝔻 : Doms blkᵍ foldᴮ)
    (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h)) (S : Schema k h) (rc : (c : Tr k) → Rb (h c))
    (B : Base (nd (sΩ k) h)) (j : L) (c′ : Tr k) (v : j ≤ h c′) (u : floor S ≤ j) (eq : route S j c′ v ≡ inj₂ u)
    (X : Set) (F : X → Ref.T 𝕋 → Ref.T 𝕋)
    (assoc : ∀ a b c → Ref._⊕_ 𝕋 (Ref._⊕_ 𝕋 a b) c ≡ Ref._⊕_ 𝕋 a (Ref._⊕_ 𝕋 b c)) where
  open Laws 𝔾 𝔻 using (Weak; Node) renaming (R to Rᵍ)
  open Aux j
  open Main k h o S rc B j c′ v u eq

  Cxtᵖ : Set
  Cxtᵖ = X × Ref.T 𝕋

  apᵖ : Cxtᵖ → Ref.T 𝕋 → Ref.T 𝕋
  apᵖ (x , P) t = F x (Ref._⊕_ 𝕋 P t)

  Bdᴬᵖ : ∀ {a} → Stᴬ a → Cxtᵖ → Set
  Bdᴬᵖ (rbs b o′ B′ β) (x , P) = Rᵍ j (F x P) (proj₁ β)
  Bdᴬᵖ (us d β)        (x , P) = Rᵍ j (F x P) (proj₁ β)

  Bdᴮᵖ : ∀ {a} → Stᴮ a → Cxtᵖ → Set
  Bdᴮᵖ (rt β) (x , P) = Rᵍ j (F x P) (proj₁ β)

  open SD 𝔾 𝔻 k h o S rc B j c′ v u eq Cxtᵖ apᵖ Bdᴬᵖ Cxtᵖ apᵖ Bdᴮᵖ public

  module _ (Le : Ref.T 𝕋 → Ref.T 𝕋 → Set) (wk : Weak) where
    open SubstDom Le wk
    open Split Le wk

    hand₁ : Hand₁
    hand₁ β (x , P) bd c {t} r q = (x , Ref._⊕_ 𝕋 P t) , q , λ s → cong (F x) (assoc P t s)

    module _ (nod : Node)
        (auxK : ∀ {b} (s′ : Stᴬ b) K″ → Bdᴬᵖ s′ K″ → ∀ {t x} → Rᵍ b t x → Rᵍ j (apᵖ K″ t) (proj₁ (Φᴬ s′ x))) where
      open AtΩ wk nod auxK

      refBr : ∀ {ρ top} → SubRead ρ top → (β : Tr⁺ j) (K : Cxtᵖ) → Bdᴮᵖ (rt β) K
        → ∀ c {η a′} → ρ c η → apᵖ K (top η) ≡ a′ → RefBr β c a′
      refBr {top = top} sr β (x , P) bd c {η} q e = (x , P) , top η , bd , sr c q , e

      lowΩᵖ : ∀ {top} → SubRead (λ c η → Rᵍ k η c) top → (β : Tr⁺ j) (K : Cxtᵖ) → Bdᴮᵖ (rt β) K
        → (ev : Kept (inj₁ (inj₁ tt))) {a κ : Ref.T 𝕋}
        → Ref.CΩ 𝕋 (apᵖ K a) κ → Graded.Nu 𝔾 j (proj₁ ev) κ
        → (∀ η → apᵖ K (top η) ≡ Ref.fsT 𝕋 (apᵖ K a) η)
        → Rᵍ j (apᵖ K a) (proj₁ (Φᴮ (rt β) (proj₁ (Ωt ℓ))))
      lowΩᵖ sr β K bd ev cΩ nu fs = lowΩ β K ev cΩ nu (λ η c r → refBr sr β K bd c r (fs η))
```
