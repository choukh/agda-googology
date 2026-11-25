# 自身行 (上折) 归到一格: 保留而参照坍缩

> 验收文件 (读记号). 判决: 编译定理 (条件), 不改树、折叠、合法性. 上折 `Up j′ d b y` 对一切下行链 d 与一切层号: 零, 后继, ℕ 极限, 嵌入, 放宽, 向下封闭, 以及结点上参照穿透 (`cmpᵀ (ν+1) κ` 是 `lt`/`eq`) 的一格用一次归纳证出 (`upAll`); 上折在结点上总保留, 所以余下的只有参照坍缩 (`gt`) 的一格 `UpMis`.
> 于是 `YiSOLow.Sys.SelfRow` 对任何域由 `UpMis` 给出 (`self←up`).
> 不给出什么: `UpMis` 没有实填; 它只在槽位读法 ν 与目标读法 κ 不满足 ν+1 ≤ κ 时出现. 来源: 槽位搬运用 `YiQDFold.mv-good`, 结点用 `YiGTGen.nodeψ`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSOUp where

open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiGIBlock using (chLᵍ; ChTᵍ; chTᵍ; upᵍ; slTᵍ)
import OCF.Lean.YiGIRel as GR
import OCF.Align.EboLeanDef as E
open import OCF.Lean.YiKVRel using (_⊴_; ⊴r; ⊴◃)
open import OCF.Lean.YiGTGen using (weakᴿ; weakenᴿ; closeᴿ; nextψ; limψ; nodeψ; app≤ν)
open import OCF.Lean.YiANFam using (Pen)
open import OCF.Lean.YiFIGen using (low→)
open import OCF.Lean.YiQDFold using (mv-good)
open import OCF.Lean.YiAbsGRow using (module Row)
open import OCF.Lean.YiWREnd using (gradedᴮ; domsᴮ; genᴮ; emptyᵀ)
open import OCF.Lean.YiSOLow
open Row gradedᴮ domsᴮ using (Rules)

UpQ : ∀ {ℓ j′} → Dn ℓ j′ → E.T → Tr j′ → Set
UpQ {ℓ} {j′} d u y = ∀ (b : Tr⁺ ℓ) κ K′ → GR.Rd ℓ κ → GR.R ℓ (E.ψ κ K′ ∷ []) (proj₁ b)
  → GR.R ℓ (E.ψ κ (K′ ++ u) ∷ []) (proj₁ (Up j′ d b y))

UpMis : Set
UpMis = ∀ {ℓ j′} (d : Dn ℓ j′) (p : Pos j′) {u ν : E.T} (g : Br j′ p → Tr j′) → E.cof u ≡ E.cΩ ν → GR.Nu j′ p ν
  → (∀ η c → GR.R (at j′ p) η (slTᵍ j′ p c) → GR.R j′ (E.fsT u η) (g c))
  → (∀ η c → GR.R (at j′ p) η (slTᵍ j′ p c) → UpQ d (E.fsT u η) (g c))
  → ∀ (b : Tr⁺ ℓ) κ K′ → GR.Rd ℓ κ → GR.R ℓ (E.ψ κ K′ ∷ []) (proj₁ b) → E.cmpᵀ (E.sucT ν) κ ≡ E.gt
  → GR.R ℓ (E.ψ κ (K′ ++ u) ∷ []) (proj₁ (Up j′ d b (Ω p g)))

Up-⊵ : ∀ {ℓ} j′ (d : Dn ℓ j′) (b : Tr⁺ ℓ) (y : Tr j′) → proj₁ b ⊴ proj₁ (Up j′ d b y)
Up-⊵ j′ d b y with zl y
... | inj₁ refl = ⊴r
... | inj₂ dd   = ⊴◃ (Upm j′ d b dd)

module UpAll (um : UpMis) where
  mutual
    upAll : ∀ {ℓ} (j′ : L) (d : Dn ℓ j′) → ∀ {u y} → GR.R j′ u y → UpQ d u y
    upAll j′ d = genᴮ j′ (UpQ d) (rules j′ d) (λ le _ q b κ K′ rd rb → closeᴿ _ (app≤ν κ K′ le) (q b κ K′ rd rb))

    rules : ∀ {ℓ} (j′ : L) (d : Dn ℓ j′) → Rules j′ (UpQ d)
    rules {ℓ} j′ d = record
      { qz = λ {u} {x} e0 b κ K′ rd rb →
          subst (λ z → GR.R ℓ (E.ψ κ (K′ ++ z) ∷ []) (proj₁ (Up j′ d b x))) (sym (emptyᵀ u e0))
            (subst (λ z → GR.R ℓ (E.ψ κ z ∷ []) (proj₁ (Up j′ d b x))) (sym (++-identityʳ K′))
              (weakenᴿ ℓ rb (Up-⊵ j′ d b x)))
      ; q1 = λ {u} {x} e1 _ q b κ K′ rd rb → nextψ ℓ κ K′ u e1 (Up j′ d b x) (q b κ K′ rd rb)
      ; qL = λ {u} {x} eω _ h b κ K′ rd rb → limψ ℓ κ K′ u eω _ (λ n → h n b κ K′ rd rb)
      ; qΩ = λ p {u} {ν} g e nu hR hQ b κ K′ rd rb →
          nodeU j′ d p g e nu hQ b κ K′ rd rb (E.cmpᵀ (E.sucT ν) κ) refl (um d p g e nu hR hQ b κ K′ rd rb)
      ; qU = embU j′ d
      ; qw = λ {u} {x} {x′} _ q lt b κ K′ rd rb → weakᴿ ℓ (q b κ K′ rd rb) (Upm j′ d b lt) }

    nodeU : ∀ {ℓ} (j′ : L) (d : Dn ℓ j′) (p : Pos j′) {u ν : E.T} (g : Br j′ p → Tr j′) → E.cof u ≡ E.cΩ ν → GR.Nu j′ p ν
      → (∀ η c → GR.R (at j′ p) η (slTᵍ j′ p c) → UpQ d (E.fsT u η) (g c))
      → ∀ (b : Tr⁺ ℓ) κ K′ → GR.Rd ℓ κ → GR.R ℓ (E.ψ κ K′ ∷ []) (proj₁ b)
      → (c : E.Cmp) → E.cmpᵀ (E.sucT ν) κ ≡ c
      → (E.cmpᵀ (E.sucT ν) κ ≡ E.gt → GR.R ℓ (E.ψ κ (K′ ++ u) ∷ []) (proj₁ (Up j′ d b (Ω p g))))
      → GR.R ℓ (E.ψ κ (K′ ++ u) ∷ []) (proj₁ (Up j′ d b (Ω p g)))
    nodeU j′ d p g e nu hQ b κ K′ rd rb E.gt eqc mis = mis eqc
    nodeU j′ d p g e nu hQ b κ K′ rd rb E.lt eqc mis = keptU j′ d p g e nu hQ b κ K′ rd rb (inj₁ eqc)
    nodeU j′ d p g e nu hQ b κ K′ rd rb E.eq eqc mis = keptU j′ d p g e nu hQ b κ K′ rd rb (inj₂ eqc)

    keptU : ∀ {ℓ} (j′ : L) (d : Dn ℓ j′) (p : Pos j′) {u ν : E.T} (g : Br j′ p → Tr j′) → E.cof u ≡ E.cΩ ν → GR.Nu j′ p ν
      → (∀ η c → GR.R (at j′ p) η (slTᵍ j′ p c) → UpQ d (E.fsT u η) (g c))
      → ∀ (b : Tr⁺ ℓ) κ K′ → GR.Rd ℓ κ → GR.R ℓ (E.ψ κ K′ ∷ []) (proj₁ b) → Pen (E.cmpᵀ (E.sucT ν) κ)
      → GR.R ℓ (E.ψ κ (K′ ++ u) ∷ []) (proj₁ (Up j′ d b (Ω p g)))
    keptU {ℓ} j′ d p {u} {ν} g e nu hQ b κ K′ rd rb pen with mv-good d p
    ... | eq , cm = nodeψ ℓ κ K′ u (mv d p) e pen (rd-nu ℓ (mv d p) (subst (λ A → GR.Rd A ν) (sym eq) (nu-rd j′ p nu)))
      (λ η c l → hQ η (mvBr d p c) (subst (GR.R (at j′ p) η) (sym (cm c)) (trR eq (low→ ℓ (mv d p) l))) b κ K′ rd rb)

    embU : ∀ {ℓ} (j′ : L) (d : Dn ℓ j′) (c : CH j′) {t u : E.T} {x : Tr j′} (y : ChTᵍ j′ c) → GR.R j′ t x → UpQ d t x
      → GR.R (chLᵍ j′ c) u (chTᵍ j′ c y) → UpQ d (t ++ u) (upᵍ x c y)
    embU {ℓ} (nd s h) d c {t} {u} {x} (y , e) rx qx ry b κ K′ rd rb =
      subst (λ z → GR.R ℓ (E.ψ κ z ∷ []) (proj₁ (Up (h c) (down d c) (Up (nd s h) d b x) y))) (++-assoc K′ t u)
        (upAll (h c) (down d c) ry (Up (nd s h) d b x) κ (K′ ++ t) rd (qx b κ K′ rd rb))

  self←up : (𝒟 : Domˢ) → Sys.SelfRow 𝒟
  self←up 𝒟 {s} {h} o r B c x y e _ β′ κ K′ rd rb ry = upAll (h c) (down stop c) ry β′ κ K′ rd rb
```
