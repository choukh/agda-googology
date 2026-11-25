# ℕ 极限层号的一步: 数据与四条律 (下折两条未做)

> 验收文件 (读记号), 不进成品. 判决: 编译定理, 无前提, 但只是 [YiZSLev](YiZSLev.lagda.md) 接口的一部分. 孩子 `g n` 都满足接口时, `nd sL g` 上的关系 `Mλ` 有: Ω 树承载 Ω_λ (`leafλ`, 用 `mc`, 孩子读法与 λ 的基本列只要逐项不低), 槽位读法低于 λ (`hi-penλ`), 折到自身 (`selfPλ`), 上折进任意高层 (`upPλ`).
> 没有做: 接口其余两条 `kc`, `df` (朝登记目标下折). 它们要先定 `nd sL g` 的目标集 (各孩子的目标经 `inc n`, 一致路径上各孩子共有的目标), 再处理嵌入行里孩子编号的比较 `way` (`YiHCLim.Lim.Fold.LFU`, `LFΩ` 在孩子是有限层时的做法). 没有否定.
> 实例: 孩子取 [YiZSTower](YiZSTower.lagda.md) 的塔, λ = ω·2 (`Inst`); 层号即 `ω 层 ⊕ ↑ ωᶜ` (`lvl2`).
> 来源: `leafλ` 照 `YiHCOmega.Tω.leafω`; `selfPλ`, `upPλ` 照 `YiZSLev.Step₊` 的两条.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiZSLim where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_; replicate)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base)
open import OCF.Lean.YiRBSib using (Rb; ψ; mono)
open import OCF.Lean.YiKVRel using (++[])
open import OCF.Lean.YiHCRel using (Mᴴ; mz; m1; mL; mΩ; mU; mw; mc; module Gen)
import OCF.Align.EboLeanDef as E
open E using (cof; cω; fsn; sucT; cmpᵀ)
open import OCF.Align.EboLeanBase using (_≤ᵀ_)
open import OCF.Lean.YiMENote using (cofψ1; fsnψ1; cofψω; fsnψω; cof++1; cof++ω; pred++; fsn++)
open import OCF.Lean.YiMWPre using (cof++Ω; fsT++)
open import OCF.Lean.YiANFam using (Pen; cofK; fsTK)
open import OCF.Lean.YiCLPhi using (rep1)
open import OCF.Lean.YiHCOmega using (ψᵘ; appᵘ)
open import OCF.Lean.YiTBRow using (nat)
open import OCF.Lean.YiTBTab using (ωᶜ)
open import OCF.Lean.YiSVOmega using (G; module Wω)
open import OCF.Lean.YiZSLev
open import OCF.Lean.YiZSTower

module Lim₊ (g : ℕ → L) (og : ∀ n → Ok (g n)) (R : ∀ n → g n ≤ g (suc n)) (ν : ℕ → E.T)
            (D : ∀ n → Data (g n)) (W : ∀ n → Laws (D n) (og n) (ν n)) (λᵀ : E.T)
            (cofL : cof (E.Ωt λᵀ) ≡ cω) (fsL : ∀ k → fsn (E.Ωt λᵀ) k ≤ᵀ E.Ωt (ν k))
            (hiL : ∀ n → Data.Hi (D n) λᵀ) (penL : ∀ n → Pen (cmpᵀ (sucT (ν n)) λᵀ)) where
  module Dm (m : ℕ) = Data (D m)
  module Wm (m : ℕ) = Laws (W m)

  ℓ : L
  ℓ = nd sL g

  o : Ok ℓ
  o = R , og

  Lowλ : (p : Pos ℓ) → E.T → Br ℓ p → Set
  Lowλ (inj₁ ())
  Lowλ (inj₂ (m , inj₁ tt)) = Dm.Mj m
  Lowλ (inj₂ (m , inj₂ p))  = Dm.Low m p

  Nuλ : Pos ℓ → E.T → Set
  Nuλ (inj₁ ())
  Nuλ (inj₂ (m , inj₁ tt)) ν′ = ν′ ≡ ν m
  Nuλ (inj₂ (m , inj₂ p))     = Dm.Nu m p

  Mλ : E.T → Tr ℓ → Set
  Mλ = Mᴴ (Sig ℓ) Lowλ Dm.Mj Nuλ

  module Gλ = Gen {Sig ℓ} {Lowλ} {Dm.Mj} {Nuλ}

  Hiλ : E.T → Set
  Hiλ μ = ∀ m → Dm.Hi m μ × Pen (cmpᵀ (sucT (ν m)) μ)

  hi-penλ : (μ : E.T) → Hiλ μ → (p : Pos ℓ) {ν′ : E.T} → Nuλ p ν′ → Pen (cmpᵀ (sucT ν′) μ)
  hi-penλ μ hi (inj₁ ())
  hi-penλ μ hi (inj₂ (m , inj₁ tt)) refl = proj₂ (hi m)
  hi-penλ μ hi (inj₂ (m , inj₂ p))  nu   = Wm.hi-pen m μ (proj₁ (hi m)) p nu

  hi-ownλ : Hiλ λᵀ
  hi-ownλ m = hiL m , penL m

  cumλ : ∀ n → Mλ (E.Ωt (ν n)) (cum (λ k → proj₁ (upz {sL} {g} k (Ωt (g k)))) n)
  cumλ zero    = mU mz (Wm.leaf zero)
  cumλ (suc n) = mU mz (Wm.leaf (suc n))

  leafλ : Mλ (E.Ωt λᵀ) (proj₁ (Ωt ℓ))
  leafλ = mL cofL (λ k → mc (fsL k) (mw (cumλ k) (◃l k)))

  selfPλ : (r : Rb ℓ) (B : Base ℓ) (β : Tr⁺ ℓ) (P₀ : E.T) → Mλ (ψᵘ λᵀ P₀) (proj₁ β)
         → ∀ {a x} → Mλ a x → Mλ (ψᵘ λᵀ (P₀ ++ a)) (proj₁ (ψ ℓ o r B ℓ self β x))
  selfPλ r B β P₀ hP (mz {x = x}) =
    ++[] (λ z → Mλ (ψᵘ λᵀ z) (proj₁ (ψ ℓ o r B ℓ self β x))) P₀
      (Gλ.m-zl (λ y → proj₁ (ψ ℓ o r B ℓ self β y)) (mono ℓ o r B ℓ self β) hP x)
  selfPλ r B β P₀ hP (m1 {t = a} {x = x} e h) =
    Gλ.m-next (ψ ℓ o r B ℓ self β x) (cofψ1 λᵀ (P₀ ++ a) (cof++1 P₀ a e))
      (λ k → trans (fsnψ1 λᵀ (P₀ ++ a) k (cof++1 P₀ a e)) (cong (λ z → replicate k (E.ψ λᵀ z)) (pred++ P₀ a e)))
      (selfPλ r B β P₀ hP h)
  selfPλ r B β P₀ hP (mL {t = a} {x = x} e h) =
    mL (cofψω λᵀ (P₀ ++ a) (cof++ω P₀ a e))
      (λ k → subst (λ z → Mλ z (proj₁ (ψ ℓ o r B ℓ self β x)))
        (sym (trans (fsnψω λᵀ (P₀ ++ a) k (cof++ω P₀ a e)) (cong (ψᵘ λᵀ) (fsn++ P₀ a k e))))
        (selfPλ r B β P₀ hP (h k)))
  selfPλ r B β P₀ hP (mΩ {t = a} {p = p} {g = gg} e nu h) =
    mΩ (cofK λᵀ (P₀ ++ a) (hi-penλ λᵀ hi-ownλ p nu) (cof++Ω P₀ a e)) nu
      (λ η c l → subst (λ z → Mλ z (proj₁ (ψ ℓ o r B ℓ self β (gg c))))
        (sym (trans (fsTK λᵀ (P₀ ++ a) η (hi-penλ λᵀ hi-ownλ p nu) (cof++Ω P₀ a e)) (cong (ψᵘ λᵀ) (fsT++ P₀ a η e))))
        (selfPλ r B β P₀ hP (h η c l)))
  selfPλ r B β P₀ hP (mU {t = s₀} {s = s₁} {x = x} {c = m} {y = y} h ch) =
    subst (λ z → Mλ (ψᵘ λᵀ z) (proj₁ (Up (g m) (down stop m) (ψ ℓ o r B ℓ self β x) y))) (++-assoc P₀ s₀ s₁)
      (Wm.upP m ℓ Lowλ Dm.Mj Nuλ λᵀ (down stop m) (hiL m) (λ p nu → nu) (λ p c l → l)
              (ψ ℓ o r B ℓ self β x) (P₀ ++ s₀) (selfPλ r B β P₀ hP h) ch)
  selfPλ r B β P₀ hP (mw h dd) = mw (selfPλ r B β P₀ hP h) (mono ℓ o r B ℓ self β dd)
  selfPλ r B β P₀ hP (mc le h) = mc (appᵘ λᵀ P₀ le) (selfPλ r B β P₀ hP h)

  module UpL (ℓ′ : L) (Low′ : (p : Pos ℓ′) → E.T → Br ℓ′ p → Set) (Chd′ : (c : CH ℓ′) → E.T → ChT ℓ′ c → Set)
             (Nu′ : Pos ℓ′ → E.T → Set) (ν′ : E.T) (hi : Hiλ ν′) where
    M′ : E.T → Tr ℓ′ → Set
    M′ = Mᴴ (Sig ℓ′) Low′ Chd′ Nu′

    module G′ = Gen {Sig ℓ′} {Low′} {Chd′} {Nu′}

    upPλ : (d : Dn ℓ′ ℓ)
         → ((p : Pos ℓ) {η : E.T} → Nuλ p η → Nu′ (mv d p) η)
         → ((p : Pos ℓ) {η : E.T} (c : Br ℓ′ (mv d p)) → Low′ (mv d p) η c → Lowλ p η (mvBr d p c))
         → (b : Tr⁺ ℓ′) (t : E.T) → M′ (ψᵘ ν′ t) (proj₁ b)
         → ∀ {s y} → Mλ s y → M′ (ψᵘ ν′ (t ++ s)) (proj₁ (Up ℓ d b y))
    upPλ d cN cL b t mb (mz {x = y}) =
      ++[] (λ z → M′ (ψᵘ ν′ z) (proj₁ (Up ℓ d b y))) t
        (G′.m-zl (λ y → proj₁ (Up ℓ d b y)) (Upm ℓ d b) mb y)
    upPλ d cN cL b t mb (m1 {t = s} {x = y} e h) =
      G′.m-next (Up ℓ d b y) (cofψ1 ν′ (t ++ s) (cof++1 t s e))
        (λ k → trans (fsnψ1 ν′ (t ++ s) k (cof++1 t s e)) (cong (λ z → replicate k (E.ψ ν′ z)) (pred++ t s e)))
        (upPλ d cN cL b t mb h)
    upPλ d cN cL b t mb (mL {t = s} {x = y} e h) =
      mL (cofψω ν′ (t ++ s) (cof++ω t s e))
        (λ k → subst (λ z → M′ z (proj₁ (Up ℓ d b y)))
          (sym (trans (fsnψω ν′ (t ++ s) k (cof++ω t s e)) (cong (ψᵘ ν′) (fsn++ t s k e))))
          (upPλ d cN cL b t mb (h k)))
    upPλ d cN cL b t mb (mΩ {t = s} {p = p} {g = gg} e nu h) =
      mΩ (cofK ν′ (t ++ s) (hi-penλ ν′ hi p nu) (cof++Ω t s e)) (cN p nu)
        (λ η c l → subst (λ z → M′ z (proj₁ (Up ℓ d b (gg (mvBr d p c)))))
          (sym (trans (fsTK ν′ (t ++ s) η (hi-penλ ν′ hi p nu) (cof++Ω t s e)) (cong (ψᵘ ν′) (fsT++ t s η e))))
          (upPλ d cN cL b t mb (h η (mvBr d p c) (cL p c l))))
    upPλ d cN cL b t mb (mU {t = s₀} {s = s₁} {x = y₀} {c = m} {y = y₁} h ch) =
      subst (λ z → M′ (ψᵘ ν′ z) (proj₁ (Up (g m) (down d m) (Up ℓ d b y₀) y₁))) (++-assoc t s₀ s₁)
        (Wm.upP m ℓ′ Low′ Chd′ Nu′ ν′ (down d m) (proj₁ (hi m))
                (λ p nu → cN (inj₂ (m , inj₂ p)) nu) (λ p c l → cL (inj₂ (m , inj₂ p)) c l)
                (Up ℓ d b y₀) (t ++ s₀) (upPλ d cN cL b t mb h) ch)
    upPλ d cN cL b t mb (mw h dd) = mw (upPλ d cN cL b t mb h) (Upm ℓ d b dd)
    upPλ d cN cL b t mb (mc le h) = mc (appᵘ ν′ t le) (upPλ d cN cL b t mb h)
```

## 实例: 塔作孩子, λ = ω·2

前提都可满足: 孩子的接口是 `pk`, 相邻路径是 `inc tt self`, ω·2 的 Ω 项的基本列第 k 项是 Ω_{ω+k}.

```agda
module Inst (oc : (k : ℕ) → Ok (G k)) where
  open Base oc
  obN : ∀ n → OkO Wω.Lω (↑ zero (nat n))
  obN zero    = tt
  obN (suc n) = tt , λ _ → obN n

  module L2 = Lim₊ J (λ n → oJ n (obN n)) (λ n → inc tt self) νᵀ
                   (λ n → Pk.D (pk n (obN n))) (λ n → Pk.W (pk n (obN n))) ω2ᵀ
                   refl (λ k → inj₂ (cong (λ z → E.Ωt (E.ψ [] (E.𝟏 ∷ []) ∷ z)) (rep1 k)))
                   (λ n → Pk.hi2 (pk n (obN n))) pen2

  lvl2 : L2.ℓ ≡ Wω.Lω ⊕ ↑ zero ωᶜ
  lvl2 = refl

  leaf2 : L2.Mλ (E.Ωt ω2ᵀ) (proj₁ (Ωt (Wω.Lω ⊕ ↑ zero ωᶜ)))
  leaf2 = L2.leafλ
```
