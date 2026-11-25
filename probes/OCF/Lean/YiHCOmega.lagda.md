# 验收一侧: ℕ 极限读回层号作目标 (上折进它, 折到它自身)

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 判决: 编译定理, 无前提 (`leafω` 带前提 `∀ k → k ≤ d k`, 实例 `sh` 满足). 关系是 [YiHCLim](YiHCLim.lagda.md) 的封闭族 `Mω`.
> `UpT.PuT`: 有限层的树上折进任意顶层 Λ 的保持 (顶层关系与下标 u 是参数; 槽位搬进顶层后的读法是前提 `hN`, `hL`, `hP`); `Tω.upB`: 孩子 m 的树上折进 ω 层; `Tω.Self.PFω`: ω 层折到自身对 ψ_ω(P₀ + a) 的保持; `Tω.leafω`: Ω_ω 对着 ω 层的 Ω 树 (用到 `mc`, 未封闭时被 `YiLRNeg.noLeafᶜ` 否定).
> 来源: `PuT` 照 `YiHCFam.Pu` (顶层从 `fn (suc N)` 换成参数), `PFω` 照 `YiHCFold.Self.PF`; 记号引理都是 `YiANFam`, `YiMENote` 里对一般下标陈述的那几条.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiHCOmega where

open import Data.Nat using (ℕ; zero; suc) renaming (_≤_ to _≤ⁿ_)
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
open import OCF.Lean.YiRBSib
open import OCF.Lean.YiKVRel using (_⊴_; ⊴r; ++[])
open import OCF.Lean.YiHCRel
import OCF.Align.EboLeanDef as E
open E using (cof; c1; cω; cΩ; pred; fsn; fsT; natT; sucT; cmpᵀ; gt; lt; hd<; ar<)
open import OCF.Align.EboLeanBase using (_≤ᵀ_)
open import OCF.Align.Standard using (++-mono)
open import OCF.Lean.YiMENote using (cofψ1; fsnψ1; cofψω; fsnψω; cof++1; cof++ω; pred++; fsn++)
open import OCF.Lean.YiMWPre using (cof++Ω; fsT++)
open import OCF.Lean.YiANFam using (Ωᴺ; Pen; cofK; fsTK)
open import OCF.Lean.YiDCRel using (Ω≤; suc-nat)
open import OCF.Lean.YiCLFam using (fn; lev; levP; FD; fd0; fds)
open import OCF.Lean.YiCLLow using (Sb; pth)
open import OCF.Lean.YiCLPhi using (ωᵀ; rep1)
open import OCF.Lean.YiHCFam using (M; Lw⁼; LwP)
open import OCF.Lean.YiLRBridge using (NwB; τ₂)
open import OCF.Lean.YiHCBridge using (MB; LwB; MβB)
open import OCF.Lean.YiHCLim using (module Lim)
```

## 记号一侧: 一般下标 u 的 ψ_u(t₀ + ·) 对项序单调; 下标 ω 与自然数的比较

```agda
ψᵘ : E.T → E.T → E.T
ψᵘ u a = E.ψ u a ∷ []

appᵘ : ∀ u t₀ {a b} → a ≤ᵀ b → ψᵘ u (t₀ ++ a) ≤ᵀ ψᵘ u (t₀ ++ b)
appᵘ u t₀ (inj₁ p)    = inj₁ (hd< (ar< (++-mono t₀ p)))
appᵘ u t₀ (inj₂ refl) = inj₂ refl

penω : ∀ k → Pen (cmpᵀ (sucT (natT k)) ωᵀ)
penω k = inj₁ (cong (λ z → cmpᵀ z ωᵀ) (suc-nat k))

gtω-nat : ∀ j → cmpᵀ (sucT ωᵀ) (natT j) ≡ gt
gtω-nat zero    = refl
gtω-nat (suc j) = refl

gtω-self : cmpᵀ (sucT ωᵀ) ωᵀ ≡ gt
gtω-self = refl

penB : ∀ {N} (ℓ : L) (e : ℓ ≡ fn N) (t : Pos⁼ ℓ) {ν} → NwB ℓ e t ν → Pen (cmpᵀ (sucT ν) ωᵀ)
penB {N} _ refl t refl = penω (lev N t)
```

## 上折进任意顶层

顶层 Λ 上的关系 `MT` 与 ψ 的下标 u 是参数. `D₀` 是从 Λ 下到 `fn N` 的链; 前提只说 `fn N` 的槽位沿 `D₀` 搬进 Λ 后的读法. 再往下的后继孩子 (`FD`) 由递归处理.

```agda
module UpT {Λ : L} {LowT : (p : Pos Λ) → E.T → Br Λ p → Set} {ChdT : (c : CH Λ) → E.T → ChT Λ c → Set}
           {NuT : Pos Λ → E.T → Set} (u : E.T) {N : ℕ} (D₀ : Dn Λ (fn N))
           (hN : (p : Pos (fn N)) {ν : E.T} → ν ≡ natT (levP N p) → NuT (mv D₀ p) ν)
           (hL : (p : Pos (fn N)) {η : E.T} (c : Br Λ (mv D₀ p)) → LowT (mv D₀ p) η c → LwP N p η (mvBr D₀ p c))
           (hP : ∀ k → Pen (cmpᵀ (sucT (natT k)) u)) where

  MT : E.T → Tr Λ → Set
  MT = Mᴴ (Sig Λ) LowT ChdT NuT

  module GT = Gen {Sig Λ} {LowT} {ChdT} {NuT}

  dnT : ∀ {j} → FD N j → Dn Λ (fn j)
  dnT fd0     = D₀
  dnT (fds d) = down (dnT d) tt

  mvNT : ∀ {j} (d : FD N j) (p : Pos (fn j)) {ν} → ν ≡ natT (levP j p) → NuT (mv (dnT d) p) ν
  mvNT fd0     p nu = hN p nu
  mvNT (fds d) p nu = mvNT d (inj₂ (tt , inj₂ p)) nu

  mvLT : ∀ {j} (d : FD N j) (p : Pos (fn j)) {η} (c : Br Λ (mv (dnT d) p))
       → LowT (mv (dnT d) p) η c → LwP j p η (mvBr (dnT d) p c)
  mvLT fd0     p c l = hL p c l
  mvLT (fds d) p c l = mvLT d (inj₂ (tt , inj₂ p)) c l

  penT : ∀ {j} (p : Pos (fn j)) {ν} → ν ≡ natT (levP j p) → Pen (cmpᵀ (sucT ν) u)
  penT {j} p refl = hP (levP j p)

  PuT⁰ : (d : FD N zero) (b : Tr⁺ Λ) {t : E.T}
       → MT (ψᵘ u t) (proj₁ b)
       → ∀ {s y} → M⁰ s y → MT (ψᵘ u (t ++ s)) (proj₁ (Up zero (dnT d) b y))
  PuT⁰ d b {t} mb (mz {x = y}) =
    ++[] (λ r → MT (ψᵘ u r) (proj₁ (Up zero (dnT d) b y))) t
      (GT.m-zl (λ y → proj₁ (Up zero (dnT d) b y)) (Upm zero (dnT d) b) mb y)
  PuT⁰ d b {t} mb (m1 {t = s} {x = y} e r) =
    GT.m-next (Up zero (dnT d) b y) (cofψ1 u (t ++ s) (cof++1 t s e))
      (λ k → trans (fsnψ1 u (t ++ s) k (cof++1 t s e))
               (cong (λ r → replicate k (E.ψ u r)) (pred++ t s e)))
      (PuT⁰ d b mb r)
  PuT⁰ d b {t} mb (mL {t = s} {x = y} e h) =
    mL (cofψω u (t ++ s) (cof++ω t s e))
      (λ k → subst (λ r → MT r (proj₁ (Up zero (dnT d) b y)))
        (sym (trans (fsnψω u (t ++ s) k (cof++ω t s e)) (cong (ψᵘ u) (fsn++ t s k e))))
        (PuT⁰ d b mb (h k)))
  PuT⁰ d b mb (mΩ {p = ()} _ _ _)
  PuT⁰ d b mb (mU {c = ()} _ _)
  PuT⁰ d b mb (mw m r) = mw (PuT⁰ d b mb m) (Upm zero (dnT d) b r)
  PuT⁰ d b {t} mb (mc le m) = mc (appᵘ u t le) (PuT⁰ d b mb m)

  mutual
    PuT : ∀ j (d : FD N j) (b : Tr⁺ Λ) {t : E.T}
        → MT (ψᵘ u t) (proj₁ b)
        → ∀ {s y} → M j s y → MT (ψᵘ u (t ++ s)) (proj₁ (Up (fn j) (dnT d) b y))
    PuT zero    = PuT⁰
    PuT (suc j) = PuTˢ j

    PuTˢ : ∀ j (d : FD N (suc j)) (b : Tr⁺ Λ) {t : E.T}
         → MT (ψᵘ u t) (proj₁ b)
         → ∀ {s y} → M (suc j) s y → MT (ψᵘ u (t ++ s)) (proj₁ (Up (fn (suc j)) (dnT d) b y))
    PuTˢ j d b {t} mb (mz {x = y}) =
      ++[] (λ r → MT (ψᵘ u r) (proj₁ (Up (fn (suc j)) (dnT d) b y))) t
        (GT.m-zl (λ y → proj₁ (Up (fn (suc j)) (dnT d) b y)) (Upm (fn (suc j)) (dnT d) b) mb y)
    PuTˢ j d b {t} mb (m1 {t = s} {x = y} e r) =
      GT.m-next (Up (fn (suc j)) (dnT d) b y) (cofψ1 u (t ++ s) (cof++1 t s e))
        (λ k → trans (fsnψ1 u (t ++ s) k (cof++1 t s e))
                 (cong (λ r → replicate k (E.ψ u r)) (pred++ t s e)))
        (PuTˢ j d b mb r)
    PuTˢ j d b {t} mb (mL {t = s} {x = y} e h) =
      mL (cofψω u (t ++ s) (cof++ω t s e))
        (λ k → subst (λ r → MT r (proj₁ (Up (fn (suc j)) (dnT d) b y)))
          (sym (trans (fsnψω u (t ++ s) k (cof++ω t s e)) (cong (ψᵘ u) (fsn++ t s k e))))
          (PuTˢ j d b mb (h k)))
    PuTˢ j d b {t} mb (mΩ {t = s} {p = p} {g = g} e nu h) =
      mΩ (cofK u (t ++ s) (penT p nu) (cof++Ω t s e)) (mvNT d p nu)
        (λ η c l → subst (λ r → MT r (proj₁ (Up (fn (suc j)) (dnT d) b (g (mvBr (dnT d) p c)))))
          (sym (trans (fsTK u (t ++ s) η (penT p nu) (cof++Ω t s e))
                 (cong (ψᵘ u) (fsT++ t s η e))))
          (PuTˢ j d b mb (h η (mvBr (dnT d) p c) (mvLT d p c l))))
    PuTˢ j d b {t} mb (mU {t = s₀} {s = s₁} {x = y₀} {y = y₁} m ch) =
      subst (λ r → MT (ψᵘ u r)
          (proj₁ (Up (fn j) (dnT (fds d)) (Up (fn (suc j)) (dnT d) b y₀) y₁)))
        (++-assoc t s₀ s₁)
        (PuT j (fds d) (Up (fn (suc j)) (dnT d) b y₀) (PuTˢ j d b mb m) ch)
    PuTˢ j d b mb (mw m r) = mw (PuTˢ j d b mb m) (Upm (fn (suc j)) (dnT d) b r)
    PuTˢ j d b {t} mb (mc le m) = mc (appᵘ u t le) (PuTˢ j d b mb m)
```

## ω 层作目标

```agda
module Tω (G : ℕ → L) (d : ℕ → ℕ) (eG : ∀ n → G n ≡ fn (d n)) (R : (n : ℕ) → G n ≤ G (suc n))
          (canR : ∀ n → Σ (Sb (d (suc n)) (d n)) λ s → τ₂ (eG n) (eG (suc n)) (R n) ≡ pth s) where
  open Lim G d eG R canR

  module Gω = Gen {Sig Lω} {Lowω} {λ m → MB (G m) (eG m)} {Nuω}

  ψω : E.T → E.T
  ψω = ψᵘ ωᵀ

  cumω : ∀ n → Mω (Ωᴺ (d n)) (cum (λ k → proj₁ (upz {sL} {G} k (Ωt (G k)))) n)
  cumω zero    = mU mz (MβB (G zero) (eG zero))
  cumω (suc n) = mU mz (MβB (G (suc n)) (eG (suc n)))

  leafω : (∀ k → k ≤ⁿ d k) → Mω (E.Ωt ωᵀ) (proj₁ (Ωt Lω))
  leafω dk = mL refl (λ k → mc (subst (λ t → E.Ωt t ≤ᵀ Ωᴺ (d k)) (sym (rep1 k)) (Ω≤ (dk k))) (mw (cumω k) (◃l k)))

  upJ : ∀ {N} (ℓ : L) (e : ℓ ≡ fn N) (D : Dn Lω ℓ)
      → ((p : Pos ℓ) {ν : E.T} → NwB ℓ e (inj₂ p) ν → Nuω (mv D p) ν)
      → ((p : Pos ℓ) {η : E.T} (c : Br Lω (mv D p)) → Lowω (mv D p) η c → LwB ℓ e (inj₂ p) η (mvBr D p c))
      → (b : Tr⁺ Lω) {t : E.T} → Mω (ψω t) (proj₁ b)
      → ∀ {s y} → MB ℓ e s y → Mω (ψω (t ++ s)) (proj₁ (Up ℓ D b y))
  upJ {N} _ refl D hN hL b mb m = UpT.PuT ωᵀ D hN hL penω N fd0 b mb m

  upB : ∀ m (b : Tr⁺ Lω) {t : E.T} → Mω (ψω t) (proj₁ b)
      → ∀ {s y} → MB (G m) (eG m) s y → Mω (ψω (t ++ s)) (proj₁ (Up (G m) (down stop m) b y))
  upB m b mb ch = upJ (G m) (eG m) (down stop m) (λ p nu → nu) (λ p c l → l) b mb ch

  module Self (oc : (k : ℕ) → Ok (G k)) (r : Rb Lω) (B : Base Lω) (β : Tr⁺ Lω) where
    F⁺ : Tr Lω → Tr⁺ Lω
    F⁺ x = ψ Lω (R , oc) r B Lω self β x

    F : Tr Lω → Tr Lω
    F x = proj₁ (F⁺ x)

    monoF : {x y : Tr Lω} → Lω ⊢ x ◃ y → Lω ⊢ F x ◃ F y
    monoF = mono Lω (R , oc) r B Lω self β

    PFω : ∀ {P₀} → Mω (ψω P₀) (proj₁ β) → ∀ {a x} → Mω a x → Mω (ψω (P₀ ++ a)) (F x)
    PFω {P₀} hP (mz {x = x}) = ++[] (λ z → Mω (ψω z) (F x)) P₀ (Gω.m-zl F monoF hP x)
    PFω {P₀} hP (m1 {t = a} {x = x} e h) =
      Gω.m-next (F⁺ x) (cofψ1 ωᵀ (P₀ ++ a) (cof++1 P₀ a e))
        (λ k → trans (fsnψ1 ωᵀ (P₀ ++ a) k (cof++1 P₀ a e))
                 (cong (λ z → replicate k (E.ψ ωᵀ z)) (pred++ P₀ a e)))
        (PFω hP h)
    PFω {P₀} hP (mL {t = a} {x = x} e h) =
      mL (cofψω ωᵀ (P₀ ++ a) (cof++ω P₀ a e))
        (λ k → subst (λ z → Mω z (F x))
          (sym (trans (fsnψω ωᵀ (P₀ ++ a) k (cof++ω P₀ a e)) (cong ψω (fsn++ P₀ a k e))))
          (PFω hP (h k)))
    PFω hP (mΩ {p = inj₁ ()} _ _ _)
    PFω {P₀} hP (mΩ {t = a} {p = inj₂ (m , t)} {g = g} e nu h) =
      mΩ (cofK ωᵀ (P₀ ++ a) (penB (G m) (eG m) t nu) (cof++Ω P₀ a e)) nu
        (λ η c l → subst (λ z → Mω z (F (g c)))
          (sym (trans (fsTK ωᵀ (P₀ ++ a) η (penB (G m) (eG m) t nu) (cof++Ω P₀ a e))
                 (cong ψω (fsT++ P₀ a η e))))
          (PFω hP (h η c l)))
    PFω {P₀} hP (mU {t = s₀} {s = s₁} {x = x} {c = m} {y = y} h ch) =
      subst (λ z → Mω (ψω z) (proj₁ (Up (G m) (down stop m) (F⁺ x) y))) (++-assoc P₀ s₀ s₁)
        (upB m (F⁺ x) (PFω hP h) ch)
    PFω hP (mw h dd) = mw (PFω hP h) (monoF dd)
    PFω {P₀} hP (mc le h) = mc (appᵘ ωᵀ P₀ le) (PFω hP h)
```
