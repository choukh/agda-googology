# 参照一侧的引理: ψ_ν(P + t) 的余尾与基本列, 零树处的反演

> 验收文件 (读记号). 判决: 编译定理, 无前提. 记号一侧: 前缀 P 之后的 ψ_ν(P + t) 在 t 的余尾 Ω_{κ+1} 满足 κ+1 ≤ ν 时保持余尾并与代入交换 (`keepψ`), κ+1 > ν 时余尾 ω, 第 n 项走 γ-链 (`collψ`). 主线关系一侧: 对零树的关系只有参照项 0 (`R-zero`); 第 0 层的读法只有 0 (`rd0`); `Nu` 与槽位层的 `Rd` 互推 (`nu→rd`, `rd→nu`).
> 不给出什么: 不涉及树、折叠; 只是 [YiBAEbo](YiBAEbo.lagda.md) 用到的引理.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBALemma where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import OCF.Lean.YiRWBlock hiding (R)
import OCF.Align.EboLeanDef as E
open import OCF.Align.EboLeanBase using (_≤ᵀ_)
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiGIRel as GR
open import OCF.Lean.YiKVRel using (¬◃z)
```

## 前缀之后的 ψ

```agda
cof++ : ∀ P y ys → E.cof (P ++ (y ∷ ys)) ≡ E.cof (y ∷ ys)
cof++ []           y ys = refl
cof++ (x ∷ [])     y ys = refl
cof++ (x ∷ x′ ∷ xs) y ys = cof++ (x′ ∷ xs) y ys

fsT++ : ∀ P y ys η → E.fsT (P ++ (y ∷ ys)) η ≡ P ++ E.fsT (y ∷ ys) η
fsT++ []           y ys η = refl
fsT++ (x ∷ [])     y ys η = refl
fsT++ (x ∷ x′ ∷ xs) y ys η = cong (x ∷_) (fsT++ (x′ ∷ xs) y ys η)

cofψ++ : ∀ u P y ys → E.cof (E.ψ u (P ++ (y ∷ ys)) ∷ []) ≡ E.cofA u (E.cof (y ∷ ys))
cofψ++ u []       y ys = refl
cofψ++ u (x ∷ xs) y ys = cong (E.cofA u) (cof++ (x ∷ xs) y ys)

fsTψ++ : ∀ u P y ys η → E.fsT (E.ψ u (P ++ (y ∷ ys)) ∷ []) η ≡ E.fsT₊ u (P ++ (y ∷ ys)) (E.cof (P ++ (y ∷ ys))) η
fsTψ++ u []       y ys η = refl
fsTψ++ u (x ∷ xs) y ys η = refl

fsnψ++ : ∀ u P y ys n → E.fsn (E.ψ u (P ++ (y ∷ ys)) ∷ []) n ≡ E.fsn₊ u (P ++ (y ∷ ys)) (E.cof (P ++ (y ∷ ys))) n
fsnψ++ u []       y ys n = refl
fsnψ++ u (x ∷ xs) y ys n = refl
```

保持与坍缩两种情形. `NotGt m`: 比较结果不是 "大于" (κ+1 ≤ ν).

```agda
NotGt : E.Cmp → Set
NotGt E.gt = ⊥
NotGt _    = ⊤

cofψ₊-keep : ∀ u μ m → NotGt m → E.cofψ₊ u μ m ≡ E.cΩ μ
cofψ₊-keep u μ E.lt _ = refl
cofψ₊-keep u μ E.eq _ = refl
cofψ₊-keep u μ E.gt ()

fsTc-keep : ∀ u b μ m η → NotGt m → E.fsTc u b μ m η ≡ E.ψ u (E.fsT b η) ∷ []
fsTc-keep u b μ E.lt η _ = refl
fsTc-keep u b μ E.eq η _ = refl
fsTc-keep u b μ E.gt η ()

fsT₊-keep : ∀ u b {μ} c η → c ≡ E.cΩ μ → NotGt (E.cmpᵀ (E.sucT μ) u) → E.fsT₊ u b c η ≡ E.ψ u (E.fsT b η) ∷ []
fsT₊-keep u b {μ} .(E.cΩ μ) η refl ng = fsTc-keep u b μ (E.cmpᵀ (E.sucT μ) u) η ng

fsn₊-coll : ∀ u b {μ} c n → c ≡ E.cΩ μ → E.cmpᵀ (E.sucT μ) u ≡ E.gt
  → E.fsn₊ u b c n ≡ E.ψ u (E.fsT b (E.γT b μ n)) ∷ []
fsn₊-coll u b {μ} .(E.cΩ μ) n refl g = cong (λ m → E.fsnc u b μ m n) g

keepψ : ∀ ν P t {κ} → E.cof t ≡ E.cΩ κ → NotGt (E.cmpᵀ (E.sucT κ) ν)
  → (E.cof (E.ψ ν (P ++ t) ∷ []) ≡ E.cΩ κ) × (∀ η → E.fsT (E.ψ ν (P ++ t) ∷ []) η ≡ E.ψ ν (P ++ E.fsT t η) ∷ [])
keepψ ν P [] () ng
keepψ ν P (y ∷ ys) {κ} e ng =
  trans (cofψ++ ν P y ys) (trans (cong (E.cofA ν) e) (cofψ₊-keep ν κ (E.cmpᵀ (E.sucT κ) ν) ng)) ,
  λ η → trans (fsTψ++ ν P y ys η)
          (trans (fsT₊-keep ν (P ++ (y ∷ ys)) (E.cof (P ++ (y ∷ ys))) η (trans (cof++ P y ys) e) ng)
                 (cong (λ b → E.ψ ν b ∷ []) (fsT++ P y ys η)))

collψ : ∀ ν P t {κ} → E.cof t ≡ E.cΩ κ → E.cmpᵀ (E.sucT κ) ν ≡ E.gt
  → (E.cof (E.ψ ν (P ++ t) ∷ []) ≡ E.cω)
  × (∀ n → E.fsn (E.ψ ν (P ++ t) ∷ []) n ≡ E.ψ ν (P ++ E.fsT t (E.γT (P ++ t) κ n)) ∷ [])
collψ ν P [] () g
collψ ν P (y ∷ ys) {κ} e g =
  trans (cofψ++ ν P y ys) (trans (cong (E.cofA ν) e) (cong (E.cofψ₊ ν κ) g)) ,
  λ n → trans (fsnψ++ ν P y ys n)
          (trans (fsn₊-coll ν (P ++ (y ∷ ys)) (E.cof (P ++ (y ∷ ys))) n (trans (cof++ P y ys) e) g)
                 (cong (λ b → E.ψ ν b ∷ []) (fsT++ P y ys (E.γT (P ++ (y ∷ ys)) κ n))))
```

单项 ψ 的参数与列表前缀可消去.

```agda
argψ : E.T → E.T
argψ (E.ψ _ a ∷ _) = a
argψ _             = []

tl : E.T → E.T
tl (_ ∷ xs) = xs
tl []       = []

++-canc : ∀ (P : E.T) {a b} → P ++ a ≡ P ++ b → a ≡ b
++-canc []       e = e
++-canc (x ∷ xs) e = ++-canc xs (cong tl e)

ψ∷-canc : ∀ {ν} P {a b} → E.ψ ν (P ++ a) ∷ [] ≡ E.ψ ν (P ++ b) ∷ [] → a ≡ b
ψ∷-canc P e = ++-canc P (cong argψ e)
```

## 余尾 0 与 ω 的两条记号事实

非空项的余尾不是 0; 余尾 ω 的项的第 1 项非空.

```agda
cofψ₊≢c0 : ∀ u μ m → E.cofψ₊ u μ m ≡ E.c0 → ⊥
cofψ₊≢c0 u μ E.lt ()
cofψ₊≢c0 u μ E.eq ()
cofψ₊≢c0 u μ E.gt ()

cofA≢c0 : ∀ u c → E.cofA u c ≡ E.c0 → ⊥
cofA≢c0 u E.c0     ()
cofA≢c0 u E.c1     ()
cofA≢c0 u E.cω     ()
cofA≢c0 u (E.cΩ μ) e = cofψ₊≢c0 u μ (E.cmpᵀ (E.sucT μ) u) e

cofψ0≡c0 : ∀ u c → E.cofψ0 u c ≡ E.c0 → c ≡ E.c0
cofψ0≡c0 u E.c0     _  = refl
cofψ0≡c0 u E.c1     ()
cofψ0≡c0 u E.cω     ()
cofψ0≡c0 u (E.cΩ _) ()

cons≢c0 : ∀ y ys → E.cof (y ∷ ys) ≡ E.c0 → ⊥
cons≢c0 y (y′ ∷ ys)              e = cons≢c0 y′ ys e
cons≢c0 (E.ψ u (z ∷ zs)) []      e = cofA≢c0 u (E.cof (z ∷ zs)) e
cons≢c0 (E.ψ (w ∷ ws) []) []     e = cons≢c0 w ws (cofψ0≡c0 (w ∷ ws) (E.cof (w ∷ ws)) e)
cons≢c0 (E.ψ [] []) []           ()

c0→[] : ∀ t → E.cof t ≡ E.c0 → t ≡ []
c0→[] []       _ = refl
c0→[] (y ∷ ys) e = ⊥-elim (cons≢c0 y ys e)

fsnc≢[] : ∀ u b μ m → E.fsnc u b μ m 1 ≡ [] → ⊥
fsnc≢[] u b μ E.lt ()
fsnc≢[] u b μ E.eq ()
fsnc≢[] u b μ E.gt ()

fsn₊≢[] : ∀ u b c → (c ≡ E.c0 → ⊥) → E.fsn₊ u b c 1 ≡ [] → ⊥
fsn₊≢[] u b E.c0     n _ = n refl
fsn₊≢[] u b E.c1     _ ()
fsn₊≢[] u b E.cω     _ ()
fsn₊≢[] u b (E.cΩ μ) _ f = fsnc≢[] u b μ (E.cmpᵀ (E.sucT μ) u) f

fsn0≢[] : ∀ u c → E.cofψ0 u c ≡ E.cω → E.fsn0 u c 1 ≡ [] → ⊥
fsn0≢[] u E.c0     () _
fsn0≢[] u E.c1     () _
fsn0≢[] u E.cω     _  ()
fsn0≢[] u (E.cΩ _) () _

fsn1 : ∀ t → E.cof t ≡ E.cω → E.fsn t 1 ≡ [] → ⊥
fsn1 []                       () _
fsn1 (x ∷ y ∷ ys)             _  ()
fsn1 (E.ψ u (y ∷ ys) ∷ [])    _  f = fsn₊≢[] u (y ∷ ys) (E.cof (y ∷ ys)) (cons≢c0 y ys) f
fsn1 (E.ψ (w ∷ ws) [] ∷ [])   e  f = fsn0≢[] (w ∷ ws) (E.cof (w ∷ ws)) e f
fsn1 (E.ψ [] [] ∷ [])         () _
```

## 零树处的反演

`Mᴴ` 的每一条构造子: 零树只能由 `mz`, 极限 (第 1 项非空, 矛盾) 与向下封闭得到.

```agda
≤[] : ∀ {s} → s ≤ᵀ [] → s ≡ []
≤[] (inj₁ ())
≤[] (inj₂ e) = e

module _ {S : Sg} {Low : (p : P S) → E.T → B S p → Set} {Chd : (c : C S) → E.T → D S c → Set}
         {Nu : P S → E.T → Set} where
  inv0 : ∀ {τ x} → H.Mᴴ S Low Chd Nu τ x → x ≡ zero → τ ≡ []
  inv0 H.mz                  _    = refl
  inv0 (H.m1 _ _)            ()
  inv0 (H.mL {t = t} e h)    z    = ⊥-elim (fsn1 t e (inv0 (h 1) z))
  inv0 (H.mΩ _ _ _)          ()
  inv0 (H.mU _ _)            ()
  inv0 (H.mw _ d)            refl = ⊥-elim (¬◃z d)
  inv0 (H.mc le m)           z with inv0 m z
  ... | refl = ≤[] le

R-zero : ∀ ℓ {τ} → GR.R ℓ τ zero → τ ≡ []
R-zero zero     r = inv0 r refl
R-zero (nd s h) r = inv0 r refl

rd0 : ∀ {μ} → GR.Rd zero μ → μ ≡ []
rd0 (GR.c0 e)    = c0→[] _ e
rd0 (GR.ca ())
rd0 (GR.cL e h)  = ⊥-elim (fsn1 _ e (rd0 (h 1)))
rd0 (GR.cc le r) with rd0 r
... | refl = ≤[] le
```

## `Nu` 即槽位层的读法

```agda
mutual
  nu→rd : ∀ ℓ p {κ} → GR.Nu ℓ p κ → GR.Rd (at ℓ p) κ
  nu→rd (nd s h)      (inj₂ (c , t)) = nu⁼→rd (h c) t
  nu→rd (nd (sΩ k) h) (inj₁ t)       = nu⁼→rd k t

  nu⁼→rd : ∀ a t {κ} → GR.Nu⁼ a t κ → GR.Rd (proj₁ (sl⁼ a t)) κ
  nu⁼→rd a (inj₁ _) r = r
  nu⁼→rd a (inj₂ p) r = nu→rd a p r

mutual
  rd→nu : ∀ ℓ p {κ} → GR.Rd (at ℓ p) κ → GR.Nu ℓ p κ
  rd→nu (nd s h)      (inj₂ (c , t)) = rd→nu⁼ (h c) t
  rd→nu (nd (sΩ k) h) (inj₁ t)       = rd→nu⁼ k t

  rd→nu⁼ : ∀ a t {κ} → GR.Rd (proj₁ (sl⁼ a t)) κ → GR.Nu⁼ a t κ
  rd→nu⁼ a (inj₁ _) r = r
  rd→nu⁼ a (inj₂ p) r = rd→nu a p r
```
