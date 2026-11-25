# 验收 (换基): η = ω+1 的层, 回灌链第 0 步在未封闭关系下的否定

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 编译定理, 无前提. 孩子 c = `suc ωᶜ` 时兄弟孩子折的层 `ℓ₊` 上的关系 `M₊` (ω 槽位的分支关系取 `YiLRLow` 的 `Mω`), 它的 Ω 树对着 Ω_{ω+1} (`Mβ₊`). 朝第 2 层的那一行在 ω 槽位不保留 (`keep₊`), 回灌链第 0 步要 `Mω (Ω_ω) (第一个回灌值)`, 标准底时第一个回灌值是 `next⁺ (ω 层的 Ω 树)` (`feed₊`).
> 否定 (`chain0₊`, `noLeafᶜ`, `noFeedᶜ`, `noLeafᵉ`): 这一步不成立. 机制同 `YiRLNeg`: Ω_ω 的基本列第 1 项 Ω₁ 的余尾是 `cΩ []`, 只有槽位在第 0 层的 Ω 结点能给出; 谓词 `Q` (第一位置之下没有这样的结点, 对嵌入的孩子遗传) 沿 `◃` 向下封闭, 对 `+`, `next⁺` 封闭, ω 层的 Ω 树满足它 (孩子从第 2 层起).
> 否定的是 "按 `YiRBFam.LFΩ` 的回灌链, 用未封闭的 `Mω` 证 η = ω+1 的判据" 的第 0 步; 不否定判据本身, 不否定换基, 不涉及封闭后的关系.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLRNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (B₀; kp)
open import OCF.Lean.YiRBSib
open import OCF.Lean.YiRBCrit using (wˢ; sh)
open import OCF.Lean.YiRLCrit using (ℓˢ)
open import OCF.Lean.YiKVRel using (Mᴰ; M⁰; mz; m1; mL; mΩ; mU; mw)
import OCF.Align.EboLeanDef as E
open E using (cof; c1; cω; cΩ; fsn; γT; natT; sucT)
open import OCF.Lean.YiMENote using (cof++)
open import OCF.Lean.YiCLFam using (fn; M; Nw; lev)
open import OCF.Lean.YiCLLow using (Sb; pth)
open import OCF.Lean.YiCLPhi using (ωᵀ)
open import OCF.Lean.YiCLCrit using (ωᶜ)
open import OCF.Lean.YiLRBridge using (Sᶜ; MB; NwB; τ₂)
open import OCF.Lean.YiLRLow using (module Lim; Gᶜ; eᶜ; Rᶜ; canRᶜ; module Wᶜ; Gᵉ; dd; eᵉ; Rᵉ; canRᵉ; module Wᵉ)
```

## 谓词 Q

```agda
NZ : L → Set
NZ zero     = ⊥
NZ (nd _ _) = ⊤

Q : (ℓ : L) → Tr ℓ → Set
Q ℓ        zero          = ⊤
Q ℓ        (suc x)       = Q ℓ x
Q ℓ        (lim f _)     = ∀ n → Q ℓ (f n)
Q ℓ        (Ω p g)       = NZ (at ℓ p) × Q ℓ (g (fromBr ℓ p zero))
Q zero     (up _ () _ _)
Q (nd s h) (up x c y _)  = Q (nd s h) x × Q (h c) y

Q↓ : (ℓ : L) {x′ x : Tr ℓ} → ℓ ⊢ x′ ◃ x → Q ℓ x → Q ℓ x′
Q↓ ℓ        ◃s            q = q
Q↓ ℓ        (◃l n)        q = q n
Q↓ ℓ        ◃w            q = proj₂ q
Q↓ zero     (◃u _ () _ _)
Q↓ (nd s h) (◃u x c y e)  q = proj₁ q
Q↓ zero     (◃c _ () _)
Q↓ (nd s h) (◃c x c r)    q = proj₁ q , Q↓ (h c) r (proj₂ q)
Q↓ ℓ        (◃t d e)      q = Q↓ ℓ d (Q↓ ℓ e q)

Q+ : (ℓ : L) {b : Tr ℓ} → Q ℓ b → (y : Tr ℓ) → Q ℓ y → Q ℓ (b + y)
Q+ ℓ        qb zero          qy = qb
Q+ ℓ        qb (suc y)       qy = Q+ ℓ qb y qy
Q+ ℓ        qb (lim f a)     qy = λ n → Q+ ℓ qb (f n) (qy n)
Q+ ℓ        qb (Ω p g)       qy = proj₁ qy , Q+ ℓ qb (g (fromBr ℓ p zero)) (proj₂ qy)
Q+ zero     qb (up _ () _ _) qy
Q+ (nd s h) qb (up y c w e)  qy = Q+ (nd s h) qb y (proj₁ qy) , proj₂ qy

Qnext : (ℓ : L) (β : Tr⁺ ℓ) → Q ℓ (proj₁ β) → Q ℓ (proj₁ (next⁺ β))
Qnext ℓ (b , nb) qb = go
  where
  go : (n : ℕ) → Q ℓ (iter (b +_) b n)
  go zero    = qb
  go (suc n) = Q+ ℓ qb (iter (b +_) b n) (go n)

QΩS : (h : ⊤ → L) → NZ (h tt) → Q (nd sS h) (proj₁ (Ωt (nd sS h)))
QΩS h nz = nz , tt , tt

QΩL : (g : ℕ → L) → (∀ n → Q (g n) (proj₁ (Ωt (g n)))) → Q (nd sL g) (proj₁ (Ωt (nd sL g)))
QΩL g qg = go
  where
  go : (n : ℕ) → Q (nd sL g) (cum (λ k → proj₁ (upz {sL} {g} k (Ωt (g k)))) n)
  go zero    = tt , qg zero
  go (suc n) = Q+ (nd sL g) (go n) _ (tt , qg (suc n))
```

## 余尾 `cΩ []` 的项不对着满足 Q 的树

```agda
c1≢cΩ : ∀ {ν} → c1 ≡ cΩ ν → ⊥
c1≢cΩ ()

cω≢cΩ : ∀ {ν} → cω ≡ cΩ ν → ⊥
cω≢cΩ ()

cΩ≢cω : ∀ {ν} → cΩ ν ≡ cω → ⊥
cΩ≢cω ()

c1≢cω : c1 ≡ cω → ⊥
c1≢cω ()

cΩ-inj : ∀ {ν μ} → cΩ ν ≡ cΩ μ → ν ≡ μ
cΩ-inj refl = refl

no1⁰ : ∀ {t x} → M⁰ t x → cof t ≡ cΩ [] → ⊥
no1⁰ mz ()
no1⁰ (m1 e r) w = c1≢cΩ (trans (sym e) w)
no1⁰ (mL e h) w = cω≢cΩ (trans (sym e) w)
no1⁰ (mΩ {p = ()} _ _ _) w
no1⁰ (mU {c = ()} _ _) w
no1⁰ (mw m d) w = no1⁰ m w

module No1 {σ : Sh} {h : Ch σ → L} {Low : (p : Pos (nd σ h)) → E.T → Br (nd σ h) p → Set}
           {Chd : (c : Ch σ) → E.T → Tr (h c) → Set} {Nu : Pos (nd σ h) → E.T → Set}
           (hN : ∀ p → Nu p [] → NZ (at (nd σ h) p) → ⊥)
           (hC : ∀ c {t y} → Chd c t y → cof t ≡ cΩ [] → Q (h c) y → ⊥) where
  no1 : ∀ {t x} → Mᴰ (Sig (nd σ h)) Low Chd Nu t x → cof t ≡ cΩ [] → Q (nd σ h) x → ⊥
  no1 mz () q
  no1 (m1 e r) w q = c1≢cΩ (trans (sym e) w)
  no1 (mL e r) w q = cω≢cΩ (trans (sym e) w)
  no1 (mΩ {p = p} e nu r) w q = hN p (subst (Nu p) (cΩ-inj (trans (sym e) w)) nu) (proj₁ q)
  no1 (mU {t = t} {s = []} m ch) w q = no1 m (subst (λ z → cof z ≡ cΩ []) (++-identityʳ t) w) (proj₁ q)
  no1 (mU {t = t} {s = y ∷ ys} m ch) w q = hC _ ch (trans (sym (cof++ t y ys)) w) (proj₂ q)
  no1 (mw m d) w q = no1 m w (Q↓ (nd σ h) d q)

atLev : ∀ n (t : Pos⁼ (fn n)) → proj₁ (sl⁼ (fn n) t) ≡ fn (lev n t)
atLev n       (inj₁ tt)              = refl
atLev zero    (inj₂ ())
atLev (suc n) (inj₂ (inj₁ ()))
atLev (suc n) (inj₂ (inj₂ (tt , t))) = atLev n t

nat0 : ∀ k → [] ≡ natT k → k ≡ 0
nat0 zero    _  = refl
nat0 (suc k) ()

hNfin : ∀ n (p : Pos (fn (suc n))) → Nw n p [] → NZ (at (fn (suc n)) p) → ⊥
hNfin n (inj₁ ())
hNfin n (inj₂ (tt , t)) nu nz = subst NZ (cong fn (nat0 (lev n t) nu)) (subst NZ (atLev n t) nz)

noN : ∀ n {t x} → M n t x → cof t ≡ cΩ [] → Q (fn n) x → ⊥
noN zero    m w q = no1⁰ m w
noN (suc n) m w q = No1.no1 (hNfin n) (λ c ch w′ q′ → noN n ch w′ q′) m w q

hNB : ∀ {N} (ℓ : L) (e : ℓ ≡ fn N) (t : Pos⁼ ℓ) → NwB ℓ e t [] → NZ (proj₁ (sl⁼ ℓ t)) → ⊥
hNB {N} _ refl t nu nz = subst NZ (cong fn (nat0 (lev N t) nu)) (subst NZ (atLev N t) nz)

hCB : ∀ {N} (ℓ : L) (e : ℓ ≡ fn N) {t y} → MB ℓ e t y → cof t ≡ cΩ [] → Q ℓ y → ⊥
hCB {N} _ refl m w q = noN N m w q
```

## Ω_ω 不对着满足 Q 的树

```agda
split1 : ∀ (t s : E.T) {x} → t ++ s ≡ x ∷ [] → (t ≡ [] × s ≡ x ∷ []) ⊎ (t ≡ x ∷ [] × s ≡ [])
split1 []           s        w = inj₁ (refl , w)
split1 (y ∷ [])     []       w = inj₂ (w , refl)
split1 (y ∷ [])     (z ∷ zs) ()
split1 (y ∷ y′ ∷ t) s        ()

module No2 {σ : Sh} {h : Ch σ → L} {Low : (p : Pos (nd σ h)) → E.T → Br (nd σ h) p → Set}
           {Chd : (c : Ch σ) → E.T → Tr (h c) → Set} {Nu : Pos (nd σ h) → E.T → Set}
           (no1h : ∀ {t x} → Mᴰ (Sig (nd σ h)) Low Chd Nu t x → cof t ≡ cΩ [] → Q (nd σ h) x → ⊥)
           (hC2 : ∀ c {t y} → Chd c t y → t ≡ E.Ωt ωᵀ → Q (h c) y → ⊥) where
  no2 : ∀ {t x} → Mᴰ (Sig (nd σ h)) Low Chd Nu t x → t ≡ E.Ωt ωᵀ → Q (nd σ h) x → ⊥
  no2 mz () q
  no2 (m1 e r) w q = c1≢cω (trans (sym e) (cong cof w))
  no2 (mL e r) w q = no1h (r 1) (subst (λ z → cof (fsn z 1) ≡ cΩ []) (sym w) refl) q
  no2 (mΩ e nu r) w q = cΩ≢cω (trans (sym e) (cong cof w))
  no2 (mU {t = t} {s = s₁} m ch) w q =
    [ (λ p → hC2 _ ch (proj₂ p) (proj₂ q)) , (λ p → no2 m (proj₁ p) (proj₁ q)) ]′ (split1 t s₁ w)
  no2 (mw m d) w q = no2 m w (Q↓ (nd σ h) d q)

no2⁰ : ∀ {t x} → M⁰ t x → t ≡ E.Ωt ωᵀ → ⊥
no2⁰ mz ()
no2⁰ (m1 e r) w = c1≢cω (trans (sym e) (cong cof w))
no2⁰ (mL e r) w = no1⁰ (r 1) (subst (λ z → cof (fsn z 1) ≡ cΩ []) (sym w) refl)
no2⁰ (mΩ {p = ()} _ _ _) w
no2⁰ (mU {c = ()} _ _) w
no2⁰ (mw m d) w = no2⁰ m w

no2N : ∀ n {t x} → M n t x → t ≡ E.Ωt ωᵀ → Q (fn n) x → ⊥
no2N zero    m w q = no2⁰ m w
no2N (suc n) m w q = No2.no2 (noN (suc n)) (λ c ch w′ q′ → no2N n ch w′ q′) m w q

hC2B : ∀ {N} (ℓ : L) (e : ℓ ≡ fn N) {t y} → MB ℓ e t y → t ≡ E.Ωt ωᵀ → Q ℓ y → ⊥
hC2B {N} _ refl m w q = no2N N m w q

module NegLim (G : ℕ → L) (d : ℕ → ℕ) (eG : ∀ n → G n ≡ fn (d n)) (R : (n : ℕ) → G n ≤ G (suc n))
              (canR : ∀ n → Σ (Sb (d (suc n)) (d n)) λ s → τ₂ (eG n) (eG (suc n)) (R n) ≡ pth s) where
  open Lim G d eG R canR

  hNω : ∀ p → Nuω p [] → NZ (at Lω p) → ⊥
  hNω (inj₁ ())
  hNω (inj₂ (m , t)) nu nz = hNB (G m) (eG m) t nu nz

  noω1 : ∀ {t x} → Mω t x → cof t ≡ cΩ [] → Q Lω x → ⊥
  noω1 m w q = No1.no1 hNω (λ c ch w′ q′ → hCB (G c) (eG c) ch w′ q′) m w q

  noωω : ∀ {t x} → Mω t x → t ≡ E.Ωt ωᵀ → Q Lω x → ⊥
  noωω m w q = No2.no2 noω1 (λ c ch w′ q′ → hC2B (G c) (eG c) ch w′ q′) m w q
```

## 实例: ω 层的 Ω 树与第一个回灌值

```agda
QΩᶜ : ∀ n → Q (Gᶜ n) (proj₁ (Ωt (Gᶜ n)))
QΩᶜ zero    = QΩS (λ _ → fn 1) tt
QΩᶜ (suc n) = QΩS (λ _ → Gᶜ n) (nz n)
  where
  nz : ∀ n → NZ (Gᶜ n)
  nz zero    = tt
  nz (suc n) = tt

QΩᵉ : ∀ n → Q (Gᵉ n) (proj₁ (Ωt (Gᵉ n)))
QΩᵉ zero    = QΩS (λ _ → fn 1) tt
QΩᵉ (suc n) = QΩS (λ _ → Sᶜ (Gᵉ n)) tt

module Nᶜ = NegLim Gᶜ sh eᶜ Rᶜ canRᶜ
module Nᵉ = NegLim Gᵉ dd eᵉ Rᵉ canRᵉ

noLeafᶜ : Wᶜ.Mω (E.Ωt ωᵀ) (proj₁ (Ωt Wᶜ.Lω)) → ⊥
noLeafᶜ m = Nᶜ.noωω m refl (QΩL Gᶜ QΩᶜ)

noFeedᶜ : Wᶜ.Mω (E.Ωt ωᵀ) (proj₁ (next⁺ (Ωt Wᶜ.Lω))) → ⊥
noFeedᶜ m = Nᶜ.noωω m refl (Qnext Wᶜ.Lω (Ωt Wᶜ.Lω) (QΩL Gᶜ QΩᶜ))

noLeafᵉ : Wᵉ.Mω (E.Ωt ωᵀ) (proj₁ (Ωt Wᵉ.Lω)) → ⊥
noLeafᵉ m = Nᵉ.noωω m refl (QΩL Gᵉ QΩᵉ)
```

## η = ω+1: 层, 关系, Ω 树, 那一行在 ω 槽位的形状

```agda
ℓ₊ : L
ℓ₊ = Sᶜ Wᶜ.Lω

lvl₊ : ℓˢ (suc ωᶜ) ≡ ℓ₊
lvl₊ = refl

path₊ : wˢ (suc ωᶜ) ≡ inc tt (inc 0 self)
path₊ = refl

p₊ : Pos ℓ₊
p₊ = inj₂ (tt , inj₁ tt)

Low₊ : (p : Pos ℓ₊) → E.T → Br ℓ₊ p → Set
Low₊ (inj₁ ())
Low₊ (inj₂ (tt , inj₁ tt)) = Wᶜ.Mω
Low₊ (inj₂ (tt , inj₂ p))  = Wᶜ.Lowω p

Nu₊ : Pos ℓ₊ → E.T → Set
Nu₊ (inj₁ ())
Nu₊ (inj₂ (tt , inj₁ tt)) ν = ν ≡ ωᵀ
Nu₊ (inj₂ (tt , inj₂ p))  = Wᶜ.Nuω p

M₊ : E.T → Tr ℓ₊ → Set
M₊ = Mᴰ (Sig ℓ₊) Low₊ (λ _ → Wᶜ.Mω) Nu₊

Mβ₊ : M₊ (E.Ωt (sucT ωᵀ)) (proj₁ (Ωt ℓ₊))
Mβ₊ = mΩ refl refl (λ η c l → mU mz (mw l ◃s))

keep₊ : (o : Ok ℓ₊) → kp ℓ₊ o p₊ (inc tt (inc 0 self)) ≡ nothing
keep₊ o = refl

feed₊ : (o : Ok ℓ₊) (r : Rb ℓ₊)
      → fromBr ℓ₊ p₊ (proj₁ (ψ ℓ₊ o r (B₀ ℓ₊) (at ℓ₊ p₊) (posW ℓ₊ p₊) (B₀ ℓ₊ (at ℓ₊ p₊) (posW ℓ₊ p₊))
                         (up zero tt (suc zero) (z◃ zero ◃s))))
      ≡ proj₁ (next⁺ (Ωt Wᶜ.Lω))
feed₊ o r = refl

chain0₊ : (o : Ok ℓ₊) (r : Rb ℓ₊) (b : E.T)
        → Low₊ p₊ (γT b ωᵀ 0)
            (fromBr ℓ₊ p₊ (proj₁ (ψ ℓ₊ o r (B₀ ℓ₊) (at ℓ₊ p₊) (posW ℓ₊ p₊) (B₀ ℓ₊ (at ℓ₊ p₊) (posW ℓ₊ p₊))
                                (up zero tt (suc zero) (z◃ zero ◃s)))))
        → ⊥
chain0₊ o r b m = noFeedᶜ m
```
