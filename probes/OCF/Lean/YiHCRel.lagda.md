# 验收一侧: 遗传封闭的关系 (每个结点都可按项序换成较大的参照项)

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 判决: 编译定理, 无前提. `Mᴴ` 是 `YiKVRel.Mᴰ` 加一条构造子 `mc : s ≤ᵀ t → Mᴴ t x → Mᴴ s x`; 低层的 `Mᴴ` 作分支关系与孩子关系时, 结点规则里用的就是封闭后的关系. `YiMHRel.M̂` 的 `ĉ` 即 `mc`, `l̂` 即 `mL`.
> `Gen`: 加法, `next`, 累加 (照 `YiKVRel.Gen`, 各加 `mc` 一行). 第 0 层出口 `exitᴴ`: 条件 `Exᴴ` 对推导递归, 每个 `mc` 结点上两个项是标准形且较大的可数 (照 `YiMHRel.exit̂`).
> 不给出什么: 不涉及上界; `Exᴴ` 在哪些推导上成立不在这里. 族与保持见 [YiHCFam](YiHCFam.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiHCRel where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_; replicate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiKVRel using (_⊴_; ⊴r; ⊴◃; ⊴-◃; +⊴; ¬◃z; readRW; ◃→≼)
import OCF.Align.EboLeanDef as E
open E using (HC; h0; h1; hω; cof; c1; cω; cΩ; pred; fsn; fsT; 𝟏; tl<)
open import OCF.Align.EboLeanBase using (_≤ᵀ_; NF; Ctbl)
open import OCF.Align.EboLeanTree using (hc)
open import OCF.Align.Value using (_≼_; z≼; s≼s; l≼; ≼-trans)
open import OCF.Lean.YiRefTw2 using (Rt)
open import OCF.Lean.YiCFMono using (mono≤ⁿ)
```

## 关系

```agda
data Mᴴ (S : Sg) (Low : (p : P S) → E.T → B S p → Set) (Chd : (c : C S) → E.T → D S c → Set)
        (Nu : P S → E.T → Set) : E.T → T S → Set where
  mz : ∀ {x} → Mᴴ S Low Chd Nu [] x
  m1 : ∀ {t x} → cof t ≡ c1 → Mᴴ S Low Chd Nu (pred t) x → Mᴴ S Low Chd Nu t (suc x)
  mL : ∀ {t x} → cof t ≡ cω → (∀ n → Mᴴ S Low Chd Nu (fsn t n) x) → Mᴴ S Low Chd Nu t x
  mΩ : ∀ {t ν p g} → cof t ≡ cΩ ν → Nu p ν
     → (∀ η c → Low p η c → Mᴴ S Low Chd Nu (fsT t η) (g c)) → Mᴴ S Low Chd Nu t (Ω p g)
  mU : ∀ {t s x c y e} → Mᴴ S Low Chd Nu t x → Chd c s y → Mᴴ S Low Chd Nu (t ++ s) (up x c y e)
  mw : ∀ {t x x′} → Mᴴ S Low Chd Nu t x → Lt S x x′ → Mᴴ S Low Chd Nu t x′
  mc : ∀ {s t x} → s ≤ᵀ t → Mᴴ S Low Chd Nu t x → Mᴴ S Low Chd Nu s x

∷≤ : ∀ p {s t} → s ≤ᵀ t → (p ∷ s) ≤ᵀ (p ∷ t)
∷≤ p (inj₁ q)    = inj₁ (tl< q)
∷≤ p (inj₂ refl) = inj₂ refl
```

## 对一切层成立的引理

```agda
module Gen {S : Sg} {Low : (p : P S) → E.T → B S p → Set} {Chd : (c : C S) → E.T → D S c → Set}
           {Nu : P S → E.T → Set} where
  private
    M : E.T → T S → Set
    M = Mᴴ S Low Chd Nu

  m⊴ : ∀ {t x x′} → M t x → x ⊴ x′ → M t x′
  m⊴ m ⊴r     = m
  m⊴ m (⊴◃ d) = mw m d

  m1∷ : ∀ p s {x} → cof s ≡ c1 → M (p ∷ pred s) x → M (p ∷ s) (suc x)
  m1∷ p []      () r
  m1∷ p (_ ∷ _) e  r = m1 e r

  mL∷ : ∀ p s {x} → cof s ≡ cω → (∀ n → M (p ∷ fsn s n) x) → M (p ∷ s) x
  mL∷ p []      () h
  mL∷ p (_ ∷ _) e  h = mL e h

  mΩ∷ : ∀ p s {ν q g} → cof s ≡ cΩ ν → Nu q ν
      → (∀ η c → Low q η c → M (p ∷ fsT s η) (g c)) → M (p ∷ s) (Ω q g)
  mΩ∷ p []      () nu h
  mΩ∷ p (_ ∷ _) e  nu h = mΩ e nu h

  m-add : ∀ {p b s y} → M (p ∷ []) b → M s y → M (p ∷ s) (b + y)
  m-add {b = b} mb (mz {x = y})          = m⊴ mb (+⊴ b y)
  m-add {p = p} mb (m1 {t = s} e r)      = m1∷ p s e (m-add mb r)
  m-add {p = p} mb (mL {t = s} e h)      = mL∷ p s e (λ n → m-add mb (h n))
  m-add {p = p} mb (mΩ {t = s} e nu h)   = mΩ∷ p s e nu (λ η c l → m-add mb (h η c l))
  m-add mb (mU m ch)                     = mU (m-add mb m) ch
  m-add {b = b} mb (mw m d)              = mw (m-add mb m) (+-mono b d)
  m-add {p = p} mb (mc le m)             = mc (∷≤ p le) (m-add mb m)

  m-rep : ∀ {p b} → M (p ∷ []) b → ∀ n → M (replicate (suc n) p) (iter (b +_) b n)
  m-rep mb zero    = mb
  m-rep mb (suc n) = m-add mb (m-rep mb n)

  m-next : ∀ {t p} (b : T⁺ {S}) → cof t ≡ cω → (∀ n → fsn t n ≡ replicate n p)
         → M (p ∷ []) (proj₁ b) → M t (proj₁ (next⁺ b))
  m-next {t} {p} (b , nb) e q mb = mL e (λ n → subst (λ s → M s (proj₁ (next⁺ (b , nb)))) (sym (q n)) (go n))
    where
    go : ∀ n → M (replicate n p) (proj₁ (next⁺ (b , nb)))
    go zero    = mz
    go (suc n) = mw (m-rep mb n) (◃l n)

  m-right : ∀ {t y} (a : T S) → M t y → M t (a + y)
  m-right a mz             = mz
  m-right a (m1 e r)       = m1 e (m-right a r)
  m-right a (mL e h)       = mL e (λ n → m-right a (h n))
  m-right a (mΩ e nu h)    = mΩ e nu (λ η c l → m-right a (h η c l))
  m-right a (mU m ch)      = mU (m-right a m) ch
  m-right a (mw m d)       = mw (m-right a m) (+-mono a d)
  m-right a (mc le m)      = mc le (m-right a m)

  m-cum : ∀ {t} (F : ℕ → T⁺ {S}) (n : ℕ) → M t (proj₁ (F n)) → M t (proj₁ (limc⁺ F))
  m-cum {t} F n m = mw (go n m) (◃l n)
    where
    go : ∀ n → M t (proj₁ (F n)) → M t (cum (λ k → proj₁ (F k)) n)
    go zero    m = m
    go (suc n) m = m-right (cum (λ k → proj₁ (F k)) n) m

  m-zl : {S′ : Sg} (Φ : T S′ → T S) → (∀ {x y} → Lt S′ x y → Lt S (Φ x) (Φ y))
       → ∀ {t} → M t (Φ zero) → (y : T S′) → M t (Φ y)
  m-zl Φ mono m y with zl y
  ... | inj₁ refl = m
  ... | inj₂ d    = mw m (mono d)
```

## 第 0 层与出口

`Exᴴ m`: 推导 m 的每个 `mc` 结点 (参照 s, 较大的项 t) 上 s, t 是标准形, t 可数. 出口对推导归纳: `mc` 处用记号一侧的单调 `mono≤ⁿ`, 其余各行同 `YiKVRel.lower⁰`.

```agda
M⁰ : E.T → Tr zero → Set
M⁰ = Mᴴ (Sig zero) (λ ()) (λ ()) (λ ())

module G⁰ = Gen {Sig zero} {λ ()} {λ ()} {λ ()}

pos⁰ : (y : Tr zero) → zero ⊢ zero ◃ y → M⁰ (𝟏 ∷ []) y
pos⁰ zero      d = ⊥-elim (¬◃z d)
pos⁰ (suc y)   d = m1 refl mz
pos⁰ (lim f a) d with zl (f 1)
... | inj₁ e  = ⊥-elim (¬◃z (subst (λ v → zero ⊢ f 0 ◃ v) (sym e) (a 0)))
... | inj₂ d′ = mw (pos⁰ (f 1) d′) (◃l 1)
pos⁰ (Ω () _)      d
pos⁰ (up _ () _ _) d

Exᴴ : ∀ {s x} → M⁰ s x → Set
Exᴴ mz                   = ⊤
Exᴴ (m1 _ r)             = Exᴴ r
Exᴴ (mL _ h)             = ∀ n → Exᴴ (h n)
Exᴴ (mΩ {p = ()} _ _ _)
Exᴴ (mU {c = ()} _ _)
Exᴴ (mw m _)             = Exᴴ m
Exᴴ (mc {s} {t} _ m)     = NF s × NF t × Ctbl t × Exᴴ m

private
  c1≢cω : c1 ≡ cω → ⊥
  c1≢cω ()

exitᴴ : ∀ {s x} (m : M⁰ s x) → Exᴴ m → (h : HC s) → Rt h ≼ readRW x
exitᴴ mz       ex (h0 _)    = z≼
exitᴴ mz       ex (h1 () _)
exitᴴ mz       ex (hω () _)
exitᴴ (m1 e r) ex (h0 _)    = z≼
exitᴴ (m1 e r) ex (h1 _ h)  = s≼s (exitᴴ r ex h)
exitᴴ (m1 e r) ex (hω e′ _) = ⊥-elim (c1≢cω (trans (sym e) e′))
exitᴴ (mL e r) ex (h0 _)    = z≼
exitᴴ (mL e r) ex (h1 e′ _) = ⊥-elim (c1≢cω (trans (sym e′) e))
exitᴴ (mL e r) ex (hω _ h)  = l≼ (λ n → exitᴴ (r n) (ex n) (h n))
exitᴴ (mΩ {p = ()} _ _ _) ex h
exitᴴ (mU {c = ()} _ _) ex h
exitᴴ (mw m d) ex h = ≼-trans (exitᴴ m ex h) (◃→≼ d)
exitᴴ (mc le m) (ns , nt , ct , ex) h = ≼-trans (mono≤ⁿ ns nt ct h (hc nt ct) le) (exitᴴ m ex (hc nt ct))
```
