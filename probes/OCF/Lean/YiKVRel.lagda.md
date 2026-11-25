# 候选 A: 值的关系 (验收)

> 验收文件 (读记号). 编译定理, 无前提: 精简块签名上的下界关系 `Mᴰ` (同 `YiMEBase`, 搬到 `YiRWBlock`); 第 0 层的出口 `lower⁰ : M⁰ t x → (h : HC t) → Rt h ≼ readRW x` (直接对关系归纳); 第 1 层的关系 `M¹`; 候选折叠在第 1 层上的三条保持: 上折对和 (`Pu`, `Qu`), 折到自身对 ψ₁(t₀ + a) (`PF`), 折到第 0 层对 ψ₀(t₀ + a) (`QH`, 结点处记号的 γ-链对块的回灌链 `chain`). 前缀 t₀ 任意, 对满足下界条件的任意底与起点成立.
> 不涉及上界; 第 1 层的行是后继形状的行, 与精简块逐字相同. 用在 `YiKVValue`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiKVRel where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_; replicate)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiKVPath
open import OCF.Lean.YiKVFold
open import OCF.Lean.YiCertFold using (Base; node⁺)
import OCF.Align.EboLeanDef as E
open E using (HC; h0; h1; hω; cof; c0; c1; cω; cΩ; pred; fsn; fsT; γT; 𝟏; natT) renaming (ψ to ψᵉ)
open import OCF.Lean.YiMENote using (cofψ1; fsnψ1; cofψω; fsnψω; cofψΩ; fsnψΩ; fsTψΩ; cof++; cof++1; cof++ω; pred++; fsn++)
open import OCF.Lean.YiRefTw2 using (Rt)
import OCF.Align.Level as O
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼-refl; ≼-trans; ≼-suc)
```

## 关系

`Mᴰ S Low Chd Nu t x`: 记号项 t 不高于树 x 的证据 (逐字同 `YiMEBase.Mᴰ`, 签名换成精简块的).

```agda
data Mᴰ (S : Sg) (Low : (p : P S) → E.T → B S p → Set) (Chd : (c : C S) → E.T → D S c → Set)
        (Nu : P S → E.T → Set) : E.T → T S → Set where
  mz : ∀ {x} → Mᴰ S Low Chd Nu [] x
  m1 : ∀ {t x} → cof t ≡ c1 → Mᴰ S Low Chd Nu (pred t) x → Mᴰ S Low Chd Nu t (suc x)
  mL : ∀ {t x} → cof t ≡ cω → (∀ n → Mᴰ S Low Chd Nu (fsn t n) x) → Mᴰ S Low Chd Nu t x
  mΩ : ∀ {t ν p g} → cof t ≡ cΩ ν → Nu p ν
     → (∀ η c → Low p η c → Mᴰ S Low Chd Nu (fsT t η) (g c)) → Mᴰ S Low Chd Nu t (Ω p g)
  mU : ∀ {t s x c y e} → Mᴰ S Low Chd Nu t x → Chd c s y → Mᴰ S Low Chd Nu (t ++ s) (up x c y e)
  mw : ∀ {t x x′} → Mᴰ S Low Chd Nu t x → Lt S x x′ → Mᴰ S Low Chd Nu t x′

infix 4 _⊴_
data _⊴_ {S : Sg} (t : T S) : T S → Set where
  ⊴r : t ⊴ t
  ⊴◃ : ∀ {t′} → Lt S t t′ → t ⊴ t′

module _ {S : Sg} where
  ⊴-◃ : {a b c : T S} → a ⊴ b → Lt S b c → Lt S a c
  ⊴-◃ ⊴r     e = e
  ⊴-◃ (⊴◃ d) e = ◃t d e

  +⊴ : (b y : T S) → b ⊴ b + y
  +⊴ b zero         = ⊴r
  +⊴ b (suc y)      = ⊴◃ (⊴-◃ (+⊴ b y) ◃s)
  +⊴ b (lim f a)    = ⊴◃ (⊴-◃ (+⊴ b (f zero)) (◃l zero))
  +⊴ b (Ω p g)      = ⊴◃ (⊴-◃ (+⊴ b (g (b₀ S p))) ◃w)
  +⊴ b (up y c w e) = ⊴◃ (⊴-◃ (+⊴ b y) (◃u (b + y) c w e))

  ¬◃z : {x : T S} → Lt S x zero → ⊥
  ¬◃z (◃t d e) = ¬◃z e
```

## 对一切层成立的引理

```agda
module Gen {S : Sg} {Low : (p : P S) → E.T → B S p → Set} {Chd : (c : C S) → E.T → D S c → Set}
           {Nu : P S → E.T → Set} where
  private
    M : E.T → T S → Set
    M = Mᴰ S Low Chd Nu

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

## 第 0 层: 读回与出口

`readRW` 与 `YiBRValue.readRW` 逐字相同. 出口对关系直接归纳.

```agda
readRW : Tr zero → O.Ordᶜ O.zero
readRW zero      = O.zero
readRW (suc x)   = O.suc (readRW x)
readRW (lim f _) = O.lim (λ n → readRW (f n))

M⁰ : E.T → Tr zero → Set
M⁰ = Mᴰ (Sig zero) (λ ()) (λ ()) (λ ())

module G⁰ = Gen {Sig zero} {λ ()} {λ ()} {λ ()}

◃→≼ : {x y : Tr zero} → zero ⊢ x ◃ y → readRW x ≼ readRW y
◃→≼ {x} ◃s           = ≼-suc (≼-refl (readRW x))
◃→≼ (◃l {f = f} n)   = ≼l n (≼-refl (readRW (f n)))
◃→≼ (◃w {p = ()})
◃→≼ (◃u _ () _ _)
◃→≼ (◃c _ () _)
◃→≼ (◃t d e)         = ≼-trans (◃→≼ d) (◃→≼ e)

private
  c1≢cω : c1 ≡ cω → ⊥
  c1≢cω ()

lower⁰ : ∀ {t x} → M⁰ t x → (h : HC t) → Rt h ≼ readRW x
lower⁰ mz       (h0 _)    = z≼
lower⁰ mz       (h1 () _)
lower⁰ mz       (hω () _)
lower⁰ (m1 e r) (h0 _)    = z≼
lower⁰ (m1 e r) (h1 _ h)  = s≼s (lower⁰ r h)
lower⁰ (m1 e r) (hω e′ _) = ⊥-elim (c1≢cω (trans (sym e) e′))
lower⁰ (mL e r) (h0 _)    = z≼
lower⁰ (mL e r) (h1 e′ _) = ⊥-elim (c1≢cω (trans (sym e′) e))
lower⁰ (mL e r) (hω _ h)  = l≼ (λ n → lower⁰ (r n) (h n))
lower⁰ (mΩ {p = ()} _ _ _) h
lower⁰ (mU {c = ()} _ _) h
lower⁰ (mw m d) h = ≼-trans (lower⁰ m h) (◃→≼ d)

pos⁰ : (y : Tr zero) → zero ⊢ zero ◃ y → M⁰ (𝟏 ∷ []) y
pos⁰ zero      d = ⊥-elim (¬◃z d)
pos⁰ (suc y)   d = m1 refl mz
pos⁰ (lim f a) d with zl (f 1)
... | inj₁ e  = ⊥-elim (¬◃z (subst (λ v → zero ⊢ f 0 ◃ v) (sym e) (a 0)))
... | inj₂ d′ = mw (pos⁰ (f 1) d′) (◃l 1)
pos⁰ (Ω () _)      d
pos⁰ (up _ () _ _) d
```

## 第 1 层的关系

第 1 层只有一个槽位 (第 0 层的树作分支) 与一个孩子 (第 0 层); 结点的共尾下标只许 0.

```agda
one two : L
one = nd sS (λ _ → zero)
two = nd sS (λ _ → one)

q1 : Pos one
q1 = inj₂ (tt , inj₁ tt)

Low¹ : (p : Pos one) → E.T → Br one p → Set
Low¹ (inj₂ (tt , inj₁ tt)) = M⁰
Low¹ (inj₁ ())
Low¹ (inj₂ (tt , inj₂ ()))

Nu¹ : Pos one → E.T → Set
Nu¹ _ ν = ν ≡ []

M¹ : E.T → Tr one → Set
M¹ = Mᴰ (Sig one) Low¹ (λ _ → M⁰) Nu¹

module G¹ = Gen {Sig one} {Low¹} {λ _ → M⁰} {Nu¹}

u₀ u₁ : E.T
u₀ = []
u₁ = natT 1

ψ₀ᵗ ψ₁ᵗ : E.T → E.T
ψ₀ᵗ a = ψᵉ u₀ a ∷ []
ψ₁ᵗ a = ψᵉ u₁ a ∷ []

Ω₁ᵗ : E.T
Ω₁ᵗ = E.Ωt u₁

Mβ₀ : M¹ Ω₁ᵗ (proj₁ (Ωt one))
Mβ₀ = mΩ refl refl (λ η c l → mU mz (mw l ◃s))
```

记号一侧: 和 t + s 的余尾 Ω 与 Ω-基本列落在 s 上.

```agda
cof++Ω : ∀ t s {ν} → cof s ≡ cΩ ν → cof (t ++ s) ≡ cΩ ν
cof++Ω t []       ()
cof++Ω t (y ∷ ys) e = trans (cof++ t y ys) e

fsT++ : ∀ t y ys η → fsT (t ++ y ∷ ys) η ≡ t ++ fsT (y ∷ ys) η
fsT++ []           y ys η = refl
fsT++ (x ∷ [])     y ys η = refl
fsT++ (x ∷ x′ ∷ t) y ys η = cong (x ∷_) (fsT++ (x′ ∷ t) y ys η)

++[] : (Z : E.T → Set) (t : E.T) → Z t → Z (t ++ [])
++[] Z t q = subst Z (sym (++-identityʳ t)) q
```

## 孩子里的和: 上折与第 0 层的折叠

`up x _ y` 的折叠以 x 的折叠为起点再折 y; 记号一侧是 ψ_u(t + s). 对 `M⁰ s y` 归纳.

```agda
Pu : ∀ {t} (b : Tr⁺ one) → M¹ (ψ₁ᵗ t) (proj₁ b) → ∀ {s y} → M⁰ s y
   → M¹ (ψ₁ᵗ (t ++ s)) (proj₁ (Up zero (down stop tt) b y))
Pu {t} b mb (mz {x = y}) =
  ++[] (λ z → M¹ (ψ₁ᵗ z) (proj₁ (Up zero (down stop tt) b y))) t
    (G¹.m-zl (λ y → proj₁ (Up zero (down stop tt) b y)) (Upm zero (down stop tt) b) mb y)
Pu {t} b mb (m1 {t = s} {x = y} e r) =
  G¹.m-next (Up zero (down stop tt) b y) (cofψ1 u₁ (t ++ s) (cof++1 t s e))
    (λ n → trans (fsnψ1 u₁ (t ++ s) n (cof++1 t s e)) (cong (λ z → replicate n (ψᵉ u₁ z)) (pred++ t s e)))
    (Pu b mb r)
Pu {t} b mb (mL {t = s} {x = y} e h) =
  mL (cofψω u₁ (t ++ s) (cof++ω t s e))
    (λ n → subst (λ z → M¹ z (proj₁ (Up zero (down stop tt) b y)))
      (sym (trans (fsnψω u₁ (t ++ s) n (cof++ω t s e)) (cong ψ₁ᵗ (fsn++ t s n e))))
      (Pu b mb (h n)))
Pu b mb (mΩ {p = ()} _ _ _)
Pu b mb (mU {c = ()} _ _)
Pu b mb (mw m d) = mw (Pu b mb m) (Upm zero (down stop tt) b d)

Qu : ∀ {t} (o0 : Ok zero) (B0 : Base zero) (w : zero ≤ zero) (b : Tr⁺ zero) → M⁰ (ψ₀ᵗ t) (proj₁ b)
   → ∀ {s y} → M⁰ s y → M⁰ (ψ₀ᵗ (t ++ s)) (proj₁ (ψ zero o0 B0 zero w b y))
Qu {t} o0 B0 w b mb (mz {x = y}) =
  ++[] (λ z → M⁰ (ψ₀ᵗ z) (proj₁ (ψ zero o0 B0 zero w b y))) t
    (G⁰.m-zl (λ y → proj₁ (ψ zero o0 B0 zero w b y)) (mono zero o0 B0 zero w b) mb y)
Qu {t} o0 B0 w b mb (m1 {t = s} {x = y} e r) =
  G⁰.m-next (ψ zero o0 B0 zero w b y) (cofψ1 u₀ (t ++ s) (cof++1 t s e))
    (λ n → trans (fsnψ1 u₀ (t ++ s) n (cof++1 t s e)) (cong (λ z → replicate n (ψᵉ u₀ z)) (pred++ t s e)))
    (Qu o0 B0 w b mb r)
Qu {t} o0 B0 w b mb (mL {t = s} {x = y} e h) =
  mL (cofψω u₀ (t ++ s) (cof++ω t s e))
    (λ n → subst (λ z → M⁰ z (proj₁ (ψ zero o0 B0 zero w b y)))
      (sym (trans (fsnψω u₀ (t ++ s) n (cof++ω t s e)) (cong ψ₀ᵗ (fsn++ t s n e))))
      (Qu o0 B0 w b mb (h n)))
Qu o0 B0 w b mb (mΩ {p = ()} _ _ _)
Qu o0 B0 w b mb (mU {c = ()} _ _)
Qu o0 B0 w b mb (mw m d) = mw (Qu o0 B0 w b mb m) (mono zero o0 B0 zero w b d)
```

## 第 1 层: 折到自身对 ψ₁(t₀ + a)

结点保留, 记号一侧是规则 5Ω (下标相等, 穿透).

```agda
module PFm (t₀ : E.T) (o1 : Ok one) (Bs : Base one) (β : Tr⁺ one) (hβ : M¹ (ψ₁ᵗ t₀) (proj₁ β)) where
  F⁺ : Tr one → Tr⁺ one
  F⁺ x = ψ one o1 Bs one self β x

  F : Tr one → Tr one
  F x = proj₁ (F⁺ x)

  PF : ∀ {a x} → M¹ a x → M¹ (ψ₁ᵗ (t₀ ++ a)) (F x)
  PF (mz {x = x}) = ++[] (λ z → M¹ (ψ₁ᵗ z) (F x)) t₀ (G¹.m-zl F (mono one o1 Bs one self β) hβ x)
  PF (m1 {t = a} {x = x} e r) =
    G¹.m-next (F⁺ x) (cofψ1 u₁ (t₀ ++ a) (cof++1 t₀ a e))
      (λ n → trans (fsnψ1 u₁ (t₀ ++ a) n (cof++1 t₀ a e)) (cong (λ z → replicate n (ψᵉ u₁ z)) (pred++ t₀ a e)))
      (PF r)
  PF (mL {t = a} {x = x} e h) =
    mL (cofψω u₁ (t₀ ++ a) (cof++ω t₀ a e))
      (λ n → subst (λ z → M¹ z (F x)) (sym (trans (fsnψω u₁ (t₀ ++ a) n (cof++ω t₀ a e)) (cong ψ₁ᵗ (fsn++ t₀ a n e))))
        (PF (h n)))
  PF (mΩ {t = []} () _ _)
  PF (mΩ {t = y ∷ ys} {p = inj₂ (tt , inj₁ tt)} {g = g} e refl h) =
    mΩ (cofψΩ u₁ (t₀ ++ y ∷ ys) (cof++Ω t₀ (y ∷ ys) e)) refl
      (λ η c l → subst (λ z → M¹ z (F (g c)))
        (sym (trans (fsTψΩ u₁ (t₀ ++ y ∷ ys) η (cof++Ω t₀ (y ∷ ys) e)) (cong ψ₁ᵗ (fsT++ t₀ y ys η))))
        (PF (h η c l)))
  PF (mΩ {p = inj₁ ()} _ _ _)
  PF (mΩ {p = inj₂ (tt , inj₂ ())} _ _ _)
  PF (mU {t = a} {s = s} {x = x} m ch) =
    subst (λ z → M¹ (ψ₁ᵗ z) _) (++-assoc t₀ a s) (Pu (F⁺ x) (PF m) ch)
  PF (mw m d) = mw (PF m) (mono one o1 Bs one self β d)
```

## 第 1 层: 折到第 0 层对 ψ₀(t₀ + a)

目标第 0 层时结点不保留, 块取回灌链的部分和; 记号走规则 6 的 γ-链 (γ₀ = 1, γₙ₊₁ = ψ₀(a[γₙ])). 回灌链的函数与起点, 路径无关 (目标是槽位所在的第 0 层, 起点是底在那里的分量), 所以链对一切起点共用 `chain`.

```agda
module QHm (t₀ : E.T) (o1 : Ok one) (Bs : Base one) (hb′ : M⁰ (ψ₀ᵗ t₀) (proj₁ (Bs zero (inc tt self)))) where
  H⁺ : zero ≤ one → Tr⁺ zero → Tr one → Tr⁺ zero
  H⁺ w b x = ψ one o1 Bs zero w b x

  Hc : Tr one → Tr zero
  Hc x = proj₁ (H⁺ (inc tt self) (Bs zero (inc tt self)) x)

  vch : (Tr zero → Tr one) → ℕ → Tr zero
  vch g = iter (λ z → Hc (g z)) zero

  node1 : (w : zero ≤ one) (b : Tr⁺ zero) (g : Tr zero → Tr one)
        → proj₁ (H⁺ w b (Ω q1 g)) ≡ proj₁ (limc⁺ (λ m → H⁺ w b (g (vch g m))))
  node1 (inc tt v) b g = refl
  node1 (inu vs)   b g = refl

  mutual
    QH : (w : zero ≤ one) (b : Tr⁺ zero) → M⁰ (ψ₀ᵗ t₀) (proj₁ b) → ∀ {a x} → M¹ a x → M⁰ (ψ₀ᵗ (t₀ ++ a)) (proj₁ (H⁺ w b x))
    QH w b hb (mz {x = x}) = ++[] (λ z → M⁰ (ψ₀ᵗ z) (proj₁ (H⁺ w b x))) t₀ (G⁰.m-zl (λ x → proj₁ (H⁺ w b x)) (mono one o1 Bs zero w b) hb x)
    QH w b hb (m1 {t = a} {x = x} e r) =
      G⁰.m-next (H⁺ w b x) (cofψ1 u₀ (t₀ ++ a) (cof++1 t₀ a e))
        (λ n → trans (fsnψ1 u₀ (t₀ ++ a) n (cof++1 t₀ a e)) (cong (λ z → replicate n (ψᵉ u₀ z)) (pred++ t₀ a e)))
        (QH w b hb r)
    QH w b hb (mL {t = a} {x = x} e h) =
      mL (cofψω u₀ (t₀ ++ a) (cof++ω t₀ a e))
        (λ n → subst (λ z → M⁰ z (proj₁ (H⁺ w b x))) (sym (trans (fsnψω u₀ (t₀ ++ a) n (cof++ω t₀ a e)) (cong ψ₀ᵗ (fsn++ t₀ a n e))))
          (QH w b hb (h n)))
    QH w b hb (mΩ {t = []} () _ _)
    QH w b hb (mΩ {t = y ∷ ys} {p = inj₂ (tt , inj₁ tt)} {g = g} e refl h) =
      subst (M⁰ (ψ₀ᵗ (t₀ ++ y ∷ ys))) (sym (node1 w b g))
        (mL (cofψΩ u₀ (t₀ ++ y ∷ ys) (cof++Ω t₀ (y ∷ ys) e))
          (λ n → subst (λ z → M⁰ z (proj₁ (limc⁺ (λ m → H⁺ w b (g (vch g m))))))
            (sym (trans (fsnψΩ u₀ (t₀ ++ y ∷ ys) n (cof++Ω t₀ (y ∷ ys) e))
                        (cong ψ₀ᵗ (fsT++ t₀ y ys (γT (t₀ ++ y ∷ ys) [] n)))))
            (G⁰.m-cum (λ m → H⁺ w b (g (vch g m))) (suc n)
              (QH w b hb (h (γT (t₀ ++ y ∷ ys) [] n) (vch g (suc n)) (chain h n))))))
    QH w b hb (mΩ {p = inj₁ ()} _ _ _)
    QH w b hb (mΩ {p = inj₂ (tt , inj₂ ())} _ _ _)
    QH (inc tt v) b hb (mU {t = a} {s = s} {x = x} m ch) =
      subst (λ z → M⁰ (ψ₀ᵗ z) _) (++-assoc t₀ a s) (Qu (proj₂ o1 tt) _ v (H⁺ (inc tt v) b x) (QH (inc tt v) b hb m) ch)
    QH (inu vs) b hb (mU {t = a} {s = s} {x = x} m ch) =
      subst (λ z → M⁰ (ψ₀ᵗ z) _) (++-assoc t₀ a s) (Qu (proj₂ o1 tt) _ (vs tt) (H⁺ (inu vs) b x) (QH (inu vs) b hb m) ch)
    QH w b hb (mw m d) = mw (QH w b hb m) (mono one o1 Bs zero w b d)

    chain : ∀ {y ys} {g : Tr zero → Tr one} → (∀ η c → M⁰ η c → M¹ (fsT (y ∷ ys) η) (g c))
          → ∀ n → M⁰ (γT (t₀ ++ y ∷ ys) [] n) (vch g (suc n))
    chain {g = g} h zero = pos⁰ (Hc (g zero)) (proj₂ (H⁺ (inc tt self) (Bs zero (inc tt self)) (g zero)))
    chain {y} {ys} {g} h (suc n) =
      subst (λ z → M⁰ (ψ₀ᵗ z) (vch g (suc (suc n)))) (sym (fsT++ t₀ y ys (γT (t₀ ++ y ∷ ys) [] n)))
        (QH (inc tt self) (Bs zero (inc tt self)) hb′ (h _ (vch g (suc n)) (chain h n)))
```
