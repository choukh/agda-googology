# 验收 (换基): 判据在 η = 1 处的否定

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 编译的否定定理, 无前提: `negˢ : CritAt gˢ 1 → ⊥`, `negᵗ : CritAt gᵗ 1 → ⊥` (`YiRBCrit.CritAt`: 塔第 1 项的 Ω 树第 `nat 1` 支朝第 2 层的那一行对着 ψ₂(Ω₁), 关系 `YiCLFam.M 2`), 两种换基都是.
> 机制: ψ₂(Ω₁) 的余尾是 `cΩ []`, 关系里只有槽位在第 0 层的 Ω 结点 (`mΩ`) 或松弛 (`mw`) 能给出它; 谓词 `Q` (第一位置之下没有这样的结点) 沿 `◃` 向下封闭, 对第 2 层的自身折叠, 上折, 加法, `next⁺` 封闭, 那一支满足 `Q`. 否定的对象是规范实例 (标准底, 起点 Ω₂ 树).
> 否定的是 "用不带项序封闭的关系 `M 2` 陈述 η = 1 处的判据", 不否定两种换基, 不否定值 (那一支对着 ψ₂(Ω₃), `YiRBCrit.sib-shift`). η = ω 处只有归约 `noω`: 满足 `Q` 的树不对着 ψ₂(Ω_ω) (实例 `noω-Ω₂`); c = ω 那一支是否满足 `Q` 未证, 所以 η = ω 处的判据未证也未否定.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiRLNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiRBSib
open import OCF.Lean.YiRBCrit using (two; h₁; o2; CritAt; gˢ; gᵗ)
open import OCF.Lean.YiKVRel using (M⁰; mz; m1; mL; mΩ; mU; mw)
import OCF.Align.EboLeanDef as E
open E using (cof; Cof; c1; cω; cΩ; natT)
open import OCF.Lean.YiANFam using (ψᴺ; Ωᴺ)
open import OCF.Lean.YiCLFam using (nat; fn; M)
open import OCF.Lean.YiCLPhi using (ωᵀ)
open import OCF.Lean.YiRLCrit using (fsnω)
```

## 谓词

`Q₁`: 第 1 层的树, 第一位置之下没有 Ω 结点. `Q`: 第 2 层的树, 第一位置之下的 Ω 结点槽位都在第 1 层, 嵌入的孩子满足 `Q₁`.

```agda
Q₁ : Tr (fn 1) → Set
Q₁ zero         = ⊤
Q₁ (suc y)      = Q₁ y
Q₁ (lim f a)    = (n : ℕ) → Q₁ (f n)
Q₁ (Ω p g)      = ⊥
Q₁ (up y c w e) = Q₁ y

Q : Tr two → Set
Q zero                          = ⊤
Q (suc x)                       = Q x
Q (lim f a)                     = (n : ℕ) → Q (f n)
Q (Ω (inj₁ ()) g)
Q (Ω (inj₂ (tt , inj₁ tt)) g)   = Q (g zero)
Q (Ω (inj₂ (tt , inj₂ _)) g)    = ⊥
Q (up x c y e)                  = Q x × Q₁ y

Q₁↓ : ∀ {y′ y} → fn 1 ⊢ y′ ◃ y → Q₁ y → Q₁ y′
Q₁↓ ◃s           q = q
Q₁↓ (◃l n)       q = q n
Q₁↓ ◃w           ()
Q₁↓ (◃u x c y e) q = q
Q₁↓ (◃c x c d)   q = q
Q₁↓ (◃t d e)     q = Q₁↓ d (Q₁↓ e q)

Q↓ : ∀ {x′ x} → two ⊢ x′ ◃ x → Q x → Q x′
Q↓ ◃s                               q         = q
Q↓ (◃l n)                           q         = q n
Q↓ (◃w {p = inj₁ ()})
Q↓ (◃w {p = inj₂ (tt , inj₁ tt)})   q         = q
Q↓ (◃w {p = inj₂ (tt , inj₂ _)})    ()
Q↓ (◃u x c y e)                     (qx , _)  = qx
Q↓ (◃c x c d)                       (qx , qy) = qx , Q₁↓ d qy
Q↓ (◃t d e)                         q         = Q↓ d (Q↓ e q)
```

## 满足谓词的树不对着 ψ₂(Ω₁)

```agda
t₁ : E.T
t₁ = ψᴺ 2 (Ωᴺ 1)

private
  unΩ : Cof → E.T
  unΩ (cΩ ν) = ν
  unΩ _      = []

  c1≢ : cΩ [] ≡ c1 → ⊥
  c1≢ ()

  cω≢ : cΩ [] ≡ cω → ⊥
  cω≢ ()

  nil≢ : [] ≡ natT 1 → ⊥
  nil≢ ()

  split1 : (t s : E.T) {p : E.PT} → t ++ s ≡ p ∷ [] → (t ≡ p ∷ []) ⊎ (s ≡ p ∷ [])
  split1 []          s       q = inj₂ q
  split1 (a ∷ [])    []      q = inj₁ q
  split1 (a ∷ [])    (b ∷ s) ()
  split1 (a ∷ b ∷ t) s       ()

no⁰ : ∀ {t y} → M⁰ t y → t ≡ t₁ → ⊥
no⁰ mz                  ()
no⁰ (m1 e r)            refl = c1≢ e
no⁰ (mL e h)            refl = cω≢ e
no⁰ (mΩ {p = ()} _ _ _)
no⁰ (mU {c = ()} _ _)
no⁰ (mw m d)            q    = no⁰ m q

no¹ : ∀ {t y} → M 1 t y → t ≡ t₁ → Q₁ y → ⊥
no¹ mz                        ()   _
no¹ (m1 e r)                  refl _  = c1≢ e
no¹ (mL e h)                  refl _  = cω≢ e
no¹ (mΩ _ _ _)                _    ()
no¹ (mU {t = t} {s = s} m ch) q    qx with split1 t s q
... | inj₁ qt = no¹ m qt qx
... | inj₂ qs = no⁰ ch qs
no¹ (mw m d)                  q    qy = no¹ m q (Q₁↓ d qy)

no² : ∀ {t x} → M 2 t x → t ≡ t₁ → Q x → ⊥
no² mz                                      ()   _
no² (m1 e r)                                refl _         = c1≢ e
no² (mL e h)                                refl _         = cω≢ e
no² (mΩ {p = inj₁ ()} _ _ _)
no² (mΩ {p = inj₂ (tt , inj₁ tt)} e nu h)   refl _         = nil≢ (trans (cong unΩ e) nu)
no² (mΩ {p = inj₂ (tt , inj₂ _)} _ _ _)     _    ()
no² (mU {t = t} {s = s} m ch)               q    (qx , qy) with split1 t s q
... | inj₁ qt = no² m qt qx
... | inj₂ qs = no¹ ch qs qy
no² (mw m d)                                q    qx        = no² m q (Q↓ d qx)
```

## 谓词对运算封闭

```agda
Q+ : ∀ {b} → Q b → (y : Tr two) → Q y → Q (b + y)
Q+ qb zero                          _         = qb
Q+ qb (suc y)                       qy        = Q+ qb y qy
Q+ qb (lim f a)                     qy        = λ n → Q+ qb (f n) (qy n)
Q+ qb (Ω (inj₁ ()) g)
Q+ qb (Ω (inj₂ (tt , inj₁ tt)) g)   qy        = Q+ qb (g zero) qy
Q+ qb (Ω (inj₂ (tt , inj₂ _)) g)    ()
Q+ qb (up y c w e)                  (qx , qw) = Q+ qb y qx , qw

Qit : ∀ {b} → Q b → ∀ n → Q (iter (b +_) b n)
Qit      qb zero    = qb
Qit {b} qb (suc n) = Q+ qb (iter (b +_) b n) (Qit qb n)

Qnext : (b : Tr⁺ two) → Q (proj₁ b) → Q (proj₁ (next⁺ b))
Qnext b qb = Qit qb

Qcum : (F : ℕ → Tr two) → (∀ n → Q (F n)) → ∀ n → Q (cum F n)
Qcum F q zero    = q 0
Qcum F q (suc n) = Q+ (Qcum F q n) (F (suc n)) (q (suc n))

Qι : (y : Tr zero) → Q (ι two y)
Qι zero          = tt
Qι (suc y)       = Qι y
Qι (lim f a)     = λ n → Qι (f n)
Qι (Ω () _)
Qι (up _ () _ _)

QUp0 : (d : Dn two zero) (b : Tr⁺ two) → Q (proj₁ b) → (w : Tr zero) → Q (proj₁ (Up zero d b w))
QUp0 d b qb zero          = qb
QUp0 d b qb (suc w)       = Qnext (Up zero d b w) (QUp0 d b qb w)
QUp0 d b qb (lim f a)     = λ n → QUp0 d b qb (f n)
QUp0 d b qb (Ω () _)
QUp0 d b qb (up _ () _ _)

QUp1 : (b : Tr⁺ two) → Q (proj₁ b) → (y : Tr (fn 1)) → Q₁ y → Q (proj₁ (Up (fn 1) (down stop tt) b y))
QUp1 b qb zero          _  = qb
QUp1 b qb (suc y)       qy = Qnext (Up (fn 1) (down stop tt) b y) (QUp1 b qb y qy)
QUp1 b qb (lim f a)     qy = λ n → QUp1 b qb (f n) (qy n)
QUp1 b qb (Ω p g)       ()
QUp1 b qb (up y tt w e) qy = QUp0 (down (down stop tt) tt) (Up (fn 1) (down stop tt) b y) (QUp1 b qb y qy) w
```

## 第 2 层的自身折叠, 层号 3 的 Ω 树朝第 2 层的折叠

```agda
QF : (o : Ok two) (r : Rb two) (B : Base two) (β : Tr⁺ two) → Q (proj₁ β)
   → (z : Tr two) → Q z → Q (proj₁ (ψ two o r B two self β z))
QF o r B β qβ zero                          _         = qβ
QF o r B β qβ (suc z)                       qz        = Qnext (ψ two o r B two self β z) (QF o r B β qβ z qz)
QF o r B β qβ (lim f a)                     qz        = λ n → QF o r B β qβ (f n) (qz n)
QF o r B β qβ (Ω (inj₁ ()) g)
QF o r B β qβ (Ω (inj₂ (tt , inj₁ tt)) g)   qz        = QF o r B β qβ (g zero) qz
QF o r B β qβ (Ω (inj₂ (tt , inj₂ _)) g)    ()
QF o r B β qβ (up x tt y e)                 (qx , qy) = QUp1 (ψ two o r B two self β x) (QF o r B β qβ x qx) y qy

three : L
three = nd sS (λ _ → two)

module _ (o : Ok three) (r : Rb three) (B : Base three) (β : Tr⁺ two) (qβ : Q (proj₁ β)) (qb : Q (proj₁ (B two (inc tt self)))) where
  private
    B′ : Base two
    B′ i u = B i (inc tt u)

    zk : ℕ → Tr two
    zk = iter (λ z → proj₁ (next⁺ (ψ two (proj₂ o tt) (proj₂ r tt) B′ two self (B two (inc tt self)) z))) zero

    Fk : ℕ → Tr⁺ two
    Fk k = next⁺ (ψ two (proj₂ o tt) (proj₂ r tt) B′ two self β (zk k))

    qz : ∀ k → Q (zk k)
    qz zero    = tt
    qz (suc k) = Qnext (ψ two (proj₂ o tt) (proj₂ r tt) B′ two self (B two (inc tt self)) (zk k))
                       (QF (proj₂ o tt) (proj₂ r tt) B′ (B two (inc tt self)) qb (zk k) (qz k))

    core : Q (proj₁ (limc⁺ Fk))
    core = Qcum (λ k → proj₁ (Fk k))
      (λ k → Qnext (ψ two (proj₂ o tt) (proj₂ r tt) B′ two self β (zk k)) (QF (proj₂ o tt) (proj₂ r tt) B′ β qβ (zk k) (qz k)))

  QcoreC : Q (proj₁ (ψ three o r B two (inc tt self) β (proj₁ (Ωt three))))
  QcoreC = core

  QcoreU : Q (proj₁ (ψ three o r B two (inu (λ _ → self)) β (proj₁ (Ωt three))))
  QcoreU = core
```

## 否定

```agda
qΩ : Q (proj₁ (Ωt two))
qΩ = tt , tt

tail₁ : Tr zero
tail₁ = proj₁ (ψ₀ʳ (h₁ (nat 1)) (proj₂ (Ok-tw 1) (nat 1)) (rb-no _) (proj₁ (Ωt (h₁ (nat 1)))))

negˢ : CritAt gˢ 1 → ⊥
negˢ m = no² m refl
  (Q+ (QcoreC (proj₂ (Ok-tw 1) (nat 3)) (rb-no _) (B₀ _) (Ωt two) qΩ qΩ) (ι two tail₁) (Qι tail₁))

negᵗ : CritAt gᵗ 1 → ⊥
negᵗ m = no² m refl
  (Q+ (QcoreU (Ok⊕ two (↑ zero (nat 1)) o2 (OkO↑ two zero tt (z≤ two) (nat 1))) (rb-no _) (B₀ _) (Ωt two) qΩ qΩ)
      (ι two tail₁) (Qι tail₁))
```

## η = ω 处的归约

ψ₂(Ω_ω) 的余尾是 ω, 基本列第 1 项是 ψ₂(Ω₁) (`YiRLCrit.fsnω`); 所以满足 `Q` 的树也不对着 ψ₂(Ω_ω). 前提可满足: Ω₂ 树 (`noω-Ω₂`).

```agda
tω : E.T
tω = ψᴺ 2 (E.Ωt ωᵀ)

private
  ω1≢ : cω ≡ c1 → ⊥
  ω1≢ ()

  ωΩ≢ : ∀ {ν} → cω ≡ cΩ ν → ⊥
  ωΩ≢ ()

no⁰ω : ∀ {t y} → M⁰ t y → t ≡ tω → ⊥
no⁰ω mz                  ()
no⁰ω (m1 e r)            refl = ω1≢ e
no⁰ω (mL e h)            refl = no⁰ (h 1) (fsnω 1)
no⁰ω (mΩ {p = ()} _ _ _)
no⁰ω (mU {c = ()} _ _)
no⁰ω (mw m d)            q    = no⁰ω m q

no¹ω : ∀ {t y} → M 1 t y → t ≡ tω → Q₁ y → ⊥
no¹ω mz                        ()   _
no¹ω (m1 e r)                  refl _  = ω1≢ e
no¹ω (mL e h)                  refl qy = no¹ (h 1) (fsnω 1) qy
no¹ω (mΩ _ _ _)                _    ()
no¹ω (mU {t = t} {s = s} m ch) q    qx with split1 t s q
... | inj₁ qt = no¹ω m qt qx
... | inj₂ qs = no⁰ω ch qs
no¹ω (mw m d)                  q    qy = no¹ω m q (Q₁↓ d qy)

noω : ∀ {t x} → M 2 t x → t ≡ tω → Q x → ⊥
noω mz                                      ()   _
noω (m1 e r)                                refl _         = ω1≢ e
noω (mL e h)                                refl qx        = no² (h 1) (fsnω 1) qx
noω (mΩ {p = inj₁ ()} _ _ _)
noω (mΩ {p = inj₂ (tt , inj₁ tt)} e nu h)   refl _         = ωΩ≢ e
noω (mΩ {p = inj₂ (tt , inj₂ _)} _ _ _)     _    ()
noω (mU {t = t} {s = s} m ch)               q    (qx , qy) with split1 t s q
... | inj₁ qt = noω m qt qx
... | inj₂ qs = no¹ω ch qs qy
noω (mw m d)                                q    qx        = noω m q (Q↓ d qx)

noω-Ω₂ : M 2 tω (proj₁ (Ωt two)) → ⊥
noω-Ω₂ m = noω m refl qΩ
```
