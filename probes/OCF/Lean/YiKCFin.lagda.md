# 候选 A: A1 在 η = 0, 1, 2 处对一切 c 成立 (验收)

> 验收文件 (读记号), 树、折叠、合法性一行不改. 编译定理, 无前提: `a1₀`, `a1₁`, `a1₂`: 对一切满足 `M⁰ η c` 的第 0 层的树 c (η = 0, 1, 2), 孩子 two 的第 1 层底的第 c 支 `g₁ c` 不低于 ψ₁(Ω_η); `YiKVInst.A1-at` 只在 c = η 的三个点上.
> 做法: c = η 处对一切量化域内的底与起点重做 `a1-1`, `a1-2` (`s1`, `s2`), 再沿 `YiKCStep.clos` 上行; c 之下字面地有 1 或 2 (`pos1`, `two⊴`).
> 只到层号 2; 一般的后继情形 `A1S` 未证. 不涉及上界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiKCFin where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiKVPath
open import OCF.Lean.YiKVFold
open import OCF.Lean.YiKVRel
open import OCF.Lean.YiKVCheck using (o¹; h₁; c1; c2; g₁)
open import OCF.Lean.YiKVInst using (module Φm)
open import OCF.Lean.YiKVValue using (Ω₂ᵗ)
open import OCF.Lean.YiCertFold using (Base; B₀)
open import OCF.Lean.YiKCSem using (o2)
open import OCF.Lean.YiKCStep
import OCF.Align.EboLeanDef as E
open E using (cof; cω; γT; natT)
```

## c 之下字面地有 1, 2

```agda
c1≢cω : E.c1 ≡ cω → ⊥
c1≢cω ()

pos1 : ∀ {t c} → M⁰ t c → t ≡ natT 1 → zero ⊢ zero ◃ c
pos1 mz                  ()
pos1 (m1 {x = x} e r)    q    = z◃ x ◃s
pos1 (mL e h)            refl = ⊥-elim (c1≢cω e)
pos1 (mΩ {p = ()} _ _ _) q
pos1 (mU {c = ()} _ _)   q
pos1 (mw {x = x} m d)    q    = z◃ x d

suc-⊴ : {a b : Tr zero} → zero ⊢ a ◃ b → suc a ⊴ b
suc-⊴ ◃s             = ⊴r
suc-⊴ (◃l {a = r} n) = ⊴◃ (⊴-◃ (suc-⊴ (r n)) (◃l (suc n)))
suc-⊴ (◃w {p = ()})
suc-⊴ (◃u _ () _ _)
suc-⊴ (◃c _ () _)
suc-⊴ (◃t d e)       = ⊴◃ (⊴-◃ (suc-⊴ d) e)

lift⊴ : {a x : Tr zero} → a ⊴ x → suc a ⊴ suc x
lift⊴ ⊴r     = ⊴r
lift⊴ (⊴◃ d) = ⊴◃ (⊴-◃ (suc-⊴ d) ◃s)

two⊴ : ∀ {t c} → M⁰ t c → t ≡ natT 2 → c2 ⊴ c
two⊴ mz                  ()
two⊴ (m1 e r)            refl = lift⊴ (suc-⊴ (pos1 r refl))
two⊴ (mL e h)            refl = ⊥-elim (c1≢cω e)
two⊴ (mΩ {p = ()} _ _ _) q
two⊴ (mU {c = ()} _ _)   q
two⊴ (mw m d)            q    = ⊴◃ (⊴-◃ (two⊴ m q) d)

clos⊴ : ∀ {t x x′} → x ⊴ x′ → S t x → S t x′
clos⊴ ⊴r     s = s
clos⊴ (⊴◃ d) s = clos d s

up1 : ∀ {t} → S t c1 → (c : Tr zero) → zero ⊢ zero ◃ c → S t c
up1 s zero            d = ⊥-elim (¬◃z d)
up1 s (suc zero)      d = s
up1 s (suc (suc x))   d = clos ◃s (up1 s (suc x) (z◃ x ◃s))
up1 s (suc (lim f a)) d = clos ◃s (up1 s (lim f a) (z◃ (f zero) (◃l zero)))
up1 s (lim f a)       d with zl (f 1)
... | inj₁ e  = ⊥-elim (¬◃z (subst (λ v → zero ⊢ f 0 ◃ v) (sym e) (a 0)))
... | inj₂ d′ = clos (◃l 1) (up1 s (f 1) d′)
```

## c = 1, 2 处, 对量化域内的一切底与起点

c = 1: Ω₁ 树的槽位在地板上, 保留; 就是 `YiKVInst.Φm.ΦF` 作用在 Ω₁ 树上. c = 2: 结点不保留, 链是源层第 1 层的自身折叠 (起点是源底在第 1 层的分量, 在 Ω₁ 之上), 各项再经 `φ`.

```agda
s1 : S (ψ₁ᵗ Ω₁ᵗ) c1
s1 Bm β ok hβ = Φm.ΦF o2 (B₀ two) Bm β hβ Mβ₀

module Two (Bm : Base two) (β : Tr⁺ one) (ok : OKB Bm) (hβ : M¹ Ω₁ᵗ (proj₁ β)) where
  Bs : Base one
  Bs i u = Bm i (inc tt u)

  b : Tr⁺ one
  b = Bm one (inc tt self)

  hb : M¹ Ω₁ᵗ (proj₁ b)
  hb = G¹.m⊴ Mβ₀ (ok one (inc tt self))

  module PP = PFm [] (proj₂ o2 tt) Bs b hb
  module FF = Φm o2 (B₀ two) Bs β hβ

  zz : ℕ → Tr one
  zz = iter (λ c → proj₁ (next⁺ (PP.F⁺ c))) zero

  form : proj₁ (Φ⁺ c2 Bm β (proj₁ (Ωt two))) ≡ proj₁ (limc⁺ (λ k → next⁺ (FF.Φ⁺ (zz k))))
  form = refl

  sγ : ∀ n → M¹ (γT Ω₂ᵗ u₁ n) (zz (suc n))
  sγ zero    = mw hb (◃l zero)
  sγ (suc n) = mw (PP.PF (sγ n)) (◃l zero)

  res : M¹ (ψ₁ᵗ Ω₂ᵗ) (proj₁ (Φ⁺ c2 Bm β (proj₁ (Ωt two))))
  res = mL refl (λ n → G¹.m-cum (λ k → next⁺ (FF.Φ⁺ (zz k))) (suc n) (mw (FF.ΦF (sγ n)) (◃l zero)))

s2 : S (ψ₁ᵗ Ω₂ᵗ) c2
s2 Bm β ok hβ = Two.res Bm β ok hβ
```

## 对一切 c

```agda
S1 : ∀ {c} → M⁰ (natT 1) c → S (ψ₁ᵗ (E.Ωt (natT 1))) c
S1 {c} l = up1 s1 c (pos1 l refl)

S2 : ∀ {c} → M⁰ (natT 2) c → S (ψ₁ᵗ (E.Ωt (natT 2))) c
S2 l = clos⊴ (two⊴ l refl) s2

a1₀ : (c : Tr zero) → M¹ (ψ₁ᵗ (E.Ωt [])) (proj₁ (g₁ c))
a1₀ c = S0 c (B₀ (h₁ c)) (Ωt one) (λ i u → ⊴r) Mβ₀

a1₁ : ∀ {c} → M⁰ (natT 1) c → M¹ (ψ₁ᵗ (E.Ωt (natT 1))) (proj₁ (g₁ c))
a1₁ {c} l = S1 l (B₀ (h₁ c)) (Ωt one) (λ i u → ⊴r) Mβ₀

a1₂ : ∀ {c} → M⁰ (natT 2) c → M¹ (ψ₁ᵗ (E.Ωt (natT 2))) (proj₁ (g₁ c))
a1₂ {c} l = S2 l (B₀ (h₁ c)) (Ωt one) (λ i u → ⊴r) Mβ₀
```

后继情形 `A1S` 在 η = 1, 2 处的实例 (前提可满足的一部分): 对一切 x.

```agda
a1s-1 : (x : Tr zero) → S (ψ₁ᵗ (E.Ωt (natT 1))) (suc x)
a1s-1 x = up1 s1 (suc x) (z◃ x ◃s)

a1s-2 : ∀ {x} → M⁰ (natT 1) x → S (ψ₁ᵗ (E.Ωt (natT 2))) (suc x)
a1s-2 l = S2 (m1 refl l)
```
