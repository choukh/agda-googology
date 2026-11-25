# 换基替身对偏移的单调: 承载谓词沿字面路径上行

> 判决: 编译定理, 无前提, 不读记号. 目标层 j 与谓词 P (起点), Q (输出; 对 `◃` 向上封闭, 对左加封闭) 任意: 偏移 u 上 "Ω 树朝 j 沿 `lift` 的折叠对一切底与起点落在 Q" (`Car u`) 沿不含 Ω 形状的字面路径 u ⊑ u′ 上行 (`liftS`, `liftL`, `mono-path`); 所以 `seen` 在 c 处承载 d ◃ c 的 d 处承载的 (`seen◃`), 也承载自身折叠承载的 (`seen-self`).
> 不给出什么: 不构造 Q; 后继一步的参照提升不在这里 (见 [YiSVStep](YiSVStep.lagda.md)); 偏移含 Ω 形状时没有做.
> 来源: `liftS`, `liftL` 与 `YiLTLift.upS`, `upL` 同形 (那里目标是第 0 层, 关系是具体的 `M⁰`, 折叠是比较表折叠); `⊴` 一组照 `YiKVRel`, `NoΩ`, `noΩ-↑` 照 `YiRKCell`, `one⊑` 的递归照 `YiKVRel.pos⁰`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSVMono where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
import OCF.Lean.YiRBSib as R
open import OCF.Lean.YiBSBase using (Schema; schema; seen; raiseO; floor; offsets; ok-offsets)

infix 4 _⊴_
data _⊴_ {ℓ : L} (x : Tr ℓ) : Tr ℓ → Set where
  ⊴r : x ⊴ x
  ⊴◃ : ∀ {y} → ℓ ⊢ x ◃ y → x ⊴ y

⊴-◃ : ∀ {ℓ} {a b c : Tr ℓ} → a ⊴ b → ℓ ⊢ b ◃ c → ℓ ⊢ a ◃ c
⊴-◃ ⊴r     e = e
⊴-◃ (⊴◃ d) e = ◃t d e

⊴-trans : ∀ {ℓ} {a b c : Tr ℓ} → a ⊴ b → b ⊴ c → a ⊴ c
⊴-trans p ⊴r     = p
⊴-trans p (⊴◃ e) = ⊴◃ (⊴-◃ p e)

+⊴ : ∀ {ℓ} (b y : Tr ℓ) → b ⊴ b + y
+⊴ b zero         = ⊴r
+⊴ b (suc y)      = ⊴◃ (⊴-◃ (+⊴ b y) ◃s)
+⊴ b (lim f a)    = ⊴◃ (⊴-◃ (+⊴ b (f zero)) (◃l zero))
+⊴ b (Ω p g)      = ⊴◃ (⊴-◃ (+⊴ b (g _)) ◃w)
+⊴ b (up y c w e) = ⊴◃ (⊴-◃ (+⊴ b y) (◃u (b + y) c w e))

ψ-⊵ : (ℓ : L) (o : Ok ℓ) (r : R.Rb ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr⁺ j) (x : Tr ℓ)
    → proj₁ β ⊴ proj₁ (R.ψ ℓ o r B j w β x)
ψ-⊵ ℓ o r B j w β x with zl x
... | inj₁ refl = ⊴r
... | inj₂ d    = ⊴◃ (R.mono ℓ o r B j w β d)

OKB : ∀ {ℓ} → Base ℓ → Set
OKB {ℓ} B = (i : L) (u : i ≤ ℓ) → proj₁ (Ωt i) ⊴ proj₁ (B i u)

NoΩ : L → Set
NoΩ zero          = ⊤
NoΩ (nd sS h)     = NoΩ (h tt)
NoΩ (nd sL h)     = (n : ℕ) → NoΩ (h n)
NoΩ (nd (sΩ _) _) = ⊥

noΩ-ch : ∀ s h (c : Ch s) → NoΩ (nd s h) → NoΩ (h c)
noΩ-ch sS h tt n = n
noΩ-ch sL h c  n = n c
noΩ-ch (sΩ _) h c ()

noΩ-↑ : (c : Tr zero) → NoΩ (↑ zero c)
noΩ-↑ zero      = tt
noΩ-↑ (suc c)   = noΩ-↑ c
noΩ-↑ (lim f a) = λ n → noΩ-↑ (f n)

z⊑ : (u : L) → NoΩ u → zero ⊑ u
z⊑ zero          n = self
z⊑ (nd sS h)     n = inc tt (z⊑ (h tt) n)
z⊑ (nd sL h)     n = inc zero (z⊑ (h zero) (n zero))
z⊑ (nd (sΩ _) _) ()
```

## 承载谓词与上行

`Car u` 对层号证据 (形如 `Ok⊕`), 换基证据, 底 (只要不低于各层的 Ω 树), 起点 (只要满足 P) 都量化; 上行时孩子层的底与起点会换, 所以不能固定. 后继形状用回灌链的第 1 项, ℕ 极限形状用第 n 个部分和的末项.

```agda
Sᶻ : Schema zero (λ c → zero ⊕ ↑ zero c)
Sᶻ = schema zero (↑ zero) tt self (OkO↑ zero zero tt self) (λ c → refl)

module Mono (j : L) (oj : Ok j) (P Q : Tr j → Set)
  (P↑ : ∀ {x y} → P x → j ⊢ x ◃ y → P y)
  (Q↑ : ∀ {x y} → Q x → j ⊢ x ◃ y → Q y)
  (Q+ : ∀ (a : Tr j) {y} → Q y → Q (a + y)) where

  P⊴ : ∀ {x y} → P x → x ⊴ y → P y
  P⊴ p ⊴r     = p
  P⊴ p (⊴◃ d) = P↑ p d

  Q⊴ : ∀ {x y} → Q x → x ⊴ y → Q y
  Q⊴ p ⊴r     = p
  Q⊴ p (⊴◃ d) = Q↑ p d

  Car : L → Set
  Car u = (ob : OkO j u) (r : R.Rb (j ⊕ u)) (B : Base (j ⊕ u)) (β : Tr⁺ j) → OKB B → P (proj₁ β)
        → Q (proj₁ (R.ψ (j ⊕ u) (Ok⊕ j u oj ob) r B j (lift j u) β (proj₁ (Ωt (j ⊕ u)))))

  liftS : (h : ⊤ → L) → Car (h tt) → Car (nd sS h)
  liftS h car ob r B β ok hβ =
    Q↑ (Q+ _ (Q↑ (Q↑ (car (proj₂ ob tt) (proj₂ r tt) (λ i u → B i (inc tt u)) β (λ i u → ok i (inc tt u)) hβ)
                      (R.mono (j ⊕ h tt) (Ok⊕ j (h tt) oj (proj₂ ob tt)) (proj₂ r tt) (λ i u → B i (inc tt u)) j (lift j (h tt)) β
                        (⊴-◃ (ok (j ⊕ h tt) (inc tt self)) (◃l zero))))
                  (◃l zero)))
       (◃l 1)

  module _ (g : ℕ → L) (n : ℕ) (car : Car (g n)) (ob : OkO j (nd sL g)) (r : R.Rb (j ⊕ nd sL g)) (B : Base (j ⊕ nd sL g))
           (β : Tr⁺ j) (ok : OKB B) (hβ : P (proj₁ β)) where
    private
      ℓ : L
      ℓ = j ⊕ nd sL g
      O : Ok ℓ
      O = Ok⊕ j (nd sL g) oj ob
      w : j ≤ ℓ
      w = lift j (nd sL g)

      upQ : (x : Tr ℓ) → Q (proj₁ (R.ψ ℓ O r B j w β (up x n (proj₁ (Ωt (j ⊕ g n))) (proj₂ (Ωt (j ⊕ g n))))))
      upQ x = car (proj₂ ob n) (proj₂ r n) (λ i u → R.ψ ℓ O r B i (inc n u) (B i (inc n u)) x) (R.ψ ℓ O r B j w β x)
                  (λ i u → ⊴-trans (ok i (inc n u)) (ψ-⊵ ℓ O r B i (inc n u) (B i (inc n u)) x))
                  (P⊴ hβ (ψ-⊵ ℓ O r B j w β x))

      F : ℕ → Tr ℓ
      F k = proj₁ (upz {sL} {λ c → j ⊕ g c} k (Ωt (j ⊕ g k)))

    liftL′ : (m : ℕ) → m ≡ n → Q (proj₁ (R.ψ ℓ O r B j w β (cum F m)))
    liftL′ zero    refl = upQ zero
    liftL′ (suc m) refl = upQ (cum F m)

    liftL″ : Q (proj₁ (R.ψ ℓ O r B j w β (proj₁ (Ωt ℓ))))
    liftL″ = Q↑ (liftL′ n refl) (◃l n)

  liftL : (g : ℕ → L) (n : ℕ) → Car (g n) → Car (nd sL g)
  liftL g n car ob r B β ok hβ = liftL″ g n car ob r B β ok hβ

  step : ∀ s h (c : Ch s) → NoΩ (nd s h) → Car (h c) → Car (nd s h)
  step sS     h tt n  = liftS h
  step sL     h c  n  = liftL h c
  step (sΩ _) h c  ()

  mono-path : ∀ {u u′} → u ⊑ u′ → NoΩ u′ → Car u → Car u′
  mono-path self n car = car
  mono-path {u′ = nd s h} (inc c v) n car = step s h c n (mono-path v (noΩ-ch s h c n) car)
  mono-path {u′ = nd s h} (inu vs)  n car = step s h (c₀ s) n (mono-path (vs (c₀ s)) (noΩ-ch s h (c₀ s) n) car)

  seen-car : ∀ {k h} (S : Schema k h) (u : floor S ≤ j) (β : Tr⁺ j) (c : Tr k)
           → Car (offsets S c) → P (proj₁ β) → Q (proj₁ (seen S j oj u β c))
  seen-car S u β c car hβ = car _ (R.rb-no _) (B₀ _) β (λ i u′ → ⊴r) hβ

  seen-mono : ∀ {k h} (S : Schema k h) (u : floor S ≤ j) (β : Tr⁺ j) {c′ c : Tr k}
            → offsets S c′ ⊑ offsets S c → NoΩ (offsets S c)
            → Car (offsets S c′) → P (proj₁ β) → Q (proj₁ (seen S j oj u β c))
  seen-mono S u β {c = c} v n car = seen-car S u β c (mono-path v n car)

  seen◃ : (u : zero ≤ j) (β : Tr⁺ j) {d c : Tr zero} → zero ⊢ d ◃ c
        → Car (↑ zero d) → P (proj₁ β) → Q (proj₁ (seen Sᶻ j oj u β c))
  seen◃ u β {c = c} e = seen-mono Sᶻ u β (◃→⊑ zero e) (noΩ-↑ c)

  seen-self : (c : Tr zero) (u : zero ≤ j) (β : Tr⁺ j) → Car zero → P (proj₁ β) → Q (proj₁ (seen Sᶻ j oj u β c))
  seen-self c u β = seen-mono Sᶻ u β {c′ = zero} {c = c} (z⊑ (↑ zero c) (noΩ-↑ c)) (noΩ-↑ c)
```

## 第 0 层的非零树在 1 之上

```agda
¬◃z : ∀ {ℓ} {x : Tr ℓ} → ℓ ⊢ x ◃ zero → ⊥
¬◃z (◃t d e) = ¬◃z e

one⊑ : (c : Tr zero) → zero ⊢ zero ◃ c → ↑ zero (suc zero) ⊑ ↑ zero c
one⊑ zero d = ⊥-elim (¬◃z d)
one⊑ (suc y) d with zl y
... | inj₁ refl = self
... | inj₂ d′   = inc tt (one⊑ y d′)
one⊑ (lim f a) d with zl (f 1)
... | inj₁ e  = ⊥-elim (¬◃z (subst (λ v → zero ⊢ f 0 ◃ v) (sym e) (a 0)))
... | inj₂ d′ = inc 1 (one⊑ (f 1) d′)
one⊑ (Ω () _)      d
one⊑ (up _ () _ _) d
```
