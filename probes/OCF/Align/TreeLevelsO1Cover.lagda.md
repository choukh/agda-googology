# 路线乙 O1：覆盖定理及其非空的生成域版本

**第 4 层；阶段无关的条件定理，不是候选的值验收。** 本篇把交接中的
`Cover` 实验落成模块。另给带生成域的版本：解释可依赖“此项在定义域内”
的证据，不能默认为每个裸记号项都已有解释。`HC` 是沿记号基本列的
可数良基证据；以参照树解释 `HC` 给出整个生成域接口的非空实例。
这个实例读记号且使用参照的良基证明，不进入树侧成品。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeLevelsO1Cover where

open import Data.Nat using (ℕ)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans)
open import OCF.Lean.CRwBase using (Cd; hs)
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; s≤s; l≤; ≤l)
open import OCF.Lean.NegFold1Base using (≤ᵛ-trans; ≤ᵛ-refl)
open import OCF.Align.EboLeanDef
  using (T; cof; pred; fsn; HC; h0; h1; hω; c0; c1; cω; EBOψ)
import OCF.Align.EboLean3Tree as E
open import OCF.Align.TerminalFoldAccept using (read; reference; all-branches)
```

## 裸解释版本：逐字保留交接的两个一步律

```agda
module Cover
  (ι : T → Cd)
  (ι-suc : ∀ t → cof t ≡ c1 → hs (ι (pred t)) ≤ᵛ ι t)
  (ι-lim : ∀ t → cof t ≡ cω → ∀ n → ι (fsn t n) ≤ᵛ ι t)
  where

  cover : ∀ {t} (h : HC t) → read (E.tree h) ≤ᵛ ι t
  cover (h0 _) = z≤
  cover {t} (h1 e h) = ≤ᵛ-trans (s≤s (cover h)) (ι-suc t e)
  cover {t} (hω e h) = l≤ (λ n → ≤ᵛ-trans (cover (h n)) (ι-lim t e n))

  terminal : ∀ {X : Cd} → (∀ k → ι (EBOψ k) ≤ᵛ X) → reference ≤ᵛ X
  terminal up = all-branches
    (λ k → ≤ᵛ-trans (cover (E.hc-tower k)) (up k))
```

## 生成域版本：把解释存在性、一步律、全塔覆盖分别列出

`GeneratedCover` 不要求不可数共尾的裸项也有可数值。参数 `A` 是候选
自身的对象类型，`observe` 是候选自身的可数输出观察。
没有将 `reference ≤ᵛ X` 塞进记录字段。

```agda
record GeneratedCover (A : Set) (observe : A → Cd) : Set₁ where
  field
    Domain : T → Set
    ι : ∀ {t} → Domain t → A
    predecessor : ∀ {t} → Domain t → cof t ≡ c1 → Domain (pred t)
    branch : ∀ {t} → Domain t → cof t ≡ cω → ∀ n → Domain (fsn t n)
    tower : ∀ k → Domain (EBOψ k)
    successor-law : ∀ {t} (d : Domain t) (e : cof t ≡ c1) →
      hs (observe (ι (predecessor d e))) ≤ᵛ observe (ι d)
    limit-law : ∀ {t} (d : Domain t) (e : cof t ≡ cω) n →
      observe (ι (branch d e n)) ≤ᵛ observe (ι d)

module Generated {A : Set} {observe : A → Cd}
  (C : GeneratedCover A observe) where
  open GeneratedCover C

  cover : ∀ {t} (h : HC t) (d : Domain t) → read (E.tree h) ≤ᵛ observe (ι d)
  cover (h0 _) d = z≤
  cover (h1 e h) d = ≤ᵛ-trans
    (s≤s (cover h (predecessor d e))) (successor-law d e)
  cover (hω e h) d = l≤ (λ n → ≤ᵛ-trans
    (cover (h n) (branch d e n)) (limit-law d e n))

  terminal : ∀ {X : Cd} →
    (∀ k → observe (ι (tower k)) ≤ᵛ X) → reference ≤ᵛ X
  terminal up = all-branches
    (λ k → ≤ᵛ-trans (cover (E.hc-tower k) (tower k)) (up k))
```

## 非空实例：同项的不同 HC 证据给互相支配的参照树

这里证的是值关系，不是证明相等或函数相等，不需要 UIP 或函数外延。

```agda
c0≠c1 : c0 ≡ c1 → ⊥
c0≠c1 ()
c0≠cω : c0 ≡ cω → ⊥
c0≠cω ()
c1≠c0 : c1 ≡ c0 → ⊥
c1≠c0 ()
c1≠cω : c1 ≡ cω → ⊥
c1≠cω ()
cω≠c0 : cω ≡ c0 → ⊥
cω≠c0 ()
cω≠c1 : cω ≡ c1 → ⊥
cω≠c1 ()

hc-value : ∀ {t} (h k : HC t) → read (E.tree h) ≤ᵛ read (E.tree k)
hc-value (h0 _) k = z≤
hc-value (h1 e h) (h0 f) = ⊥-elim (c1≠c0 (trans (sym e) f))
hc-value (h1 e h) (h1 f k) = s≤s (hc-value h k)
hc-value (h1 e h) (hω f k) = ⊥-elim (c1≠cω (trans (sym e) f))
hc-value (hω e h) (h0 f) = ⊥-elim (cω≠c0 (trans (sym e) f))
hc-value (hω e h) (h1 f k) = ⊥-elim (cω≠c1 (trans (sym e) f))
hc-value (hω e h) (hω f k) = l≤ (λ n → ≤l n (hc-value (h n) (k n)))

hc-pred : ∀ {t} → HC t → cof t ≡ c1 → HC (pred t)
hc-pred (h0 e) f = ⊥-elim (c0≠c1 (trans (sym e) f))
hc-pred (h1 e h) f = h
hc-pred (hω e h) f = ⊥-elim (cω≠c1 (trans (sym e) f))

hc-branch : ∀ {t} → HC t → cof t ≡ cω → ∀ n → HC (fsn t n)
hc-branch (h0 e) f n = ⊥-elim (c0≠cω (trans (sym e) f))
hc-branch (h1 e h) f n = ⊥-elim (c1≠cω (trans (sym e) f))
hc-branch (hω e h) f n = h n

reference-cover : GeneratedCover Cd (λ x → x)
reference-cover = record
  { Domain = HC
  ; ι = λ h → read (E.tree h)
  ; predecessor = hc-pred
  ; branch = hc-branch
  ; tower = E.hc-tower
  ; successor-law = λ d e → hc-value (h1 e (hc-pred d e)) d
  ; limit-law = λ d e n → ≤ᵛ-trans
      (≤l n (≤ᵛ-refl (read (E.tree (hc-branch d e n)))))
      (hc-value (hω e (hc-branch d e)) d)
  }
```

**范围。** 已填实例说明生成域接口可满足，不说明现有候选满足它。
裸解释版的 `T → Cd` 仍待候选定义；生成域版没有冒称已经交出了这个裸解释。
每个候选还须给出真实解释、相应的一步律，以及所有 Ω 塔的共同值上界。
