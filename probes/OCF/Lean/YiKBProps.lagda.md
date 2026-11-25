# YiKB 折叠的便宜性质

> 空白页独立样本 (只导入标准库与 YiKB). 编译定理: 一步坍缩严格高于累加器 (`infl-s`, `infl-sp`), 闭项非零 (`nz-tw`, `nz-EBO`), 沿 View 的直接前驱单调 (`g-suc`, `g-lim`, `g-low`, `g-top`), 嵌入的分支域一致 (`dom-lift`).
> 诊断 (编译定理): 上确界结点 `ℓ` 上方一层的顶坍缩到 `ℓ` 后, 叶只有各孩子的顶 (`restart`); 它说明本设计在上确界结点里没有 "孩子位置上的全值分支".
> 不否定什么; `≼ᵗ` 是同一类型内的结构序, 不是值序; 对任意两棵树的单调性没有证, 也没有否定.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiKBProps where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiKBBlock
open import OCF.Lean.YiKBFold
```

## 结构序

同位置的分支逐点比较, 叶只与自己比较.

```agda
infix 4 _≼ᵗ_
data _≼ᵗ_ {P : Set} {D : P → Set} {F : Set} : Tr P D F → Tr P D F → Set where
  z≼  : ∀ {b} → zero ≼ᵗ b
  s≼s : ∀ {a b} → a ≼ᵗ b → suc a ≼ᵗ suc b
  ≼l  : ∀ {a f} n → a ≼ᵗ f n → a ≼ᵗ lim f
  l≼  : ∀ {f b} → (∀ n → f n ≼ᵗ b) → lim f ≼ᵗ b
  ≼b  : ∀ {a p h} x → a ≼ᵗ h x → a ≼ᵗ br p h
  b≼b : ∀ {p h h′} → (∀ x → h x ≼ᵗ h′ x) → br p h ≼ᵗ br p h′
  f≼f : ∀ {u} → lf u ≼ᵗ lf u

rfl : ∀ {P D F} (t : Tr P D F) → t ≼ᵗ t
rfl zero     = z≼
rfl (suc t)  = s≼s (rfl t)
rfl (lim f)  = l≼ (λ n → ≼l n (rfl (f n)))
rfl (br p h) = b≼b (λ x → rfl (h x))
rfl (lf u)   = f≼f

NZ : ∀ {P D F} → Tr P D F → Set
NZ t = Σ _ (λ a → suc a ≼ᵗ t)
```

## 输出严格高于累加器

每个分支域都有元素 (`dz`), 所以保留的分支下也能给出见证.

```agda
dz : (ℓ : L) (p : Pos ℓ) → Dom ℓ p
dz (s ℓ)        top     = zero
dz (s ℓ)        (low p) = dz ℓ p
dz (sp b i g w) top     = zero
dz (sp b i g w) (low p) = dz b p

inflG : ∀ {P F F′} {D : P → Set} (k : Tr P D F′ → F → Tr P D F′) →
        (∀ a u → suc a ≼ᵗ k a u) → (∀ p → D p) →
        ∀ acc t → suc acc ≼ᵗ gstep k acc t
inflG k ki d acc zero           = s≼s (rfl acc)
inflG k ki d acc (suc t)        = ≼l 1 (inflG k ki d acc t)
inflG k ki d acc (lim f)        = ≼l 0 (inflG k ki d acc (f 0))
inflG k ki d acc (br top h)     = ≼l 1 (inflG k ki d acc (h acc))
inflG k ki d acc (br (low p) h) = ≼b (d p) (inflG k ki d acc (h (d p)))
inflG k ki d acc (lf u)         = ki acc u

inflE : ∀ {a b} (e : a ≤ˢ b) (acc : T b) (t : T a) → suc acc ≼ᵗ E e acc t
inflE e acc zero     = s≼s (rfl acc)
inflE e acc (suc t)  = ≼l 1 (inflE e acc t)
inflE e acc (lim f)  = ≼l 0 (inflE e acc (f 0))
inflE {b = b} e acc (br p h) = ≼b (dz b (lift e p)) (inflE e acc (h (coe e p (dz b (lift e p)))))
inflE {a = s a}        e acc (lf t) = inflE (pre e) acc t
inflE {a = sp _ _ _ _} e acc (lf _) = s≼s (rfl acc)

infl-s : ∀ ℓ acc t → suc acc ≼ᵗ step (s ℓ) acc t
infl-s ℓ = inflG (E rf′) (inflE rf′) (dz ℓ)

infl-leaf : ∀ b i g w acc u → suc acc ≼ᵗ leafsp b i g w acc u
infl-leaf b i g w acc (pk x t) = ≼l 0 (rfl (suc acc))

infl-sp : ∀ b i g w acc t → suc acc ≼ᵗ step (sp b i g w) acc t
infl-sp b i g w = inflG (leafsp b i g w) (infl-leaf b i g w) (dz b)
```

## 闭项非零

```agda
nz-down : ∀ ℓ (e : ℓ ↘ z) (t : T ℓ) → NZ t → NZ (down ℓ e t)
nz-down ℓ rf t n = n
nz-down (s ℓ) (ss e) t _ = nz-down ℓ e _ (Ωtop ℓ , infl-s ℓ (Ωtop ℓ) t)
nz-down (sp b i g w) (sb e) t _ = nz-down b e _ (Ωtop b , infl-sp b i g w (Ωtop b) t)

nz-tw : ∀ n → NZ (twᶜ n)
nz-tw zero    = zero , rfl (suc zero)
nz-tw (suc n) = nz-down (tw n) (tw↘ n) _
  (Ωtop (tw n) , infl-sp (tw n) iΩ lev (lv↘ rf′) (Ωtop (tw n)) (Ωtop (tw (suc n))))

nz-EBO : NZ EBOᶜ
nz-EBO = Ωtop z , infl-sp z iℕ tw tw↘ (Ωtop z) (Ωtop Λ)
```

## 沿 View 的直接前驱单调

后继的前驱, 极限的第 n 项, 保留分支的第 x 支, 顶分支在回灌点上的支: 它们的坍缩都不高于整体的坍缩. 顶分支在任意点上的支没有这样的陈述.

```agda
module _ {P F F′ : Set} {D : P → Set} (k : Tr P D F′ → F → Tr P D F′) (acc : Tr P D F′) where
  g-suc : ∀ t → gstep k acc t ≼ᵗ gstep k acc (suc t)
  g-suc t = ≼l 1 (rfl _)

  g-lim : ∀ f n → gstep k acc (f n) ≼ᵗ gstep k acc (lim f)
  g-lim f n = ≼l n (rfl _)

  g-low : ∀ p h x → gstep k acc (h x) ≼ᵗ gstep k acc (br (low p) h)
  g-low p h x = ≼b x (rfl _)

  g-top : ∀ h n → gstep k acc (h (iter (λ x → gstep k acc (h x)) n acc)) ≼ᵗ gstep k acc (br top h)
  g-top h n = ≼l (suc n) (rfl _)
```

## 嵌入一致

位置沿后继链搬上去以后, 分支域是同一个类型.

```agda
dom-lift : ∀ {a b} (e : a ≤ˢ b) (p : Pos a) → Dom b (lift e p) ≡ Dom a p
dom-lift rf′     p = refl
dom-lift (ss′ e) p = dom-lift e p
```

## 诊断: 上确界结点上方一层的顶

`Cl S t`: `t` 由零, 后继, 极限, 分支与满足 `S` 的叶组成. `restart`: 对任意上确界结点 `ℓ`, `Ωtop (s ℓ)` 坍缩到 `ℓ` 的结果里, 叶都是某个孩子的顶. 白话: 这一步没有造出 "ω 的 (孩子里的树) 次幂" 这样的新叶, 因为 `E` 在上确界结点的叶上只记 `suc acc`.

```agda
data Cl {P : Set} {D : P → Set} {F : Set} (S : F → Set) : Tr P D F → Set where
  cz : Cl S zero
  cs : ∀ {t} → Cl S t → Cl S (suc t)
  cl : ∀ {f} → (∀ n → Cl S (f n)) → Cl S (lim f)
  cb : ∀ {p h} → (∀ x → Cl S (h x)) → Cl S (br p h)
  cf : ∀ {u} → S u → Cl S (lf u)

E-Cl : ∀ {b i g w} {S S′ : Lf (sp b i g w) → Set} (acc : T (sp b i g w)) {t : T (sp b i g w)} →
       Cl S acc → Cl S′ t → Cl S (E rf′ acc t)
E-Cl acc ca cz = cs ca
E-Cl {b} {i} {g} {w} {S} {S′} acc ca (cs {t} ct) = cl it
  where
  it : ∀ n → Cl S (iter (λ r → E rf′ r t) n acc)
  it zero    = ca
  it (suc n) = E-Cl {S′ = S′} _ (it n) ct
E-Cl acc ca (cl c) = cl (λ n → E-Cl acc ca (c n))
E-Cl acc ca (cb c) = cb (λ x → E-Cl acc ca (c x))
E-Cl acc ca (cf _) = cs ca

Tops : ∀ b i g w → Lf (sp b i g w) → Set
Tops b i g w u = Σ (Ix b i) (λ x → u ≡ pk x (Ωtop (g x)))

top-Cl : ∀ b i g w → Cl (Tops b i g w) (Ωtop (sp b i g w))
top-Cl b iℕ       g w = cl (λ n → cf (n , refl))
top-Cl b (inj₂ q) g w = cb (λ x → cf (x , refl))

restart : ∀ b i g w →
  Cl (Tops b i g w) (step (s (sp b i g w)) (Ωtop (sp b i g w)) (Ωtop (s (sp b i g w))))
restart b i g w = cl it
  where
  A = Ωtop (sp b i g w)
  it : ∀ n → Cl (Tops b i g w) (iter (λ x → E rf′ A x) n A)
  it zero    = top-Cl b i g w
  it (suc n) = E-Cl {S′ = Tops b i g w} A (top-Cl b i g w) (it n)
```
