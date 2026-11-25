# 层号的值: 代数, 正规层号, 类型界

> 判决: 编译定理, 无前提 (排中律只在 `Cl` 里作参数). 层号值序 `≼ᴸ` (与 S1 的值序同一定义) 下 `⊕` 两侧单调、右侧严格、结合; `↑` 把树的序送到严格值序 (`↑-strict`), `↑ (x + y) ≈ ↑ x ⊕ ↑ y`.
> 正规 `Nm`: 极限形状的每个孩子下都有严格更高的正规孩子, 后继形状不要求孩子. `tw n`, `Λ`, `Ωt` 后继层的读回有闭项证据; 遗传式正规 `NmH` 在 `tw 2` 上不成立 (`¬NmH-tw2`), 读回层号一般不正规 (`¬Nm-↑dg`).
> 类型界 `tb↑`: `Tr ℓ` 的树读成的层号严格低于 `ℓ` 的后继层号的 Ω 树读成的层号. `Ωt` 的值单调在 `YiRVOmega`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiRVLevel where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
```

## 值序

|zero| = 0, |nd s h| = sup (|h c| + 1). 与 S1 的 `_≼ᴸ_` 逐字相同.

```agda
infix 4 _≼ᴸ_ _≺ᴸ_ _≈ᴸ_
data _≼ᴸ_ : L → L → Set
_≺ᴸ_ : L → L → Set
data _≼ᴸ_ where
  z≼ : ∀ {b} → zero ≼ᴸ b
  n≼ : ∀ {s h b} → ((c : Ch s) → h c ≺ᴸ b) → nd s h ≼ᴸ b
a ≺ᴸ zero   = ⊥
a ≺ᴸ nd s h = Σ (Ch s) λ c → a ≼ᴸ h c

_≈ᴸ_ : L → L → Set
a ≈ᴸ b = (a ≼ᴸ b) × (b ≼ᴸ a)

mutual
  ≼ᴸ-trans : ∀ {a b c} → a ≼ᴸ b → b ≼ᴸ c → a ≼ᴸ c
  ≼ᴸ-trans z≼ e = z≼
  ≼ᴸ-trans {b = b} {c} (n≼ f) e = n≼ (λ x → ≺≼ b c (f x) e)

  ≺≼ : ∀ {a} b c → a ≺ᴸ b → b ≼ᴸ c → a ≺ᴸ c
  ≺≼ zero c () e
  ≺≼ (nd s h) zero (x , d) (n≼ f) = f x
  ≺≼ (nd s h) (nd s′ h′) (x , d) (n≼ f) = proj₁ (f x) , ≼ᴸ-trans d (proj₂ (f x))

≼ᴸ-refl : ∀ a → a ≼ᴸ a
≼ᴸ-refl zero     = z≼
≼ᴸ-refl (nd s h) = n≼ (λ c → c , ≼ᴸ-refl (h c))

≼≺ : ∀ {a b} c → a ≼ᴸ b → b ≺ᴸ c → a ≺ᴸ c
≼≺ zero le ()
≼≺ (nd s h) le (x , d) = x , ≼ᴸ-trans le d

mutual
  up≼ : ∀ {a s h} c → a ≼ᴸ h c → a ≼ᴸ nd s h
  up≼ c z≼ = z≼
  up≼ {s = s} {h} c (n≼ f) = n≼ (λ x → c , ≺→≼ (h c) (f x))

  ≺→≼ : ∀ {a} b → a ≺ᴸ b → a ≼ᴸ b
  ≺→≼ zero ()
  ≺→≼ (nd s h) (c , d) = up≼ c d

≺-trans : ∀ {a b} c → a ≺ᴸ b → b ≺ᴸ c → a ≺ᴸ c
≺-trans {b = b} c d e = ≼≺ c (≺→≼ b d) e

≺-irrefl : ∀ a → a ≺ᴸ a → ⊥
≺-irrefl zero ()
≺-irrefl (nd s h) (c , n≼ f) = ≺-irrefl (h c) (f c)

≈ᴸ-refl : ∀ a → a ≈ᴸ a
≈ᴸ-refl a = ≼ᴸ-refl a , ≼ᴸ-refl a

≈ᴸ-trans : ∀ {a b c} → a ≈ᴸ b → b ≈ᴸ c → a ≈ᴸ c
≈ᴸ-trans (d , d′) (e , e′) = ≼ᴸ-trans d e , ≼ᴸ-trans e′ d′

nd-cong : ∀ {s h h′} → ((c : Ch s) → h c ≈ᴸ h′ c) → nd s h ≈ᴸ nd s h′
nd-cong e = n≼ (λ c → c , proj₁ (e c)) , n≼ (λ c → c , proj₂ (e c))
```

经典二分 (排中律作参数, 与 S1 的 `Dk` 同一证明).

```agda
LEM : Set₁
LEM = (A : Set) → A ⊎ (A → ⊥)

module Cl (lem : LEM) where
  notAll : ∀ {I : Set} {P : I → Set} → (((i : I) → P i) → ⊥) → Σ I (λ i → P i → ⊥)
  notAll {I} {P} na with lem (Σ I (λ i → P i → ⊥))
  ... | inj₁ e  = e
  ... | inj₂ ne = ⊥-elim (na dn)
    where
    dn : (i : I) → P i
    dn i with lem (P i)
    ... | inj₁ p  = p
    ... | inj₂ np = ⊥-elim (ne (i , np))

  neg : ∀ {A B : Set} → A ⊎ B → (A → ⊥) → B
  neg (inj₁ a) n = ⊥-elim (n a)
  neg (inj₂ b) n = b

  Dk : (a b : L) → (a ≼ᴸ b) ⊎ (b ≺ᴸ a)
  Dk zero b = inj₁ z≼
  Dk (nd s h) zero = inj₂ (c₀ s , z≼)
  Dk (nd s h) (nd s′ h′) with lem ((c : Ch s) → Σ (Ch s′) λ c′ → h c ≼ᴸ h′ c′)
  ... | inj₁ f  = inj₁ (n≼ f)
  ... | inj₂ nf with notAll nf
  ...   | c , nc = inj₂ (c , n≼ (λ c′ → neg (Dk (h c) (h′ c′)) (λ le → nc (c′ , le))))
```

## ⊕ 的代数

|a ⊕ b| = |a| + |b| 的各个方向: 两个下界, 两侧单调, 右侧严格, 零为左单位, 结合.

```agda
≼⊕ˡ : (a b : L) → a ≼ᴸ a ⊕ b
≼⊕ˡ a zero     = ≼ᴸ-refl a
≼⊕ˡ a (nd s h) = up≼ (c₀ s) (≼⊕ˡ a (h (c₀ s)))

≼⊕ʳ : (a b : L) → b ≼ᴸ a ⊕ b
≼⊕ʳ a zero     = z≼
≼⊕ʳ a (nd s h) = n≼ (λ c → c , ≼⊕ʳ a (h c))

⊕-monoˡ : ∀ {a a′} → a ≼ᴸ a′ → (b : L) → a ⊕ b ≼ᴸ a′ ⊕ b
⊕-monoˡ d zero     = d
⊕-monoˡ d (nd s h) = n≼ (λ c → c , ⊕-monoˡ d (h c))

mutual
  ⊕-monoʳ : (a : L) {b b′ : L} → b ≼ᴸ b′ → a ⊕ b ≼ᴸ a ⊕ b′
  ⊕-monoʳ a {b′ = b′} z≼ = ≼⊕ˡ a b′
  ⊕-monoʳ a {b′ = b′} (n≼ f) = n≼ (λ c → ⊕-strictʳ a b′ (f c))

  ⊕-strictʳ : (a : L) {b : L} (b′ : L) → b ≺ᴸ b′ → a ⊕ b ≺ᴸ a ⊕ b′
  ⊕-strictʳ a zero ()
  ⊕-strictʳ a (nd s′ h′) (c′ , d) = c′ , ⊕-monoʳ a d

⊕-pos : (a : L) {b : L} → zero ≺ᴸ b → a ≺ᴸ a ⊕ b
⊕-pos a {nd s h} (c , _) = c , ≼⊕ˡ a (h c)

z⊕ : (b : L) → zero ⊕ b ≈ᴸ b
z⊕ zero     = ≈ᴸ-refl zero
z⊕ (nd s h) = nd-cong (λ c → z⊕ (h c))

⊕-assoc : (a b c : L) → (a ⊕ b) ⊕ c ≈ᴸ a ⊕ (b ⊕ c)
⊕-assoc a b zero     = ≈ᴸ-refl (a ⊕ b)
⊕-assoc a b (nd s h) = nd-cong (λ x → ⊕-assoc a b (h x))
```

## 读回 ↑ 的代数

```agda
↑-strict : (k : L) {x y : Tr k} → k ⊢ x ◃ y → ↑ k x ≺ᴸ ↑ k y
↑-strict k        ◃s           = tt , ≼ᴸ-refl _
↑-strict k        (◃l n)       = n , ≼ᴸ-refl _
↑-strict k        ◃w           = zero , ≼ᴸ-refl _
↑-strict (nd s h) (◃u x c y e) = ⊕-pos (↑ (nd s h) x) (↑-strict (h c) e)
↑-strict (nd s h) (◃c x c d)   = ⊕-strictʳ (↑ (nd s h) x) _ (↑-strict (h c) d)
↑-strict k        (◃t d e)     = ≺-trans _ (↑-strict k d) (↑-strict k e)

↑-+ : (k : L) (x y : Tr k) → ↑ k (x + y) ≈ᴸ ↑ k x ⊕ ↑ k y
↑-+ k        x zero         = ≈ᴸ-refl (↑ k x)
↑-+ k        x (suc y)      = nd-cong (λ _ → ↑-+ k x y)
↑-+ k        x (lim f a)    = nd-cong (λ n → ↑-+ k x (f n))
↑-+ k        x (Ω p g)      = nd-cong (λ c → ↑-+ k x (g (fromBr k p c)))
↑-+ (nd s h) x (up y c w e) =
  ≈ᴸ-trans (⊕-monoˡ (proj₁ (↑-+ (nd s h) x y)) (↑ (h c) w) , ⊕-monoˡ (proj₂ (↑-+ (nd s h) x y)) (↑ (h c) w))
           (⊕-assoc (↑ (nd s h) x) (↑ (nd s h) y) (↑ (h c) w))
```

## 正规层号

`Nm`: ℕ 极限与 Ω 形状的每个孩子之下都有严格更高、且正规的孩子 (共尾正规); 后继形状对孩子不作要求. 为何足够: `YiRVOmega.M` 只在右侧用 `Nm`, 每到极限形状就换到更高的正规孩子, 到后继形状就停. 遗传式 `NmH` (N1 原文: 极限孩子严格增, Ω 孩子无最大元, 且对一切孩子遗传) 在塔上填不进去, 见本节末.

```agda
Nm : L → Set
Nm zero          = ⊤
Nm (nd sS h)     = ⊤
Nm (nd sL g)     = (n : ℕ) → Σ ℕ λ m → (g n ≺ᴸ g m) × Nm (g m)
Nm (nd (sΩ k) h) = (c : Tr k) → Σ (Tr k) λ c′ → (h c ≺ᴸ h c′) × Nm (h c′)

Nm-⊕ : (a b : L) → Nm a → Nm b → Nm (a ⊕ b)
Nm-⊕ a zero          na nb = na
Nm-⊕ a (nd sS h)     na nb = tt
Nm-⊕ a (nd sL g)     na nb n with nb n
... | m , lt , nm = m , ⊕-strictʳ a (g m) lt , Nm-⊕ a (g m) na nm
Nm-⊕ a (nd (sΩ k) h) na nb c with nb c
... | c′ , lt , nm = c′ , ⊕-strictʳ a (h c′) lt , Nm-⊕ a (h c′) na nm

tw≺ : (n : ℕ) → tw n ≺ᴸ tw (suc n)
tw≺ n = zero , ≼ᴸ-refl (tw n)

Nm-tw : (n : ℕ) → Nm (tw n)
Nm-tw zero    = tt
Nm-tw (suc n) = λ c → suc c , (tt , ≼ᴸ-refl _) , tt

Nm-Λ : Nm Λ
Nm-Λ n = suc n , tw≺ n , Nm-tw (suc n)
```

读回层号: 后继, ℕ 极限, 嵌入三种构造子保持正规 (Ω 结点处 `Nm` 就是 "分支读回共尾严格增" 本身). `Ωt` 在后继层上的读回正规.

```agda
Nm-↑lim : (k : L) (f : ℕ → Tr k) (a : (n : ℕ) → k ⊢ f n ◃ f (suc n))
        → ((n : ℕ) → Nm (↑ k (f n))) → Nm (↑ k (lim f a))
Nm-↑lim k f a nf n = suc n , ↑-strict k (a n) , nf (suc n)

Nm-↑up : ∀ {s h} (x : Tr (nd s h)) (c : Ch s) (y : Tr (h c)) (e : h c ⊢ zero ◃ y)
       → Nm (↑ (nd s h) x) → Nm (↑ (h c) y) → Nm (↑ (nd s h) (up x c y e))
Nm-↑up {s} {h} x c y e nx ny = Nm-⊕ (↑ (nd s h) x) (↑ (h c) y) nx ny

sc : L → L
sc ℓ = nd sS (λ _ → ℓ)

Nm-↑Ωt-sc : (ℓ : L) → Nm (↑ (sc ℓ) (proj₁ (Ωt (sc ℓ))))
Nm-↑Ωt-sc ℓ c = suc c , (tt , ≼ᴸ-refl _) , tt
```

类型界: `Tr ℓ` 的树 x 本身就是 `Ωt (sc ℓ)` 的一个分支下标.

```agda
tb↑ : (ℓ : L) (x : Tr ℓ) → ↑ ℓ x ≺ᴸ ↑ (sc ℓ) (proj₁ (Ωt (sc ℓ)))
tb↑ ℓ x = x , up≼ tt (≼⊕ʳ zero (↑ ℓ x))
```

反例: 遗传式正规在 `tw 2` 不成立 (孩子 `tw 1 ⊕ ↑ dg` 的孩子全是 `tw 1`); 合法树 `dg` 的读回就是 N1 的退化层号 `Dg`, 不正规.

```agda
NmH : L → Set
NmH zero          = ⊤
NmH (nd sS h)     = NmH (h tt)
NmH (nd sL g)     = ((n : ℕ) → g n ≺ᴸ g (suc n)) × ((n : ℕ) → NmH (g n))
NmH (nd (sΩ k) h) = NmH k × ((c : Tr k) → Σ (Tr k) λ c′ → h c ≺ᴸ h c′) × ((c : Tr k) → NmH (h c))

dg₁ : Tr (tw 1)
dg₁ = Ω (inj₁ (inj₁ tt)) (λ _ → zero)

¬NmH-tw2 : NmH (tw 2) → ⊥
¬NmH-tw2 (_ , _ , hs) with proj₁ (proj₂ (hs dg₁)) zero
... | c′ , lt = ≺-irrefl (tw 1) lt

dg : Tr (sc zero)
dg = Ω (inj₂ (tt , inj₁ tt)) (λ _ → zero)

¬Nm-↑dg : Nm (↑ (sc zero) dg) → ⊥
¬Nm-↑dg n = proj₁ (proj₂ (n zero))
```
