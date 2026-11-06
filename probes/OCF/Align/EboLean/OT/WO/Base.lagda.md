# M(A)、τ^A、𝒜^A、W(A)：Setzer [Se98] Definitions 4.5, 4.12, 4.18, 5.6 与 Assumption 4.10

> **EboLean 删节拷贝 (记号侧验收工作, 读 Setzer 的记号 OT_I).** 归档 `Mahlo.Inacc.WO.Base` 的拷贝, 只改了模块名, 并删去了 EBO 路线 ([EboLean](../../../EboLean.lagda.md)) 用不到的定义 (由定义级切片判定, 删后从头编译核对). 讲解文字照旧, 可能提到已删的定义; 归档原文未动.

方案 A 的类型论核心。Setzer 在 ML₁W 里用 W-类型手工构造 `W(A)`（Def 5.6：树 `W₁^A := Wx:N. τ̂^A(x)`，加正确性谓词 `Cor^A`，再取根的下标）；这里 V := `Set`，直接写成**带参数 A 的归纳族**——Dybjer 式归约（索引归纳定义 ↔ W-类型 + 等式）就是 Def 5.6 做的事，Agda 的 `data` 把它内建了。宇宙层级随 A 多态：A : `Pred ℓ` 则 `𝒲 A : Pred ℓ`。

「集合 P(N)」= `Pred 0ℓ`（`Tm → Set`，宇宙元素），「类 Cl(N)」= 任意层级。§4 的引理都对层级多态，所以既可用于集合也可用于类。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

module OCF.Align.EboLean.OT.WO.Base where

open import OCF.Align.EboLean.OT.Syntax
open import OCF.Align.EboLean.OT.Order
open import OCF.Align.EboLean.OT.Closure
open import OCF.Align.EboLean.OT.Arith
open import OCF.Align.EboLean.OT.BoolLemmas
open import OCF.Align.EboLean.OT.WO.K

open import Level using (Level; _⊔_; 0ℓ)
open import Data.Bool.Base using (Bool; true; false)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂; ∃)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private variable
  ℓ ℓ′ ℓ″ : Level
  A B : Pred ℓ
```

## 1. 类的代数

`a` 兼作集合 `{x ∈ OT | x ≺ a}`（原文 Def 2.9 后的约定），写 `↓ a`；`A|b := A ∩ (b + 1)`。

```agda
infix 4 _⊆_ _≅_ _⊑_
infixr 6 _∩_

_⊆_ : Pred ℓ → Pred ℓ′ → Set _
A ⊆ B = ∀ {x} → A x → B x

_≅_ : Pred ℓ → Pred ℓ′ → Set _
A ≅ B = (A ⊆ B) × (B ⊆ A)

_∩_ : Pred ℓ → Pred ℓ′ → Pred _
(A ∩ B) x = A x × B x

↓ : Tm → Pred 0ℓ
↓ a x = OT x × x ≺ a

_∣_ : Pred ℓ → Tm → Pred ℓ
(A ∣ b) x = A x × x ⪯ b



≅-refl : A ≅ A
≅-refl = (λ p → p) , (λ p → p)

≅-sym : A ≅ B → B ≅ A
≅-sym (f , g) = g , f

≅-trans : ∀ {C : Pred ℓ″} → A ≅ B → B ≅ C → A ≅ C
≅-trans (f , g) (h , k) = (λ p → h (f p)) , (λ p → g (k p))
```

## 2. M(A)、τ^A(a)、𝒜^A(B)（Def 4.5）

```agda
M : Pred ℓ → Pred ℓ                     -- M(A) := {y ∈ OT | y ∈ C^y(A)}
M A y = C y A y

τ : Pred ℓ → Tm → Pred ℓ                -- τ^A(a) := C^a(A) ∩ a
τ A a b = C a A b × b ≺ a

𝒜 : Pred ℓ → Pred ℓ′ → Pred _           -- 𝒜^A(B) := {y ∈ M(A) | τ^A(y) ⊆ B}
𝒜 A B y = M A y × (τ A y ⊆ B)
```

Remark 4.6 (b)：`M(A), τ^A(a) ⊆ OT`；Lemma 4.9 (d)：`0, I ∈ M(A)`；Lemma 4.7 (h)：`A ∩ a ⊆ C^a(A)`——这三条不用任何序的性质。

```agda
M⊆OT : M A ⊆ OT
M⊆OT (c! o _) = o


C⊆OT : ∀ {a} → C a A ⊆ OT
C⊆OT (c! o _) = o

0∈M : M A zer
0∈M = c! (ot! refl) (here [])

I∈M : M A I′
I∈M = c! (ot! refl) (here [])
```

`A ∩ a ⊆ C^a(A)`：x ∈ OT，x ≺ a，则 `{x} ∈ K^a(x)`（除 x = 0, I，那时 ∅ ∈ K^a(x)）。

```agda
∈K-self : ∀ {a} x → x ≺ a → A x → Any (All A) (K a x)
∈K-self zer                 p q = here []
∈K-self (zer ▹ I)           p q = here []
∈K-self {A} {a} (zer ▹ phi b c) p q = Any-++⁺ʳ (K a b ⊗ K a c) (↾⁺ {A = A} p q)
∈K-self {A} {a} (zer ▹ Om b)    p q = Any-++⁺ʳ (K a b) (↾⁺ {A = A} p q)
∈K-self {A} {a} (zer ▹ psi κ c) p q with lt a (regTm κ)
... | true  = Any-++⁺ʳ (KR a κ ⊗ K a c) (↾⁺ {A = A} p q)
... | false = ↾⁺ {A = A} p q
∈K-self {A} {a} (b ▹ q′ ▹ p′)  p q = Any-++⁺ʳ (K a (b ▹ q′) ⊗ KP a p′) (↾⁺ {A = A} p q)

A∩a⊆C : ∀ {a} → (A ∩ ↓ a) ⊆ C a A
A∩a⊆C {x = x} (q , o , p) = c! o (∈K-self x p q)
```

## 3. W(A)：归纳族（Def 5.6 的 Agda 形式）

```agda
data 𝒲 (A : Pred ℓ) : Pred ℓ where
  sup : ∀ {a} → M A a → τ A a ⊆ 𝒲 A → 𝒲 A a
```

Assumption 4.10：(a) `𝒜^A(W(A)) ⊆ W(A)`；(b) `𝒜^A(B) ∩ W(A) ⊆ B → W(A) ⊆ B`（Notation 4.11 的「Ind(x ∈ W(A))」）。(b) 是对证书的结构递归——Agda 的终止检查器就是 W-类型的消去子。

```agda

𝒲-ind : (𝒜 A B ∩ 𝒲 A) ⊆ B → 𝒲 A ⊆ B
𝒲-ind h w@(sup m f) = h ((m , λ t → 𝒲-ind h (f t)) , w)
```

Lemma 4.13 (a)：`∀x ∈ W(A). τ^A(x) ⊆ W(A) ∧ x ∈ M(A)`。Remark 5.7 (b)：`W(A) ⊆ M(A)`。

```agda
𝒲-τ : ∀ {a} → 𝒲 A a → τ A a ⊆ 𝒲 A
𝒲-τ (sup _ f) = f

𝒲-M : 𝒲 A ⊆ M A
𝒲-M (sup m _) = m

𝒲⊆OT : 𝒲 A ⊆ OT
𝒲⊆OT w = M⊆OT (𝒲-M w)
```

## 4. 段、突出集、进步性、A⁺（Def 4.12, 4.18）

- `A ⊑ B := A ⊆ OT ∧ ∀x ∈ A. A|x ≅ B|x`（A 是 B 的段）。
- `Ag(A) := A ⊆ OT ∧ A ⊑ W(A)`（突出集）。
- `Prog(A, B) := ∀x ∈ A. A ∩ x ⊆ B → x ∈ B`；`Prog(B) := Prog(Ω₁, B)`。
- `A⁺ := ⋃_{z ∈ A} ((W(A) ∩ z⁺) ∪ {z⁺})`。

```agda
_⊑_ : Pred ℓ → Pred ℓ′ → Set _
A ⊑ B = (A ⊆ OT) × (∀ {x} → A x → (A ∣ x) ≅ (B ∣ x))

Ag : Pred ℓ → Set _
Ag A = (A ⊆ OT) × (A ⊑ 𝒲 A)

Prog : Pred ℓ → Pred ℓ′ → Set _
Prog A B = ∀ {x} → A x → (A ∩ ↓ x) ⊆ B → B x

Prog₁ : Pred ℓ → Set _
Prog₁ B = Prog (↓ Ω₁) B

_⁺ : Pred ℓ → Pred ℓ
(A ⁺) y = ∃ λ z → A z × ((𝒲 A y × y ≺ plus z) ⊎ (y ≡ plus z))
```

Remark 4.20：`a ∈ A`，`Ag(A)` ⟹ `τ^A(a) ≅ A ∩ a`。证明：`A ∩ a ⊆ C^a(A) ∩ a = τ^A(a)`；反向 `a ∈ A ⊆ W(A)`，`τ^A(a) ⊆ W(A) ∩ a ≅ A ∩ a`（段性质）。

```agda
Ag⇒A⊆𝒲 : Ag A → A ⊆ 𝒲 A
Ag⇒A⊆𝒲 (_ , _ , seg) p = proj₁ (proj₁ (seg p) (p , ⪯-refl))


Rem4-20⊇ : ∀ {a} → (A ∩ ↓ a) ⊆ τ A a
Rem4-20⊇ (q , o , r) = A∩a⊆C (q , o , r) , r

```

`⪯-refl`、`≺⇒⪯` 来自 [../BoolLemmas](../BoolLemmas.lagda.md)：`le` 的平凡性质，不依赖序理论。
