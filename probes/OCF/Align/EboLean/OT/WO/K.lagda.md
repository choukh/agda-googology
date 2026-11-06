# 有限支撑集 K^a(b) 与类 C^a(A)：Setzer [Se98] Definitions 5.1–5.4, Lemma 5.5

> **EboLean 删节拷贝 (记号侧验收工作, 读 Setzer 的记号 OT_I).** 归档 `Mahlo.Inacc.WO.K` 的拷贝, 只改了模块名, 并删去了 EBO 路线 ([EboLean](../../../EboLean.lagda.md)) 用不到的定义 (由定义级切片判定, 删后从头编译核对). 讲解文字照旧, 可能提到已删的定义; 归档原文未动.

良序证明的第一个类型论构造。`C^a(A)`（Assumption 4.4）是「由 A ∩ a 中的原子经全部序数函数生成、但 ψ_κ 只许 a ≺ κ 的项」。Setzer 不把它定义成归纳类（那要更强的理论），而是先原始递归地算出有限集族 `K^a(b)`——b 的**支撑集候选**——再令

> `C^a(A) := {y ∈ OT | ∃L ∈ K^a(y). L ⊆ A}`。

于是 `C^a(A)` 只用有限的 Σ／× 从 A 搭出，「correctly defined from A : Cl(N)」；宇宙层级随 A。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

module OCF.Align.EboLean.OT.WO.K where

open import OCF.Align.EboLean.OT.Syntax
open import OCF.Align.EboLean.OT.Order
open import OCF.Align.EboLean.OT.Closure

open import Level using (Level; _⊔_)
open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.List.Base using (List; []; _∷_; _++_; map; concatMap)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open OT public

private variable ℓ ℓ′ : Level
```

## 1. 有限集的有限集（Def 5.1）

有限集用表；`A ⊗ B := {K ∪ L | K ∈ A, L ∈ B}`；`{{d}} ↾ a := {{d}}` 若 d ≺ a，否则 ∅。

```agda
FinFin : Set
FinFin = List (List Tm)

_⊗_ : FinFin → FinFin → FinFin
A ⊗ B = concatMap (λ K → map (λ L → K ++ L) B) A

_↾_ : Tm → Tm → FinFin                  -- {{d}} ↾ a
d ↾ a = if lt d a then (d ∷ []) ∷ [] else []
```

## 2. K^a(b)（Def 5.3）

按 b 的结构（原文按 length(b)）：

- `K^a(0) := K^a(I) := {∅}`
- `d =NF φ b c` 或 `d =₀NF b + c`：`K^a(d) := (K^a(b) ⊗ K^a(c)) ∪ ({{d}} ↾ a)`
- `d =NF Ω_b`：`K^a(d) := K^a(b) ∪ ({{d}} ↾ a)`
- `d =NF ψ_κ c`：`a ≺ κ` 时 `(K^a(κ) ⊗ K^a(c)) ∪ ({{d}} ↾ a)`；否则原文 `{{d}}`——这里写 `{{d}} ↾ a`，与 Assumption 4.4 (d) 第二支「d ∈ C^a(A) ↔ d ∈ A ∩ a」直接吻合（原文两者等价是因为 ψ_κ c ≺ κ ⪯ a）。

原文 `K^a(d) := ∅` 若 `d ∉ OT ∨ a ∉ OT`：这里不在 K 内查，OT 条件放进 `C`（§3）。

```agda
mutual
  K : Tm → Tm → FinFin
  K a zer         = [] ∷ []
  K a (zer ▹ p)   = KP a p
  K a (b ▹ q ▹ p) = (K a (b ▹ q) ⊗ KP a p) ++ ((b ▹ q ▹ p) ↾ a)

  KP : Tm → PTm → FinFin
  KP a I         = [] ∷ []
  KP a (phi b c) = (K a b ⊗ K a c) ++ (⟨ phi b c ⟩ ↾ a)
  KP a (Om b)    = K a b ++ (⟨ Om b ⟩ ↾ a)
  KP a (psi κ c) = if lt a (regTm κ)
                     then (KR a κ ⊗ K a c) ++ (⟨ psi κ c ⟩ ↾ a)
                     else ⟨ psi κ c ⟩ ↾ a

  KR : Tm → Reg → FinFin                -- K^a(κ)
  KR a (ΩR b) = K a b ++ (⟨ Om b ⟩ ↾ a)
  KR a IR     = [] ∷ []
```

## 3. C^a(A)（Def 5.4）

同 `≺`、`OT`：包成记录，`K a y` 在 ψ 处展开成 `if lt a κ …`，裸写会让隐参 `a` 推不出来。

```agda
Pred : (ℓ : Level) → Set _
Pred ℓ = Tm → Set ℓ


record C (a : Tm) (A : Pred ℓ) (y : Tm) : Set ℓ where   -- y ∈ C^a(A)
  constructor c!
  field
    inOT : OT y
    supp : Any (All A) (K a y)
open C public
```

## 4. Lemma 5.5（Assumption 4.4 的验证）

先证 Remark 5.2 的两条表引理：`∃K ∈ A ⊗ B. K ⊆ C ⟺ (∃K ∈ A. K ⊆ C) ∧ (∃L ∈ B. L ⊆ C)`；`∃K ∈ {{d}} ↾ a. K ⊆ C ⟺ d ≺ a ∧ d ∈ C`。

```agda
Any-++⁺ˡ : ∀ {P : List Tm → Set ℓ′} {X Y : FinFin} → Any P X → Any P (X ++ Y)
Any-++⁺ˡ (here p)  = here p
Any-++⁺ˡ (there q) = there (Any-++⁺ˡ q)

Any-++⁺ʳ : ∀ {P : List Tm → Set ℓ′} (X : FinFin) {Y} → Any P Y → Any P (X ++ Y)
Any-++⁺ʳ []       q = q
Any-++⁺ʳ (_ ∷ X)  q = there (Any-++⁺ʳ X q)

Any-++⁻ : ∀ {P : List Tm → Set ℓ′} (X : FinFin) {Y} → Any P (X ++ Y) → Any P X ⊎ Any P Y
Any-++⁻ []      q         = inj₂ q
Any-++⁻ (_ ∷ X) (here p)  = inj₁ (here p)
Any-++⁻ (_ ∷ X) (there q) with Any-++⁻ X q
... | inj₁ r = inj₁ (there r)
... | inj₂ r = inj₂ r

module _ {A : Pred ℓ} where

  All-++⁺ : ∀ {K L} → All A K → All A L → All A (K ++ L)
  All-++⁺ []       q = q
  All-++⁺ (p ∷ ps) q = p ∷ All-++⁺ ps q

  All-++⁻ : ∀ K {L} → All A (K ++ L) → All A K × All A L
  All-++⁻ []       q       = [] , q
  All-++⁻ (x ∷ K) (p ∷ ps) = let (l , r) = All-++⁻ K ps in p ∷ l , r
```

```agda
  -- Remark 5.2 (a)
  ⊗⁺ : ∀ {X Y : FinFin} → Any (All A) X → Any (All A) Y → Any (All A) (X ⊗ Y)
  ⊗⁺ {X = K ∷ X} {Y} (here p)  q = Any-++⁺ˡ (map-lemma q)
    where
      map-lemma : ∀ {Y} → Any (All A) Y → Any (All A) (map (λ L → K ++ L) Y)
      map-lemma (here r)  = here (All-++⁺ p r)
      map-lemma (there r) = there (map-lemma r)
  ⊗⁺ {X = K ∷ X} {Y} (there q) r = Any-++⁺ʳ (map (λ L → K ++ L) Y) (⊗⁺ q r)

  ⊗⁻ : ∀ (X : FinFin) {Y} → Any (All A) (X ⊗ Y) → Any (All A) X × Any (All A) Y
  ⊗⁻ (K ∷ X) {Y} q with Any-++⁻ (map (λ L → K ++ L) Y) q
  ... | inj₁ r = here (proj₁ (unmap r)) , proj₂ (unmap r)
    where
      unmap : ∀ {Y} → Any (All A) (map (λ L → K ++ L) Y) → All A K × Any (All A) Y
      unmap {L ∷ Y} (here s)  = let (l , r) = All-++⁻ K s in l , here r
      unmap {L ∷ Y} (there s) = let (l , r) = unmap s in l , there r
  ... | inj₂ r = let (l , r′) = ⊗⁻ X r in there l , r′

  -- Remark 5.2 (b)
  ↾⁺ : ∀ {d a} → d ≺ a → A d → Any (All A) (d ↾ a)
  ↾⁺ {d} {a} (lt! p) q with lt d a
  ↾⁺ (lt! refl) q | true = here (q ∷ [])

  ↾⁻ : ∀ {d a} → Any (All A) (d ↾ a) → d ≺ a × A d
  ↾⁻ {d} {a} q with lt d a in eq
  ↾⁻ (here (q ∷ [])) | true = lt! eq , q
```

Lemma 5.5 本身（(a) 由定义；(b)–(d) 由上面的表引理与 `isOT` 的展开）留到 `Base` 里按需要的形状陈述。
