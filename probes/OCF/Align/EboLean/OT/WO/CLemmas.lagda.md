# C^a(A) 的展开：Setzer [Se98] Lemma 5.5

> **EboLean 删节拷贝 (记号侧验收工作, 读 Setzer 的记号 OT_I).** 归档 `Mahlo.Inacc.WO.CLemmas` 的拷贝, 只改了模块名, 并删去了 EBO 路线 ([EboLean](../../../EboLean.lagda.md)) 用不到的定义 (由定义级切片判定, 删后从头编译核对). 讲解文字照旧, 可能提到已删的定义; 归档原文未动.

Assumption 4.4 (c)(d) 按四种 =NF 形状的消去／引入形式。全部由 K 的定义与 [K](K.lagda.md) 的表引理得出，**不依赖序理论**。另有：K^a(y) 的每个集合里的元素都 ≺ a（所以 C^a(A) 只看 A ∩ a）。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

module OCF.Align.EboLean.OT.WO.CLemmas where

open import OCF.Align.EboLean.OT.Syntax
open import OCF.Align.EboLean.OT.Order
open import OCF.Align.EboLean.OT.Closure
open import OCF.Align.EboLean.OT.BoolLemmas
open import OCF.Align.EboLean.OT.OTLemmas
open import OCF.Align.EboLean.OT.WO.K
open import OCF.Align.EboLean.OT.WO.Base

open import Level using (Level)
open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.List.Base using (List; []; _∷_; _++_; map; concatMap)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

private variable
  ℓ ℓ′ : Level
  A B : Pred ℓ

KR≡ : ∀ a κ → KR a κ ≡ K a (regTm κ)
KR≡ a (ΩR b) = refl
KR≡ a IR     = refl
```

## 1. 消去

和的引理对一般的 `b ▹ p` 陈述，附 `NZ b`（见 Syntax 的说明）。

```agda
C-+⁻ : ∀ {a b p} → NZ b → C a A (b ▹ p)
     → (A (b ▹ p) × (b ▹ p) ≺ a) ⊎ (C a A b × C a A ⟨ p ⟩)
C-+⁻ {A = A} {a} {b ▹ q} {p} _ (c! o r) with Any-++⁻ (K a (b ▹ q) ⊗ KP a p) r
... | inj₁ s = let (sb , sc) = ⊗⁻ {A = A} (K a (b ▹ q)) s
                   (ob , oc , _) = OT-+⁻ o
               in inj₂ (c! ob sb , c! oc sc)
... | inj₂ s = let (x≺a , x∈A) = ↾⁻ {A = A} s in inj₁ (x∈A , x≺a)

C-φ⁻ : ∀ {a b c} → C a A ⟨ phi b c ⟩
     → (A ⟨ phi b c ⟩ × ⟨ phi b c ⟩ ≺ a) ⊎ (C a A b × C a A c)
C-φ⁻ {A = A} {a} {b} {c} (c! o r) with Any-++⁻ (K a b ⊗ K a c) r
... | inj₁ s = let (sb , sc) = ⊗⁻ {A = A} (K a b) s
                   (ob , oc , _) = OT-φ⁻ o
               in inj₂ (c! ob sb , c! oc sc)
... | inj₂ s = let (x≺a , x∈A) = ↾⁻ {A = A} s in inj₁ (x∈A , x≺a)

C-Ω⁻ : ∀ {a b} → C a A ⟨ Om b ⟩ → (A ⟨ Om b ⟩ × ⟨ Om b ⟩ ≺ a) ⊎ C a A b
C-Ω⁻ {A = A} {a} {b} (c! o r) with Any-++⁻ (K a b) r
... | inj₁ s = let (ob , _) = OT-Ω⁻ o in inj₂ (c! ob s)
... | inj₂ s = let (x≺a , x∈A) = ↾⁻ {A = A} s in inj₁ (x∈A , x≺a)

C-ψ⁻ : ∀ {a κ c} → C a A ⟨ psi κ c ⟩
     → (A ⟨ psi κ c ⟩ × ⟨ psi κ c ⟩ ≺ a)
     ⊎ (a ≺ regTm κ × C a A (regTm κ) × C a A c)
C-ψ⁻ {A = A} {a} {κ} {c} (c! o r) with lt a (regTm κ) in eq
... | false = let (x≺a , x∈A) = ↾⁻ {A = A} r in inj₁ (x∈A , x≺a)
... | true with Any-++⁻ (KR a κ ⊗ K a c) r
...   | inj₂ s = let (x≺a , x∈A) = ↾⁻ {A = A} s in inj₁ (x∈A , x≺a)
...   | inj₁ s = let (sκ , sc) = ⊗⁻ {A = A} (KR a κ) s
                     (oc , oκ , _) = OT-ψ⁻ o
                 in inj₂ (lt! eq , c! oκ (subst (Any (All A)) (KR≡ a κ) sκ) , c! oc sc)
```

## 2. 引入（分量都在 C^a(A) 的那一支；原子那一支是 `A∩a⊆C`）

```agda
C-+⁺ : ∀ {a b p} → NZ b → OT (b ▹ p) → C a A b → C a A ⟨ p ⟩ → C a A (b ▹ p)
C-+⁺ {A = A} {b = _ ▹ _} _ o (c! _ rb) (c! _ rc) = c! o (Any-++⁺ˡ (⊗⁺ {A = A} rb rc))

C-φ⁺ : ∀ {a b c} → OT ⟨ phi b c ⟩ → C a A b → C a A c → C a A ⟨ phi b c ⟩
C-φ⁺ {A = A} o (c! _ rb) (c! _ rc) = c! o (Any-++⁺ˡ (⊗⁺ {A = A} rb rc))

C-Ω⁺ : ∀ {a b} → OT ⟨ Om b ⟩ → C a A b → C a A ⟨ Om b ⟩
C-Ω⁺ o (c! _ rb) = c! o (Any-++⁺ˡ rb)

C-ψ⁺ : ∀ {a κ c} → OT ⟨ psi κ c ⟩ → a ≺ regTm κ → C a A (regTm κ) → C a A c
     → C a A ⟨ psi κ c ⟩
C-ψ⁺ {A = A} {a} {κ} {c} o (lt! eq) (c! _ rκ) (c! _ rc) =
  c! o (subst (λ t → Any (All A) (if t then (KR a κ ⊗ K a c) ++ (⟨ psi κ c ⟩ ↾ a)
                                         else (⟨ psi κ c ⟩ ↾ a)))
              (sym eq)
              (Any-++⁺ˡ (⊗⁺ {A = A} (subst (Any (All A)) (sym (KR≡ a κ)) rκ) rc)))
```

## 3. K^a(y) 的元素都 ≺ a；C^a 对 A ∩ a 单调

```agda
Bounded : Tm → FinFin → Set
Bounded a X = All (All (λ x → x ≺ a)) X

Bounded-++ : ∀ {a} X {Y} → Bounded a X → Bounded a Y → Bounded a (X ++ Y)
Bounded-++ []      p       q = q
Bounded-++ (_ ∷ X) (p ∷ ps) q = p ∷ Bounded-++ X ps q

Bounded-map : ∀ {a} K Y → All (λ x → x ≺ a) K → Bounded a Y
            → Bounded a (map (λ L → K ++ L) Y)
Bounded-map K []      p []       = []
Bounded-map K (L ∷ Y) p (r ∷ rs) = All-++⁺ p r ∷ Bounded-map K Y p rs

Bounded-⊗ : ∀ {a} X {Y} → Bounded a X → Bounded a Y → Bounded a (X ⊗ Y)
Bounded-⊗ []      {Y} []       q = []
Bounded-⊗ (K ∷ X) {Y} (p ∷ ps) q =
  Bounded-++ (map (λ L → K ++ L) Y) (Bounded-map K Y p q) (Bounded-⊗ X ps q)

Bounded-↾ : ∀ {a} d → Bounded a (d ↾ a)
Bounded-↾ {a} d with lt d a in eq
... | true  = (lt! eq ∷ []) ∷ []
... | false = []

mutual
  K-bounded : ∀ a y → Bounded a (K a y)
  K-bounded a zer         = [] ∷ []
  K-bounded a (zer ▹ p)   = KP-bounded a p
  K-bounded a (b ▹ q ▹ p) =
    Bounded-++ (K a (b ▹ q) ⊗ KP a p)
      (Bounded-⊗ (K a (b ▹ q)) (K-bounded a (b ▹ q)) (KP-bounded a p))
      (Bounded-↾ (b ▹ q ▹ p))

  KP-bounded : ∀ a p → Bounded a (KP a p)
  KP-bounded a I         = [] ∷ []
  KP-bounded a (phi b c) =
    Bounded-++ (K a b ⊗ K a c) (Bounded-⊗ (K a b) (K-bounded a b) (K-bounded a c))
      (Bounded-↾ ⟨ phi b c ⟩)
  KP-bounded a (Om b)    = Bounded-++ (K a b) (K-bounded a b) (Bounded-↾ ⟨ Om b ⟩)
  KP-bounded a (psi κ c) with lt a (regTm κ)
  ... | true  = Bounded-++ (KR a κ ⊗ K a c)
                  (Bounded-⊗ (KR a κ) (KR-bounded a κ) (K-bounded a c))
                  (Bounded-↾ ⟨ psi κ c ⟩)
  ... | false = Bounded-↾ ⟨ psi κ c ⟩

  KR-bounded : ∀ a κ → Bounded a (KR a κ)
  KR-bounded a (ΩR b) = Bounded-++ (K a b) (K-bounded a b) (Bounded-↾ ⟨ Om b ⟩)
  KR-bounded a IR     = [] ∷ []
```

`(A ∩ a) ⊆ B ⟹ C^a(A) ⊆ C^a(B)`；因此 `A ∩ a ≅ B ∩ a ⟹ C^a(A) ≅ C^a(B)`。

```agda
All-mono-≺ : ∀ {a} {L : List Tm} → All (λ x → x ≺ a) L
           → (∀ {x} → x ≺ a → A x → B x) → All A L → All B L
All-mono-≺ []       h []       = []
All-mono-≺ (b ∷ bs) h (p ∷ ps) = h b p ∷ All-mono-≺ bs h ps

Any-All-mono : ∀ {a} {X : FinFin} → Bounded a X
             → (∀ {x} → x ≺ a → A x → B x) → Any (All A) X → Any (All B) X
Any-All-mono (bs ∷ _)  h (here p)  = here (All-mono-≺ bs h p)
Any-All-mono (_ ∷ bss) h (there q) = there (Any-All-mono bss h q)

C-mono : ∀ {a} → (∀ {x} → x ≺ a → A x → B x) → C a A ⊆ C a B
C-mono {a = a} h {x = y} (c! o r) = c! o (Any-All-mono (K-bounded a y) h r)

C-cong : ∀ {a} → (∀ {x} → x ≺ a → A x → B x) → (∀ {x} → x ≺ a → B x → A x)
       → C a A ≅ C a B
C-cong f g = C-mono f , C-mono g

```
