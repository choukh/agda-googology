# 封闭性：Definition 4.14 与 Lemma 4.16

> **EboLean 删节拷贝 (记号侧验收工作, 读 Setzer 的记号 OT_I).** 归档 `Mahlo.Inacc.WO.Closed` 的拷贝, 只改了模块名, 并删去了 EBO 路线 ([EboLean](../../../EboLean.lagda.md)) 用不到的定义 (由定义级切片判定, 删后从头编译核对). 讲解文字照旧, 可能提到已删的定义; 归档原文未动.

Setzer [Se98] §4.3。「弱向下封闭」（=NF 分量与 κ⁻ 都在 A 里）、「弱向上封闭、以 P 为界」（=NF 合成在 A 里，只要合成项满足守卫 P）。原文的界是「≺ 某个 C 的元素」或「≺ a」；这里守卫 `P : Pred` 一般化，`_≺C_` 与 `(_≺ a)` 是两个实例，无界就是 `λ _ → ⊤`。

Lemma 4.16 (a)：`C^c(A)` 弱向下封闭（只要 `A ∩ c` 弱向下封闭——**不需要** `A ⊆ M(A)`，因为直接沿 K 的结构证，绕开原文经 ã 的转换）、弱向上封闭；`τ^A(c)` 同，以 c 为界；`W(A) ∩ a⁺`、`M(A) ∩ a⁺` 弱向下封闭。(b)：`A ∩ κ ⊑ W(A) ⟹ A ∩ κ` 弱向下封闭。

「向下封闭」「向上封闭」（Def 4.14 (b)(d)，Remark 4.15）在 [Closed2](Closed2.lagda.md)。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

open import OCF.Align.EboLean.OT.WO.Facts

module OCF.Align.EboLean.OT.WO.Closed (F : OTFacts) where

open OTFacts F

open import OCF.Align.EboLean.OT.Syntax
open import OCF.Align.EboLean.OT.Order
open import OCF.Align.EboLean.OT.Closure
open import OCF.Align.EboLean.OT.Arith
open import OCF.Align.EboLean.OT.BoolLemmas
open import OCF.Align.EboLean.OT.OTLemmas
open import OCF.Align.EboLean.OT.WO.K
open import OCF.Align.EboLean.OT.WO.Base
open import OCF.Align.EboLean.OT.WO.CLemmas
open import OCF.Align.EboLean.OT.WO.OrderLemmas F
open import OCF.Align.EboLean.OT.WO.Lemma47 F
open import OCF.Align.EboLean.OT.WO.Lemma413 F
open import OCF.Align.EboLean.OT.WO.Dist F

open import Level using (Level; _⊔_; 0ℓ)
open import Data.Bool.Base using (Bool; true; false; _∧_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

private variable
  ℓ ℓ′ : Level
  A B : Pred ℓ
```

## 0. 两个句法视图

正则基数的形状：`Ω′_{z+1}` 或 `I`；`Ω_z`（正规化）的三种结果。

```agda
data RegView : Reg → Set where
  succ  : ∀ z → RegView (ΩR (z ▹ phi zer zer))
  inacc : RegView IR

isZero-sound : ∀ {a} → isZero a ≡ true → a ≡ zer
isZero-sound {a = zer} _ = refl

regView : ∀ κ → isRR κ ≡ true → RegView κ
regView IR _ = inacc
regView (ΩR (z ▹ phi zer zer)) _ = succ z
regView (ΩR (z ▹ phi (_ ▹ _) _)) ()
regView (ΩR (z ▹ phi zer (_ ▹ _))) ()
regView (ΩR (z ▹ psi _ _)) ()
regView (ΩR (z ▹ Om _)) ()
regView (ΩR (z ▹ I)) ()
regView (ΩR zer) ()

data ΩView (z : Tm) : Set where
  Ω-0  : isZero z ≡ true → Ω z ≡ zer → ΩView z
  Ω-Fi : isFiT z ≡ true → Ω z ≡ z → ΩView z
  Ω-Om : isZero z ≡ false → isFiT z ≡ false → Ω z ≡ ⟨ Om z ⟩ → ΩView z

Ω-view : ∀ z → ΩView z
Ω-view z with isZero z in e₀
... | true = Ω-0 e₀ (if-true e₀)
... | false with isFiT z in e₁
...   | true  = Ω-Fi e₁ (trans (if-false e₀) (if-true e₁))
...   | false = Ω-Om e₀ e₁ (trans (if-false e₀) (if-false e₁))

-- 0 以下没有东西
¬≺0 : ∀ {z} → z ≺ zer → ⊥
¬≺0 {z} p = ≺⇒¬⪯ p (0⪯ z)
```

## 1. Definition 4.14

```agda
_≺C_ : Tm → Pred ℓ → Set ℓ
z ≺C C = ∃ λ c → C c × z ≺ c

Unb : Pred 0ℓ
Unb _ = ⊤

record WDC (A : Pred ℓ) : Set ℓ where          -- 弱向下封闭
  field
    wdc-+ : ∀ {b p} → NZ b → OT (b ▹ p) → A (b ▹ p) → A b × A ⟨ p ⟩
    wdc-φ : ∀ {b c} → OT ⟨ phi b c ⟩ → A ⟨ phi b c ⟩ → A b × A c
    wdc-Ω : ∀ {b} → OT ⟨ Om b ⟩ → A ⟨ Om b ⟩ → A b
    wdc-ψ : ∀ {κ c} → OT ⟨ psi κ c ⟩ → A ⟨ psi κ c ⟩ → A (κ⁻ κ)
open WDC public

record WUC (A : Pred ℓ) (P : Pred ℓ′) : Set (ℓ ⊔ ℓ′) where   -- 弱向上封闭，以 P 为界
  field
    wuc-+ : ∀ {b p} → NZ b → OT (b ▹ p) → P (b ▹ p) → A b → A ⟨ p ⟩ → A (b ▹ p)
    wuc-φ : ∀ {b c} → OT ⟨ phi b c ⟩ → P ⟨ phi b c ⟩ → A b → A c → A ⟨ phi b c ⟩
    wuc-Ω : ∀ {b} → OT ⟨ Om b ⟩ → P ⟨ Om b ⟩ → A b → A ⟨ Om b ⟩
    wuc-0 : P zer → A zer
    wuc-I : P I′ → A I′
open WUC public
```

守卫的单调性与 `A ∩ ↓ c` 的限制：

```agda
Mono : Pred ℓ → Set ℓ
Mono P = ∀ {w z} → w ⪯ z → P z → P w


≺a-mono : ∀ {a} → Mono (λ z → z ≺ a)
≺a-mono w⪯z z≺a = ⪯≺-trans w⪯z z≺a

WDC-restrict : ∀ {c d} → d ⪯ c → WDC (A ∩ ↓ c) → WDC (A ∩ ↓ d)
WDC-restrict {A = A} {c} {d} d⪯c w = record
  { wdc-+ = λ {b} {p} nz o (x , ox , x≺d) →
      let (l , r) = wdc-+ w nz o (x , ox , ≺⪯-trans x≺d d⪯c)
      in (proj₁ l , proj₁ (proj₂ l) , ≺-trans (≺-+ˡ nz o) x≺d)
       , (proj₁ r , proj₁ (proj₂ r) , ≺-trans (≺-+ʳ nz o) x≺d)
  ; wdc-φ = λ o (x , ox , x≺d) →
      let (l , r) = wdc-φ w o (x , ox , ≺⪯-trans x≺d d⪯c)
      in (proj₁ l , proj₁ (proj₂ l) , ≺-trans (≺-φˡ o) x≺d)
       , (proj₁ r , proj₁ (proj₂ r) , ≺-trans (≺-φʳ o) x≺d)
  ; wdc-Ω = λ o (x , ox , x≺d) →
      let l = wdc-Ω w o (x , ox , ≺⪯-trans x≺d d⪯c)
      in proj₁ l , proj₁ (proj₂ l) , ≺-trans (≺-Ω o) x≺d
  ; wdc-ψ = λ o (x , ox , x≺d) →
      let l = wdc-ψ w o (x , ox , ≺⪯-trans x≺d d⪯c)
      in proj₁ l , proj₁ (proj₂ l) , ⪯≺-trans (κ⁻⪯ψ o) x≺d
  }
```

## 2. Lemma 4.16 (a)：C^c(A)、τ^A(c)

`Ω_z ∈ C^c(A)` 从 `z ∈ C^c(A)`：

```agda
C-Ωz : ∀ {c z} → C c A z → C c A (Ω z)
C-Ωz {c = c} {z} cz with Ω-view z
... | Ω-0 _ e    = subst (C c _) (sym e) (c! OT-0 (here []))
... | Ω-Fi _ e   = subst (C c _) (sym e) cz
... | Ω-Om e₀ e₁ e = subst (C c _) (sym e) (C-Ω⁺ (OT-Ω⁺ (C⊆OT cz) e₁ e₀) cz)
```

`κ⁻ ∈ C^c(A)` 从 `κ ∈ C^c(A)`、`c ≺ κ`（κ ∈ R）——4.16 (a) 证明的 ψ 情形核心：

```agda
C-κ⁻ : ∀ {c κ} → WDC (A ∩ ↓ c) → isRR κ ≡ true → c ≺ regTm κ → C c A (regTm κ) → C c A (κ⁻ κ)
C-κ⁻ {c = c} {κ} w rκ c≺κ cκ with regView κ rκ
... | inacc  = c! OT-0 (here [])
... | succ zer = c! OT-0 (here [])
... | succ (z ▹ q) with C-Ω⁻ cκ
...   | inj₁ (_ , κ≺c) = ⊥-elim (≺-asym c≺κ κ≺c)
...   | inj₂ c₁ with C-+⁻ tt c₁
...     | inj₂ (cz , _) = C-Ωz cz
...     | inj₁ (z1∈A , z1≺c) =
          C-Ωz (A∩a⊆C (proj₁ (wdc-+ w tt (C⊆OT c₁) (z1∈A , C⊆OT c₁ , z1≺c))))
```

```agda
C-WDC : ∀ {c} → WDC (A ∩ ↓ c) → WDC (C c A)
C-WDC {A = A} {c} w = record
  { wdc-+ = λ {b} {p} nz o cx → case+ nz o cx (C-+⁻ nz cx)
  ; wdc-φ = λ o cx → caseφ o cx (C-φ⁻ cx)
  ; wdc-Ω = λ o cx → caseΩ o cx (C-Ω⁻ cx)
  ; wdc-ψ = λ o cx → caseψ o cx (C-ψ⁻ cx)
  }
  where
    case+ : ∀ {b p} → NZ b → OT (b ▹ p) → C c A (b ▹ p)
          → (A (b ▹ p) × (b ▹ p) ≺ c) ⊎ (C c A b × C c A ⟨ p ⟩) → C c A b × C c A ⟨ p ⟩
    case+ nz o cx (inj₂ r) = r
    case+ nz o cx (inj₁ (x∈A , x≺c)) =
      let (l , r) = wdc-+ w nz o (x∈A , o , x≺c) in A∩a⊆C l , A∩a⊆C r
    caseφ : ∀ {b d} → OT ⟨ phi b d ⟩ → C c A ⟨ phi b d ⟩
          → (A ⟨ phi b d ⟩ × ⟨ phi b d ⟩ ≺ c) ⊎ (C c A b × C c A d) → C c A b × C c A d
    caseφ o cx (inj₂ r) = r
    caseφ o cx (inj₁ (x∈A , x≺c)) =
      let (l , r) = wdc-φ w o (x∈A , o , x≺c) in A∩a⊆C l , A∩a⊆C r
    caseΩ : ∀ {b} → OT ⟨ Om b ⟩ → C c A ⟨ Om b ⟩
          → (A ⟨ Om b ⟩ × ⟨ Om b ⟩ ≺ c) ⊎ C c A b → C c A b
    caseΩ o cx (inj₂ r) = r
    caseΩ o cx (inj₁ (x∈A , x≺c)) = A∩a⊆C (wdc-Ω w o (x∈A , o , x≺c))
    caseψ : ∀ {κ d} → OT ⟨ psi κ d ⟩ → C c A ⟨ psi κ d ⟩
          → (A ⟨ psi κ d ⟩ × ⟨ psi κ d ⟩ ≺ c) ⊎ (c ≺ regTm κ × C c A (regTm κ) × C c A d)
          → C c A (κ⁻ κ)
    caseψ o cx (inj₁ (x∈A , x≺c)) = A∩a⊆C (wdc-ψ w o (x∈A , o , x≺c))
    caseψ o cx (inj₂ (c≺κ , cκ , _)) = C-κ⁻ w (proj₁ (proj₂ (proj₂ (OT-ψ⁻ o)))) c≺κ cκ

C-WUC : ∀ {c} → WUC (C c A) Unb
C-WUC = record
  { wuc-+ = λ nz o _ cb cp → C-+⁺ nz o cb cp
  ; wuc-φ = λ o _ cb cd → C-φ⁺ o cb cd
  ; wuc-Ω = λ o _ cb → C-Ω⁺ o cb
  ; wuc-0 = λ _ → c! OT-0 (here [])
  ; wuc-I = λ _ → c! OT-I (here [])
  }

τ-WDC′ : ∀ {c} → WDC (C c A) → WDC (τ A c)
τ-WDC′ {A = A} {c} w = record
  { wdc-+ = λ nz o (cx , x≺c) →
      let (l , r) = wdc-+ w nz o cx
      in (l , ≺-trans (≺-+ˡ nz o) x≺c) , (r , ≺-trans (≺-+ʳ nz o) x≺c)
  ; wdc-φ = λ o (cx , x≺c) →
      let (l , r) = wdc-φ w o cx
      in (l , ≺-trans (≺-φˡ o) x≺c) , (r , ≺-trans (≺-φʳ o) x≺c)
  ; wdc-Ω = λ o (cx , x≺c) → wdc-Ω w o cx , ≺-trans (≺-Ω o) x≺c
  ; wdc-ψ = λ o (cx , x≺c) → wdc-ψ w o cx , ⪯≺-trans (κ⁻⪯ψ o) x≺c
  }


C-WDC-tilde : A ⊆ M A → ∀ {x} → OT x → WDC (A ∩ ↓ (tilde x)) → WDC (C x A)
C-WDC-tilde {A = A} h {x} ox w = record
  { wdc-+ = λ nz o cx → let (l , r) = wdc-+ w′ nz o (to cx) in from l , from r
  ; wdc-φ = λ o cx → let (l , r) = wdc-φ w′ o (to cx) in from l , from r
  ; wdc-Ω = λ o cx → from (wdc-Ω w′ o (to cx))
  ; wdc-ψ = λ o cx → from (wdc-ψ w′ o (to cx))
  }
  where
    w′ : WDC (C (tilde x) A)
    w′ = C-WDC w
    to = proj₁ (C-tilde h ox)
    from = proj₂ (C-tilde h ox)

τ-WUC : ∀ {c} → WUC (τ A c) (λ z → z ≺ c)
τ-WUC = record
  { wuc-+ = λ nz o g (cb , _) (cp , _) → C-+⁺ nz o cb cp , g
  ; wuc-φ = λ o g (cb , _) (cd , _) → C-φ⁺ o cb cd , g
  ; wuc-Ω = λ o g (cb , _) → C-Ω⁺ o cb , g
  ; wuc-0 = λ g → c! OT-0 (here []) , g
  ; wuc-I = λ g → c! OT-I (here []) , g
  }
```

## 3. Lemma 4.16 (a)：W(A) ∩ a⁺、M(A) ∩ a⁺ 弱向下封闭

`x ∈ W(A)`，`x ≺ a⁺`：x ∈ C^x(A) ≅ C^x̃(A)，x̃ ⪯ ã，`A ∩ x̃` 弱向下封闭，故分量 y ∈ C^x̃(A) ≅ C^x(A)；y ≺ x 则 y ∈ τ^A(x) ⊆ W(A)（κ⁻ = x 时直接）。

```agda
module _ {A : Pred ℓ} (h : A ⊆ M A) {a : Tm} (oa : OT a) (w : WDC (A ∩ ↓ (tilde a))) where

  -- 分量落回 C^x(A)
  private
    Cx-WDC : ∀ {x} → OT x → x ≺ plus a → WDC (C x A)
    Cx-WDC ox x≺a⁺ = C-WDC-tilde h ox (WDC-restrict (≺plus⇒tilde⪯tilde ox oa x≺a⁺) w)

    down : ∀ {x y} → 𝒲 A x → x ≺ plus a → C x A y → y ⪯ x → (𝒲 A ∩ ↓ (plus a)) y
    down {x} {y} wx x≺a⁺ cy y⪯x with ⪯⇒≺⊎≡ y⪯x
    ... | inj₂ refl = wx , C⊆OT cy , x≺a⁺
    ... | inj₁ y≺x  = 𝒲-τ wx (cy , y≺x) , C⊆OT cy , ≺-trans y≺x x≺a⁺


  𝒲∩-WDC : WDC (𝒲 A ∩ ↓ (plus a))
  𝒲∩-WDC = record
    { wdc-+ = λ nz o (wx , ox , x≺a⁺) →
        let (l , r) = wdc-+ (Cx-WDC ox x≺a⁺) nz o (𝒲-M wx)
        in down wx x≺a⁺ l (≺⇒⪯ (≺-+ˡ nz o)) , down wx x≺a⁺ r (≺⇒⪯ (≺-+ʳ nz o))
    ; wdc-φ = λ o (wx , ox , x≺a⁺) →
        let (l , r) = wdc-φ (Cx-WDC ox x≺a⁺) o (𝒲-M wx)
        in down wx x≺a⁺ l (≺⇒⪯ (≺-φˡ o)) , down wx x≺a⁺ r (≺⇒⪯ (≺-φʳ o))
    ; wdc-Ω = λ o (wx , ox , x≺a⁺) →
        down wx x≺a⁺ (wdc-Ω (Cx-WDC ox x≺a⁺) o (𝒲-M wx)) (≺⇒⪯ (≺-Ω o))
    ; wdc-ψ = λ o (wx , ox , x≺a⁺) →
        down wx x≺a⁺ (wdc-ψ (Cx-WDC ox x≺a⁺) o (𝒲-M wx)) (κ⁻⪯ψ o)
    }

```

## 4. Lemma 4.17 (a) 与 Lemma 4.16 (b)

```agda
0∈𝒲 : 𝒲 A zer
0∈𝒲 = sup 0∈M (λ (_ , z≺0) → ⊥-elim (¬≺0 z≺0))
```

(b) `A ∩ k ⊑ W(A) ⟹ A ∩ k` 弱向下封闭。x ∈ A ∩ k ⊆ W(A) ⊆ M(A)，x ∈ C^x(A) 而 x ∉ A ∩ x，故分量在 C^x(A) ∩ x = τ^A(x) ⊆ W(A)|x ≅ (A ∩ k)|x。ψ 情形：π ∈ C^x(A)，π = Ω_{z+1}，z + 1 ∈ C^x(A)；若 z + 1 ≺ x 则 z + 1 ∈ A（同上），由 + 情形 z ∈ A ∩ x ⊆ C^x(A)；否则直接 z ∈ C^x(A)；于是 π⁻ = Ω_z ∈ C^x(A) ∩ x。

```agda
module _ {A : Pred ℓ} {k : Tm} (seg : (A ∩ ↓ k) ⊑ 𝒲 A) where

  private
    S = A ∩ ↓ k

    -- τ^A(x) 的元素落回 A ∩ k（x ∈ A ∩ k）
    back : ∀ {x y} → S x → C x A y → y ≺ x → S y
    back sx cy y≺x =
      proj₁ (proj₂ (proj₂ seg sx) (𝒲-τ (⊑⇒⊆ seg sx) (cy , y≺x) , ≺⇒⪯ y≺x))

    Mx : ∀ {x} → S x → M A x
    Mx sx = 𝒲-M (⊑⇒⊆ seg sx)

  L4-16b-+ : ∀ {b p} → NZ b → OT (b ▹ p) → S (b ▹ p) → S b × S ⟨ p ⟩
  L4-16b-+ nz o sx with C-+⁻ nz (Mx sx)
  ... | inj₁ (_ , x≺x) = ⊥-elim (≺-irrefl x≺x)
  ... | inj₂ (cb , cp) = back sx cb (≺-+ˡ nz o) , back sx cp (≺-+ʳ nz o)

  L4-16b-φ : ∀ {b c} → OT ⟨ phi b c ⟩ → S ⟨ phi b c ⟩ → S b × S c
  L4-16b-φ o sx with C-φ⁻ (Mx sx)
  ... | inj₁ (_ , x≺x) = ⊥-elim (≺-irrefl x≺x)
  ... | inj₂ (cb , cc) = back sx cb (≺-φˡ o) , back sx cc (≺-φʳ o)

  L4-16b-Ω : ∀ {b} → OT ⟨ Om b ⟩ → S ⟨ Om b ⟩ → S b
  L4-16b-Ω o sx with C-Ω⁻ (Mx sx)
  ... | inj₁ (_ , x≺x) = ⊥-elim (≺-irrefl x≺x)
  ... | inj₂ cb = back sx cb (≺-Ω o)

  private
    -- z + 1 ∈ C^x(A) ⟹ z ∈ C^x(A)（x ∈ A ∩ k）
    fromz1 : ∀ {x} → S x → ∀ z → C x A (z ▹ phi zer zer) → C x A z
    fromz1 sx zer      c₁ = c! OT-0 (here [])
    fromz1 sx (z′ ▹ q) c₁ with C-+⁻ tt c₁
    ... | inj₂ (cz′ , _)     = cz′
    ... | inj₁ (z1∈A , z1≺x) =
      let r = proj₁ (L4-16b-+ tt (C⊆OT c₁) (z1∈A , C⊆OT c₁ , ≺-trans z1≺x (proj₂ (proj₂ sx))))
      in A∩a⊆C (proj₁ r , proj₁ (proj₂ r) , ≺-trans (≺-+ˡ tt (C⊆OT c₁)) z1≺x)

    -- Ω_{z+1} ∈ C^x(A)，x ≺ Ω_{z+1} ⟹ z ∈ C^x(A)
    κz : ∀ {x} z → S x → x ≺ ⟨ Om (z ▹ phi zer zer) ⟩ → C x A ⟨ Om (z ▹ phi zer zer) ⟩ → C x A z
    κz z sx x≺κ cκ with C-Ω⁻ cκ
    ... | inj₁ (_ , κ≺x) = ⊥-elim (≺-asym x≺κ κ≺x)
    ... | inj₂ c₁        = fromz1 sx z c₁

  L4-16b-ψ : ∀ {κ c} → OT ⟨ psi κ c ⟩ → S ⟨ psi κ c ⟩ → S (κ⁻ κ)
  L4-16b-ψ {κ} {c} o sx with C-ψ⁻ (Mx sx)
  ... | inj₁ (_ , x≺x) = ⊥-elim (≺-irrefl x≺x)
  ... | inj₂ (x≺κ , cκ , _) with regView κ (proj₁ (proj₂ (proj₂ (OT-ψ⁻ o))))
  ...   | inacc  = proj₁ (proj₂ (proj₂ seg sx) (0∈𝒲 , 0⪯ _))
  ...   | succ z = back sx (C-Ωz (κz z sx x≺κ cκ)) (κ⁻≺ψ o)

  L4-16b : WDC S
  L4-16b = record { wdc-+ = L4-16b-+ ; wdc-φ = L4-16b-φ ; wdc-Ω = L4-16b-Ω ; wdc-ψ = L4-16b-ψ }
```
