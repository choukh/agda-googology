# Lemma 4.31：𝕎 对 Ω 封闭（I 以下）

> **EboLean 删节拷贝 (记号侧验收工作, 读 Setzer 的记号 OT_I).** 归档 `Mahlo.Inacc.WO.Lemma431` 的拷贝, 只改了模块名, 并删去了 EBO 路线 ([EboLean](../../../EboLean.lagda.md)) 用不到的定义 (由定义级切片判定, 删后从头编译核对). 讲解文字照旧, 可能提到已删的定义; 归档原文未动.

> **EboLean 删节.** 归档原文的 (b) 部分（ψ_I 0、ψ_I(x+1) ∈ 𝕎，`Bω`、`Ωⁿ∈𝕎`、模块 `ψI`）只为 I 层与 Γ-迭代服务，EBO 的 τ-像没有 ψ_I，已删去；同时删去它独用的 9 条句法事实字段（见 [Facts](Facts.lagda.md) 文首）。

Setzer [Se98] Lemma 4.31。

- (a) `∀x ∈ 𝕎 ∩ I. Ω_x ∈ 𝕎`：对 a ∈ 𝕎 归纳（Ag(𝕎)）。a ∈ Fi′ 时 Ω_a = a；否则 Ω′_a ∈ M(𝕎)，取 B := {(Ω_y)⁺ | y ∈ τ^𝕎(a)}（由归纳假设与 𝕎 对 ⁺ 封闭，B ⊆ 𝕎|Ω′_a），τ^𝕎(Ω′_a) 的每个 y 有 ỹ = Ω_c、c ∈ τ^𝕎(a)、y ≺ (Ω_c)⁺，Lemma 4.30 收尾。
- (b) `ψ_I 0 ∈ 𝕎`；`ψ_I x ∈ 𝕎 ⟹ ψ_I(x+1) ∈ 𝕎`：同样用 4.30，B := {Ωⁿ_{c+1} | n}（c := 0 或 ψ_I x），由 (a) 与 Fi′ 元素对 Ω、+1 封闭得 B ⊆ 𝕎|d；Remark 2.14 (i) 给 τ^𝕎(d) ⪯ B。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

open import OCF.Align.EboLean.OT.WO.Facts

module OCF.Align.EboLean.OT.WO.Lemma431 (F : OTFacts) where

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
open import OCF.Align.EboLean.OT.WO.Closed F
open import OCF.Align.EboLean.OT.WO.Closed2 F
open import OCF.Align.EboLean.OT.WO.CTilde F
open import OCF.Align.EboLean.OT.WO.Lemma47ef F
open import OCF.Align.EboLean.OT.WO.Lemma423 F
open import OCF.Align.EboLean.OT.WO.Union F
open import OCF.Align.EboLean.OT.WO.Lemma430 F

open import Level using (Level; _⊔_; 0ℓ; suc)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat.Base using (ℕ; zero)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; Σ)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
```

## 工具

```agda
-- 基数的形状：Ω′_c、ψ_I e、I
data CarView : Tm → Set where
  car-Ω  : ∀ c → CarView ⟨ Om c ⟩
  car-ψ  : ∀ e → CarView ⟨ psi IR e ⟩
  car-I  : CarView I′

carView : ∀ x → isCarT x ≡ true → CarView x
carView (zer ▹ Om c)     _ = car-Ω c
carView (zer ▹ psi IR e) _ = car-ψ e
carView (zer ▹ I)        _ = car-I
carView (zer ▹ psi (ΩR _) _) ()
carView (zer ▹ phi _ _) ()
carView zer ()
carView (_ ▹ _ ▹ _) ()

-- Ω y ⪯ Ω′_a（y ≺ a），故 (Ω y)⁺ ⪯ Ω′_a
Ωy⁺⪯Ω′ : ∀ {y a} → OT y → OT ⟨ Om a ⟩ → y ≺ a → plus (Ω y) ⪯ ⟨ Om a ⟩
Ωy⁺⪯Ω′ oy oa y≺a = plus-least (Ω-OT oy) oa refl (Ω≺Ω′ oy oa y≺a)

-- W(𝕎)|b 落回 𝕎（b ∈ 𝕎）
W→𝕎 : ∀ {b z} → 𝕎 b → 𝒲 𝕎 z → z ⪯ b → 𝕎 z
W→𝕎 b∈𝕎 w t = ⊑← (proj₂ Ag𝕎) b∈𝕎 w t

τ𝕎⊆𝕎 : ∀ {b} → 𝕎 b → τ 𝕎 b ⊆ 𝕎
τ𝕎⊆𝕎 b∈𝕎 t = W→𝕎 b∈𝕎 (𝒲-τ (𝕎⊆𝒲𝕎 b∈𝕎) t) (≺⇒⪯ (proj₂ t))
```

## (a)

```agda
𝕎-Ω : ∀ {a} → 𝕎 a → a ≺ I′ → 𝕎 (Ω a)
𝕎-Ω {a} a∈𝕎 a≺I = Ag-ind Ag𝕎 prog a∈𝕎 a≺I
  where
    prog : Prog 𝕎 (λ a → a ≺ I′ → 𝕎 (Ω a))
    prog {x = a} a∈𝕎 ih a≺I with Ω-view a
    ... | Ω-0 _ e      = subst 𝕎 (sym e) (0∈A a∈𝕎)
      where 0∈A = Ag423.0∈A Ag𝕎
    ... | Ω-Fi _ e     = subst 𝕎 (sym e) a∈𝕎
    ... | Ω-Om e₀ e₁ e = subst 𝕎 (sym e) (L430.L4-30 mΩ Ω≺I B cover B⊆)
      where
        oa : OT a
        oa = 𝕎⊆OT a∈𝕎
        oΩ : OT ⟨ Om a ⟩
        oΩ = OT-Ω⁺ oa e₁ e₀
        Ω≺I : ⟨ Om a ⟩ ≺ I′
        Ω≺I = subst (λ t → t ≺ I′) e (Fi-closed-Ω refl OT-I oa a≺I)
        a⪯Ω : a ⪯ ⟨ Om a ⟩
        a⪯Ω = ⪯-Ω oΩ
        -- Ω′_a ∈ M(𝕎)
        mΩ : M 𝕎 ⟨ Om a ⟩
        mΩ = C-Ω⁺ oΩ (A∩a⊆C (a∈𝕎 , oa , ≺-Ω oΩ))
        -- 见证集 A ∋ a；τ^𝕎(a) ≅ τ^A(a)（A 与 𝕎 在 a 以下一致），B 用 τ^A(a) 才是集合
        A : Pred 0ℓ
        A = proj₁ a∈𝕎
        agA : Ag A
        agA = proj₁ (proj₂ a∈𝕎)
        a∈A : A a
        a∈A = proj₂ (proj₂ a∈𝕎)
        A⊑𝕎 : A ⊑ 𝕎
        A⊑𝕎 = Ag⇒⊑𝕎 A agA
        CaA≅ : C a A ≅ C a 𝕎
        CaA≅ = C-cong (λ z≺a q → ⊑→ A⊑𝕎 a∈A q (≺⇒⪯ z≺a)) (λ z≺a w → ⊑← A⊑𝕎 a∈A w (≺⇒⪯ z≺a))
        -- B := {(Ω y)⁺ | y ∈ τ^A(a)}
        B : Pred 0ℓ
        B x = ∃ λ y → τ A a y × x ≡ plus (Ω y)
        B⊆ : B ⊆ (𝕎 ∣ ⟨ Om a ⟩)
        B⊆ (y , (cy , y≺a) , refl) =
          𝕎-plus (ih (τ𝕎⊆𝕎 a∈𝕎 (proj₁ CaA≅ cy , y≺a) , C⊆OT cy , y≺a) (≺-trans y≺a a≺I))
          , Ωy⁺⪯Ω′ (C⊆OT cy) oΩ y≺a
        -- τ^𝕎(Ω′_a) ⪯ B
        cover : ∀ {y} → τ 𝕎 ⟨ Om a ⟩ y → ∃ λ b → B b × y ⪯ b
        cover {y} t@(cy , y≺Ω) = plus (Ω c) , (c , (proj₂ CaA≅ cc , c≺a) , refl) , ≺⇒⪯ y≺Ωc⁺
          where
            oy : OT y
            oy = C⊆OT cy
            -- ỹ ∈ τ^𝕎(Ω′_a)
            tỹ : τ 𝕎 ⟨ Om a ⟩ (tilde y)
            tỹ = dc-tilde (Rem4-15.DC′ (τ-WDC′ (C-WDC-tilde 𝕎⊆M oΩ (WDC-∩↓ (Ag423.Ag-WDC Ag𝕎) _)))
                                       τ-WUC ≺a-mono proj₂)
                          oy t
            -- ỹ = Ω_c，c ∈ τ^𝕎(a)：按 ỹ ∈ Car′ ∪ {0} 的形状
            nz-a : NZ a
            nz-a = nz-of e₀
              where
                nz-of : ∀ {b} → isZero b ≡ false → NZ b
                nz-of {b = _ ▹ _} _ = tt
            0≺a : zer ≺ a
            0≺a = ⪯-sub⇒≺ (size-NZ a nz-a) (0⪯ a)
            -- τ^𝕎(Ω′_a) 的元素落进 C^a(𝕎)
            toCa : ∀ {z} → τ 𝕎 ⟨ Om a ⟩ z → C a 𝕎 z
            toCa (cz , _) = C-anti 𝕎⊆M oa oΩ a⪯Ω cz
            pick : ∃ λ c → C a 𝕎 c × c ≺ a × Ω c ≡ tilde y
            pick with tilde y in eỹ | tilde-Car oy | tỹ
            ... | ỹ | inj₂ e0 | _ = zer , c! OT-0 (here []) , 0≺a , sym e0
            ... | ỹ | inj₁ ca | tỹ′ = byCar (carView ỹ ca) tỹ′
              where
                -- Fi′ 的元素 ≺ Ω′_a ⟹ ⪯ a，且 ≠ a（a ∉ Fi′）
                fi≺a : ∀ {z} → isFiT z ≡ true → OT z → z ≺ ⟨ Om a ⟩ → z ≺ a
                fi≺a {z} fz oz z≺Ω with ⪯⇒≺⊎≡ (Fi≺Ω⇒⪯ fz oz oΩ z≺Ω)
                ... | inj₁ q = q
                ... | inj₂ refl = ⊥-elim (true≢false (trans (sym fz) e₁))
                byCar : ∀ {ỹ} → CarView ỹ → τ 𝕎 ⟨ Om a ⟩ ỹ → ∃ λ c → C a 𝕎 c × c ≺ a × Ω c ≡ ỹ
                byCar (car-Ω c) t@(cỹ , ỹ≺Ω) =
                  c , toCa tc , Ω-mono⁻ (C⊆OT cỹ) oΩ ỹ≺Ω , eqΩ
                  where
                    tc : τ 𝕎 ⟨ Om a ⟩ c
                    tc = wdc-Ω (τ-WDC′ (C-WDC-tilde 𝕎⊆M oΩ (WDC-∩↓ (Ag423.Ag-WDC Ag𝕎) _))) (C⊆OT cỹ) t
                    eqΩ : Ω c ≡ ⟨ Om c ⟩
                    eqΩ = trans (if-false (proj₂ (proj₂ (OT-Ω⁻ (C⊆OT cỹ))))) (if-false (proj₁ (proj₂ (OT-Ω⁻ (C⊆OT cỹ)))))
                byCar (car-ψ e) t@(cỹ , ỹ≺Ω) =
                  ⟨ psi IR e ⟩ , toCa t , fi≺a refl (C⊆OT cỹ) ỹ≺Ω , refl
                byCar car-I t@(cỹ , ỹ≺Ω) =
                  I′ , toCa t , fi≺a refl OT-I ỹ≺Ω , refl
            c = proj₁ pick
            cc = proj₁ (proj₂ pick)
            c≺a = proj₁ (proj₂ (proj₂ pick))
            y≺Ωc⁺ : y ≺ plus (Ω c)
            y≺Ωc⁺ = subst (λ t → y ≺ t) (cong plus (sym (proj₂ (proj₂ (proj₂ pick))))) (x≺plus-tilde oy)
```

## (b)

```agda
-- 0 + 1 = 1

one∈𝕎 : ∀ {c} → 𝕎 c → 𝕎 one
one∈𝕎 {c} c∈𝕎 = wuc-φ (wuc 𝕎-UC) OT-one (plus c , 𝕎-plus c∈𝕎 , one≺c⁺) 0∈𝕎 0∈𝕎
  where
    0∈𝕎 = Ag423.0∈A Ag𝕎 c∈𝕎
    one≺c⁺ : one ≺ plus c
    one≺c⁺ = Car-closed-+1 (plus-Car (𝕎⊆OT c∈𝕎)) (plus-OT (𝕎⊆OT c∈𝕎)) OT-0 (0≺Car (plus-Car (𝕎⊆OT c∈𝕎)))
      where
        0≺Car : ∀ {κ} → isCarT κ ≡ true → zer ≺ κ
        0≺Car {κ} cκ with carView κ cκ
        ... | car-Ω c = ⪯-sub⇒≺ (Data.Nat.Base.s≤s (Data.Nat.Base.s≤s Data.Nat.Base.z≤n)) (0⪯ _)
        ... | car-ψ e = ⪯-sub⇒≺ (Data.Nat.Base.s≤s (Data.Nat.Base.s≤s Data.Nat.Base.z≤n)) (0⪯ _)
        ... | car-I   = ⪯-sub⇒≺ (Data.Nat.Base.s≤s (Data.Nat.Base.s≤s Data.Nat.Base.z≤n)) (0⪯ _)

-- 0 ∈ 𝕎：{0} 是突出集
0∈𝕎 : 𝕎 zer
0∈𝕎 = Z , agZ , refl
  where
    Z : Pred 0ℓ
    Z x = x ≡ zer
    agZ : Ag Z
    agZ = (λ { refl → OT-0 }) , (λ { refl → OT-0 })
        , λ { refl → (λ { (refl , t) → 0∈𝒲 , t }) , (λ (w , t) → ⪯0⇒≡0 t , t) }

-- x + 1 的两种形状
x+1-view : ∀ x → OT x → (x ≡ zer × x + one ≡ one) ⊎ (NZ x × x + one ≡ x ▹ phi zer zer)
x+1-view zer     _  = inj₁ (refl , refl)
x+1-view (a ▹ p) ox = inj₂ (tt , +one (a ▹ p) tt ox)

```
