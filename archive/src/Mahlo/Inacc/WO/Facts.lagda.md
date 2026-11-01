# 良序证明所需的句法事实：Setzer [Se98] Assumption 4.3 的显式化

Setzer 在 §4 开头（Assumption 4.3）说：假定 §2 里定义的每个原始递归集合与函数在 Martin-Löf 类型论里有对应物，**且同样的引理成立**——即 Lemma 2.4（≺′ 是线序，"easy, but tedious"）、Remark 2.12、2.14、2.15。原文没有列出 §4 究竟用了哪几条。这里把它们收进一个记录：§4 的每个模块以 `(F : OTFacts)` 为参数，**用到什么就加什么字段**；最后由句法模块（P1／P2）构造这个记录，端点定理才算无条件成立。

纪律：字段只许是关于 `Tm`／`lt`／`isOT`／Def 2.10–2.13 函数的**可判定**陈述，绝不涉及 `𝒲`、`Acc`、类。这样记录不是公设——它是一张待办清单，每条都能用有限的情形分析证。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

module Mahlo.Inacc.WO.Facts where

open import Mahlo.Inacc.Syntax
open import Mahlo.Inacc.Order
open import Mahlo.Inacc.Closure
open import Mahlo.Inacc.Arith

open import Data.Bool.Base using (Bool; true; false)
open import Data.Sum.Base using (_⊎_)
open import Data.Product using (_×_; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary.Negation.Core using (¬_)

record OTFacts : Set where
  field
    -- Lemma 2.4：≺′ 是 T′ 上的线序
    ≺-irrefl : ∀ {x} → ¬ (x ≺ x)
    ≺-trans  : ∀ {x y z} → x ≺ y → y ≺ z → x ≺ z
    ≺-trich  : ∀ x y → x ≺ y ⊎ x ≡ y ⊎ y ≺ x
    0⪯       : ∀ x → zer ⪯ x                                  -- (≺′1)

    -- Remark 2.12 (h)：子项不超过整项（和的前缀／后缀一般形式）
    ⪯-prefix : ∀ {y z} → NZ z → OT (app y z) → y ⪯ app y z
    ⪯-app    : ∀ {y z} → NZ y → NZ z → OT (app y z) → z ⪯ app y z
    ⪯-φˡ : ∀ {b c} → OT ⟨ phi b c ⟩ → b ⪯ ⟨ phi b c ⟩
    ⪯-φʳ : ∀ {b c} → OT ⟨ phi b c ⟩ → c ⪯ ⟨ phi b c ⟩
    ⪯-Ω  : ∀ {b} → OT ⟨ Om b ⟩ → b ⪯ ⟨ Om b ⟩
    ψ≺κ  : ∀ {κ c} → OT ⟨ psi κ c ⟩ → ⟨ psi κ c ⟩ ≺ regTm κ   -- (≺′6)(≺′8)
    κ⁻≺ψ : ∀ {b c} → OT ⟨ psi (ΩR b) c ⟩ → κ⁻ (ΩR b) ≺ ⟨ psi (ΩR b) c ⟩   -- κ ≠ I 时 κ⁻ ≺ ψ_κ c
    κ⁻≺κ : ∀ {κ} → isRR κ ≡ true → OT (regTm κ) → κ⁻ κ ≺ regTm κ
    one⪯P : ∀ {p} → OT ⟨ p ⟩ → one ⪯ ⟨ p ⟩                     -- 1 是最小的非零项

    -- 序的几条结构性质（Lemma 4.17 (b) 用）
    -- b ≺ d ≺ b + c ⟹ d = b + d′，0 ≺ d′ ≺ c
    between-app : ∀ {b c d} → NZ b → NZ c → OT (app b c) → OT d → b ≺ d → d ≺ app b c
                → ∃ λ d′ → d ≡ app b d′ × NZ d′ × d′ ≺ c
    -- Remark 2.12 (f)：Veblen 比较（(≺′3) 的读出）
    φ-cmp : ∀ {b c d₁ d₂} → OT ⟨ phi b c ⟩ → OT ⟨ phi d₁ d₂ ⟩ → ⟨ phi d₁ d₂ ⟩ ≺ ⟨ phi b c ⟩
          → (d₁ ≺ b × d₂ ≺ ⟨ phi b c ⟩) ⊎ (d₁ ≡ b × d₂ ≺ c) ⊎ (b ≺ d₁ × ⟨ phi d₁ d₂ ⟩ ⪯ c)
    -- (≺′4)：d ∈ G′，max{b,c} ≺ d ⟹ φ′_b c ≺ d
    φ≺G : ∀ {b c d} → isGT d ≡ true → OT d → OT ⟨ phi b c ⟩ → b ≺ d → c ≺ d → ⟨ phi b c ⟩ ≺ d
    -- (≺′7)(≺′11)：Fi′ 的元素落在 Ω′_b 之下就落在 b 之下（含）
    Fi≺Ω⇒⪯ : ∀ {y b} → isFiT y ≡ true → OT y → OT ⟨ Om b ⟩ → y ≺ ⟨ Om b ⟩ → y ⪯ b
    -- Remark 2.12 (g)：(≺′9)
    Ω-mono⁻ : ∀ {y b} → OT ⟨ Om y ⟩ → OT ⟨ Om b ⟩ → ⟨ Om y ⟩ ≺ ⟨ Om b ⟩ → y ≺ b
    -- (≺′6)：ψ_{Ω_z} c ≺ d ∈ Car′ ⟹ Ω_z ⪯ d
    ψ≺Car⇒κ⪯ : ∀ {z c d} → isCarT d ≡ true → OT ⟨ psi (ΩR z) c ⟩ → OT d
             → ⟨ psi (ΩR z) c ⟩ ≺ d → ⟨ Om z ⟩ ⪯ d

    -- Remark 2.15 (c)：u ≺ κ ⟹ (u ∈ C̃_κ(a) ⟺ u ≺ ψ_κ a)——坍缩函数定义的核心
    C̃⇒≺ψ : ∀ {κ a u} → OT ⟨ psi κ a ⟩ → OT u → u ≺ regTm κ → inC̃ κ a u ≡ true → u ≺ ⟨ psi κ a ⟩
    ≺ψ⇒C̃ : ∀ {κ a u} → OT ⟨ psi κ a ⟩ → OT u → u ≺ ⟨ psi κ a ⟩ → inC̃ κ a u ≡ true
    -- Remark 2.15 (d)(e)：ψ_π d ∈ C̃_κ(a) 的分解（κ = I 与 κ = Ω′_z 两种）
    C̃-ψ-I : ∀ {π d a} → OT ⟨ psi π d ⟩ → OT ⟨ psi IR a ⟩ → inC̃ IR a ⟨ psi π d ⟩ ≡ true
           → ⟨ psi π d ⟩ ≺ ⟨ psi IR a ⟩
           ⊎ (inC̃ IR a (regTm π) ≡ true × inC̃ IR a d ≡ true × d ≺ a)
    C̃-ψ-Ω : ∀ {π d z a} → OT ⟨ psi π d ⟩ → OT ⟨ psi (ΩR z) a ⟩ → inC̃ (ΩR z) a ⟨ psi π d ⟩ ≡ true
           → ⟨ psi π d ⟩ ⪯ κ⁻ (ΩR z)
           ⊎ (inC̃ (ΩR z) a (regTm π) ≡ true × inC̃ (ΩR z) a d ≡ true × d ≺ a)
    -- (≺′5)：ψ_I b ≺ ψ_I d ⟹ b ≺ d
    ψI-cmp : ∀ {b d} → OT ⟨ psi IR b ⟩ → OT ⟨ psi IR d ⟩ → ⟨ psi IR b ⟩ ≺ ⟨ psi IR d ⟩ → b ≺ d
    -- κ⁻ 是 κ = Ω′_z（z ∈ Suc′）以下最大的基数
    Car≺κ⇒⪯κ⁻ : ∀ {c z} → OT c → isCarT c ≡ true → isRR (ΩR z) ≡ true → OT ⟨ Om z ⟩
               → c ≺ ⟨ Om z ⟩ → c ⪯ κ⁻ (ΩR z)
    -- (κ⁻)⁺ = κ；(τ⁺)⁻ = τ
    plus-κ⁻ : ∀ {z} → isRR (ΩR z) ≡ true → OT ⟨ Om z ⟩ → plus (κ⁻ (ΩR z)) ≡ ⟨ Om z ⟩
    κ⁻∘plus : ∀ {τ z} → isCarT τ ≡ true → OT τ → plus τ ≡ ⟨ Om z ⟩ → κ⁻ (ΩR z) ≡ τ

    -- Remark 2.12 (a)：OT 对函数封闭
    +-OT : ∀ {x y} → OT x → OT y → OT (x + y)
    φ-OT : ∀ {x y} → OT x → OT y → OT (φ x y)

    -- Def 2.13 / Remark 2.14：ã 是 a 以下（含）最大的基数（或 0）
    tilde-OT   : ∀ {x} → OT x → OT (tilde x)
    tilde⪯     : ∀ {x} → OT x → tilde x ⪯ x                   -- 2.14 (f)
    tilde-Car  : ∀ {x} → OT x → isCarT (tilde x) ≡ true ⊎ tilde x ≡ zer
    tilde-max  : ∀ {x κ} → OT x → OT κ → isCarT κ ≡ true → κ ⪯ x → κ ⪯ tilde x
    tilde-idem : ∀ {x} → OT x → tilde (tilde x) ≡ tilde x

    -- Def 2.13 / Remark 2.14：a⁺ 是 a 之上最小的基数
    plus-OT    : ∀ {x} → OT x → OT (plus x)
    ≺plus      : ∀ {x} → OT x → x ≺ plus x                   -- 2.14 (f)
    plus-Car   : ∀ {x} → OT x → isCarT (plus x) ≡ true
    plus-least : ∀ {x κ} → OT x → OT κ → isCarT κ ≡ true → x ≺ κ → plus x ⪯ κ

    -- Remark 2.14 (e)(f)：x̃⁺ = x⁺；x⁺ = Ω′_{y+1} 且 Ω_y = x̃；x^{−Fi} ⪯ x
    tilde-plus : ∀ {x} → OT x → plus (tilde x) ≡ plus x
    plus-form  : ∀ {x} → OT x → ∃ λ y → plus x ≡ ⟨ Om (y ▹ phi zer zer) ⟩ × Ω y ≡ tilde x
    mFi⪯       : ∀ {x} → OT x → mFi x ⪯ x

    -- 正则基数在 Ω₁ 之上
    Ω₁⪯R : ∀ {κ} → OT (regTm κ) → isRR κ ≡ true → Ω₁ ⪯ regTm κ

    -- Ω 的比较；Fi′ 的元素（含 I）对 Ω 与 +1 封闭（Lemma 4.31 用）
    Ω≺Ω′        : ∀ {y a} → OT y → OT ⟨ Om a ⟩ → y ≺ a → Ω y ≺ ⟨ Om a ⟩
    Fi-closed-Ω : ∀ {f y} → isFiT f ≡ true → OT f → OT y → y ≺ f → Ω y ≺ f
    Car-closed-+1 : ∀ {κ y} → isCarT κ ≡ true → OT κ → OT y → y ≺ κ → y + one ≺ κ
    +1-mono     : ∀ {x y} → OT x → OT y → x ⪯ y → x + one ⪯ y + one
    Ωⁿ-mono     : ∀ {x y} n → OT x → OT y → x ⪯ y → Ωⁿ x n ⪯ Ωⁿ y n
    Ωⁿ-OT       : ∀ {x} n → OT x → OT (Ωⁿ x n)
    -- Remark 2.14 (g)(i)：x^{−Fi} 的形状；x ≺ Ωⁿ_{x^{−Fi}+1}
    mFi-Fi      : ∀ {x} → OT x → isFiT (mFi x) ≡ true ⊎ mFi x ≡ zer
    mFi-OT      : ∀ {x} → OT x → OT (mFi x)
    ψI0-least   : ∀ {z} → isFiT z ≡ true → OT z → ⟨ psi IR zer ⟩ ⪯ z
    Fi≺ψI+1⇒⪯  : ∀ {z x} → isFiT z ≡ true → OT z → OT ⟨ psi IR (x + one) ⟩
                → z ≺ ⟨ psi IR (x + one) ⟩ → z ⪯ ⟨ psi IR x ⟩
    Ωⁿ-bound    : ∀ {x} → OT x → x ≺ I′ → ∃ λ n → x ≺ Ωⁿ (mFi x + one) n
    -- ψ_κ 单调（(≺′5) 第一支）
    ψκ-mono     : ∀ {κ b c} → OT ⟨ psi κ b ⟩ → OT ⟨ psi κ c ⟩ → b ≺ c → ⟨ psi κ b ⟩ ≺ ⟨ psi κ c ⟩
    ψI-mono     : ∀ {b c} → OT ⟨ psi IR b ⟩ → OT ⟨ psi IR c ⟩ → b ≺ c → ⟨ psi IR b ⟩ ≺ ⟨ psi IR c ⟩
    -- b + 1 是 b 之上最小的项
    +1-least    : ∀ {b c} → OT b → OT c → b ≺ c → b + one ⪯ c
    -- Remark 2.14 (g)：ψ_I 0 ⪯ x ≺ I 时 x^{−Fi} = ψ_I b，x^{+Fi} = ψ_I(b+1)，x^{−Fi} ⪯ x ≺ x^{+Fi}
    Fi-form     : ∀ {x} → OT x → ⟨ psi IR zer ⟩ ⪯ x → x ≺ I′
                → ∃ λ b → OT ⟨ psi IR b ⟩ × mFi x ≡ ⟨ psi IR b ⟩ × pFi x ≡ ⟨ psi IR (b + one) ⟩
                        × x ≺ ⟨ psi IR (b + one) ⟩
    -- x ≺ ψ_I 0 时 x^{+Fi} = ψ_I 0
    pFi-0       : ∀ {x} → OT x → x ≺ ⟨ psi IR zer ⟩ → pFi x ≡ ⟨ psi IR zer ⟩
```
