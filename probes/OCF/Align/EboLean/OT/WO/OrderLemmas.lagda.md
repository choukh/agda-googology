# 从 `OTFacts` 导出的序引理

> **EboLean 删节拷贝 (记号侧验收工作, 读 Setzer 的记号 OT_I).** 归档 `Mahlo.Inacc.WO.OrderLemmas` 的拷贝, 只改了模块名, 并删去了 EBO 路线 ([EboLean](../../../EboLean.lagda.md)) 用不到的定义 (由定义级切片判定, 删后从头编译核对). 讲解文字照旧, 可能提到已删的定义; 归档原文未动.

线序的常用推论：⪯ 的传递、反对称、全性，≺ 与 ⪯ 的混合传递，「不小于即大于等于」。全部由 `≺-irrefl`、`≺-trans`、`≺-trich` 推出。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

open import OCF.Align.EboLean.OT.WO.Facts

module OCF.Align.EboLean.OT.WO.OrderLemmas (F : OTFacts) where

open OTFacts F

open import OCF.Align.EboLean.OT.Syntax
open import OCF.Align.EboLean.OT.Order
open import OCF.Align.EboLean.OT.Closure
open import OCF.Align.EboLean.OT.Arith
open import OCF.Align.EboLean.OT.BoolLemmas

open import Data.Bool.Base using (Bool; true; false)
open import Data.Product using (_×_; _,_)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import OCF.Align.EboLean.OT.BoolLemmas using (true≢false)
open import Relation.Nullary.Negation.Core using (¬_)

⪯-trans : ∀ {x y z} → x ⪯ y → y ⪯ z → x ⪯ z
⪯-trans p q with ⪯⇒≺⊎≡ p | ⪯⇒≺⊎≡ q
... | inj₁ p′  | inj₁ q′  = ≺⇒⪯ (≺-trans p′ q′)
... | inj₁ p′  | inj₂ refl = ≺⇒⪯ p′
... | inj₂ refl | _        = q

≺⪯-trans : ∀ {x y z} → x ≺ y → y ⪯ z → x ≺ z
≺⪯-trans p q with ⪯⇒≺⊎≡ q
... | inj₁ q′  = ≺-trans p q′
... | inj₂ refl = p

⪯≺-trans : ∀ {x y z} → x ⪯ y → y ≺ z → x ≺ z
⪯≺-trans p q with ⪯⇒≺⊎≡ p
... | inj₁ p′  = ≺-trans p′ q
... | inj₂ refl = q

≺-asym : ∀ {x y} → x ≺ y → ¬ (y ≺ x)
≺-asym p q = ≺-irrefl (≺-trans p q)

≺⇒¬⪯ : ∀ {x y} → x ≺ y → ¬ (y ⪯ x)
≺⇒¬⪯ p q = ≺-irrefl (≺⪯-trans p q)

⪯-antisym : ∀ {x y} → x ⪯ y → y ⪯ x → x ≡ y
⪯-antisym p q with ⪯⇒≺⊎≡ p
... | inj₂ e = e
... | inj₁ p′ = ⊥-elim (≺⇒¬⪯ p′ q)

⪯-total : ∀ x y → x ⪯ y ⊎ y ⪯ x
⪯-total x y with ≺-trich x y
... | inj₁ p        = inj₁ (≺⇒⪯ p)
... | inj₂ (inj₁ e) = inj₁ (≡⇒⪯ e)
... | inj₂ (inj₂ p) = inj₂ (≺⇒⪯ p)

¬≺⇒⪰ : ∀ {x y} → ¬ (x ≺ y) → y ⪯ x
¬≺⇒⪰ {x} {y} n with ≺-trich x y
... | inj₁ p        = ⊥-elim (n p)
... | inj₂ (inj₁ e) = ≡⇒⪯ (sym e)
... | inj₂ (inj₂ p) = ≺⇒⪯ p


≺-or-⪰ : ∀ x y → x ≺ y ⊎ y ⪯ x
≺-or-⪰ x y with ≺-trich x y
... | inj₁ p        = inj₁ p
... | inj₂ (inj₁ e) = inj₂ (≡⇒⪯ (sym e))
... | inj₂ (inj₂ p) = inj₂ (≺⇒⪯ p)

⪯0⇒≡0 : ∀ {x} → x ⪯ zer → x ≡ zer
⪯0⇒≡0 {x} p = ⪯-antisym p (0⪯ x)
```

## ã 的推论

`ã ⪯ b ⪯ a ⟹ b̃ = ã`（Lemma 4.9 (e) 与 4.7 (a) 用）。

```agda
tilde-between : ∀ {a b} → OT a → OT b → tilde a ⪯ b → b ⪯ a → tilde b ≡ tilde a
tilde-between {a} {b} oa ob p q with tilde-Car oa | tilde-Car ob
... | inj₁ ca | inj₁ cb =
  ⪯-antisym (tilde-max oa (tilde-OT ob) cb (⪯-trans (tilde⪯ ob) q))
            (tilde-max ob (tilde-OT oa) ca p)
... | inj₁ ca | inj₂ eb =
  -- b̃ = 0：ã ⪯ b 且 ã ∈ Car ⟹ ã ⪯ b̃ = 0 ⟹ ã = 0
  trans eb (sym (⪯0⇒≡0 (subst (λ z → tilde a ⪯ z) eb (tilde-max ob (tilde-OT oa) ca p))))
... | inj₂ ea | inj₁ cb =
  -- ã = 0：b̃ ⪯ b ⪯ a，b̃ ∈ Car ⟹ b̃ ⪯ ã = 0
  trans (⪯0⇒≡0 (subst (λ z → tilde b ⪯ z) ea (tilde-max oa (tilde-OT ob) cb (⪯-trans (tilde⪯ ob) q)))) (sym ea)
... | inj₂ ea | inj₂ eb = trans eb (sym ea)
```

## ã、a⁺ 的更多推论

```agda
tilde-mono : ∀ {x y} → OT x → OT y → x ⪯ y → tilde x ⪯ tilde y
tilde-mono {x} {y} ox oy p with tilde-Car ox
... | inj₁ cx = tilde-max oy (tilde-OT ox) cx (⪯-trans (tilde⪯ ox) p)
... | inj₂ ex = subst (λ z → z ⪯ tilde y) (sym ex) (0⪯ (tilde y))

-- y ≺ c⁺ ⟹ ỹ ⪯ c
≺plus⇒tilde⪯ : ∀ {y c} → OT y → OT c → y ≺ plus c → tilde y ⪯ c
≺plus⇒tilde⪯ {y} {c} oy oc p with tilde-Car oy
... | inj₂ ey = subst (λ z → z ⪯ c) (sym ey) (0⪯ c)
... | inj₁ cy with ≺-or-⪰ c (tilde y)
...   | inj₂ q = q
...   | inj₁ c≺ỹ = ⊥-elim (≺⇒¬⪯ p (⪯-trans (plus-least oc (tilde-OT oy) cy c≺ỹ) (tilde⪯ oy)))

-- x ⪯ c ⟹ x ≺ c⁺

Car≺plus⇒⪯ : ∀ {a c} → OT a → OT c → isCarT a ≡ true → a ≺ plus c → a ⪯ c
Car≺plus⇒⪯ oa oc ca p = ¬≺⇒⪰ (λ c≺a → ≺⇒¬⪯ p (plus-least oc oa ca c≺a))

-- x ≺ x̃⁺
x≺plus-tilde : ∀ {x} → OT x → x ≺ plus (tilde x)
x≺plus-tilde {x} ox = subst (λ t → x ≺ t) (sym (tilde-plus ox)) (≺plus {x} ox)

-- x^{−I} ⪯ x
mI⪯ : ∀ {x} → OT x → mI x ⪯ x
mI⪯ {x} ox with lt x I′ in e
... | true  = 0⪯ x
... | false = ¬≺⇒⪰ (λ (lt! q) → true≢false (trans (sym q) e))

-- y ≺ c⁺ ⟹ ỹ ⪯ c̃
≺plus⇒tilde⪯tilde : ∀ {y c} → OT y → OT c → y ≺ plus c → tilde y ⪯ tilde c
≺plus⇒tilde⪯tilde {y} {c} oy oc p =
  subst (λ z → z ⪯ tilde c) (tilde-idem oy) (tilde-mono (tilde-OT oy) oc (≺plus⇒tilde⪯ oy oc p))
```

## 子项严格小于整项

`⪯` 事实加「大小不同 ⟹ 不相等」给出 `≺`。

```agda
open import Data.Nat.Base using (ℕ; suc; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (m≤m+n; m≤n+m; ≤-trans; +-monoˡ-≤; +-mono-≤; <-irrefl; m<m+n; n≤1+n)

size≢⇒≢ : ∀ {s t} → size s < size t → ¬ (s ≡ t)
size≢⇒≢ p refl = <-irrefl refl p

⪯-sub⇒≺ : ∀ {s t} → size s < size t → s ⪯ t → s ≺ t
⪯-sub⇒≺ lt p with ⪯⇒≺⊎≡ p
... | inj₁ q = q
... | inj₂ e = ⊥-elim (size≢⇒≢ lt e)

size≥1 : ∀ a → 1 ≤ size a
size≥1 zer = s≤s z≤n
size≥1 (a ▹ p) = ≤-trans (size≥1 a) (m≤m+n (size a) (sizeP p))

sizeP≥1 : ∀ p → 1 ≤ sizeP p
sizeP≥1 (phi _ _) = s≤s z≤n
sizeP≥1 (psi _ _) = s≤s z≤n
sizeP≥1 (Om _) = s≤s z≤n
sizeP≥1 I = s≤s z≤n

size-NZ : ∀ b → NZ b → 1 < size b
size-NZ (a ▹ p) _ = +-mono-≤ (size≥1 a) (sizeP≥1 p)

size-▹ˡ : ∀ b p → size b < size (b ▹ p)
size-▹ˡ b p = m<m+n (size b) (sizeP≥1 p)

size-▹ʳ : ∀ b p → NZ b → size ⟨ p ⟩ < size (b ▹ p)
size-▹ʳ b p nz = +-monoˡ-≤ (sizeP p) (size-NZ b nz)

size-φˡ : ∀ b c → size b < size ⟨ phi b c ⟩
size-φˡ b c = s≤s (≤-trans (n≤1+n (size b)) (m≤m+n (suc (size b)) (size c)))

size-φʳ : ∀ b c → size c < size ⟨ phi b c ⟩
size-φʳ b c = s≤s (m≤n+m (size c) (suc (size b)))

size-Ω : ∀ b → size b < size ⟨ Om b ⟩
size-Ω b = s≤s (n≤1+n (size b))

-- 和的末分量拆分（⪯-prefix／⪯-app 的实例）
⪯-+ˡ : ∀ {a q p} → OT (a ▹ q ▹ p) → (a ▹ q) ⪯ (a ▹ q ▹ p)
⪯-+ˡ {a} {q} {p} o = ⪯-prefix {y = a ▹ q} {z = ⟨ p ⟩} tt o

⪯-+ʳ : ∀ {a q p} → OT (a ▹ q ▹ p) → ⟨ p ⟩ ⪯ (a ▹ q ▹ p)
⪯-+ʳ {a} {q} {p} o = ⪯-app {y = a ▹ q} {z = ⟨ p ⟩} tt tt o

size-ψc : ∀ κ c → size c < size ⟨ psi κ c ⟩
size-ψc κ c = s≤s (m≤n+m (size c) (suc (sizeR κ)))

size-ψκ : ∀ z c → size ⟨ Om z ⟩ < size ⟨ psi (ΩR z) c ⟩
size-ψκ z c = s≤s (m≤m+n (suc (suc (size z))) (size c))


≺-+ˡ : ∀ {b p} → NZ b → OT (b ▹ p) → b ≺ (b ▹ p)
≺-+ˡ {b = a ▹ q} {p} _ o = ⪯-sub⇒≺ (size-▹ˡ (a ▹ q) p) (⪯-+ˡ o)

≺-+ʳ : ∀ {b p} → NZ b → OT (b ▹ p) → ⟨ p ⟩ ≺ (b ▹ p)
≺-+ʳ {b = a ▹ q} {p} nz o = ⪯-sub⇒≺ (size-▹ʳ (a ▹ q) p nz) (⪯-+ʳ o)

≺-φˡ : ∀ {b c} → OT ⟨ phi b c ⟩ → b ≺ ⟨ phi b c ⟩
≺-φˡ {b} {c} o = ⪯-sub⇒≺ (size-φˡ b c) (⪯-φˡ o)

≺-φʳ : ∀ {b c} → OT ⟨ phi b c ⟩ → c ≺ ⟨ phi b c ⟩
≺-φʳ {b} {c} o = ⪯-sub⇒≺ (size-φʳ b c) (⪯-φʳ o)

≺-Ω : ∀ {b} → OT ⟨ Om b ⟩ → b ≺ ⟨ Om b ⟩
≺-Ω {b} o = ⪯-sub⇒≺ (size-Ω b) (⪯-Ω o)

-- κ⁻ ⪯ ψ_κ c（κ = I 时 κ⁻ = 0）
κ⁻⪯ψ : ∀ {κ c} → OT ⟨ psi κ c ⟩ → κ⁻ κ ⪯ ⟨ psi κ c ⟩
κ⁻⪯ψ {κ = ΩR b} o = ≺⇒⪯ (κ⁻≺ψ o)
κ⁻⪯ψ {κ = IR} {c} o = 0⪯ ⟨ psi IR c ⟩

-- 0 ≺ κ（κ ∈ R′）
0≺reg : ∀ κ → zer ≺ regTm κ
0≺reg (ΩR a) = ⪯-sub⇒≺ (s≤s (s≤s z≤n)) (0⪯ _)
0≺reg IR     = ⪯-sub⇒≺ (s≤s (s≤s z≤n)) (0⪯ _)

-- size (mFi x) ≤ size x（mFi 沿分量下降）
open import Data.Nat.Properties using (≤-refl; <⇒≤)

```
