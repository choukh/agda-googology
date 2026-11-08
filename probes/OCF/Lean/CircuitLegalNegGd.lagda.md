# 合法源树仍不保证旧 Gd 随世界增长

直接检验共享 LegalTransport，在原 Sb 1 上给实例。关键是原 AdT
接纳带 Gd 但不合法的坐标；源树的 LgB 只约束合法世界界内的坐标。
没有合法化旧反例，也不否定更小的实际生成域。

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Lean.CircuitLegalNegGd where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdIf using (Tw)
open import OCF.Lean.ThirdTw using (Sb)
import OCF.Lean.ThirdLeg as L
import OCF.Lean.ThirdFold as F
open import OCF.Lean.CircuitLegalIf using (LegalTransport)

one two : Cd
one = hs hz
two = hs one
U : KS
U = Sb 1
module W₀ = L.W hz tt
module W₁ = L.W one tt
w₀ w₁ : Wd U
w₀ = W₀.wS 1
w₁ = W₁.wS 1
lw₀ : LgW U w₀
lw₀ = W₀.lwS 1
lw₁ : LgW U w₁
lw₁ = W₁.lwS 1

default-self : ∀ c → _≤w_ (Tw S⊥ c) (L.wT S⊥ tt c) (L.wT S⊥ tt c)
default-self hz = tt
default-self (hs c) = default-self c , hself
default-self (hl f) = λ n → default-self (f n)
default-self (hΩ () f)
grow : _≤w_ U w₀ w₁
grow (inj₁ _) = tt , hsuc hself
grow (inj₂ c) = default-self (hs c)

module Old = F U w₀ lw₀
module New = F U w₁ lw₁
m : HB U
m = hΩ (inj₁ tt , inj₂ tt) (λ _ → hs hz)
legal-m : LgB m
legal-m = (λ _ _ _ _ → hself) , (λ _ _ → tt)

bad : HB (Tw U (hs m))
bad = hΩ (inj₁ (two , inj₂ tt)) (λ _ → hz)

flag : Cd → HB (Tw U (hs m))
flag hz = hz
flag (hs _) = bad
flag (hl _) = bad
flag (hΩ () _)

at : HB (Tw U m) → HB (Tw U m) → HB (Tw U (hs m))
at hz b = hz
at (hs a) b = hz
at (hl f) b = hz
at (hΩ (e , κ) f) hz = flag e
at (hΩ κ f) (hs b) = hz
at (hΩ κ f) (hl g) = hz
at (hΩ κ f) (hΩ κ′ g) = hz

at-old : ∀ a b → Old.Gd m a → Old.Gd (hs m) (at a b)
at-old hz b p = tt
at-old (hs a) b p = tt
at-old (hl f) b p = tt
at-old (hΩ (hz , κ) f) hz p = tt
at-old (hΩ (hs e , κ) f) hz ((() , q) , r)
at-old (hΩ (hl e , κ) f) hz ((() , q) , r)
at-old (hΩ (hΩ () f , κ) g) hz p
at-old (hΩ κ f) (hs b) p = tt
at-old (hΩ κ f) (hl g) p = tt
at-old (hΩ κ f) (hΩ κ′ g) p = tt

at-step : ∀ {w} a b → a ⊲[ w ] b → at a b ≡ hz
at-step hz b p = refl
at-step (hs a) b p = refl
at-step (hl f) b p = refl
at-step (hΩ κ f) hz ()
at-step (hΩ κ f) (hs b) p = refl
at-step (hΩ κ f) (hl g) p = refl
at-step (hΩ κ f) (hΩ κ′ g) p = refl

g : HB (Tw U m) → HB (Tw U (hs m))
g hz = hz
g (hs a) = hz
g (hl f) = at (f 0) (f 1)
g (hΩ κ f) = hz

old-branch : ∀ c → Old.Gd m c → Old.Gd (hs m) (g c)
old-branch hz p = tt
old-branch (hs a) p = tt
old-branch (hl f) p = at-old (f 0) (f 1) (p 0)
old-branch (hΩ κ f) p = tt

legal-zero : ∀ c → LgB c → g c ≡ hz
legal-zero hz p = refl
legal-zero (hs a) p = refl
legal-zero (hl f) p = at-step {L.wT U w₀ m} (f 0) (f 1) (proj₁ p 0)
legal-zero (hΩ κ f) p = refl

input : HB (Tw U (hs m))
input = hΩ (inj₂ tt) g
old-input : Old.Gd (hs m) input
old-input = tt , old-branch

legal-input : LgB input
legal-input = mono , child
  where
  mono : ∀ {w c d} → LgW (Tw U (hs m)) w →
    Bd (Tw U (hs m)) (inj₂ tt) c w → Bd (Tw U (hs m)) (inj₂ tt) d w →
    Pr (Tw U (hs m)) (inj₂ tt) w c d → g c ⊲[ w ] g d
  mono {c = c} {d = d} lw pc pd r rewrite legal-zero c (lgB⊲ pc (proj₁ lw) (proj₂ lw))
    | legal-zero d (lgB⊲ pd (proj₁ lw) (proj₂ lw)) = hself
  child : ∀ {w c} → LgW (Tw U (hs m)) w →
    Bd (Tw U (hs m)) (inj₂ tt) c w → LgB (g c)
  child {c = c} lw pc rewrite legal-zero c (lgB⊲ pc (proj₁ lw) (proj₂ lw)) = tt

branch : HB (Tw U m)
branch = hΩ (one , inj₂ tt) (λ _ → hz)
activated : HB (Tw U m)
activated = hl (λ { zero → branch ; (suc _) → hz })
activated-new : New.Gd m activated
activated-new zero = (hself , tt) , (λ _ _ → tt)
activated-new (suc n) = tt
activated-not-legal : ¬ LgB activated
activated-not-legal p with proj₁ p {L.wT U w₀ m} 0
... | ()

two-not-one : ¬ (_⊲[_]_ {S⊥} two tt one)
two-not-one (hsuc ())
no-new-input : ¬ New.Gd (hs m) input
no-new-input p = two-not-one (proj₁ (proj₁ (proj₂ p activated activated-new)))

no-legal-transport : ¬ LegalTransport
no-legal-transport move = no-new-input
  (move 1 w₀ w₁ lw₀ lw₁ grow (hs m) legal-m input legal-input old-input)
```

所有共享合同前提均实填，包含原 Sb 1、合法高度、合法输入、合法增长世界。
失败位置是新 AdT 坐标 activated，且已证明它不合法；这不表示实际正常输出
必然遇到此坐标，不否定把坐标域同时收紧后的生成合同或整条路线。
