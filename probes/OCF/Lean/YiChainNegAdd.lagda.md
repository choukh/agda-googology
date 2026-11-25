# YiChainNeg：累加的链为什么卡在 `≼ˣ`，按左加数划界

**验收文件，档位：编译定理 (正反两面)。** 链点是左加 (`X + y`)，`≼ˣ` 对左加封闭与否就是构造路的机制：左加 1 时，在严格的右树上封闭 (`add1-strict`)，对一般右树推出 LPO (`add1→LPO`，探针退化)；
左加 ω 时，即使限于严格的右树也推出 LPO (`addω→LPO`，探针严格)；`≼ˣ` 对严格树的完备性也推出 LPO (`cplˣS→LPO`)。两边加值相等的前缀则封闭 (`+ˣ`)。
不否定 `ChainP` (它在 LEM 下成立，`YiChainNegLEM`)；否定的只是 "先证一般的左加封闭" 与 "只靠严格性" 这两种证法。§4：去掉 `sˣ` 的第二前提的定义域就是 `≼` 本身。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiChainNegAdd where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Barrier using (LPO; any; any-up; any-witness; true→any)
import OCF.Align.Level as L
open L using (Ordᶜ)
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼; ≼-refl; ≼-trans; ≼-suc; ≼-+ʳ; +-mono; tα; bit; 𝟏; ≼lim⁻)
open import OCF.Align.YiVmConExact using (_≼ˣ_; zˣ; sˣ; wˣ; ≼lˣ; lˣ; ˣ→≼; reflˣ; irr)
open import OCF.Align.YiVmConLPO using (O; split)
open import OCF.Align.YiMonoVM using (VMᴸ)
open import OCF.Lean.YiLeanTw3 using (pts; module Pt)
open Pt using (co)
open import OCF.Lean.YiLeanAccFin using (read)
open import OCF.Align.YiBtValBT using (module D)
open import OCF.Lean.YiChainNegLEM using (val₁)
```

## 1 左加 1

`Strict`：每个 ℕ 极限的相邻项值严格上升。严格树的每个前驱要么是字面的自然数，要么吸收左边的 1 (`dec1`)，这一判定是结构的，于是 `≼ˣ` 对左加 1 封闭。
一般的右树上，前驱 `tα α` (0 或 1 的极限) 吸收与否就是 LPO 的判定。

```agda
Strict : Ordᶜ L.zero → Set
Strict L.zero = ⊤
Strict (L.suc a) = Strict a
Strict (L.lim f) = (∀ n → L.suc (f n) ≼ f (suc n)) × (∀ n → Strict (f n))
Strict (L.limᵢ () f)
Strict (L.up () x)

nat : ℕ → Ordᶜ L.zero
nat = L.natᶜ

1+≼s : ∀ x → 𝟏 L.+ x ≼ L.suc x
1+≼s L.zero = ≼-refl 𝟏
1+≼s (L.suc x) = s≼s (1+≼s x)
1+≼s (L.lim f) = l≼ (λ n → ≼-trans (1+≼s (f n)) (s≼s (≼l n (≼-refl (f n)))))
1+≼s (L.limᵢ () f)
1+≼s (L.up () x)

1+nat : ∀ k → 𝟏 L.+ nat k ≡ L.suc (nat k)
1+nat zero = refl
1+nat (suc k) = cong L.suc (1+nat k)

dec1 : ∀ b → Strict b → (Σ ℕ λ k → b ≡ nat k) ⊎ (𝟏 L.+ b ≼ b)
dec1 L.zero s = inj₁ (0 , refl)
dec1 (L.suc b) s with dec1 b s
... | inj₁ (k , refl) = inj₁ (suc k , refl)
... | inj₂ e = inj₂ (s≼s e)
dec1 (L.lim f) (st , _) = inj₂ (l≼ (λ n → ≼l (suc n) (≼-trans (1+≼s (f n)) (st n))))
dec1 (L.limᵢ () f) s
dec1 (L.up () x) s

add1-strict : ∀ {x z} → Strict z → x ≼ˣ z → x ≼ˣ (𝟏 L.+ z)
add1-strict s zˣ = zˣ
add1-strict {L.suc a} {L.suc b} s (sˣ d e) with dec1 b s
... | inj₁ (k , refl) = subst (λ w → L.suc a ≼ˣ L.suc w) (sym (1+nat k)) (wˣ (sˣ d e))
... | inj₂ ab = sˣ (add1-strict s d) (≼-trans ab e)
add1-strict s (wˣ d) = wˣ (add1-strict s d)
add1-strict (_ , sg) (≼lˣ n d) = ≼lˣ n (add1-strict (sg n) d)
add1-strict s (lˣ d) = lˣ (λ n → add1-strict s (d n))

Add1ˣ : Set
Add1ˣ = ∀ x z → x ≼ˣ z → x ≼ˣ (𝟏 L.+ z)

hb1 : ∀ α bb → L.suc (tα α) ≼ˣ (𝟏 L.+ bit bb) → tα α ≼ O ⊎ 𝟏 ≼ tα α
hb1 α false (sˣ d e) = inj₁ (ˣ→≼ d)
hb1 α false (wˣ ())
hb1 α true (sˣ d e) = inj₂ e
hb1 α true (wˣ d) = hb1 α false d

inv1 : ∀ α → L.suc (tα α) ≼ˣ (𝟏 L.+ L.suc (tα α)) → tα α ≼ O ⊎ 𝟏 ≼ tα α
inv1 α (sˣ d e) = inj₂ (≼-trans (≼-+ʳ 𝟏 (tα α)) e)
inv1 α (wˣ (≼lˣ n d)) = hb1 α (any α n) d

add1→LPO : Add1ˣ → LPO
add1→LPO c α = split α (inv1 α (c (L.suc (tα α)) (L.suc (tα α)) (reflˣ _)))
```

两边都加上值相等的前缀时 `≼ˣ` 封闭 (`+ˣ`)，无须判定；障碍只在一边有前缀 (累加的链对不累加的参照)。

```agda
≼ˣ-+ʳ : ∀ {c d} → c ≼ˣ d → ∀ b → c ≼ˣ (d L.+ b)
≼ˣ-+ʳ p L.zero = p
≼ˣ-+ʳ p (L.suc b) = wˣ (≼ˣ-+ʳ p b)
≼ˣ-+ʳ p (L.lim f) = ≼lˣ 0 (≼ˣ-+ʳ p (f 0))
≼ˣ-+ʳ p (L.limᵢ () f)
≼ˣ-+ʳ p (L.up () x)

+ˣ : ∀ {c d a b} → c ≼ˣ d → d ≼ c → a ≼ˣ b → (c L.+ a) ≼ˣ (d L.+ b)
+ˣ {b = b} p q zˣ = ≼ˣ-+ʳ p b
+ˣ p q (sˣ r e) = sˣ (+ˣ p q r) (+-mono q e)
+ˣ p q (wˣ r) = wˣ (+ˣ p q r)
+ˣ p q (≼lˣ n r) = ≼lˣ n (+ˣ p q r)
+ˣ p q (lˣ r) = lˣ (λ n → +ˣ p q (r n))
```

## 2 严格的探针

`Yw W α` 的第 n 项：α 到 n 都假时是 n，否则是 `W + n`；`W` 严格且在一切 n 之上时它是严格树。`hitV`：`suc v ≼ Yw W α` 且 `suc v` 不在任何 n 之下，就给出 α 的真位。

```agda
ω′ : Ordᶜ L.zero
ω′ = L.lim nat

nat-st : ∀ n → Strict (nat n)
nat-st zero = tt
nat-st (suc n) = nat-st n

ω′-st : Strict ω′
ω′-st = (λ n → ≼-refl _) , nat-st

+st : ∀ {W} → Strict W → ∀ y → Strict y → Strict (W L.+ y)
+st s L.zero _ = s
+st s (L.suc y) t = +st s y t
+st {W} s (L.lim f) (st , sf) = (λ n → +-mono (≼-refl W) (st n)) , (λ n → +st s (f n) (sf n))
+st s (L.limᵢ () f) t
+st s (L.up () x) t

hb : Ordᶜ L.zero → Bool → ℕ → Ordᶜ L.zero
hb W false n = nat n
hb W true n = W L.+ nat n

Yw : Ordᶜ L.zero → (ℕ → Bool) → Ordᶜ L.zero
Yw W α = L.lim (λ n → hb W (any α n) n)

hb-step : ∀ {W} → (∀ n → nat n ≼ W) → ∀ b b′ → (b ≡ true → b′ ≡ true) → ∀ n → L.suc (hb W b n) ≼ hb W b′ (suc n)
hb-step w false false up n = ≼-refl _
hb-step {W} w false true up n = ≼-trans (w (suc n)) (≼-+ʳ W (nat (suc n)))
hb-step w true true up n = ≼-refl _
hb-step w true false up n with up refl
... | ()

hb-st : ∀ {W} → Strict W → ∀ b n → Strict (hb W b n)
hb-st s false n = nat-st n
hb-st s true n = +st s (nat n) (nat-st n)

Yw-st : ∀ {W} → Strict W → (∀ n → nat n ≼ W) → ∀ α → Strict (Yw W α)
Yw-st s w α = (λ n → hb-step w (any α n) (any α (suc n)) (any-up n) n) , (λ n → hb-st s (any α n) n)

hitb : ∀ {W v : Ordᶜ L.zero} → (∀ n → ¬ (L.suc v ≼ nat n)) → ∀ b n → L.suc v ≼ hb W b n → b ≡ true
hitb no false n e = ⊥-elim (no n e)
hitb no true n e = refl

hitV : ∀ {W v : Ordᶜ L.zero} α → (∀ n → ¬ (L.suc v ≼ nat n)) → L.suc v ≼ Yw W α → Σ ℕ λ k → α k ≡ true
hitV {W} α no d with ≼lim⁻ d
... | n , e = any-witness n (hitb {W} no (any α n) n e)

no-nat : ∀ n → ¬ (L.suc ω′ ≼ nat n)
no-nat n e = irr (nat n) (≼-trans (s≼s (≼l n (≼-refl (nat n)))) e)

nat≼ω′ : ∀ n → nat n ≼ ω′
nat≼ω′ n = ≼l n (≼-refl (nat n))
```

`≼ˣ` 对严格树不完备：`suc ω ≼ suc (Yw ω α)` 一致成立，`≼ˣ` 的推导在顶上要么取相等 (`sˣ`，α 全假)，要么取严格 (`wˣ`，有真位)。

```agda
CplˣS : Set
CplˣS = ∀ x y → Strict x → Strict y → x ≼ y → x ≼ˣ y

natle : ∀ b n → nat n ≼ hb ω′ b n
natle false n = ≼-refl _
natle true n = ≼-trans (nat≼ω′ n) (≼-+ʳ ω′ (nat n))

ω′≼Y : ∀ α → ω′ ≼ Yw ω′ α
ω′≼Y α = l≼ (λ n → ≼l n (natle (any α n) n))

big : ∀ {W} α k → any α (suc k) ≡ true → L.suc W ≼ Yw W α
big {W} α k p = ≼l (suc k) (subst (λ b → L.suc W ≼ hb W b (suc k)) (sym p) (s≼s (≼-+ʳ W (nat k))))

allf : ∀ α → Yw ω′ α ≼ ω′ → ∀ k → α k ≡ false
allf α e k with α k in eq
... | false = refl
... | true = ⊥-elim (irr ω′ (≼-trans (big α k (any-up k (true→any k eq))) e))

invS : ∀ α → L.suc ω′ ≼ˣ L.suc (Yw ω′ α) → (Σ ℕ λ k → α k ≡ true) ⊎ (∀ k → α k ≡ false)
invS α (sˣ d e) = inj₂ (allf α e)
invS α (wˣ d) = inj₁ (hitV α no-nat (ˣ→≼ d))

cplˣS→LPO : CplˣS → LPO
cplˣS→LPO c α = invS α (c _ _ ω′-st (Yw-st ω′-st nat≼ω′ α) (s≼s (ω′≼Y α)))
```

## 3 左加 ω

探针 `b = Yw ω² α`：α 全假时值 ω (不吸收左边的 ω)，有真位时值 ω²+ω (吸收)。`suc b ≼ˣ ω + suc b` 的推导在顶上必须判定吸收与否。`b` 是严格树。

```agda
mulω : ℕ → Ordᶜ L.zero
mulω zero = L.zero
mulω (suc k) = ω′ L.+ mulω k

ω² : Ordᶜ L.zero
ω² = L.lim mulω

sω : ∀ k → L.suc (mulω k) ≼ mulω (suc k)
sω zero = ≼l 1 (≼-refl 𝟏)
sω (suc k) = +-mono (≼-refl ω′) (sω k)

mulω-st : ∀ k → Strict (mulω k)
mulω-st zero = tt
mulω-st (suc k) = +st ω′-st (mulω k) (mulω-st k)

ω²-st : Strict ω²
ω²-st = sω , mulω-st

nat≼ω² : ∀ n → nat n ≼ ω²
nat≼ω² n = ≼l 1 (nat≼ω′ n)

absW : ∀ n → ω′ L.+ (ω² L.+ nat n) ≼ ω² L.+ nat n
absW zero = l≼ (λ j → ≼l (suc j) (≼-refl _))
absW (suc n) = s≼s (absW n)

pieceb : ∀ α k → any α k ≡ true → ∀ b n → any α n ≡ b → ω′ L.+ hb ω² b n ≼ Yw ω² α
pieceb α k p false n q = ≼l k (subst (λ bb → ω′ L.+ nat n ≼ hb ω² bb k) (sym p)
  (≼-trans (+-mono (≼-refl ω′) (nat≼ω′ n)) (≼-trans (≼l 2 (≼-refl _)) (≼-+ʳ ω² (nat k)))))
pieceb α k p true n q = ≼l n (subst (λ bb → ω′ L.+ (ω² L.+ nat n) ≼ hb ω² bb n) (sym q) (absW n))

absorbW : ∀ α k → any α k ≡ true → ω′ L.+ Yw ω² α ≼ Yw ω² α
absorbW α k p = l≼ (λ n → pieceb α k p (any α n) n refl)

noT : ∀ α → L.suc (Yw ω² α) ≼ ω′ L.+ Yw ω² α → ∀ k → α k ≡ false
noT α d k with α k in eq
... | false = refl
... | true = ⊥-elim (irr _ (≼-trans d (absorbW α k (true→any k eq))))

one≼ : ∀ b → 𝟏 ≼ hb ω² b 1
one≼ false = ≼-refl 𝟏
one≼ true = s≼s z≼

AddωS : Set
AddωS = ∀ x z → Strict z → x ≼ˣ z → x ≼ˣ (ω′ L.+ z)

invω : ∀ α → L.suc (Yw ω² α) ≼ˣ (ω′ L.+ L.suc (Yw ω² α)) → (Σ ℕ λ k → α k ≡ true) ⊎ (∀ k → α k ≡ false)
invω α (sˣ d e) = inj₁ (hitV α no-nat (≼-trans (≼l 1 (+-mono (≼-refl ω′) (one≼ (any α 1)))) e))
invω α (wˣ d) = inj₂ (noT α (ˣ→≼ d))

addω→LPO : AddωS → LPO
addω→LPO c α = invω α (c _ _ (Yw-st ω²-st nat≼ω² α) (reflˣ _))
```

## 4 去掉 `sˣ` 的第二前提

`≼ʳ` 与 `≼ˣ` 同形，只是 `sʳ` 不带顶的值的证据；它与值序 `≼` 互推 (第 0 层)，所以这个定义域上的值单调就是 `VMᴸ` 本身 (`vmʳ↔`)。n = 1 的链点对无条件在里面 (`in-ʳ₁`)。

```agda
infix 4 _≼ʳ_
data _≼ʳ_ : Ordᶜ L.zero → Ordᶜ L.zero → Set where
  zʳ  : ∀ {b} → L.zero ≼ʳ b
  sʳ  : ∀ {a b} → a ≼ʳ b → L.suc a ≼ʳ L.suc b
  wʳ  : ∀ {a b} → a ≼ʳ b → a ≼ʳ L.suc b
  ≼lʳ : ∀ {a g} n → a ≼ʳ g n → a ≼ʳ L.lim g
  lʳ  : ∀ {f b} → (∀ n → f n ≼ʳ b) → L.lim f ≼ʳ b

ʳ→≼ : ∀ {a b} → a ≼ʳ b → a ≼ b
ʳ→≼ zʳ = z≼
ʳ→≼ (sʳ d) = s≼s (ʳ→≼ d)
ʳ→≼ (wʳ d) = ≼-suc (ʳ→≼ d)
ʳ→≼ (≼lʳ n d) = ≼l n (ʳ→≼ d)
ʳ→≼ (lʳ d) = l≼ (λ n → ʳ→≼ (d n))

≼→ʳ : ∀ {a b : Ordᶜ L.zero} → a ≼ b → a ≼ʳ b
≼→ʳ z≼ = zʳ
≼→ʳ (s≼s d) = sʳ (≼→ʳ d)
≼→ʳ (≼l n d) = ≼lʳ n (≼→ʳ d)
≼→ʳ (l≼ d) = lʳ (λ n → ≼→ʳ (d n))
≼→ʳ (≼i {p = ()} x ex d)
≼→ʳ (i≼ {p = ()} d)
≼→ʳ (≼u {r = ()} d)
≼→ʳ (u≼ {r = ()} d)

VMʳ : Set
VMʳ = ∀ (x : Ordᶜ L.zero) (hx : L.HS x) (y : Ordᶜ L.zero) (hy : L.HS y) → x ≼ʳ y →
  L.ψ⁰ (L.Ω (L.toLevel x hx)) ≼ L.ψ⁰ (L.Ω (L.toLevel y hy))

vmʳ↔ : (VMʳ → VMᴸ) × (VMᴸ → VMʳ)
vmʳ↔ = (λ v x hx y hy d → v x hx y hy (≼→ʳ d)) , (λ v x hx y hy d → v x hx y hy (ʳ→≼ d))

in-ʳ₁ : D.γ 1 ≼ʳ read (co (pts 1))
in-ʳ₁ = ≼→ʳ val₁
```
