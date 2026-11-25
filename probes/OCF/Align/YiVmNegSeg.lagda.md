# YiVmNeg：保初始段的前驱嵌入推出 LPO

**验收文件，档位：编译定理。** 否定的是 `VMᴸ` 的一种证法："由值序 x ≼ y 给出像向下封闭的前驱嵌入" (`EmbVᴰ`，即保初始段)。`embVᴰ→LPO`：它推出 LPO；只限严格的树 (`SHS`)、向下封闭只要双重否定，也推出 LPO。在探针族上，这类嵌入的存在与 LPO 等价 (`seg→LPO`, `LPO→seg`)。
不否定 `VMᴸ`，也不否定不要求初始段的 `EmbV`：同一探针族上有一致的普通嵌入与 `VMᴸ` 的实例 (`probe-emb`, `probe-vm`)。探针严格，不是退化对象。弱化见 §5；前置引理在 `YiVmNegBase`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiVmNegSeg where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Barrier using (LPO)
open import OCF.Align.Level
open import OCF.Align.Value using (_≼_; s≼s; ⊑→≼)
open import OCF.Align.BTBOFullEmb using (PEmb; Ψ-emb)
open PEmb
open import OCF.Align.YiMonoEmb using (PEmb-⊑; PEmb-suc)
open import OCF.Align.YiVmNegBase
```

## 1 陈述

`PEmbᴰ`：前驱嵌入，像向下封闭 (任一像之下的前驱都是像)。这是 "保初始段" 的写法。`PEmbᴰ¬¬` 只要求向下封闭的双重否定。

```agda
record PEmbᴰ (a b : Ordᴵ) : Set where
  field
    emb  : PEmb a b
    down : Down emb

record PEmbᴰ¬¬ (a b : Ordᴵ) : Set where
  field
    emb  : PEmb a b
    down : Down¬¬ emb

ᴰ→¬¬ : ∀ {a b} → PEmbᴰ a b → PEmbᴰ¬¬ a b
ᴰ→¬¬ P = record { emb = PEmbᴰ.emb P ; down = λ r q k → k (PEmbᴰ.down P r q) }

EmbVᴰ : Set
EmbVᴰ = ∀ (x : Ordᶜ zero) (hx : HS x) (y : Ordᶜ zero) (hy : HS y) → x ≼ y →
  PEmbᴰ (toLevel x hx) (toLevel y hy)

EmbVᴰˢ¬¬ : Set
EmbVᴰˢ¬¬ = ∀ (x : Ordᶜ zero) (sx : SHS x) (y : Ordᶜ zero) (sy : SHS y) → x ≼ y →
  PEmbᴰ¬¬ (toLevel x (SHS→HS sx)) (toLevel y (SHS→HS sy))

embVᴰ→ˢ : EmbVᴰ → EmbVᴰˢ¬¬
embVᴰ→ˢ ev x sx y sy d = ᴰ→¬¬ (ev x (SHS→HS sx) y (SHS→HS sy) d)
```

## 2 探针族

x = ω+1 固定；y_α = Y α + 1，`Y α` 在 α 全假时值 ω，否则值 ω·2。值序 x ≼ y_α 对一切 α 一致地给出 (`probe≼`)。

```agda
xP : Ordᶜ zero
xP = suc ωᶜ

hxP : HS xP
hxP = hs hω

yP : (ℕ → Bool) → Ordᶜ zero
yP α = suc (Y α)

hyP : ∀ α → HS (yP α)
hyP α = hs (hY α)

probe-strict : SHS xP × (∀ α → SHS (yP α))
probe-strict = ss SHS-ω , λ α → ss (SY α)

probe≼ : ∀ α → xP ≼ yP α
probe≼ α = s≼s (⊑→≼ ωᶜ (ω⊑Y α))

SegP : Set
SegP = ∀ α → PEmbᴰ¬¬ (toLevel xP hxP) (toLevel (yP α) (hyP α))
```

## 3 否定

顶 A 的像若 `≅ᴵ` `B α` 本身，则 α 全假：否则 ω 是 `B α` 的前驱，它在像里的原像只能是顶 (与 `ω≇B` 矛盾) 或一个自然数 (与 `no-nat-ω` 矛盾)。顶的像若落在 `B α` 的第 n 项里，则 α 到 n 有真：否则像 ≅ 一个自然数，与 `cnt` 矛盾。

```agda
r₀ : A ≺ᴵ suc A
r₀ = via (≅ᴵ-refl A) zero

top-case : ∀ α (P : PEmb (suc A) (suc (B α))) → Down¬¬ P → map P r₀ ≅ᴵ B α → ∀ k → α k ≡ false
top-case α P dn e k with α k in ek
... | false = refl
... | true = ⊥-elim (dn r₀ ωm λ
      { (d , via e₁ zero , e′) → ω≇B α k ek (≅ᴵ-trans (≅ᴵ-sym e′) (≅ᴵ-trans (coh P (via e₁ zero) r₀ e₁) e))
      ; (d , via e₁ (suc q₁) , e′) →
          let (j , ej) = ≺ω (≺ᴵ-respʳ (via e₁ q₁) (toLevel-ω hω)) in no-nat-ω P dn (via e₁ (suc q₁)) j ej e′ })
  where
  ωm : ωᴵ ≺ᴵ map P r₀
  ωm = ≺ᴵ-respʳ (ω≺B α k ek) (≅ᴵ-sym e)

seg→LPO : SegP → LPO
seg→LPO S α = main (PEmbᴰ¬¬.emb (S α)) (PEmbᴰ¬¬.down (S α))
  where
  main : (P : PEmb (suc A) (suc (B α))) → Down¬¬ P → (Σ ℕ λ k → α k ≡ true) ⊎ (∀ k → α k ≡ false)
  main P dn with bnd P r₀
  ... | via e zero = inj₂ (top-case α P dn e)
  ... | via e (suc (lim n q)) with inB (seen α n) n (hl₁ (hY α) n) q
  ...   | inj₁ st = inj₁ (seen→Σ α n st)
  ...   | inj₂ (t , et) = ⊥-elim (cnt P r₀ nsA (≅ᴵ-trans e et))

embVᴰˢ→LPO : EmbVᴰˢ¬¬ → LPO
embVᴰˢ→LPO ev = seg→LPO (λ α → ev xP (ss SHS-ω) (yP α) (ss (SY α)) (probe≼ α))

embVᴰ→LPO : EmbVᴰ → LPO
embVᴰ→LPO ev = embVᴰˢ→LPO (embVᴰ→ˢ ev)
```

## 4 前提的可满足性与不否定的部分

结构可比时恒等映射保初始段 (`PEmbᴰ-⊑`, `embVᴰ-⊑`)；有 LPO 时探针族上的保初始段嵌入都存在 (`LPO→seg`)，所以 `SegP` 与 LPO 等价。

```agda
PEmbᴰ-⊑ : ∀ {a b} → a ⊑ᴵ b → PEmbᴰ a b
PEmbᴰ-⊑ k = record { emb = PEmb-⊑ k ; down = λ r {e} q → e , ≺ᴵ-trans q r , ≅ᴵ-refl e }

embVᴰ-⊑ : ∀ (x : Ordᶜ zero) (hx : HS x) (y : Ordᶜ zero) (hy : HS y) → x ⊑⁰ y → PEmbᴰ (toLevel x hx) (toLevel y hy)
embVᴰ-⊑ x hx y hy k = PEmbᴰ-⊑ (toLevel-⊑ hx hy k)

dec→seg : ∀ α → (Σ ℕ λ k → α k ≡ true) ⊎ (∀ k → α k ≡ false) → PEmbᴰ (toLevel xP hxP) (toLevel (yP α) (hyP α))
dec→seg α (inj₁ (k , ek)) = PEmbᴰ-⊑ (s⊑′ (≺-suc (≺ᴵ-respˡ (toLevel-ω hω) (ω≺B α k ek))))
dec→seg α (inj₂ f) = PEmbᴰ-⊑ (s⊑ (l≅ (λ n → ≅ᴵ-trans (toLevel-nat n (hl₁ hω n))
                 (≅ᴵ-sym (hbF≅ (seen α n) n (hl₁ (hY α) n) (seen-F α f n))))) zero)

LPO→seg : LPO → ∀ α → PEmbᴰ (toLevel xP hxP) (toLevel (yP α) (hyP α))
LPO→seg lpo α = dec→seg α (lpo α)

seg↔LPO : (SegP → LPO) × (LPO → SegP)
seg↔LPO = seg→LPO , λ lpo α → ᴰ→¬¬ (LPO→seg lpo α)
```

## 5 弱化

结论弱化成双重否定后，探针族上的命题无条件成立 (`¬¬seg`)，否定失效；但双重否定的嵌入只给 ψ⁰ 不等式的双重否定，不给 `VMᴸ`。向下封闭只要求在顶的像之下 (`DownTop`) 时，仍推出 LPO (`segTop→LPO`)。

```agda
¬¬seg : ∀ α → ¬ ¬ PEmbᴰ (toLevel xP hxP) (toLevel (yP α) (hyP α))
¬¬seg α k = k (dec→seg α (inj₂ allF))
  where
  allF : ∀ n → α n ≡ false
  allF n with α n in e
  ... | false = refl
  ... | true = ⊥-elim (k (dec→seg α (inj₁ (n , e))))

DownTop : ∀ {a b} → PEmb (suc a) b → Set
DownTop {a} P = ∀ {e} → e ≺ᴵ map P (via (≅ᴵ-refl a) zero) →
  ¬ ¬ (Σ Ordᴵ λ d → Σ (d ≺ᴵ suc a) λ s → map P s ≅ᴵ e)

top→down : ∀ {a b} (P : PEmb (suc a) b) → DownTop P → Down¬¬ P
top→down P dt (via e zero) q = dt (≺ᴵ-respʳ q (coh P (via e zero) (via (≅ᴵ-refl _) zero) e))
top→down P dt (via e (suc q′)) q = dt (≺ᴵ-trans q (mono P (via e (suc q′)) (via (≅ᴵ-refl _) zero) (via e q′)))

segTop→LPO : (∀ α → Σ (PEmb (toLevel xP hxP) (toLevel (yP α) (hyP α))) DownTop) → LPO
segTop→LPO S = seg→LPO (λ α → record { emb = proj₁ (S α) ; down = top→down (proj₁ (S α)) (proj₂ (S α)) })
```

不要求初始段时，探针族上有一致的嵌入：顶映到顶，自然数映到自然数 (`probe-emb`)，从而 `VMᴸ` 在探针族上成立 (`probe-vm`)。这个嵌入向下封闭恰当 α 全假 (`probe-down→F`)。

```agda
probe-emb : ∀ α → PEmb (toLevel xP hxP) (toLevel (yP α) (hyP α))
probe-emb α = PEmb-suc (PEmb-⊑ (toLevel-⊑ hω (hY α) (ω⊑Y α)))

probe-vm : ∀ α → ψ⁰ (Ω (toLevel xP hxP)) ≼ ψ⁰ (Ω (toLevel (yP α) (hyP α)))
probe-vm α = Ψ-emb (probe-emb α)

probe-down→F : ∀ α → Down¬¬ (probe-emb α) → ∀ k → α k ≡ false
probe-down→F α dn = top-case α (probe-emb α) dn (≅ᴵ-refl (B α))
```
