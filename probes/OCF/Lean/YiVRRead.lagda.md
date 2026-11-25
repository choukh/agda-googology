# 值关系: 读回与用例

> 验收文件 (读回 `YiBRValue.readRW`, 值序 `OCF.Align.Value`). 编译定理, 无前提: 第 0 层上 `Le` 就是读回的值序 (`le→≼`, `≼→le`); 所以折叠到第 0 层的读回对底, 起点, 树都单调 (`fold-≼`), 两边同值则同值 (`fold-≈`, 同值指 `≈ᵛ`, 不是逐构造子的 `≅`).
> 第 1 层: 底的关系只剩第 0 层的分量, 陈述只用读回 (`fold₁-≼`, `fold₁-≈`). 用例一 (塔第 1 项, 左边是第 0 层的树 a 的嵌入): 孩子 two 的两个底相关, 最小见证形状的折叠同值 (`base-two`, `wit-≼`, `wit-ω`). 用例二 (左边是零): 孩子 c 的一族规范树嵌入后的值不高于孩子 c+1 的 Ω 树的 (`kid-suc`, `kid-Ω`).
> 不否定什么. 左边是 `Ωt (tw 1)` 的见证不在域里 (`YiVRRel.β-not`); 对它只有条件定理 (`zz-can`, `wit-β`), 前提 `K.Bc two ⊴ K.Bc two` 是否可满足没有判决.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiVRRead where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold
open import OCF.Lean.YiVRRel
open import OCF.Lean.YiVRFold
open import OCF.Lean.YiBRValue using (readRW)
open import OCF.Lean.YiKidGen using (plus≽)
import OCF.Lean.YiKidRW as K
import OCF.Align.Level as L
import OCF.Align.Value as V
open V using (_≈ᵛ_)
```

## 第 0 层: 关系就是读回的值序

```agda
le→≼ : {x y : Tr zero} → Le zero x y → readRW x V.≼ readRW y
le→≼ z≼       = V.z≼
le→≼ (s≼s d)  = V.s≼s (le→≼ d)
le→≼ (≼s d)   = V.≼-suc (le→≼ d)
le→≼ (≼l n d) = V.≼l n (le→≼ d)
le→≼ (l≼ h)   = V.l≼ (λ n → le→≼ (h n))

≼→le : (x y : Tr zero) → readRW x V.≼ readRW y → Le zero x y
≼→le zero      y         p          = z≼
≼→le (suc x)   (suc y)   (V.s≼s p)  = s≼s (≼→le x y p)
≼→le (suc x)   (lim g s) (V.≼l n p) = ≼l n (≼→le (suc x) (g n) p)
≼→le (lim f r) zero      (V.l≼ h)   = l≼ (λ n → ≼→le (f n) zero (h n))
≼→le (lim f r) (suc y)   (V.l≼ h)   = l≼ (λ n → ≼→le (f n) (suc y) (h n))
≼→le (lim f r) (lim g s) (V.l≼ h)   = l≼ (λ n → ≼→le (f n) (lim g s) (h n))
≼→le (lim f r) (lim g s) (V.≼l n p) = ≼l n (≼→le (lim f r) (g n) p)
```

## 折叠到第 0 层的读回

量化域: 层号 ℓ 满足 `Dflt ℓ`; 底在非 `self` 的路径上相关; 树相关 (`Le ℓ x x′`), 同一棵树时即 x 在规范域.

```agda
fold-≼ : (ℓ : L) (o : Ok ℓ) → Dflt ℓ → (B B′ : Base ℓ) → B ⊴ B′ → (w : zero ≤ ℓ) (β β′ : Tr⁺ zero)
  → readRW (proj₁ β) V.≼ readRW (proj₁ β′) → {x x′ : Tr ℓ} → Le ℓ x x′
  → readRW (proj₁ (ψ ℓ o B zero w β x)) V.≼ readRW (proj₁ (ψ ℓ o B′ zero w β′ x′))
fold-≼ ℓ o D B B′ hB w β β′ hβ hx = le→≼ (fl ℓ o D B B′ hB zero w β β′ (≼→le _ _ hβ) hx)

fold-≈ : (ℓ : L) (o : Ok ℓ) → Dflt ℓ → (B B′ : Base ℓ) → B ⊴ B′ → B′ ⊴ B → (w : zero ≤ ℓ) (β β′ : Tr⁺ zero)
  → readRW (proj₁ β) ≈ᵛ readRW (proj₁ β′) → (x : Tr ℓ) → Can ℓ x
  → readRW (proj₁ (ψ ℓ o B zero w β x)) ≈ᵛ readRW (proj₁ (ψ ℓ o B′ zero w β′ x))
fold-≈ ℓ o D B B′ hB hB′ w β β′ (p , q) x hx =
  fold-≼ ℓ o D B B′ hB w β β′ p hx , fold-≼ ℓ o D B′ B hB′ w β′ β q hx
```

## 第 1 层

第 1 层的非 `self` 路径都通到第 0 层, 所以底的关系就是第 0 层各分量读回的值序.

```agda
o₁ᴸ : Ok L1
o₁ᴸ = tt , λ _ → tt

z-only : ∀ {j} → j ≤ zero → j ≡ zero
z-only self = refl

⊴₁ : (B B′ : Base L1) → ((w : zero ≤ L1) → readRW (proj₁ (B zero w)) V.≼ readRW (proj₁ (B′ zero w))) → B ⊴ B′
⊴₁ B B′ H j (inc tt self) _ = ≼→le _ _ (H (inc tt self))
⊴₁ B B′ H j (inu vs)      _ with z-only (vs tt)
... | refl = ≼→le _ _ (H (inu vs))

fold₁-≼ : (B B′ : Base L1) → ((w : zero ≤ L1) → readRW (proj₁ (B zero w)) V.≼ readRW (proj₁ (B′ zero w)))
  → (w : zero ≤ L1) (β β′ : Tr⁺ zero) → readRW (proj₁ β) V.≼ readRW (proj₁ β′) → {x x′ : Tr L1} → Le L1 x x′
  → readRW (proj₁ (ψ L1 o₁ᴸ B zero w β x)) V.≼ readRW (proj₁ (ψ L1 o₁ᴸ B′ zero w β′ x′))
fold₁-≼ B B′ H = fold-≼ L1 o₁ᴸ (tt , λ _ → tt) B B′ (⊴₁ B B′ H)

fold₁-≈ : (B B′ : Base L1) → ((w : zero ≤ L1) → readRW (proj₁ (B zero w)) ≈ᵛ readRW (proj₁ (B′ zero w)))
  → (w : zero ≤ L1) (β β′ : Tr⁺ zero) → readRW (proj₁ β) ≈ᵛ readRW (proj₁ β′) → (x : Tr L1) → Can L1 x
  → readRW (proj₁ (ψ L1 o₁ᴸ B zero w β x)) ≈ᵛ readRW (proj₁ (ψ L1 o₁ᴸ B′ zero w β′ x))
fold₁-≈ B B′ H = fold-≈ L1 o₁ᴸ (tt , λ _ → tt) B B′ (⊴₁ B B′ (λ w → proj₁ (H w))) (⊴₁ B′ B (λ w → proj₂ (H w)))

-- 实例: 默认底, 第 1 层的 Ω 树
fold₁-Ω : (β β′ : Tr⁺ zero) → readRW (proj₁ β) V.≼ readRW (proj₁ β′)
  → readRW (proj₁ (ψ L1 o₁ᴸ (B₀ L1) zero (z≤ L1) β (proj₁ (Ωt L1)))) V.≼ readRW (proj₁ (ψ L1 o₁ᴸ (B₀ L1) zero (z≤ L1) β′ (proj₁ (Ωt L1))))
fold₁-Ω β β′ p = fold-≼ L1 o₁ᴸ (tt , λ _ → tt) (B₀ L1) (B₀ L1) B₀⊴₁ (z≤ L1) β β′ p Ω₁-can
```

## 用例一: 塔第 1 项, 孩子 two 的两个底

左边取第 0 层的树 a 的嵌入 `ι (tw 1) a`. a 与 a′ 同值而不同文时, 孩子 two 的两个底 `Bw a`, `Bw a′` 相关 (`base-two`), 最小见证形状 `up (ι a) two (Ωt 2)` 的折叠同值.

```agda
two : Tr zero
two = suc (suc zero)

h₁ : Tr zero → L
h₁ c = zero ⊕ ↑ zero c

o₁ : Ok (tw 1)
o₁ = Ok-tw 1

wit : Tr zero → Tr (tw 1)
wit a = up (ι (tw 1) a) two (proj₁ (Ωt (h₁ two))) (proj₂ (Ωt (h₁ two)))

Bw : Tr zero → Base (h₁ two)
Bw a = cb (sΩ zero) h₁ o₁ (B₀ (tw 1)) two (ι (tw 1) a)

base-two : (a a′ : Tr zero) → readRW a V.≼ readRW a′ → Bw a ⊴ Bw a′
base-two a a′ p i u _ =
  fl (tw 1) o₁ Dflt-tw1 (B₀ (tw 1)) (B₀ (tw 1)) B₀⊴-tw1 i (inc two u) (Ωt i) (Ωt i) (B₀⊴-tw1 i (inc two u) tt)
     (ι≼ (tw 1) (≼→le a a′ p))

wit≼ : (a a′ : Tr zero) → readRW a V.≼ readRW a′ → Le (tw 1) (wit a) (wit a′)
wit≼ a a′ p = u≼u (ι≼ (tw 1) (≼→le a a′ p)) (Ωt≼ (h₁ two) (NoΩ↑ two))

wit-≼ : (a a′ : Tr zero) → readRW a V.≼ readRW a′
  → readRW (proj₁ (ψ₀ (tw 1) o₁ (wit a))) V.≼ readRW (proj₁ (ψ₀ (tw 1) o₁ (wit a′)))
wit-≼ a a′ p = fold-≼ (tw 1) o₁ Dflt-tw1 (B₀ (tw 1)) (B₀ (tw 1)) B₀⊴-tw1 (z≤ (tw 1)) (Ωt zero) (Ωt zero) (V.≼-refl _) (wit≼ a a′ p)

-- 见证的折叠就是孩子层的折叠, 底是 `Bw a`
wit-form : (a : Tr zero) → ψ₀ (tw 1) o₁ (wit a)
  ≡ ψ (h₁ two) (proj₂ o₁ two) (Bw a) zero (z≤ (h₁ two)) (ψ₀ (tw 1) o₁ (ι (tw 1) a)) (proj₁ (Ωt (h₁ two)))
wit-form a = refl
```

前提可满足: 两棵同值而不同文的第 0 层的树.

```agda
nat : ℕ → Tr zero
nat zero    = zero
nat (suc n) = suc (nat n)

ωa ωb : Tr zero
ωa = lim nat (λ n → ◃s)
ωb = lim (λ n → suc (nat n)) (λ n → ◃s)

f0 : Tr zero → Tr zero
f0 (lim f _) = f zero
f0 _         = zero

ωa≢ωb : ωa ≡ ωb → ⊥
ωa≢ωb e with cong f0 e
... | ()

ωa≈ωb : readRW ωa ≈ᵛ readRW ωb
ωa≈ωb = le→≼ {ωa} {ωb} (l≼ (λ n → ≼l n (≼s (refl₀ (nat n))))) , le→≼ {ωb} {ωa} (l≼ (λ n → ≼l (suc n) (refl₀ (nat (suc n)))))

wit-ω : readRW (proj₁ (ψ₀ (tw 1) o₁ (wit ωa))) ≈ᵛ readRW (proj₁ (ψ₀ (tw 1) o₁ (wit ωb)))
wit-ω = wit-≼ ωa ωb (proj₁ ωa≈ωb) , wit-≼ ωb ωa (proj₂ ωa≈ωb)
```

## 用例二: 孩子单调的一族规范域实例 (左边是零)

塔第 1 项, 左边取零: 孩子 c 的底是默认底. 孩子 c+1 的 Ω 树的折叠是 "孩子 c 里 z+1 的折叠" 沿链 `zn c` 的部分和极限 (`rhs-form`, `refl`). 所以孩子 c 里不高于某个 `zn c n + 1` (按 `Le`) 的树, 嵌入后的值不高于孩子 c+1 的 Ω 树嵌入后的值; 孩子 c 的 Ω 树是其中之一.

```agda
st : (c : Tr zero) → Tr (h₁ c) → Tr (h₁ c)
st c z = proj₁ (ψ (h₁ c) (proj₂ o₁ c) (B₀ (h₁ c)) (h₁ c) self (Ωt (h₁ c)) (suc z))

zn : (c : Tr zero) → ℕ → Tr (h₁ c)
zn c = iter (st c) zero

rhs-form : (c : Tr zero)
  → ψ₀ (tw 1) o₁ (up zero (suc c) (proj₁ (Ωt (h₁ (suc c)))) (proj₂ (Ωt (h₁ (suc c)))))
  ≡ limc⁺ (λ n → ψ₀ (h₁ c) (proj₂ o₁ c) (suc (zn c n)))
rhs-form c = refl

lhs-form : (c : Tr zero) (y : Tr⁺ (h₁ c)) → ψ₀ (tw 1) o₁ (up zero c (proj₁ y) (proj₂ y)) ≡ ψ₀ (h₁ c) (proj₂ o₁ c) (proj₁ y)
lhs-form c y = refl

le-cum : (F : ℕ → Tr zero) (n : ℕ) → readRW (F n) V.≼ readRW (cum F n)
le-cum F zero    = V.≼-refl _
le-cum F (suc n) = plus≽ (cum F n) (F (suc n))

kid-suc : (c : Tr zero) (y : Tr⁺ (h₁ c)) (n : ℕ) → Le (h₁ c) (proj₁ y) (suc (zn c n))
  → readRW (proj₁ (ψ₀ (tw 1) o₁ (up zero c (proj₁ y) (proj₂ y))))
    V.≼ readRW (proj₁ (ψ₀ (tw 1) o₁ (up zero (suc c) (proj₁ (Ωt (h₁ (suc c)))) (proj₂ (Ωt (h₁ (suc c)))))))
kid-suc c y n d =
  V.≼l n (V.≼-trans
    (fold-≼ (h₁ c) (proj₂ o₁ c) (Dflt-noΩ (h₁ c) (NoΩ↑ c)) (B₀ (h₁ c)) (B₀ (h₁ c)) (B₀⊴-noΩ (h₁ c) (NoΩ↑ c))
            (z≤ (h₁ c)) (Ωt zero) (Ωt zero) (V.≼-refl _) d)
    (le-cum (λ m → proj₁ (ψ₀ (h₁ c) (proj₂ o₁ c) (suc (zn c m)))) n))

kid-Ω : (c : Tr zero)
  → readRW (proj₁ (ψ₀ (tw 1) o₁ (up zero c (proj₁ (Ωt (h₁ c))) (proj₂ (Ωt (h₁ c))))))
    V.≼ readRW (proj₁ (ψ₀ (tw 1) o₁ (up zero (suc c) (proj₁ (Ωt (h₁ (suc c)))) (proj₂ (Ωt (h₁ (suc c)))))))
kid-Ω c = kid-suc c (Ωt (h₁ c)) 1 (≼s (≼l 0 (Ωt≼ (h₁ c) (NoΩ↑ c))))
```

## 左边是 `Ωt (tw 1)` 的最小见证: 条件定理

`K.Bc c` 是 `YiKidRW` 里孩子 c 的底 (左边是 `Ωt (tw 1)`). 前提 `K.Bc two ⊴ K.Bc two` (这个底在非 `self` 的路径上自相关) 没有证明也没有否定: 它的第 1 层分量是结点 `z ↦ Ωt 1 + ι (ψ₀(h₁ z) (Ωt (h₁ z)))`, 自相关要这个分支函数对 z 按值单调, 两个 z 的孩子层不同. `GMono` 是这条引理的陈述 (未证, 未否定).

```agda
GMono : Set
GMono = (z z′ : Tr zero) → readRW z V.≼ readRW z′
  → readRW (proj₁ (ψ₀ (h₁ z) (proj₂ o₁ z) (proj₁ (Ωt (h₁ z))))) V.≼ readRW (proj₁ (ψ₀ (h₁ z′) (proj₂ o₁ z′) (proj₁ (Ωt (h₁ z′)))))

zz-can : K.Bc two ⊴ K.Bc two → (n : ℕ) → Can (h₁ K.oneᴿ) (K.zzᴿ n)
zz-can H zero    = z≼
zz-can H (suc n) =
  fl (h₁ two) (proj₂ o₁ two) (Dflt-noΩ (h₁ two) (NoΩ↑ two)) (K.Bc two) (K.Bc two) H (h₁ K.oneᴿ) (inc tt self)
     (K.Bc two (h₁ K.oneᴿ) (inc tt self)) (K.Bc two (h₁ K.oneᴿ) (inc tt self)) (H (h₁ K.oneᴿ) (inc tt self) tt)
     {x = up zero tt (suc (K.zzᴿ n)) (z◃ (K.zzᴿ n) ◃s)} {x′ = up zero tt (suc (K.zzᴿ n)) (z◃ (K.zzᴿ n) ◃s)}
     (u≼u z≼ (s≼s (zz-can H n)))

wit-β : (B′ : Base (h₁ two)) → K.Bc two ⊴ B′
  → readRW (proj₁ (ψ₀ (tw 1) o₁ (up K.βᴿ two (proj₁ (Ωt (h₁ two))) (proj₂ (Ωt (h₁ two))))))
    V.≼ readRW (proj₁ (ψ (h₁ two) (proj₂ o₁ two) B′ zero (z≤ (h₁ two)) K.b₁ (proj₁ (Ωt (h₁ two)))))
wit-β B′ H = fold-≼ (h₁ two) (proj₂ o₁ two) (Dflt-noΩ (h₁ two) (NoΩ↑ two)) (K.Bc two) B′ H (z≤ (h₁ two)) K.b₁ K.b₁ (V.≼-refl _)
               (Ωt≼ (h₁ two) (NoΩ↑ two))
```
