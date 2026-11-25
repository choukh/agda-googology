# 原型 (a): 值的一条定理 (同一底下的吸收)

> 验收文件, 编译定理, 无前提, 不用函数外延. 新块上, 塔第 1 项里 Ω_Ω+Ω₂ 的树 `up βΩ c2 (Ωt L2)` 的折叠读回, 不高于第 1 层的一棵树 `Y₀` 在孩子 two 下行一步后的底 `dS` 下的折叠读回 (`inv-same`). `Y₀` 由 Ω₂ 树自己的回灌链 `zz` 生成 (`YiInv` 的 `Y₀` 的写法), 结点是退化的 (非零分支上常值).
> 机制与 `YiInv.absorb` 相同, 只用后继形状层号上的结点行与第 0 层读回的加法, 与分支侧一行怎样写无关 (`absorb` 对一切 k, 一切底, 一切列).
> 不否定什么. 没有证的: `dS` 与孩子 one 的底 `BW1` 逐点同值 (只有闭分支上的 `refl` 测试), 所以这不是 "对孩子 one 的倒置".

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCertValue where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiCertPath
open import OCF.Lean.YiCertFold
open import OCF.Lean.YiCertCheck using (cb; ¬◃z; o¹; h₁; c1; c2; L1; L2; βΩ; BW)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼l; l≼; ≼-refl; ≼-trans; ≅→≼) renaming (+-mono to +ᵛ-mono)
import OCF.Align.RR4MonoFragment as MF
```

## 第 0 层的读回

```agda
T₀ : Set
T₀ = L.Ordᶜ L.zero

read : Tr zero → T₀
read zero          = L.zero
read (suc x)       = L.suc (read x)
read (lim f _)     = L.lim (λ n → read (f n))
read (Ω () _)
read (up _ () _ _)

read-+ : (x y : Tr zero) → read (x + y) L.≅ (read x L.+ read y)
read-+ x zero          = L.≅-refl⁰ (read x)
read-+ x (suc y)       = L.s≅ (read-+ x y)
read-+ x (lim f _)     = L.l≅ (λ n → read-+ x (f n))
read-+ x (Ω () _)
read-+ x (up _ () _ _)

plus≽ : (a : Tr zero) {y : T₀} (b : Tr zero) → y ≼ read b → y ≼ read (a + b)
plus≽ a b q = ≼-trans q (≼-trans (MF.≼-+ˡ (read a) (read b)) (≅→≼ (L.≅-sym (read-+ a b))))

plus≼ : (a b : Tr zero) {A B : T₀} → read a ≼ A → read b ≼ B → read (a + b) ≼ A L.+ B
plus≼ a b p q = ≼-trans (≅→≼ (read-+ a b)) (+ᵛ-mono p q)
```

## 后继形状层号上的吸收

`Tw S` 的第 n+1 项是层号 `nd sS (λ _ → k)` 的结点 (槽位是孩子层 k 本身): 零分支是第 n 项, 其余分支 c 是 `S n c`.

```agda
sel : {k : L} {A : Set} → Tr k → A → A → A
sel zero         x y = x
sel (suc _)      x y = y
sel (lim _ _)    x y = y
sel (Ω _ _)      x y = y
sel (up _ _ _ _) x y = y

sel-nz : {k : L} {A : Set} (c : Tr k) (x y : A) → k ⊢ zero ◃ c → sel c x y ≡ y
sel-nz zero         x y d = ⊥-elim (¬◃z d)
sel-nz (suc _)      x y d = refl
sel-nz (lim _ _)    x y d = refl
sel-nz (Ω _ _)      x y d = refl
sel-nz (up _ _ _ _) x y d = refl

module _ (k : L) (ok : Ok k) where

  sk : L
  sk = nd sS (λ _ → k)

  osk : Ok sk
  osk = tt , λ _ → ok

  Tw : (ℕ → Tr k → Tr sk) → ℕ → Tr sk
  Tw S zero    = zero
  Tw S (suc n) = Ω (inj₂ (tt , inj₁ tt)) (λ c → sel c (Tw S n) (S n c))

  Yw : (ℕ → Tr k → Tr sk) → Tr sk
  Yw S = lim (Tw S) (λ n → ◃w)

  module _ (B : Base sk) (β : Tr⁺ zero) (S : ℕ → Tr k → Tr sk) where

    ψ⊥ : Tr sk → Tr zero
    ψ⊥ t = proj₁ (ψ sk osk B zero (z≤ sk) β t)

    c₁ : ℕ → Tr⁺ k
    c₁ n = ψ sk osk B k (inc tt self) (B k (inc tt self)) (Tw S n)

    two-rows : ∀ n → read (ψ⊥ (Tw S n) + ψ⊥ (S n (proj₁ (c₁ n)))) ≼ read (ψ⊥ (Tw S (suc n)))
    two-rows n = subst (λ t → read (ψ⊥ (Tw S n) + ψ⊥ t) ≼ read (ψ⊥ (Tw S (suc n))))
      (sel-nz (proj₁ (c₁ n)) (Tw S n) (S n (proj₁ (c₁ n))) (proj₂ (c₁ n))) (≼l 1 (≼-refl _))

    module _ (R : ℕ → Tr⁺ zero) (dom : ∀ n c → k ⊢ zero ◃ c → read (proj₁ (R n)) ≼ read (ψ⊥ (S n c))) where

      step : ∀ n → read (ψ⊥ (Tw S n) + proj₁ (R n)) ≼ read (ψ⊥ (Tw S (suc n)))
      step n = ≼-trans (plus≼ (ψ⊥ (Tw S n)) (proj₁ (R n)) (≼-refl _) (dom n (proj₁ (c₁ n)) (proj₂ (c₁ n))))
        (≼-trans (≅→≼ (L.≅-sym (read-+ (ψ⊥ (Tw S n)) (ψ⊥ (S n (proj₁ (c₁ n))))))) (two-rows n))

      acc : ∀ n → read (cum (λ i → proj₁ (R i)) n) ≼ read (ψ⊥ (Tw S (suc n)))
      acc zero    = ≼-trans (plus≽ (ψ⊥ (Tw S zero)) (proj₁ (R zero)) (≼-refl _)) (step zero)
      acc (suc n) = ≼-trans (plus≼ (cum (λ i → proj₁ (R i)) n) (proj₁ (R (suc n))) (acc n) (≼-refl _))
        (≼-trans (≅→≼ (L.≅-sym (read-+ (ψ⊥ (Tw S (suc n))) (proj₁ (R (suc n)))))) (step (suc n)))

      absorb : read (proj₁ (limc⁺ R)) ≼ read (ψ⊥ (Yw S))
      absorb = l≼ (λ n → ≼l (suc n) (acc n))
```

## 实例: Ω_Ω+Ω₂ 的树

`dS`: 孩子 two 的底下行一步 (左边是零) 后在第 1 层的底. `zz`: Ω₂ 树朝第 0 层折叠时的回灌链.

```agda
oL2 : Ok L2
oL2 = proj₂ o¹ c2

dS : Base L1
dS = cb oL2 BW tt zero

β′ : Tr⁺ zero
β′ = ψ₀ (tw 1) o¹ βΩ

zz : ℕ → Tr L1
zz = iter (λ z → proj₁ (ψ L2 oL2 BW L1 (inc tt self) (BW L1 (inc tt self)) (up zero tt (suc z) (z◃ z ◃s)))) zero

lhs-form : ψ₀ (tw 1) o¹ (up βΩ c2 (proj₁ (Ωt L2)) (proj₂ (Ωt L2)))
         ≡ limc⁺ (λ n → ψ L1 (osk zero tt) dS zero (z≤ L1) β′ (suc (zz n)))
lhs-form = refl

S₀ : ℕ → Tr zero → Tr L1
S₀ n c = suc (zz n)

Y₀ : Tr L1
Y₀ = Yw zero tt S₀

inv-same : read (proj₁ (ψ₀ (tw 1) o¹ (up βΩ c2 (proj₁ (Ωt L2)) (proj₂ (Ωt L2)))))
         ≼ read (proj₁ (ψ L1 (osk zero tt) dS zero (z≤ L1) β′ Y₀))
inv-same = absorb zero tt dS β′ S₀ (λ n → ψ L1 (osk zero tt) dS zero (z≤ L1) β′ (suc (zz n))) (λ n c d → ≼-refl _)
```
