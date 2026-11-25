# 诊断：块内倒置

> 诊断：块内倒置, 不进成品, 树、折叠、合法性一行不改. 判决: 编译定理, 无前提. 存在孩子 one 的第 1 层树 `Y₁`, 使读作 Ω_Ω+Ω₂ 的树 `up β two (Ωt 2)` 的折叠读回不高于 `up β one Y₁` 的 (`inversion`), 严格低于 `up β one (Y₁+1)` 的 (`inversion⁺`); 常值分支的见证 `Y₀` 同样成立 (`inversion₀`); 孩子 three 的 Ω₃ 树对孩子 two 的一棵第 2 层树同样成立 (`inversion₃`).
> 机制: 孩子 c+1 在 `up zero tt …` 之后的底与孩子 c 的底逐字相同 (`base-same`, `base-same₃`, `refl`); Ω 树的折叠是低一层的一列树的折叠的部分和极限 (`lhs-form`, `refl`); 后继层号上任一列树的这种极限都被一棵同层的树吸收 (`absorb`, 对一切层号 `suc k`, 一切底, 一切列).
> 不否定什么, 陈述不引用记号. 判断 (不是定理): 记号的 ψ₀ 弱单调, 所以 `inversion⁺` 说明块的值在这两棵树上至少有一棵与记号不一致; 归到 "左边偏低" 还要块在 `up β one (Y₁+1)` 上不高于记号. 非严格的 `inversion` 单独不够, 因为记号里 ψ₀(Ω_Ω+Ω₂) = ψ₀(Ω_Ω+ψ₁(Ω_Ω+Ω₂)).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiInv where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import OCF.Lean.YiLegBlock renaming (L to LF)
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (_≤_; self; ins; Ev; Rt)
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLSRead using (read; read-+; plus≽; next≽; ◃⊑; ◃→≺)
open import OCF.Lean.YiCeilRead using (plus≼; next≼; ωx-mono)
open import OCF.Lean.YiLSTw1 using (h₁; G; εh; ρh)
open import OCF.Lean.YiT2Frame using (ε¹; ρ¹; β; one; two)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; s≼s; ≼l; l≼; ≼-refl; ≼-trans; ≅→≼; ⊑→≼; ≺→s≼)
```

## 后继层号上的吸收 (对一切 k, 一切底, 一切列)

`Tw k S` 的第 n+1 项是层号 `suc k` 的 Ω 结点 (槽位在第 k 层): 第一分支 (零) 是第 n 项, 其余分支 c 是 `S n c`. 合法性只要相邻项的步进, 由第一分支给出 (`◃w`). 折叠时第 n+1 项的链的第 1 个点非零, 所以第 1 行落在 `S n` 上.

```agda
sel : {k : LF} {A : Set} → Tr k → A → A → A
sel zero         x y = x
sel (suc _)      x y = y
sel (lim _ _)    x y = y
sel (Ω _ _)      x y = y
sel (up _ _ _ _) x y = y

sel-nz : {k : LF} {A : Set} (c : Tr k) (x y : A) → k ⊢ zero ◃ c → sel c x y ≡ y
sel-nz zero         x y d = ⊥-elim (¬◃z d)
sel-nz (suc _)      x y d = refl
sel-nz (lim _ _)    x y d = refl
sel-nz (Ω _ _)      x y d = refl
sel-nz (up _ _ _ _) x y d = refl

Tw : (k : LF) → (ℕ → Tr k → Tr (suc k)) → ℕ → Tr (suc k)
Tw k S zero    = zero
Tw k S (suc n) = Ω (inj₁ tt) (λ c → sel c (Tw k S n) (S n c))

Yw : (k : LF) → (ℕ → Tr k → Tr (suc k)) → Tr (suc k)
Yw k S = lim (Tw k S) (λ n → ◃w)

Yw-nz : (k : LF) (S : ℕ → Tr k → Tr (suc k)) → suc k ⊢ zero ◃ Yw k S
Yw-nz k S = ◃l zero
```

`absorb`: R 的每一项都不高于 `S n c` (c 非零) 的折叠时, R 的部分和极限不高于 `Yw k S` 的折叠. 证明只用第 0 层读回的加法与 `Tw k S (n+1)` 的折叠的前两行.

```agda
module _ (k : LF) (ε : Ev (suc k)) (ρ : Rt (suc k)) (B : Base (suc k)) (S : ℕ → Tr k → Tr (suc k)) where

  c₁ : ℕ → Tr k
  c₁ n = ψs (suc k) ε ρ B k (ins self) (bs B k (ins self)) (ns B k (ins self)) (Tw k S n)

  n₁ : ∀ n → k ⊢ zero ◃ c₁ n
  n₁ n = nzs (suc k) ε ρ B k (ins self) (bs B k (ins self)) (ns B k (ins self)) (Tw k S n)

  two-rows : ∀ n → read (ψ⊥ (suc k) ε ρ B (Tw k S n) + ψ⊥ (suc k) ε ρ B (S n (c₁ n)))
                 ≼ read (ψ⊥ (suc k) ε ρ B (Tw k S (suc n)))
  two-rows n = subst (λ t → read (ψ⊥ (suc k) ε ρ B (Tw k S n) + ψ⊥ (suc k) ε ρ B t) ≼ read (ψ⊥ (suc k) ε ρ B (Tw k S (suc n))))
    (sel-nz (c₁ n) (Tw k S n) (S n (c₁ n)) (n₁ n)) (≼l 1 (≼-refl _))

  module _ (R : ℕ → Tr zero) (dom : ∀ n c → k ⊢ zero ◃ c → read (R n) ≼ read (ψ⊥ (suc k) ε ρ B (S n c))) where

    step : ∀ n → read (ψ⊥ (suc k) ε ρ B (Tw k S n) + R n) ≼ read (ψ⊥ (suc k) ε ρ B (Tw k S (suc n)))
    step n = ≼-trans (plus≼ (ψ⊥ (suc k) ε ρ B (Tw k S n)) (R n) (≼-refl _) (dom n (c₁ n) (n₁ n)))
      (≼-trans (≅→≼ (L.≅-sym (read-+ (ψ⊥ (suc k) ε ρ B (Tw k S n)) (ψ⊥ (suc k) ε ρ B (S n (c₁ n)))))) (two-rows n))

    acc : ∀ n → read (cum R n) ≼ read (ψ⊥ (suc k) ε ρ B (Tw k S (suc n)))
    acc zero    = ≼-trans (plus≽ (ψ⊥ (suc k) ε ρ B (Tw k S zero)) (R zero) (≼-refl (read (R zero)))) (step zero)
    acc (suc n) = ≼-trans (plus≼ (cum R n) (R (suc n)) (acc n) (≼-refl (read (R (suc n)))))
      (≼-trans (≅→≼ (L.≅-sym (read-+ (ψ⊥ (suc k) ε ρ B (Tw k S (suc n))) (R (suc n))))) (step (suc n)))

    absorb : (nz : ∀ n → zero ⊢ zero ◃ R n) → read (limc R nz) ≼ read (ψ⊥ (suc k) ε ρ B (Yw k S))
    absorb nz = l≼ (λ n → ≼l (suc n) (acc n))
```

一行 `x + (c+1)` (嵌入) 的折叠不低于 `x + 1` 的: 两者都是 `next`, 底由第 k 层折叠的第一位置序比较.

```agda
dom₁ : (k : LF) (ε : Ev (suc k)) (ρ : Rt (suc k)) (B : Base (suc k)) (x : Tr (suc k)) (c : Tr k) → k ⊢ zero ◃ c
     → read (ψ⊥ (suc k) ε ρ B (suc x)) ≼ read (ψ⊥ (suc k) ε ρ B (up x tt (suc c) (z◃s c)))
dom₁ k ε ρ B x c d =
  ≼-trans (next≼ (ψ⊥ (suc k) ε ρ B x) (nz⊥ (suc k) ε ρ B x) (≼-refl _))
  (≼-trans (ωx-mono (⊑→≼ (read (ψ⊥ (suc k) ε ρ B x)) (◃⊑ (mono⊥ k ε ρ (dS k ε ρ B x) d))))
           (next≽ (ψ⊥ k ε ρ (dS k ε ρ B x) c) (nz⊥ k ε ρ (dS k ε ρ B x) c) (≼-refl _)))
```

## 实例: 孩子 two 的 Ω₂ 树对孩子 one

`zz` 与第十五次审查的试验同文. `base-same`: 孩子 two 在 `up zero tt …` 之后的第 1 层的底与孩子 one 的底逐字相同. `seed-form`, `zz-step`: 链 `zz` 在第 1 层里由种子 "Ω₁ + 可数" 生成.

```agda
L1 L2 L3 : LF
L1 = suc zero
L2 = suc L1
L3 = suc L2

BW : Base L2
BW = dW zero h₁ ε¹ ρ¹ (B₀ (tw 1)) two β

BW1 : Base L1
BW1 = dW zero h₁ ε¹ ρ¹ (B₀ (tw 1)) one β

base-same : dS L1 (εh two) (ρh two) BW zero ≡ BW1
base-same = refl

zz : ℕ → Tr L1
zz = iter (λ z → ψs L2 (εh two) (ρh two) BW L1 (ins self) (bs BW L1 (ins self)) (ns BW L1 (ins self)) (up zero tt (suc z) (z◃s z))) zero

seed-form : bs BW1 L1 self ≡ Ω (inj₁ tt) (λ c → Ωt L1 + ι L1 (G c))
seed-form = refl

zz-step : ∀ n → zz (suc n) ≡ next (ψs L1 tt tt BW1 L1 self (bs BW1 L1 self) (ns BW1 L1 self) (zz n))
                                   (nzs L1 tt tt BW1 L1 self (bs BW1 L1 self) (ns BW1 L1 self) (zz n))
zz-step n = refl

lhs-form : ψ₀ (tw 1) ε¹ ρ¹ (up β two (Ωt (h₁ two)) (Ωt-nz (h₁ two)))
         ≡ limc (λ n → ψ⊥ L1 tt tt BW1 (suc (zz n))) (λ n → nz⊥ L1 tt tt BW1 (suc (zz n)))
lhs-form = refl

rhs-form : (Y : Tr (h₁ one)) (e : h₁ one ⊢ zero ◃ Y) → ψ₀ (tw 1) ε¹ ρ¹ (up β one Y e) ≡ ψ⊥ L1 tt tt BW1 Y
rhs-form Y e = refl
```

两个见证. `Y₁` 的第 n+1 项在分支 c ≠ 0 上是 `zz n + (c+1)`; `Y₀` 的是常值 `zz n + 1`.

```agda
S₁ S₀ : ℕ → Tr zero → Tr L1
S₁ n c = up (zz n) tt (suc c) (z◃s c)
S₀ n c = suc (zz n)

Y₁ Y₀ : Tr (h₁ one)
Y₁ = Yw zero S₁
Y₀ = Yw zero S₀

inversion : read (ψ₀ (tw 1) ε¹ ρ¹ (up β two (Ωt (h₁ two)) (Ωt-nz (h₁ two))))
          ≼ read (ψ₀ (tw 1) ε¹ ρ¹ (up β one Y₁ (Yw-nz zero S₁)))
inversion = absorb zero tt tt BW1 S₁ (λ n → ψ⊥ L1 tt tt BW1 (suc (zz n)))
  (λ n c d → dom₁ zero tt tt BW1 (zz n) c d) (λ n → nz⊥ L1 tt tt BW1 (suc (zz n)))

inversion₀ : read (ψ₀ (tw 1) ε¹ ρ¹ (up β two (Ωt (h₁ two)) (Ωt-nz (h₁ two))))
           ≼ read (ψ₀ (tw 1) ε¹ ρ¹ (up β one Y₀ (Yw-nz zero S₀)))
inversion₀ = absorb zero tt tt BW1 S₀ (λ n → ψ⊥ L1 tt tt BW1 (suc (zz n)))
  (λ n c d → ≼-refl _) (λ n → nz⊥ L1 tt tt BW1 (suc (zz n)))
```

严格的倒置: 孩子 one 的树 `Y₁ + 1` 的折叠严格高于 (读回的后继不高于) 孩子 two 的 Ω₂ 树的折叠.

```agda
inversion⁺ : L.suc (read (ψ₀ (tw 1) ε¹ ρ¹ (up β two (Ωt (h₁ two)) (Ωt-nz (h₁ two)))))
           ≼ read (ψ₀ (tw 1) ε¹ ρ¹ (up β one (suc Y₁) (z◃s Y₁)))
inversion⁺ = ≼-trans (s≼s inversion) (≺→s≼ (◃→≺ (◃l zero)))
```

## 第二个实例: 孩子 three 的 Ω₃ 树对孩子 two

同一个机制高一层: 孩子 three 下行一步之后第 2 层的底与孩子 two 的底逐字相同 (`base-same₃`).

```agda
three : Tr zero
three = suc two

BW3 : Base L3
BW3 = dW zero h₁ ε¹ ρ¹ (B₀ (tw 1)) three β

base-same₃ : dS L2 (εh three) (ρh three) BW3 zero ≡ BW
base-same₃ = refl

zz₃ : ℕ → Tr L2
zz₃ = iter (λ z → ψs L3 (εh three) (ρh three) BW3 L2 (ins self) (bs BW3 L2 (ins self)) (ns BW3 L2 (ins self)) (up zero tt (suc z) (z◃s z))) zero

S₂ : ℕ → Tr L1 → Tr L2
S₂ n c = up (zz₃ n) tt (suc c) (z◃s c)

Y₂ : Tr (h₁ two)
Y₂ = Yw L1 S₂

inversion₃ : read (ψ₀ (tw 1) ε¹ ρ¹ (up β three (Ωt (h₁ three)) (Ωt-nz (h₁ three))))
           ≼ read (ψ₀ (tw 1) ε¹ ρ¹ (up β two Y₂ (Yw-nz L1 S₂)))
inversion₃ = absorb L1 tt tt BW S₂ (λ n → ψ⊥ L2 tt tt BW (suc (zz₃ n)))
  (λ n c d → dom₁ L1 tt tt BW (zz₃ n) c d) (λ n → nz⊥ L2 tt tt BW (suc (zz₃ n)))
```
