# φ 并进折叠: 验收文件

> 验收文件. 判决: 接口 `Iface` 由 `YiPhiFold`, `YiPhiLegal` 实填 (`phi`, 编译定理, 对一切带证据的层号; 塔与 Λ 的闭项无前提).
> 有限测试 (`refl` 或 `tt`): 塔第 2, 3 项根结点的链步前两步都保留结点, 原折叠同一步是 ℕ 极限; 孩子层是 `Ωₗ` 时下标层在基底里的结点保留.
> k = 0 的层号 (tw 1) 上新旧折叠字面不同 (`tw1-differs`, 有限反例); 没有 `Ωₗ` 的层号上的样本相同. 不否定任何路线. 入口: `YiPhiFold`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPhiCheck where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; subst)

open import OCF.Lean.YiFreshBlock
open import OCF.Lean.YiFreshFold using (_+_; iter; next; cum; Ωt; ι; eqℕ-refl)
import OCF.Lean.YiFreshFold as F
open import OCF.Lean.YiPhiBlock
open import OCF.Lean.YiPhiFold
open import OCF.Lean.YiPhiLegal
open import OCF.Lean.YiPhiIface using (Iface)
```

## 接口的实填

嵌入一致都是 `refl` (ℕ 极限指定孩子的一条先用 `eqℕ-refl`); `Ωₗ` 的两条里分支 c 是变量.

```agda
J2-lim : (g : ℕ → L) (ε : Ev (lim g)) (B : Base (lim g)) (n : ℕ) (j : L) (w : j ≤ g n) (β : Tr j)
  (x : Tr (lim g)) (y : Tr (g n))
  → ψs (lim g) ε B j (inl n w) β (up x n y)
  ≡ ψs (g n) (ε n) (dL g ε B n x) j w (ψs (lim g) ε B j (inl n w) β x) y
J2-lim g ε B n j w β x y rewrite eqℕ-refl n = refl

phi : Iface
phi = record
  { ψ⊥ = ψ⊥
  ; ψs = ψs
  ; J2-suc  = λ a ε B j w β x y → refl
  ; J2-lim  = J2-lim
  ; J2-limu = λ g ε B j ws β x n y → refl
  ; J2-Ωk   = λ k h ε B j w β x c y → refl
  ; J2-Ωu   = λ k h ε B j ws β x c y → refl
  ; J2⊥-suc = λ a ε B x y → refl
  ; J2⊥-lim = λ g ε B x n y → refl
  ; J2⊥-Ω   = λ k h ε B x c y → refl
  ; mono⊥ = mono⊥
  ; monos = monos
  ; pres⊥ = pres⊥
  ; press = press
  ; tw-leg = twᶜ-leg
  ; EBO-leg = EBOᶜ-leg
  ; kstep = λ n B β x p g → refl
  }
```

## 链步: 塔第 2, 3 项 (有限测试)

`stepᴾ n` 是塔第 n+1 项的 Ω 树的根结点在新折叠里的链步 (目标是下标层 tw n); `stepᴼ n` 是空白页原折叠的同一步.

```agda
isLim isΩ : ∀ {P B C D} → T P B C D → Set
isLim (lim _) = ⊤
isLim _       = ⊥
isΩ (Ω _ _) = ⊤
isΩ _       = ⊥

stepᴾ : (n : ℕ) → Tr (tw n) → Tr (tw n)
stepᴾ n c = ψs (tw (suc n)) (Ev-tw (suc n)) (B₀ _) (tw n) (ink self) (Ωt (tw n))
              (up zero c (Ωt (tw n ⊕ ↑ (tw n) c)))

stepᴼ : (n : ℕ) → Tr (tw n) → Tr (tw n)
stepᴼ n c = F.ψs (tw (suc n)) (F.B₀ _) (tw n) (F.ink F.self) (up zero c (Ωt (tw n ⊕ ↑ (tw n) c)))

step-is-root : (n : ℕ) (c : Tr (tw n))
  → stepᴾ n c ≡ ψs (tw (suc n)) (Ev-tw (suc n)) (B₀ _) (at (tw (suc n)) (inj₁ (inj₁ tt)))
                  (posW (tw (suc n)) (inj₁ (inj₁ tt)))
                  (bs (B₀ (tw (suc n))) (tw n) (posW (tw (suc n)) (inj₁ (inj₁ tt))))
                  (up zero c (Ωt (tw n ⊕ ↑ (tw n) c)))
step-is-root n c = refl

new-step₂ : isΩ (stepᴾ 1 zero)
new-step₂ = tt

old-step₂ : isLim (stepᴼ 1 zero)
old-step₂ = tt

new-step₃ : isΩ (stepᴾ 2 zero)
new-step₃ = tt

old-step₃ : isLim (stepᴼ 2 zero)
old-step₃ = tt
```

链的第二步: 分支是第一步的值 (一个 Ω 结点), 孩子层是 `Ωₗ`, 它的下标层在基底里; 结点仍保留 (第十三次审查的限制 1 的情形).

```agda
new-step₂′ : isΩ (stepᴾ 1 (stepᴾ 1 zero))
new-step₂′ = tt

old-step₂′ : isLim (stepᴼ 1 (stepᴼ 1 zero))
old-step₂′ = tt

new-step₃′ : isΩ (stepᴾ 2 (stepᴾ 2 zero))
new-step₃′ = tt
```

孩子层是后继 (分支 c = 1, 层号 tw 1 + 1), 嵌入的结点槽位在基底 tw 1 里 (不是顶槽位): 保留.

```agda
keep-suc : isΩ (ψs (tw 2) (Ev-tw 2) (B₀ _) (tw 1) (ink self) (Ωt (tw 1))
                  (up zero (suc zero) (Ω (inj₂ (inj₁ (inj₁ tt))) (λ _ → zero))))
keep-suc = tt

old-suc : isLim (F.ψs (tw 2) (F.B₀ _) (tw 1) (F.ink F.self)
                  (up zero (suc zero) (Ω (inj₂ (inj₁ (inj₁ tt))) (λ _ → zero))))
old-suc = tt
```

## 与原折叠的对照

没有 `Ωₗ` 的层号上的样本相同 (有限测试; 样本是不含 Ω 结点与 ℕ 极限的闭树, 含变量的项两边是不同的函数名, `refl` 比不了). tw 1 (k = 0) 上 k 侧那一行已换成孩子层的折叠, 与原来的回退字面不同: 分支 0, 孩子树 1, 新折叠的首项是 1, 原折叠是 1 + 1.

```agda
same-2 : ψ₀ (suc (suc zero)) tt (up (suc zero) tt (up zero tt (suc (suc zero))))
       ≡ F.ψ₀ (suc (suc zero)) (up (suc zero) tt (up zero tt (suc (suc zero))))
same-2 = refl

fin : ℕ → L
fin zero    = zero
fin (suc n) = suc (fin n)

Ev-fin : (n : ℕ) → Ev (fin n)
Ev-fin zero    = tt
Ev-fin (suc n) = Ev-fin n

same-ω : ψs (lim fin) Ev-fin (B₀ _) (fin 2) (inl 2 self) (Ωt (fin 2)) (up (suc zero) 2 (up (suc zero) tt (suc zero)))
       ≡ F.ψs (lim fin) (F.B₀ _) (fin 2) (F.inl 2 F.self) (up (suc zero) 2 (up (suc zero) tt (suc zero)))
same-ω = refl

hd : ∀ {P B C D} → T P B C D → T P B C D
hd (lim f) = f zero
hd x       = x

isS : ∀ {P B C D} → T P B C D → Set
isS (suc zero) = ⊤
isS _          = ⊥

tw1-new : (c : Tr zero) (y : Tr (zero ⊕ ↑ zero c))
  → ψs (tw 1) (Ev-tw 1) (B₀ _) zero (ink self) (Ωt zero) (up zero c y)
  ≡ ψs (zero ⊕ ↑ zero c) (proj₂ (proj₂ (Ev-tw 1) c)) (dW zero (λ c → zero ⊕ ↑ zero c) (Ev-tw 1) (B₀ _) c zero)
      zero (self ∙ lift zero (↑ zero c)) (Ωt zero) y
tw1-new c y = refl

tw1-old : (c : Tr zero) (y : Tr (zero ⊕ ↑ zero c))
  → F.ψs (tw 1) (F.B₀ _) zero (F.ink F.self) (up zero c y)
  ≡ Ωt zero + ι zero (F.ψ₀ (zero ⊕ ↑ zero c) y)
tw1-old c y = refl

tw1-differs : ψs (tw 1) (Ev-tw 1) (B₀ _) zero (ink self) (Ωt zero) (up zero zero (suc zero))
            ≢ F.ψs (tw 1) (F.B₀ _) zero (F.ink F.self) (up zero zero (suc zero))
tw1-differs e = subst isS (cong hd e) tt
```
