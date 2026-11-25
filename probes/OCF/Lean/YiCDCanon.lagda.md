# 由有限分支极限生成的读回域

不读记号；编译定义与树侧闭包。域只取零、后继和各分支均为字面自然数的合法 ℕ 极限。
相邻步进沿用树自身的第一位置证据，不要求按序数值严格递增；域不是所有第 0 层树。
主线塔第 1 项实际回灌的前两个下标在域内；是否覆盖后续下标另在验收文件核对。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCDCanon where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Empty using (⊥)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (B₀)
open import OCF.Lean.YiTBRow using (ψ; h₁; nat)
open import OCF.Lean.YiMTTab using (rbᶻ)

data Fin : Tr zero → Set where
  fz : Fin zero
  fs : ∀ {x} → Fin x → Fin (suc x)

data Canon : Tr zero → Set where
  cz : Canon zero
  cs : ∀ {x} → Canon x → Canon (suc x)
  cl : ∀ {f a} → (∀ n → Fin (f n)) → Canon (lim f a)

fin+ : ∀ {x y} → Fin x → Fin y → Fin (x + y)
fin+ fx fz = fx
fin+ fx (fs fy) = fs (fin+ fx fy)

fin-iter : ∀ b → Fin b → ∀ n → Fin (iter (b +_) b n)
fin-iter b fb zero = fb
fin-iter b fb (suc n) = fin+ fb (fin-iter b fb n)

fin-canon : ∀ {x} → Fin x → Canon x
fin-canon fz = cz
fin-canon (fs f) = cs (fin-canon f)

fin-nat : ∀ n → Fin (nat n)
fin-nat zero = fz
fin-nat (suc n) = fs (fin-nat n)

nat-in : ∀ n → Canon (nat n)
nat-in n = fin-canon (fin-nat n)

ω₀ : Tr zero
ω₀ = lim nat (λ n → ◃s)

omega-in : Canon ω₀
omega-in = cl fin-nat

suc-omega-in : Canon (suc ω₀)
suc-omega-in = cs omega-in

G : Tr zero → Tr (tw 1)
G c = up zero c (proj₁ (Ωt (h₁ c))) (proj₂ (Ωt (h₁ c)))

feed : Tr zero → Tr zero
feed c = proj₁ (ψ (tw 1) (Ok-tw 1) (rbᶻ (tw 1)) (B₀ (tw 1)) zero (ink self) (Ωt zero) (G c))

idx : ℕ → Tr zero
idx = iter feed zero

idx0 : Canon (idx 0)
idx0 = cz

idx1 : Canon (idx 1)
idx1 = cl (fin-iter (suc zero) (fs fz))

suc-inv : ∀ {x} → Canon (suc x) → Canon x
suc-inv (cs c) = c

fin-below : ∀ {x y} → Fin y → zero ⊢ x ◃ y → Fin x
fin-below (fs f) ◃s = f
fin-below f (◃t d e) = fin-below (fin-below f e) d

below : ∀ {x y} → Canon y → zero ⊢ x ◃ y → Canon x
below c ◃s = suc-inv c
below (cl q) (◃l n) = fin-canon (q n)
below c (◃w {p = ()})
below c (◃u _ () _ _)
below c (◃c _ () _)
below c (◃t d e) = below (below c e) d

lim-finite : ∀ {f a} → Canon (lim f a) → ∀ n → Fin (f n)
lim-finite (cl q) = q

bump : ℕ → Tr zero
bump zero = ω₀
bump (suc n) = suc (bump n)

outside : Tr zero
outside = lim bump (λ n → ◃s)

not-outside : Canon outside → ⊥
not-outside (cl q) with q 0
... | ()
```
