# 实际回灌链的结构前驱域

不读记号；编译定义与闭包。Pre 取实际链各项的第一位置前驱自反闭包，包含全部链项。
来源：YiKVRel._⊴_ 的两构造子在干净导入闭包中复置；链 G、feed、idx 直接复用 YiCDCanon。
向下封闭覆盖后继反演、极限分支及关系归纳中的 mw；不声称全体合法树都在域内。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPCDom where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiCDCanon using (G; feed; idx) public

infix 4 _⊴_
data _⊴_ (x : Tr zero) : Tr zero → Set where
  ⊴r : x ⊴ x
  ⊴◃ : ∀ {y} → zero ⊢ x ◃ y → x ⊴ y

Pre : Tr zero → Set
Pre x = Σ ℕ λ k → x ⊴ idx k

idx-in : ∀ k → Pre (idx k)
idx-in k = k , ⊴r

idx0 : Pre (idx 0)
idx0 = idx-in 0
idx1 : Pre (idx 1)
idx1 = idx-in 1
idx2 : Pre (idx 2)
idx2 = idx-in 2

below : ∀ {x y} → Pre y → zero ⊢ x ◃ y → Pre x
below (k , ⊴r) d = k , ⊴◃ d
below (k , ⊴◃ e) d = k , ⊴◃ (◃t d e)

suc-inv : ∀ {x} → Pre (suc x) → Pre x
suc-inv p = below p ◃s

lim-inv : ∀ {f a} → Pre (lim f a) → ∀ n → Pre (f n)
lim-inv p n = below p (◃l n)

least : (D : Tr zero → Set) → (∀ k → D (idx k))
      → (∀ {x y} → D y → zero ⊢ x ◃ y → D x)
      → ∀ {x} → Pre x → D x
least D all down (k , ⊴r) = all k
least D all down (k , ⊴◃ d) = down (all k) d
```
