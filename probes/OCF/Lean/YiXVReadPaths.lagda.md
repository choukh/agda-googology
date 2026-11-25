# YiXVReadPaths
> 验收文件。档位：编译定理。实际源零层的第一位置路径与弱路径，和原第一位置证明互相转换；含同一闭上界的两个实例。
> 保留原 h₁、lvl、B₀ 与折叠；初始化参照取 read(root) 的零前缀嵌入。未交原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadPaths where
open import Data.Nat using (ℕ; suc)
import OCF.Lean.YiLegBlock as S
infix 4 _≺ᵀ_ _≤ᵀ_
data _≺ᵀ_ : S.Tr S.zero → S.Tr S.zero → Set where
  root : ∀ {x : S.Tr S.zero} → x ≺ᵀ S.suc x
  under-suc : ∀ {x y : S.Tr S.zero} → x ≺ᵀ y → x ≺ᵀ S.suc y
  branch : ∀ {f : ℕ → S.Tr S.zero} {a : ∀ n → S.zero S.⊢ f n ◃ f (suc n)} n → f n ≺ᵀ S.lim f a
  under-lim : ∀ {x : S.Tr S.zero} {f : ℕ → S.Tr S.zero} {a : ∀ n → S.zero S.⊢ f n ◃ f (suc n)} n → x ≺ᵀ f n → x ≺ᵀ S.lim f a
data _≤ᵀ_ : S.Tr S.zero → S.Tr S.zero → Set where
  here : ∀ {x : S.Tr S.zero} → x ≤ᵀ x
  below : ∀ {x y : S.Tr S.zero} → x ≺ᵀ y → x ≤ᵀ y
trans : ∀ {x y z} → x ≺ᵀ y → y ≺ᵀ z → x ≺ᵀ z
trans p root = under-suc p
trans p (under-suc q) = under-suc (trans p q)
trans p (branch n) = under-lim n p
trans p (under-lim n q) = under-lim n (trans p q)
advance : ∀ {x y z} → x ≤ᵀ y → y ≺ᵀ z → x ≺ᵀ z
advance here q = q
advance (below p) q = trans p q
normal : ∀ {x y : S.Tr S.zero} → S.zero S.⊢ x ◃ y → x ≺ᵀ y
normal S.◃s = root
normal (S.◃l n) = branch n
normal (S.◃w {p = ()})
normal (S.◃u x () y e)
normal (S.◃c x () e)
normal (S.◃t p q) = trans (normal p) (normal q)
raw : ∀ {x y : S.Tr S.zero} → x ≺ᵀ y → S.zero S.⊢ x ◃ y
raw root = S.◃s
raw (under-suc p) = S.◃t (raw p) S.◃s
raw (branch n) = S.◃l n
raw (under-lim n p) = S.◃t (raw p) (S.◃l n)
left-model : S.zero ≺ᵀ S.suc (S.suc S.zero)
left-model = under-suc root
right-model : S.suc S.zero ≺ᵀ S.suc (S.suc S.zero)
right-model = root
```
