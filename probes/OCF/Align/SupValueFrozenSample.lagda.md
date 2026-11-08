# 冻结更新的限定一致性：sup 中的常值 Ω 节点

这是实际原版与冻结版的闭项比较，不据此推断一般同值。
层取常列 sup(1,1,…)；输入在第 0 分量，是分支恒为 1 的新种类节点。
两版折叠的每一基本列项字面等于 ω 的相应正倍数，故同值为 ω²，因此此输入完全看不到
世界更新。它含 Ω 节点，不只是可数输入，但分支不读坐标。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.SupValueFrozenSample where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₂)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (Lv; mul; _≤ᵛ_; l≤; ≤l)
open import OCF.Lean.Fold1Base using (Wi; ℓT; Lg*; ≤-refl)
import OCF.Lean.Fold1Fold as Old
import OCF.Lean.SupCollapseFrozen as New

m : Cd
m = hl (λ _ → hs hz)

lm : LgB m
lm = (λ n → hself) , (λ n → tt)

pt : hz ⊲ m
pt = hlim 0 (hsuc hself)

input : HB (Lv m)
input = ι 0 (hΩ (inj₂ tt) (λ _ → hs hz))

legal-input : Lg* (ℓT m) input
legal-input = (λ lw b c p → hself) , (λ c lc → tt)

ω : Cd
ω = hl (mul (hs hz))

ω² : Cd
ω² = hl (mul ω)

old new : Cd
old = Old.Φ m lm hz pt (Wi m) input
new = New.Φ m lm hz pt (Wi m) input

at : Cd → ℕ → Cd
at hz n = hz
at (hs a) n = a
at (hl f) n = f n

old-shape : ∀ n → at old n ≡ mul ω n
old-shape zero = refl
old-shape (suc n) = cong (λ a → a ⊞ ω) (old-shape n)

new-shape : ∀ n → at new n ≡ mul ω n
new-shape zero = refl
new-shape (suc n) = cong (λ a → a ⊞ ω) (new-shape n)

old≤new : old ≤ᵛ new
old≤new = l≤ (λ n → ≤l n
  (subst (λ a → a ≤ᵛ at new n) (sym (old-shape n))
    (subst (λ b → mul ω n ≤ᵛ b) (sym (new-shape n)) (≤-refl (mul ω n)))))

new≤old : new ≤ᵛ old
new≤old = l≤ (λ n → ≤l n
  (subst (λ a → a ≤ᵛ at old n) (sym (new-shape n))
    (subst (λ b → mul ω n ≤ᵛ b) (sym (old-shape n)) (≤-refl (mul ω n)))))
```

这里逐项形状对全部 n 归纳证明，然后给出双向值不等式，不使用函数外延，
不是有限展开测试。但样本范围只有此常值 Ω 分支，不能推出一般同值。

`SupCollapseClosed.Tω` 的地板分支是 `up c`，随后遇到的旧 Ω 节点会
读取其所在世界的界；回灌后再次递归时，原版传更新世界而新版传旧世界。
本样本的递归分支只有 1，从不读取这些界，所以不能覆盖 Tω。
要比较 Tω，仍需证明两条轨道中对应分支输出的值序；合法性与更新后
世界合法均不提供这个关系。这个缺口是代码审阅判断，不是否定路线。
翻译账：只验收冻结变体，不改变树或折叠定义。
