# 最小比较表: 对否定一族的前提

> 验收文件 (不读记号), 不进成品. 编译定理, 无前提. (1) 表 `rbᶻ` 的条目只在探针 `zero` 处落在对角线上 (`on-zero`; 后继与 ℕ 极限处对角线为空, `YiMTTab.ent-ss`, `ent-ll`). (2) 塔第 2 项的顶层上 "有没有条目" 是 `YiAbsObs.Sep zero` 的实例 (`sep-tw2`), 所以 `sep→wdec`, `YiTBObs.exact→wdec` 的前提在探针 `zero` 处成立; 结论 "与 `zero` 的字面相等弱可判" 对一切层的树无前提成立, 而且可判 (`dec0`), 没有矛盾.
> (3) 塔第 1 项的顶层上 `Sep` 的 "别的孩子处为假" 不成立 (`off-fails-tw1`: 孩子 `suc zero` 对 `zero` 也有条目). (4) 不带 `Maybe` 的全表仍不存在 (`YiTBObs.no-total`, 原样引用).
> 范围: 说的是表这个数据; 折叠输出头部上的 `YiAbsFrame.branch→wdec` 前提没有在这个块上陈述. 表的类型里没有孩子相等的证据, `viaE→dec` 的证据函数不是它的实例 (读类型, 判断).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiMTObs where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiMTTab
open import OCF.Lean.YiTBObs using (isJ; exact→wdec; no-total)
open import OCF.Lean.YiAbsObs using (Sep; WDec; sep→wdec)
```

## 与零的字面相等可判

```agda
dec0 : ∀ {k} (c : Tr k) → (zero ≡ c) ⊎ (zero ≡ c → ⊥)
dec0 zero         = inj₁ refl
dec0 (suc c)      = inj₂ (λ ())
dec0 (lim f a)    = inj₂ (λ ())
dec0 (Ω p g)      = inj₂ (λ ())
dec0 (up x c y e) = inj₂ (λ ())
```

## 探针 `zero`

```agda
on-zero : ∀ k h → isJ (tbᶻ k h zero zero) ≡ true
on-zero k h = refl

h₂ : Tr (tw 1) → L
h₂ c = tw 1 ⊕ ↑ (tw 1) c

off-tw2 : (c : Tr (tw 1)) → (zero ≡ c → ⊥) → isJ (tbᶻ (tw 1) h₂ c zero) ≡ false
off-tw2 zero         ne = ⊥-elim (ne refl)
off-tw2 (suc c)      ne = refl
off-tw2 (lim f a)    ne = refl
off-tw2 (Ω p g)      ne = refl
off-tw2 (up x c y e) ne = refl

sep-tw2 : Sep {C = Tr (tw 1)} zero
sep-tw2 = record { f = λ c → isJ (tbᶻ (tw 1) h₂ c zero) ; on = refl ; off = off-tw2 }

wdec-tw2 : (c : Tr (tw 1)) → WDec (zero ≡ c)
wdec-tw2 = exact→wdec (tbᶻ (tw 1) h₂) zero refl off-tw2
```

## 塔第 1 项的顶层: 对角线之外也有条目

```agda
h₁ : Tr zero → L
h₁ c = zero ⊕ ↑ zero c

off-fails-tw1 : ((c : Tr zero) → (zero ≡ c → ⊥) → isJ (tbᶻ zero h₁ c zero) ≡ false) → ⊥
off-fails-tw1 off with off (suc zero) (λ ())
... | ()
```
