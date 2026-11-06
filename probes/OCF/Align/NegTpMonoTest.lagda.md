# `T⁺` 对输入单调, 否定一路 (四): 两个合法性证明上的有限测试

> 不含记号. 入口 [NegTpMono](NegTpMono.lagda.md). **有限测试, 不是证明.**
>
> `NegTpMonoSim` 的 $h_2$ 有两个合法性证明 $l_1\ne l_2$ (`l₁≢l₂`). 想找 `LgIrr T⁺` 在值上的反例, 先看两棵输出树在字面上分不分得开:
>
> - `T⁺ h₂ l₁ ≡ T⁺ h₂ l₂` 用 `refl` 检查**不过** (报错原文: `st₁ n != st₂ n of type f₂ n ⊲[ w ] f₂ (suc n)`): 输出的范式里, 在 ℕ-极限的变量 $n$ 之下卡着合法性证明的第 $n$ 步. 这只说明输出树字面上读了合法性证明, 不说明两棵树不同 (变量处卡住不是不等).
> - 比较器 `agree d w` (宽 $w$: ℕ-极限只看前 $w$ 项; 深 $d$: 只下降 $d$ 层极限; 后继不计深度) 在宽 3 深 12 上判两棵树同形 (`t12`); 对照: 同一比较器在宽 3 深 8 上就分开了 `T⁺ h₂ l₁` 与 `T⁺ 1` (`c8`), 所以它对这类输出有分辨力. 盲区: 宽 3 之外的项, 深 12 以下, 以及同形而值不同的情形 (值只经 $\le$ 比较).
>
> 所以在这个测试能看到的范围里, `T⁺` 没有因合法性证明不同而分开; 没有找到 `LgIrr T⁺` 的反例 (测试档).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegTpMonoTest where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim)
open import OCF.Align.HtTowerTy using (hs; hz)
open import OCF.Align.HtTowerFClosed using (T⁺)
open import OCF.Align.NegTpMonoSim using (h₂; l₁; l₂)

agree  : ℕ → ℕ → A → A → Bool
agreeL : ℕ → ℕ → ℕ → (ℕ → A) → (ℕ → A) → Bool
agree d w azero azero = true
agree d w (asuc x) (asuc y) = agree d w x y
agree zero w (alim f) (alim g) = true
agree (suc d) w (alim f) (alim g) = agreeL d w w f g
agree d w _ _ = false
agreeL d w zero f g = true
agreeL d w (suc i) f g = agree d w (f i) (g i) ∧ agreeL d w i f g

t12 : agree 12 3 (T⁺ h₂ l₁) (T⁺ h₂ l₂) ≡ true
t12 = refl

-- 对照: 比较器分得开不同的输入
c8 : agree 8 3 (T⁺ h₂ l₁) (T⁺ (hs hz) tt) ≡ false
c8 = refl
```
