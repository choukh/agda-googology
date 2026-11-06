# 终点下界 (树侧): 第一个回灌高度的形状

> 不含记号, 不是验收文件. 入口 [EndLow](EndLow.lagda.md). 为 "`BTBOᴵ ≼ ⟪ T-fb 1 ⟫` 是否要折叠的单调" 这个问题提供编译过的形状事实. 只导入 `HtFeedTree`, `HtOutFeed`.
>
> 结论 (都是对具体项的 `refl`, 不是测试: 第 5 条对变量 $n$ 成立):
>
> 1. `Λ₁ = proj₁ (Λs 1)` (`T-fb 1` 的高度) 是 $\Omega$-极限 `hΩ g₁` (`Λ₁-Ω′`).
> 2. 第 0 支 $g_1(0)$ 是 ℕ-极限 `hl F` (`g₁0-lim`).
> 3. $F(0)$ 是后继 (`F0-suc`); **$F(n+1)$ 对一切 $n$ 都是 $\Omega$-极限** (`F-Ω`).
> 4. 一切 $\Omega$-极限层的 $\Omega_L$ 里有 `nκ` (`Ωd-hΩ`, 定义性的).
>
> 读法 (判断): $g_1(0)\approx\Omega\cdot\omega$, $F(n+1)\approx\Omega\cdot(n+1)$ 一类. `T-fb 1` 的第 0 层回灌走的节点都在层 $g_1(c)$ 上, $g_1(c)\sqsupseteq g_1(0)$ (`Cont`); 所以 `T-fb 1` 里 $\psi_0(\Omega_\Omega)$ 那么大的值只能出自**套在里面的**回灌: 层 $F(1)$ ($\Omega$-极限, 带 `nκ`) 上的节点折叠到第 0 层的目标, 而且是在非空的状态与世界里. 见 [EndLow](EndLow.lagda.md) "作者决定 1".
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EndLowFb where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero)
open import OCF.Align.HtFeedTree using (H; hz; hs; hl; hΩ; D; n1; _⨾_; nκ; Ωd)
open import OCF.Align.HtOutFeed using (Λs)
```

## 形状

`sh` 只看最外的构造子; `br`, `el` 取 $\Omega$-分支与 ℕ-分支 (别的构造子上返回自身, 只为全函数).

```agda
data Sh : Set where
  ʰz ʰs ʰl ʰΩ : Sh

sh : H → Sh
sh hz = ʰz
sh (hs _) = ʰs
sh (hl _) = ʰl
sh (hΩ _) = ʰΩ

br : H → A → H
br (hΩ g) c = g c
br h c = h

el : H → ℕ → H
el (hl f) n = f n
el h n = h

Λ₁ : H
Λ₁ = proj₁ (Λs 1)

Λ₁-Ω′ : sh Λ₁ ≡ ʰΩ
Λ₁-Ω′ = refl

g₁0-lim : sh (br Λ₁ azero) ≡ ʰl
g₁0-lim = refl

F0-suc : sh (el (br Λ₁ azero) 0) ≡ ʰs
F0-suc = refl

F-Ω : ∀ n → sh (el (br Λ₁ azero) (suc n)) ≡ ʰΩ
F-Ω n = refl

Ωd-hΩ : ∀ (g : A → H) {W} → Ωd (hΩ g) {W} ≡ n1 ⨾ nκ _ _
Ωd-hΩ g = refl
```
