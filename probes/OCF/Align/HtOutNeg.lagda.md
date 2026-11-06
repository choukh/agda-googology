# 高度来自折叠的输出 (四): 分支的哪些字段不能去掉

> 不含记号. 入口 [HtOut](HtOut.lagda.md). [HtOutRead](HtOutRead.lagda.md) 的 `cont→LgH` 用到 `Cont` 的两条形状字段: 极限处字面连续 (`c-lim`), 后继处步进 (`c-suc`). 下面前两条各给一个反例, 满足其余三条字段, 缺一条, 而 `hΩ g` 不合法; 第三条划出 $\Omega$-迭代回灌的障碍. 前提都可满足 (反例就是见证).
>
> 1. **`drop-lim`**: 去掉连续. 反例是 [HtFeedNeg](HtFeedNeg.lagda.md) 的 `gx` (第 $0$ 支是 $\Omega$, 后继支往上一格, 极限支一律是 $\omega'$). 它满足后继步进 (就是 `LayerTr` 的 `LgB` 对 `bi` 的要求), 不连续, `LgH (hΩ gx)` 不成立 (世界 $\omega$ 里 $\Omega$ 不在 $\omega'$ 之下). 这比 `no-weak` 多一步: `no-weak` 说弱合法的高度上没有比较, 这里说它连 `LgH` 都不满足, 而缺的那条字段正是连续.
> 2. **`drop-suc`**: 去掉步进. 反例 `gd`: $g(0)=1$, $g(c+1)=0$, 极限处连续. `LgH (hΩ gd)` 不成立 ($1\not\lhd 0$).
> 3. **`no-total`**: 连续且后继处严格变大的分支, 不能在**一切**坐标上都合法 (坐标不合法时, 极限支 `hl (g ∘ f)` 可以来回跳). 这是 $\Omega$-迭代回灌算子的障碍: `Fb` 只在合法高度上有定义 (折叠要最高层合法), 迭代时要在每个坐标上喂合法的高度, 而 `hΩ` 的分支对一切 `A` 都要有值.
>
> **范围.** 前两条只说 `Cont` 这四条字段里, 两条形状字段各自不能去掉. 不说 `LgH (hΩ g)` 推出 `Cont g` (判断不成立: 极限支取 `hl (g ∘ f)` 再加一, 应仍合法; 没有编译). `no-total` 只否定 "连续, 后继严格变大, 且一切坐标 (含不合法的) 上合法"; 不否定把分支的定义域改成合法坐标, 也不否定让折叠在不合法的最高层上也有定义. `drop-lim` 只说 "后继处步进" (`LayerTr` 的 `LgB` 对 `bi` 的要求) 这个条件推不出 `LgH`; 不说 `LayerTr.toB` 那样的每个具体读法都不合法.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtOutNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtFeedTree using (H; hz; hs; hl; hΩ; _⊲[_]_; hself; hsuc; hlim; hLim; ⊲ᴴ-tr; LgH)
open import OCF.Align.HtFeedHt using (Ωᴴ; Lg-Ωᴴ)
open import OCF.Align.HtFeedNeg using (gx; no₂; lω; natA)
```

## §1 去掉连续

```agda
hd : H → H
hd (hl f) = f 0
hd h = h

gx-suc : ∀ c → gx c ⊲[ azero ] gx (asuc c)
gx-suc c = hsuc hself

gx-lgz : LgH (gx azero)
gx-lgz = Lg-Ωᴴ

gx-lgs : ∀ c → LgH (gx c) → LgH (gx (asuc c))
gx-lgs c l = l

gx-not-lim : ¬ (∀ f → gx (alim f) ≡ hl (λ n → gx (f n)))
gx-not-lim h with cong hd (h natA)
... | ()

gx-not-Lg : ¬ LgH (hΩ gx)
gx-not-Lg (mo , _) = no₂ (mo lω (z⊲ (alim natA)))

drop-lim :
  (∀ c → gx c ⊲[ azero ] gx (asuc c)) × LgH (gx azero) × (∀ c → LgH (gx c) → LgH (gx (asuc c))) ×
  ¬ (∀ f → gx (alim f) ≡ hl (λ n → gx (f n))) × ¬ LgH (hΩ gx)
drop-lim = gx-suc , gx-lgz , gx-lgs , gx-not-lim , gx-not-Lg
```

## §2 去掉步进

```agda
gd : A → H
gd azero = hs hz
gd (asuc c) = hz
gd (alim f) = hl (λ n → gd (f n))

gd-not-Lg : ¬ LgH (hΩ gd)
gd-not-Lg (mo , _) with mo {azero} {asuc azero} tt (C.suc C.self)
... | ()

gd-not-suc : ¬ (∀ c → gd c ⊲[ azero ] gd (asuc c))
gd-not-suc h with h azero
... | ()

drop-suc :
  (∀ f → gd (alim f) ≡ hl (λ n → gd (f n))) × LgH (gd azero) × (∀ c → LgH (gd c) → LgH (gd (asuc c))) ×
  ¬ (∀ c → gd c ⊲[ azero ] gd (asuc c)) × ¬ LgH (hΩ gd)
drop-suc = (λ f → refl) , tt , (λ c l → tt) , gd-not-suc , gd-not-Lg
```

## §3 连续且严格变大的分支不能处处合法

先证 $\lhd$ 里没有 $h+1\lhd h$ 这种圈 (对 $a$ 结构递归).

```agda
no-cyc : ∀ {W} a {x} → a ⊲[ W ] x → hs x ⊲[ W ] a → ⊥
no-cyc (hs x) p hself = no-cyc x hself p
no-cyc (hs b) p (hsuc q) = no-cyc b (⊲ᴴ-tr (hsuc hself) p) q
no-cyc (hl f) p (hlim n q) = no-cyc (f n) (⊲ᴴ-tr (hlim n hself) p) q
no-cyc (hΩ g) p (hLim e q) = no-cyc (g _) (⊲ᴴ-tr (hLim e hself) p) q

no-loop : ∀ {W} a → ¬ (hs a ⊲[ W ] a)
no-loop a q = no-cyc a hself q

-- 坐标 0, 1, 0, 1, …: 不合法的 A
alt : ℕ → A
alt zero = azero
alt (suc zero) = asuc azero
alt (suc (suc n)) = alt n

no-total : ∀ (g : A → H) → (∀ f → g (alim f) ≡ hl (λ n → g (f n))) → (∀ c → hs (g c) ⊲[ azero ] g (asuc c)) → ¬ (∀ c → LgH (g c))
no-total g cl cs all = no-loop (g azero) (⊲ᴴ-tr (cs azero) (proj₁ (subst LgH (cl alt) (all (alim alt))) 1))
```
