# 层号一次封闭: 编译过的否定

> 不含记号. 入口 [LFRe](LFRe.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.
>
> 三条否定划出 `LFReTower.Ω̂` 后继一行的形状 ($\Omega_{h+1}=\sup_c(\Omega_h\boxplus\iota_h(\mathrm{up}\,c))$) 里哪两件是逼出来的, 一条说一次封闭不破 `no-retract`.
>
> - **`no-canon`**: 坐标里的 $\Omega$-节点**不能**换成它读回层的那个新种类 (`rbl`). 例子是第 2 层的坐标 (含 $\Omega_1$-节点) 读成 `SL` 的 `νL lz` 节点: 分支不单调, 节点不合法. 前提可满足: 世界 `Wn` 合法 (`Lg-Wn`). 对照 `Lg-dup`: 同一个节点, 坐标放进第 2 个分量 (`ιL k₂ ∘ up`, 种类重复) 就合法. **范围:** 只否定 "对一切合法世界" 的 `LgB`; 不否定把世界限制成相容的 (各分量的内层界不超过对应层的外层界) 之后的规范读法, 那没有试.
> - **`no-bare`**: 去掉底 $\Omega_h$, 分支只取坐标本身 ($\Omega'_{h+1}=\sup_c\iota_h(\mathrm{up}\,c)$), 塔的相邻项就不再是第一位置: 在一切世界里 $\neg(\Omega'_1\lhd\Omega'_2)$. 原因是 `ι` 把坐标放进第 $h$ 个分量, 里面只有分量 $h$ 的种类 (`OnlyK`). **范围:** 只对这个 (种类重复的) 嵌入; 与 `no-canon` 合读: 规范嵌入不合法, 重复嵌入不带底不单调, 所以底 (和的形状 $\boxplus$) 是这两条逼出的.
> - **`no-retract-SL`**: `HtTowerNeg.no-retract` 在 `SL` 上的实例: 没有种类的坐标收缩到全部高度. 一次封闭是对层号 (种类的下标) 的, 不是对坐标的: 种类 $k$ 的坐标是 `HB (Lv k)`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LFReNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy
open import OCF.Align.LFReBr using (w₀; Lg-w₀)
import OCF.Align.HtTowerNeg as TN
```

## §1 规范种类不合法

第 2 层 $k_2$: `Lv k₂ = step (step S⊥)`, 两个种类: `inj₁ (inj₂ tt)` ($\Omega_1$, 坐标是第 0 层的值) 与 `inj₂ tt` ($\Omega_2$). `cn₂` 把它们读成 `SL` 的 `νL lz`, `νL (ls lz)` (就是 `rbl` 给的读回层).

```agda
k₂ : LH
k₂ = ls (ls lz)

cn₂ : HB (Lv k₂) → HB SL
cn₂ hz = hz
cn₂ (hs c) = hs (cn₂ c)
cn₂ (hl f) = hl (λ n → cn₂ (f n))
cn₂ (hΩ (inj₁ (inj₁ ())) h)
cn₂ (hΩ (inj₁ (inj₂ _)) h) = hΩ (νL lz) (λ d → cn₂ (h d))
cn₂ (hΩ (inj₂ _) h) = hΩ (νL (ls lz)) (λ d → cn₂ (h d))

-- 第 2 层的值 Ω₁: Ω₁-种类上的恒等
upd : HB (Lv lz) → HB (Lv k₂)
upd d = up (up d)

c′ : HB (Lv k₂)
c′ = hΩ (inj₁ (inj₂ tt)) upd

Lg-c′ : LgB c′
Lg-c′ = (λ {w} lw e e′ p → up-⊲ (up-⊲ p)) , (λ d ld → Lg-up (up d) (Lg-up d ld))

one : HB (Lv k₂)
one = hs hz

one⊲c′ : ∀ {w} → proj₂ (proj₁ w) ≡ hs hz → one ⊲[ w ] c′
one⊲c′ {w} eq = hLim {c = hs hz} (sub eq) hself
  where
  sub : ∀ {b : HB (Lv lz)} → b ≡ hs hz → hs hz ⊲[ tt ] b
  sub refl = hself
```

世界 `Wn`: 第 2 层的内层 $\Omega_1$-界是 $1$, 外层界是 $c'$; 第 0 层的界是 $0$. 别的层取最小世界.

```agda
Wn : Wd SL
Wn (ls (ls lz)) = ((tt , hs hz) , hz) , c′
Wn k = w₀ k , hz

Lg-Wn : LgW SL Wn
Lg-Wn (ls (ls lz)) = ((tt , tt) , tt) , Lg-c′
Lg-Wn lz = Lg-w₀ lz , tt
Lg-Wn (ls lz) = Lg-w₀ (ls lz) , tt
Lg-Wn (ls (ls (ls k))) = Lg-w₀ (ls (ls (ls k))) , tt
Lg-Wn (ls (ls (ll f))) = Lg-w₀ (ls (ls (ll f))) , tt
Lg-Wn (ls (ls (lΩ k g))) = Lg-w₀ (ls (ls (lΩ k g))) , tt
Lg-Wn (ls (ll f)) = Lg-w₀ (ls (ll f)) , tt
Lg-Wn (ls (lΩ k g)) = Lg-w₀ (ls (lΩ k g)) , tt
Lg-Wn (ll f) = Lg-w₀ (ll f) , tt
Lg-Wn (lΩ k g) = Lg-w₀ (lΩ k g) , tt

-- 在 Wn 里 1 不是 cn₂ c′ 的第一位置: 第 0 层的界是 0
not-1⊲ : ¬ (hs hz ⊲[ Wn ] cn₂ c′)
not-1⊲ (hLim hself ())

no-canon : ¬ LgB (hΩ (νL k₂) cn₂)
no-canon (mo , _) = not-1⊲ (mo {Wn} {one} {c′} Lg-Wn (one⊲c′ refl) hself (one⊲c′ refl))

Lg-dup : LgB (hΩ (νL k₂) (λ c → ιL k₂ (up c)))
Lg-dup =
  (λ {W} lw e e′ p → ι-⊲ {LH} {FL} {k₂} {w = W} (up-⊲ p)) ,
  (λ c lc → Lg-ι k₂ (up c) (Lg-up c lc))
```

## §2 不带底的塔不单调

```agda
OnlyK : LH → HB SL → Set
OnlyK k hz = ⊤
OnlyK k (hs x) = OnlyK k x
OnlyK k (hl f) = ∀ n → OnlyK k (f n)
OnlyK k (hΩ (j , _) g) = (j ≡ k) × (∀ c → OnlyK k (g c))

ι-OnlyK : ∀ k y → OnlyK k (ιL k y)
ι-OnlyK k hz = tt
ι-OnlyK k (hs y) = ι-OnlyK k y
ι-OnlyK k (hl f) = λ n → ι-OnlyK k (f n)
ι-OnlyK k (hΩ κ g) = refl , (λ c → ι-OnlyK k (g c))

OnlyK-⊲ : ∀ {k a b W} → a ⊲[ W ] b → OnlyK k b → OnlyK k a
OnlyK-⊲ hself o = o
OnlyK-⊲ (hsuc p) o = OnlyK-⊲ p o
OnlyK-⊲ (hlim n p) o = OnlyK-⊲ p (o n)
OnlyK-⊲ (hLim {c = c} e p) (_ , o) = OnlyK-⊲ p (o c)

-- 不带底: Ω′_{h+1} = sup_c ι_h (up c)
Ω′ : LH → HB SL
Ω′ k = hΩ (νL k) (λ c → ιL k (up c))

lz≢ : lz ≡ ls lz → ⊥
lz≢ ()

no-bare : ∀ {W} → ¬ (Ω′ lz ⊲[ W ] Ω′ (ls lz))
no-bare (hLim {c = c} e p) = lz≢ (proj₁ (OnlyK-⊲ p (ι-OnlyK (ls lz) (up c))))
```

## §3 一次封闭不破 `no-retract`

```agda
no-retract-SL : ∀ κ (e : HB SL → E SL κ) (d : E SL κ → HB SL) → ¬ (∀ x → d (e x) ≡ x)
no-retract-SL = TN.no-retract {SL}
```
