# 可数层的对角, 第四轮 (一): 结构的翻译在对不上的分量里不合法

> 不含记号. 入口 [DiagK4](DiagK4.lagda.md). `DiagK3` 提的下一步: 回灌的增量经结构的翻译 $\mathrm{tr}_{c_0\to c}$ 进一切分量. 增量 `Ωtop S₀` 是 `κ₂` (坐标 `HB S₁`) 的一个坐标. 翻进坐标 `hs (hs (hs hz))` 处同一路径上的种类 (坐标 `HB (step S₁)`) 时, 外层的新种类对得上 (`inj₂ tt` 对 `inj₂ tt`), 但它的坐标类型对不上 ($H_0$ 对 `HB S₁`): 翻译后的节点要把新坐标**倒译**回旧坐标 (`back : HB S₁ → H₀`).
>
> - **`¬Lg-Tr₀`** (定理): 倒译取自然的结构写法 `back₀` (对不上的种类 `κH` 取底分支, 与 `DiagK3Zero.pr₀` 同法) 时, 翻译结果 `Tr₀` **不合法**, 尽管原增量合法 (`Lg-Ωtop`). 反例世界合法 (`lw⋆`), 两个坐标有界且有序 (`hs hz` 在 `Ωtop S₀` 之下), 倒译后次序反了 (`hs hz` 对 `hz`).
> - 原因 (判断): 合法的 $\Omega$-节点要分支对坐标单调, 倒译就要单调; `pr₀` 那里成立, 是因为原高度的合法性可以只在 "对不上的种类的界最小" 的世界里用 (`bdBot`). 倒译方向相反: 世界是翻译后那一边给的, 其中 `κH` 的界可以任意大, 底分支挡不住.
> - **`Lg-const`** (定理): 倒译取常值时合法; 这正是有损的那一种 (翻译后的节点不看坐标).
>
> **范围.** 否定的是 "对不上的种类取底分支" 这一种倒译 (自然的结构翻译), 不是一切翻译. 合法的倒译存在 (常值); 忠实又单调的倒译是否存在, 这里没有定理 (判断: 不存在, 理由同上, 见入口).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.DiagK4Neg where

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁)
open import OCF.Align.CumReadCF using (azero)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop; Lg-Ωtop)

S₁ : KS
S₁ = step S₀
```

## §1 自然的倒译: 对不上的种类取底分支

```agda
back₀ : HB S₁ → HB S₀
back₀ hz = hz
back₀ (hs x) = hs (back₀ x)
back₀ (hl f) = hl (λ n → back₀ (f n))
back₀ (hΩ (inj₁ tt) g) = hΩ tt (λ c → back₀ (g c))
back₀ (hΩ (inj₂ tt) g) = back₀ (g hz)
```

## §2 翻译后的增量

`Ωtop S₀ = hΩ κH up` 在坐标类型 `HB (step S₁)` 里的结构翻译: 外层新种类对新种类, 分支 `up c` 只含底种类, 翻成 `up (up c)`; 新坐标 $c'$ 经 `back₀` 倒译.

```agda
Tr₀ : HB (step S₁)
Tr₀ = hΩ (inj₂ tt) (λ c′ → up (up (back₀ c′)))

src-legal : LgB (Ωtop S₀)
src-legal = Lg-Ωtop S₀

w⋆ : Wd (step S₁)
w⋆ = (azero , hs hz) , Ωtop S₀

lw⋆ : LgW (step S₁) w⋆
lw⋆ = (tt , tt) , Lg-Ωtop S₀

-- 坐标 hs hz 在 w⋆ 里有界, 且在 Ωtop S₀ 之下 (κH 的界是 hs hz)
b₁ : hs hz ⊲[ proj₁ w⋆ ] Ωtop S₀
b₁ = hLim {c = hs hz} hself hself

¬Lg-Tr₀ : LgB Tr₀ → ⊥
¬Lg-Tr₀ (mo , l) with mo {w⋆} {hs hz} {Ωtop S₀} lw⋆ b₁ hself b₁
... | ()
```

## §3 常值倒译合法 (有损)

```agda
Lg-const : ∀ (h : HB S₁) → LgB h → LgB {step S₁} (hΩ (inj₂ tt) (λ _ → up h))
Lg-const h lh = (λ lw e e′ p → hself) , (λ c lc → Lg-up h lh)
```
