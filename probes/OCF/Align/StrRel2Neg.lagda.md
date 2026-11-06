# 结构关系, 第二轮 (二): 沿任意路径只由值对齐 `Walk` 的位置推出 LPO

> 不含记号. 入口 [StrRel2](StrRel2.lagda.md). `KNest2Glue.CellStep` 的格路径 $p:a\lhd W$, $p':a'\lhd W'$ 是任意的字面路径, 前提只有值: $\mathrm{Adm}(a,a';W,W')$, 起点可比, $W\le W'$. 第 0 格的路径就是这样: `κc zero` 的路径是 `⊲-tr q₀ (sum-fst W z)`, 前一段 $q_0$ 来自树里的 `nw`, 没有坐标树.
>
> **`PHead`**: 一个过程, 对一切两条合法路径与上面的值前提, 把左边 `Walk` 的每个位置 (`StrRel2Pos.WP`) 送到右边 `Walk` 的一个位置, 两层满足领先量 $\mathrm{Adm}(c,c';W,W')$.
>
> **定理 `phead→LPO : PHead → LPO`.** 证明: 由 `StrRel2Pos` 的桥 (`toW`, `fromW`), 沿 `sum-fst 0 x` 的位置就是树 $x$ 的位置, 领先量经左消去律 (`cancel`) 化成剩余长度的比较, 于是 `PHead` 推出 `StrRelNeg.VHead`, 再用 `vhead→LPO`.
>
> **范围.** 只杀 "对任意字面路径只由值求对应位置". 不杀路径带着结构 (`sum-fst` 加推导) 的情形 (`StrRel2Pos.walkHead`). 判断: 所以 `CellStep` 的第 0 格不能照原样 (任意 $q_0$) 证; 要么 $q_0$ 也由推导给出结构, 要么保留 `KNest2` 的 "树世界可比" 一类前提并换一种对齐 (见入口 §3).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel2Neg where

open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg)
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; ≤lim⁻; irr; _⊞_; ≤⊞; ⊞-mono; ⊞-asso; ⊞-assoʳ; z⊞)
open import OCF.Align.HtFeedTree using (D; hz; sum; sum-fst; Lg-sum)
open import OCF.Align.StrRelHead using (val; Sp; pre; rem; dec; Adm; ≡→≤)
open import OCF.Align.StrRelNeg using (VHead; LPO; vhead→LPO)
open import OCF.Align.StrRel2Pos using (WP; lev; toW; fromW)
```

## §1 陈述

```agda
PHead : Set
PHead = ∀ {a b a′ b′} (p : a ⊲ b) (p′ : a′ ⊲ b′) (lb : Lg b) (lb′ : Lg b′) → a ≤ a′ → Adm a a′ b b′ →
        (w : WP b p lb) → Σ (WP b′ p′ lb′) (λ w′ → Adm (lev b p lb w) (lev b′ p′ lb′ w′) b b′)
```

## §2 左消去

```agda
cancel : ∀ c x y → c ⊞ x ≤ c ⊞ y → x ≤ y
cancel c azero y h = z≤
cancel c (asuc x) azero h = ⊥-elim (irr c (≤-trans (s≤ (≤⊞ c x)) h))
cancel c (asuc x) (asuc y) (s≤ h) = s≤ (cancel c x y h)
cancel c (asuc x) (alim g) h with ≤lim⁻ h
... | n , h′ = ≤l n (cancel c (asuc x) (g n) h′)
cancel c (alim f) y h = l≤ (λ n → cancel c (f n) y (≤-trans (≤l n (≤-refl _)) h))

z⊞′ : ∀ δ → azero ⊞ δ ≤ δ
z⊞′ azero = z≤
z⊞′ (asuc δ) = s≤ (z⊞′ δ)
z⊞′ (alim g) = l≤ (λ n → ≤l n (z⊞′ (g n)))
```

## §3 定理

```agda
phead→vhead : PHead → VHead
phead→vhead ph {V} x x′ le s =
  let (w , e) = toW azero x tt s
      (w′ , (δ , h₁ , h₂)) = ph (sum-fst azero x) (sum-fst azero x′) (Lg-sum azero x tt) (Lg-sum azero x′ tt) z≤
                               (val x , z⊞ (val x) , ≤-trans (z⊞′ (val x)) le) w
      (s′ , e′) = fromW azero x′ tt w′
      c = val (pre s)
      c′ = val (pre s′)
      -- 1 + rem s ≤ δ
      a₁ : c ⊞ (asuc azero ⊞ rem s) ≤ c ⊞ δ
      a₁ = ≤-trans (⊞-asso c (asuc azero) (rem s))
             (≤-trans (proj₂ (dec azero s)) (≤-trans h₁ (⊞-mono (≡→≤ e) (≤-refl δ))))
      -- δ ≤ 1 + rem s′
      a₂ : c′ ⊞ δ ≤ c′ ⊞ (asuc azero ⊞ rem s′)
      a₂ = ≤-trans (⊞-mono (≡→≤ (sym e′)) (≤-refl δ))
             (≤-trans h₂ (≤-trans (proj₁ (dec azero s′)) (⊞-assoʳ c′ (asuc azero) (rem s′))))
  in s′ , cancel (asuc azero) (rem s) (rem s′) (≤-trans (cancel c _ δ a₁) (cancel c′ δ _ a₂))

phead→LPO : PHead → LPO
phead→LPO ph = vhead→LPO (phead→vhead ph)
```
