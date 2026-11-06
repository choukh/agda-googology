# 单层 `nκ` (三): `κ⊑` 的处理, `hi` 档无条件

> 不含记号. 入口 [KValK](KValK.lagda.md). 构造 `KValSound.KH hi` 的一个元素 `kh`, 于是 **`snd-hi = snd kh`**: `hi` 档 (含 `κ⊑`) 的跨世界单调只剩动作前提 `Ok` 与上下文 `Cx hi`.
>
> 证法 (每一步的依据):
>
> - 两边各是一串回灌的格 (`KValKIter.It`). 第 $n$ 个部分和 $\approx$ 从 `cv Y` 走一次 `Pre n` (`cl`).
> - `Pre n` $\approx$ `Cut u [V, a_n)` (`PreCut`). 左右的区间和由**包含式对齐** `CutM` 相关: 起点 $V'\le V$ (`κ⊑` 的前提), 终点 $a_{n+1}=v_n\le v'_n=a'_{n+1}$.
> - $v_n\le v'_n$: $v_n\approx\ell+$ 前 $n$ 格 (`vpt`, `ptv`), 两边的 $\ell\le\ell'$ 是 `hi` 档上下文的 `Hℓ`; 前 $n$ 格的比较就是在第 $n$ 步要证的东西, 所以对 $n$ 归纳 (`mono-n` 与 `PP` 互相调用, $n$ 递减).
> - 两边在各自的格世界里走 `Pre n`, 跨世界由 `snd-lo`.
>
> 逐格的比较 (右边第 $n$ 格从更高的层起步) 用不到: 比的是整段.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.KValKHi where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; ≤l; l≤; ≤-refl; ≤-trans)
open import OCF.Align.SumOneTree using (D; n0; nκ; sum; pt)
import OCF.Align.SumOneClosed as F
open import OCF.Align.LayerTrOne using (one)
open import OCF.Align.KValTree
open import OCF.Align.KValSem
open import OCF.Align.KValSound
open import OCF.Align.KValCut using (module Two)
open import OCF.Align.KValKIter using (module It)
```

## §1 处理

```agda
kh : KH hi
kh {V} {V′} {zz} {zz′} {u} {u′} V≤ mono mono′ kx s s′ o q q′ w w′ Y Y′ (cx a b v hl) c c′ cb =
  l≤ (λ n → ≤l n (mono-n n c c′ cb))
  where
  module L = It s (okL o) u mono q w Y a
  module R = It s′ (okR o) u′ mono′ q′ w′ Y′ b
  module T2 = Two u u′ mono mono′ kx

  vv : ∀ n → vY (L.side n) (L.Y⁰ n) ≤ vY (R.side n) (R.Y⁰ n)
  vv n = ≤-trans (cv≤ Y (F.wv (L.K n)) (F.lv (L.K n)) a (inj₁ (κ₀ (ll (L.side n)))) (inj₁ (κ₀ (ll s))))
         (≤-trans v (≤cv Y′ (F.wv (R.K n)) (F.lv (R.K n)) b (inj₁ (κ₀ (ll s′))) (inj₁ (κ₀ (ll (R.side n))))))

  mono-n : ∀ n c c′ → c ≤ c′ → pt c L.dκ n ≤ pt c′ R.dκ n
  PP : ∀ n → L.Pre n ⊑[ lo ] R.Pre n

  mono-n n c c′ h =
    ≤-trans (proj₁ (L.cl n) c c (≤-refl c))
    (≤-trans (snd-lo (PP n) (L.side n) (R.side n) (ok↾ o (F.wv (L.K n)) (F.wv (R.K n)) (F.lv (L.K n)) (F.lv (R.K n)))
                     C.self C.self n0 n0 (L.Y⁰ n) (R.Y⁰ n) (cx (L.cohY⁰ n) (R.cohY⁰ n) (vv n) tt) c c′ h)
             (proj₁ (proj₂ (R.cl n)) c′ c′ (≤-refl c′)))

  PP zero = n0⊑
  PP (suc n) =
    trˡ (proj₁ (L.PreCut (suc n)))
        (trʳ (T2.CutM _ _ (F.ap (L.K (suc n))) (F.ap (R.K (suc n))) C.self C.self _ _ (F.av (L.K (suc n))) (F.av (R.K (suc n)))
                      V≤ (≤-trans (L.vpt n) (≤-trans (mono-n n L.ℓ R.ℓ hl) (R.ptv n))))
             (proj₂ (R.PreCut (suc n))))
```

## §2 `hi` 档的单调

```agda
snd-hi : ∀ {V V′} {x : D one V} {x′ : D one V′} → x ⊑[ hi ] x′ → OutLe hi x x′
snd-hi = snd kh
```
