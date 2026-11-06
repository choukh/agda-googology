# 两种种类的折叠 (二): 第 1 层读回成高度, 丢掉高度分量

> 不含记号. 入口 [HtTowerF](HtTowerF.lagda.md). 新种类 `κH` 的坐标是 `H₀` 的高度; 它的读回层是第 1 层 (`D₁ = D (hs hz)`). 两件事:
>
> - `rd`: 第 1 层的树接在高度 $b$ 后面读成 `H₀` 的高度. 与 [HtOutRead](HtOutRead.lagda.md) 的 `rd` 同形 (`ni`, `nκ` 读成对坐标递归的 $\Omega$-分支 `nbA`), 世界成对; 第 1 层没有 `nμ` (`NZ₁ (hs hz)` 是空的). `Lg-rd`: 底合法则读出合法; `rd-fst`: 底是读出的第一位置, 在一切世界.
> - `drp₁`: 第 1 层的树不看世界的高度分量, 换成任意别的. 这是回灌时 "丢掉升高的分量" 的那一步; 在类型层的依据同 [HtTowerStrat](HtTowerStrat.lagda.md) 的 `θ-indep` (低于读回层的层不看高分量). 不需要两个世界的并 (`no-joinᴮ`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtTowerFRead where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; lg⊲; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree
```

## §1 对 `A` 坐标递归的分支

```agda
nbA : H₀ → (A → H₀ → H₀) → A → H₀
nbA b s azero = b
nbA b s (asuc c) = s c (nbA b s c)
nbA b s (alim f) = hl (λ n → nbA b s (f n))

module _ {b : H₀} {s : A → H₀ → H₀} (fs : ∀ c h {w} → h ⊲[ w ] s c h) where
  nbA-mono : ∀ {c c′} → c ⊲ c′ → ∀ {w} → nbA b s c ⊲[ w ] nbA b s c′
  nbA-mono C.self = hself
  nbA-mono (C.suc p) = ⊲ᴮ-tr (nbA-mono p) (fs _ _)
  nbA-mono (C.lim n p) = hlim n (nbA-mono p)

  Lg-nbA : LgB b → (∀ c h → LgB h → LgB (s c h)) → LgB {S₀} (hΩ tt (nbA b s))
  Lg-nbA lb ls = (λ lw e e′ p → nbA-mono p) , lg
    where
    lg : ∀ c → Lg c → LgB (nbA b s c)
    lg azero _ = lb
    lg (asuc c) l = ls c _ (lg c l)
    lg (alim f) (st , l) = (λ n → nbA-mono (st n)) , (λ n → lg (f n) (l n))
```

## §2 读回

```agda
toD : ∀ {W} → A → D₀ W
toD azero = n0
toD (asuc c) = toD c ⨾ n1
toD (alim f) = nl (λ n → toD (f n))

D₁ : Wd₂ → Set
D₁ = D (hs hz)

-- nκ 的坐标 c 上的世界: A 分量取 w₀ 接上 toD c
wκ : A → A → A
wκ w₀ c = sum {azero , hz} w₀ (toD c)

lwκ : ∀ {w₀} c → Lg w₀ → Lg (wκ w₀ c)
lwκ {w₀} c l = Lg-sum w₀ (toD c) l

pwκ : ∀ w₀ c → w₀ ⊲ wκ w₀ c
pwκ w₀ c = sum-fst w₀ (toD c)

rd  : ∀ {W} → LgW₂ W → H₀ → D₁ W → H₀
rdp : ∀ {W} → LgW₂ W → H₀ → (ℕ → D₁ W) → ℕ → H₀
rd lW b n0 = b
rd lW b n1 = hs b
rd lW b (x ⨾ y) = rd lW (rd lW b x) y
rd lW b (nl d) = hl (rdp lW b d)
rd lW b (ni (ss hself) u) = hΩ tt (nbA b (λ c h → rd lW h (u ≤rf lW (toD c))))
rd {W} lW b (nκ _ u) =
  hΩ tt (nbA b (λ c h → rd (lwκ c (proj₁ lW) , proj₂ lW) h (u (pwκ (proj₁ W) c) (lwκ c (proj₁ lW)))))
rd lW b (nμ () u)
rd lW b (nw p x) = rd (lgW≤ p lW) b x
rdp lW b d zero = b
rdp lW b d (suc n) = rd lW (rdp lW b d n) (d n)

rd-fst : ∀ {W} (lW : LgW₂ W) b (x : D₁ W) {w} → b ⊲[ w ] rd lW b x
rd-fst lW b n0 = hself
rd-fst lW b n1 = hsuc hself
rd-fst lW b (x ⨾ y) = ⊲ᴮ-tr (rd-fst lW b x) (rd-fst lW (rd lW b x) y)
rd-fst lW b (nl d) = hlim 0 hself
rd-fst lW b (ni (ss hself) u) {w} = hLim {S₀} {c = azero} (z⊲ w) hself
rd-fst lW b (nκ _ u) {w} = hLim {S₀} {c = azero} (z⊲ w) hself
rd-fst lW b (nμ () u)
rd-fst lW b (nw p x) = rd-fst (lgW≤ p lW) b x

Lg-rd  : ∀ {W} (lW : LgW₂ W) b (x : D₁ W) → LgB b → LgB (rd lW b x)
Lg-rdp : ∀ {W} (lW : LgW₂ W) b (d : ℕ → D₁ W) → LgB b → ∀ n → LgB (rdp lW b d n)
Lg-rd lW b n0 l = l
Lg-rd lW b n1 l = l
Lg-rd lW b (x ⨾ y) l = Lg-rd lW (rd lW b x) y (Lg-rd lW b x l)
Lg-rd lW b (nl d) l = (λ n → rd-fst lW (rdp lW b d n) (d n)) , Lg-rdp lW b d l
Lg-rd lW b (ni (ss hself) u) l =
  Lg-nbA (λ c h → rd-fst lW h (u ≤rf lW (toD c))) l (λ c h lh → Lg-rd lW h (u ≤rf lW (toD c)) lh)
Lg-rd {W} lW b (nκ _ u) l =
  Lg-nbA (λ c h → rd-fst (lwκ c (proj₁ lW) , proj₂ lW) h (u (pwκ (proj₁ W) c) (lwκ c (proj₁ lW)))) l
         (λ c h lh → Lg-rd (lwκ c (proj₁ lW) , proj₂ lW) h (u (pwκ (proj₁ W) c) (lwκ c (proj₁ lW))) lh)
Lg-rd lW b (nμ () u) l
Lg-rd lW b (nw p x) l = Lg-rd (lgW≤ p lW) b x l
Lg-rdp lW b d l zero = l
Lg-rdp lW b d l (suc n) = Lg-rd lW (rdp lW b d n) (d n) (Lg-rdp lW b d l n)
```

## §3 丢掉高度分量

```agda
drp₁ : ∀ {w₀ x y} → LgW₂ (w₀ , x) → D₁ (w₀ , x) → D₁ (w₀ , y)
drp₁ l n0 = n0
drp₁ l n1 = n1
drp₁ l (a ⨾ b) = drp₁ l a ⨾ drp₁ l b
drp₁ l (nl d) = nl (λ n → drp₁ l (d n))
drp₁ {x = x} l (ni (ss hself) u) =
  ni (ss hself) (λ {W″} q lW″ z → drp₁ (proj₁ lW″ , proj₂ l) (u {proj₁ W″ , x} (proj₁ q , hself) (proj₁ lW″ , proj₂ l) (drp z)))
drp₁ l (nκ zz u) = nκ zz (λ p lc → drp₁ (lc , proj₂ l) (u p lc))
drp₁ l (nμ () u)
drp₁ l (nw p t) = nw (proj₁ p , hself) (drp₁ (lgW≤ p l) t)
```
