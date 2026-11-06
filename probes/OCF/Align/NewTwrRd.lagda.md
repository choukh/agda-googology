# 新塔 (一): 第 2 层读回进 `HB (step T)` (不落回 `Ht`)

> 不含记号. 入口 [NewTwr](NewTwr.lagda.md), 接口 [NewTwrIf](NewTwrIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> [GenFoldRd](GenFoldRd.lagda.md) 的 `rd₂` 把第 2 层的数据读进固定的 `Ht` (接口 `EvSys.evH` 要 `Ht`): 过第 1 层的结点读成 `Ht` 的 κH 结点, 坐标经 `toD₁ : H₀ → D 1` 与 `encH : H₀ → HB T` 来回搬. 这里换成读进**层自己所在的类型** `HB (step T)`:
>
> - 过第 1 层的结点读成 `step T` 的**新种类** `inj₂ tt` 的 $\Omega$-结点, 坐标 $y$ 就是 `HB T` 的高度, 经 `toDᵀ : HB T → D 1` 写成第 1 层的数据作分支的输入. `toDᵀ` 把 $y$ 的 $\Omega$-结点 (任一种类 $\kappa$) 写成旧种类 `inj₁ κ` 的闭包结点 (第 1 层允许旧种类, `ZK`), 分支取世界里 $\kappa$ 的顶坐标; 这就是 `GenFoldTree.Om.Ωd` 的 $\Omega$-行的写法, 对一切种类一条, 不判定种类.
> - 过第 0 层的结点读成底种类 `inj₁ (aK G)` 的 $\Omega$-结点 (同 `rd₁`).
> - 新种类的闭包结点读成新种类的 $\Omega$-结点, 坐标 $y$ 处的分支取在新种类的界升到 界 $\boxplus\,y$ 的世界里: 坐标本来就是 `HB T`, 不需要 `encH`.
> - 旧种类的闭包结点有损地读 (当前世界的分支), 同 `rd₂`.
>
> 合法由形状给出, 对一切数据 (`Lg-rdG`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.HtTowerTy using (KS)
open import OCF.Align.GenFoldIf using (GenK; LgDn)
module OCF.Align.NewTwrRd (T : KS) (G : GenK T) (Ld : LgDn T) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (nbᴮ; nb-contB; cont→Lg)
open import OCF.Align.GenFoldIf
open import OCF.Align.GenFoldTree
open Tree T
open import OCF.Align.GenFoldRd T G Ld using (lgW≤; module NbA)
open NbA
```

## §1 `HB T` 的高度写成第 1 层的数据

```agda
toDᵀ : ∀ {W} → HB T → D (hs hz) W
toDᵀ hz = n0
toDᵀ (hs y) = toDᵀ y ⨾ n1
toDᵀ (hl f) = nl (λ n → toDᵀ (f n))
toDᵀ (hΩ κ g) = nc (inj₁ κ) tt (λ {W′} _ _ → toDᵀ (g (top (tpK G) κ (proj₁ W′))))
```

## §2 第 2 层读回进 `HB (step T)`

```agda
qy : ∀ {W} (y : HB T) → W ≤ (proj₁ W , proj₂ W ⊞ y)
qy {W} y = ≤w-rf T , ⊞-fst (proj₂ W) y

lWy : ∀ {W} → LgW L₀ W → (y : HB T) → LgB y → LgW L₀ (proj₁ W , proj₂ W ⊞ y)
lWy lW y ly = proj₁ lW , Lg-⊞ _ y (proj₂ lW) ly

D₂ : Wd L₀ → Set
D₂ = D (hs (hs hz))
```

新种类的闭包: 分支对一切更大的**合法**世界给出; 坐标 $y$ 不一定合法, 所以先把 $y$ 换成合法的 $y^\flat$ (`flatT`: $\Omega$-结点取底坐标的分支, ℕ-极限取部分和, 同 `GenFoldRd.encH` 对 `HB T` 本身), 再升界.

```agda
cumT : (ℕ → HB T) → ℕ → HB T
cumT g zero = g 0
cumT g (suc n) = cumT g n ⊞ g (suc n)

flatT : HB T → HB T
flatT hz = hz
flatT (hs y) = hs (flatT y)
flatT (hl f) = hl (cumT (λ n → flatT (f n)))
flatT (hΩ κ h) = flatT (h (bot T κ))

Lg-cumT : ∀ g → (∀ n → LgB (g n)) → ∀ n → LgB (cumT g n)
Lg-cumT g l zero = l 0
Lg-cumT g l (suc n) = Lg-⊞ (cumT g n) (g (suc n)) (Lg-cumT g l n) (l (suc n))

Lg-flatT : ∀ y → LgB (flatT y)
Lg-flatT hz = tt
Lg-flatT (hs y) = Lg-flatT y
Lg-flatT (hl f) = (λ n → ⊞-fst (cumT (λ k → flatT (f k)) n) (flatT (f (suc n)))) , Lg-cumT (λ k → flatT (f k)) (λ k → Lg-flatT (f k))
Lg-flatT (hΩ κ h) = Lg-flatT (h (bot T κ))

rdG  : ∀ {W} → LgW L₀ W → HB L₀ → D₂ W → HB L₀
rdpG : ∀ {W} → LgW L₀ W → HB L₀ → (ℕ → D₂ W) → ℕ → HB L₀
rdG lW b n0 = b
rdG lW b n1 = hs b
rdG lW b (x ⨾ y) = rdG lW (rdG lW b x) y
rdG lW b (nl d) = hl (rdpG lW b d)
rdG lW b (ni (ss hself) u) = hΩ (inj₂ tt) (nbᴮ b (λ y h → rdG lW h (u ≤rf lW (toDᵀ y))))
rdG lW b (ni (ss (hsuc hself)) u) = hΩ (inj₁ (aK G)) (λ e → nbA b (λ c h → rdG lW h (u ≤rf lW (toD₀ c))) (frE G e))
rdG lW b (nc (inj₁ κ) z u) = rdG lW b (u ≤rf lW)
rdG {W} lW b (nc (inj₂ tt) z u) =
  hΩ (inj₂ tt) (nbᴮ b (λ y h → rdG (lWy lW (flatT y) (Lg-flatT y)) h (u (qy {W} (flatT y)) (lWy lW (flatT y) (Lg-flatT y)))))
rdG lW b (nw p x) = rdG (lgW≤ p lW) b x
rdpG lW b d zero = b
rdpG lW b d (suc n) = rdG lW (rdpG lW b d n) (d n)
```

## §3 合法由形状给出

```agda
rdG-fst : ∀ {W} (lW : LgW L₀ W) b (x : D₂ W) {w} → b ⊲[ w ] rdG lW b x
rdG-fst lW b n0 = hself
rdG-fst lW b n1 = hsuc hself
rdG-fst lW b (x ⨾ y) = ⊲ᴮ-tr (rdG-fst lW b x) (rdG-fst lW (rdG lW b x) y)
rdG-fst lW b (nl d) = hlim 0 hself
rdG-fst lW b (ni (ss hself) u) {w} = hLim {L₀} {κ = inj₂ tt} {c = hz} (z⊲ᴮ (proj₂ w)) hself
rdG-fst lW b (ni (ss (hsuc hself)) u) {w} =
  hLim {L₀} {κ = inj₁ (aK G)} {c = bot T (aK G)} (botBd T (aK G) (proj₁ w))
    (nbA-fst (λ c h → rdG-fst lW h (u ≤rf lW (toD₀ c))) (frE G (bot T (aK G))))
rdG-fst lW b (nc (inj₁ κ) z u) = rdG-fst lW b (u ≤rf lW)
rdG-fst lW b (nc (inj₂ tt) z u) {w} = hLim {L₀} {κ = inj₂ tt} {c = hz} (z⊲ᴮ (proj₂ w)) hself
rdG-fst lW b (nw p x) = rdG-fst (lgW≤ p lW) b x

Lg-rdG  : ∀ {W} (lW : LgW L₀ W) b (x : D₂ W) → LgB b → LgB (rdG lW b x)
Lg-rdpG : ∀ {W} (lW : LgW L₀ W) b (d : ℕ → D₂ W) → LgB b → ∀ n → LgB (rdpG lW b d n)
Lg-rdG lW b n0 l = l
Lg-rdG lW b n1 l = l
Lg-rdG lW b (x ⨾ y) l = Lg-rdG lW (rdG lW b x) y (Lg-rdG lW b x l)
Lg-rdG lW b (nl d) l = (λ n → rdG-fst lW (rdpG lW b d n) (d n)) , Lg-rdpG lW b d l
Lg-rdG lW b (ni (ss hself) u) l =
  cont→Lg (nb-contB l (λ y h → rdG-fst lW h (u ≤rf lW (toDᵀ y))) (λ y h lh → Lg-rdG lW h (u ≤rf lW (toDᵀ y)) lh))
Lg-rdG lW b (ni (ss (hsuc hself)) u) l =
  (λ lw e e′ p → nbA-mono fs (frE-mono G (proj₁ lw) e e′ p)) ,
  (λ e le → Lg-nbA fs l (λ c h lh → Lg-rdG lW h (u ≤rf lW (toD₀ c)) lh) (frE G e) (frE-lg G le))
  where
  fs : ∀ c h {w} → h ⊲[ w ] rdG lW h (u ≤rf lW (toD₀ c))
  fs c h = rdG-fst lW h (u ≤rf lW (toD₀ c))
Lg-rdG lW b (nc (inj₁ κ) z u) l = Lg-rdG lW b (u ≤rf lW) l
Lg-rdG {W} lW b (nc (inj₂ tt) z u) l =
  cont→Lg (nb-contB l
    (λ y h → rdG-fst (lWy lW (flatT y) (Lg-flatT y)) h (u (qy {W} (flatT y)) (lWy lW (flatT y) (Lg-flatT y))))
    (λ y h lh → Lg-rdG (lWy lW (flatT y) (Lg-flatT y)) h (u (qy {W} (flatT y)) (lWy lW (flatT y) (Lg-flatT y))) lh))
Lg-rdG lW b (nw p x) l = Lg-rdG (lgW≤ p lW) b x l
Lg-rdpG lW b d l zero = l
Lg-rdpG lW b d l (suc n) = Lg-rdG lW (rdpG lW b d n) (d n) (Lg-rdpG lW b d l n)
```
