# 对一般种类结构的折叠 (二): 读回, 丢掉新种类的分量

> 不含记号. 入口 [GenFold](GenFold.lagda.md), 接口 [GenFoldIf](GenFoldIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> 三个读回, 合法都由形状给出 (对一切数据):
>
> - **`rd₁`: 第 1 层的数据读成 `HB T`** (新种类的坐标), 新种类回灌时用. 由 [HtTowerFRead](HtTowerFRead.lagda.md) 的 `rd` 改写: 过第 0 层的结点读成**底种类** `aK` 的 $\Omega$-结点 (坐标经 `frE` 读成 `A`, 对 `A` 递归, `nbA`); 闭包结点 `nc` (第 1 层只有旧种类) **有损地读**: 只读当前世界的分支. `rd` 的 `nκ` 行把世界的 `A` 分量升到坐标, 要对旧种类升界; 一般的旧种类的界在并的分量里, 升不了 (接口头, 第一个障碍), 所以只读当前世界.
> - **`drp₁`: 第 1 层的数据不看新种类的分量**, 换成任意别的 (同 `HtTowerFRead.drp₁`).
> - **`rd₂`: 第 2 层的数据读成 `Ht`**, 求值的最后一步 (接口 `EvSys.evH` 要 `Ht`). 过第 1 层的结点读成 `Ht` 的新种类 κH 的 $\Omega$-结点 (坐标 `H₀`, 对坐标递归 `HtTowerCont.nbᴮ`, 坐标经 `toD₁` 写成第 1 层的数据作输入); 过第 0 层的结点读成 κA 的 $\Omega$-结点; 旧种类的闭包结点有损地读 (当前世界的分支); **新种类的闭包结点读成 κH 的 $\Omega$-结点** (坐标 $y$ 处的分支取在新种类的界升到 界 $\boxplus$ `encH y` 的世界里, 升新种类的界是对 `step` 的第二分量, 不碰并的分量). 与 `LvRdPkg.RdF 1` 同一个位置 (第 2 层到 `Ht`), 但不经世界的翻译: `Ht` 的两个种类只由**结点** (过哪一层) 给出, 不由闭包的种类给出, 所以不要种类结构之间的映射.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.HtTowerTy using (KS)
open import OCF.Align.GenFoldIf using (GenK; LgDn)
module OCF.Align.GenFoldRd (T : KS) (G : GenK T) (Ld : LgDn T) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (nbᴮ; nb-contB; cont→Lg)
open import OCF.Align.HtTowerFTree using (Ht; H₀; S₁)
open import OCF.Align.GenFoldIf
open import OCF.Align.GenFoldTree
open Tree T
```

## §1 对 `A` 坐标递归的分支 (对一切种类结构)

```agda
module NbA {S : KS} where
  nbA : HB S → (A → HB S → HB S) → A → HB S
  nbA b s azero = b
  nbA b s (asuc c) = s c (nbA b s c)
  nbA b s (alim f) = hl (λ n → nbA b s (f n))

  module _ {b : HB S} {s : A → HB S → HB S} (fs : ∀ c h {w} → h ⊲[ w ] s c h) where
    nbA-mono : ∀ {c c′} → c ⊲ c′ → ∀ {w} → nbA b s c ⊲[ w ] nbA b s c′
    nbA-mono C.self = hself
    nbA-mono (C.suc p) = ⊲ᴮ-tr (nbA-mono p) (fs _ _)
    nbA-mono (C.lim n p) = hlim n (nbA-mono p)

    nbA-fst : ∀ c {w} → b ⊲[ w ] nbA b s c
    nbA-fst azero = hself
    nbA-fst (asuc c) = ⊲ᴮ-tr (nbA-fst c) (fs _ _)
    nbA-fst (alim f) = hlim 0 (nbA-fst (f 0))

    Lg-nbA : LgB b → (∀ c h → LgB h → LgB (s c h)) → ∀ c → Lg c → LgB (nbA b s c)
    Lg-nbA lb ls azero _ = lb
    Lg-nbA lb ls (asuc c) l = ls c _ (Lg-nbA lb ls c l)
    Lg-nbA lb ls (alim f) (st , l) = (λ n → nbA-mono (st n)) , (λ n → Lg-nbA lb ls (f n) (l n))
open NbA
```

## §2 合法向下封闭 (层的世界)

```agda
lgW≤ : ∀ {U V} → U ≤ V → LgW L₀ V → LgW L₀ U
lgW≤ p l = lgDn Ld (proj₁ p) (proj₁ l) , lgB⊲ (proj₂ p) (proj₁ l) (proj₂ l)
```

## §3 第 1 层读成 `HB T`

```agda
rd₁  : ∀ {W} → LgW L₀ W → HB T → D (hs hz) W → HB T
rdp₁ : ∀ {W} → LgW L₀ W → HB T → (ℕ → D (hs hz) W) → ℕ → HB T
rd₁ lW b n0 = b
rd₁ lW b n1 = hs b
rd₁ lW b (x ⨾ y) = rd₁ lW (rd₁ lW b x) y
rd₁ lW b (nl d) = hl (rdp₁ lW b d)
rd₁ lW b (ni (ss hself) u) = hΩ (aK G) (λ e → nbA b (λ c h → rd₁ lW h (u ≤rf lW (toD₀ c))) (frE G e))
rd₁ lW b (nc (inj₁ κ) z u) = rd₁ lW b (u ≤rf lW)
rd₁ lW b (nc (inj₂ _) () u)
rd₁ lW b (nw p x) = rd₁ (lgW≤ p lW) b x
rdp₁ lW b d zero = b
rdp₁ lW b d (suc n) = rd₁ lW (rdp₁ lW b d n) (d n)

rd₁-fst : ∀ {W} (lW : LgW L₀ W) b (x : D (hs hz) W) {w} → b ⊲[ w ] rd₁ lW b x
rd₁-fst lW b n0 = hself
rd₁-fst lW b n1 = hsuc hself
rd₁-fst lW b (x ⨾ y) = ⊲ᴮ-tr (rd₁-fst lW b x) (rd₁-fst lW (rd₁ lW b x) y)
rd₁-fst lW b (nl d) = hlim 0 hself
rd₁-fst lW b (ni (ss hself) u) {w} =
  hLim {T} {κ = aK G} {c = bot T (aK G)} (botBd T (aK G) w)
    (nbA-fst (λ c h → rd₁-fst lW h (u ≤rf lW (toD₀ c))) (frE G (bot T (aK G))))
rd₁-fst lW b (nc (inj₁ κ) z u) = rd₁-fst lW b (u ≤rf lW)
rd₁-fst lW b (nc (inj₂ _) () u)
rd₁-fst lW b (nw p x) = rd₁-fst (lgW≤ p lW) b x

Lg-rd₁  : ∀ {W} (lW : LgW L₀ W) b (x : D (hs hz) W) → LgB b → LgB (rd₁ lW b x)
Lg-rdp₁ : ∀ {W} (lW : LgW L₀ W) b (d : ℕ → D (hs hz) W) → LgB b → ∀ n → LgB (rdp₁ lW b d n)
Lg-rd₁ lW b n0 l = l
Lg-rd₁ lW b n1 l = l
Lg-rd₁ lW b (x ⨾ y) l = Lg-rd₁ lW (rd₁ lW b x) y (Lg-rd₁ lW b x l)
Lg-rd₁ lW b (nl d) l = (λ n → rd₁-fst lW (rdp₁ lW b d n) (d n)) , Lg-rdp₁ lW b d l
Lg-rd₁ lW b (ni (ss hself) u) l =
  (λ lw e e′ p → nbA-mono fs (frE-mono G lw e e′ p)) ,
  (λ e le → Lg-nbA fs l (λ c h lh → Lg-rd₁ lW h (u ≤rf lW (toD₀ c)) lh) (frE G e) (frE-lg G le))
  where
  fs : ∀ c h {w} → h ⊲[ w ] rd₁ lW h (u ≤rf lW (toD₀ c))
  fs c h = rd₁-fst lW h (u ≤rf lW (toD₀ c))
Lg-rd₁ lW b (nc (inj₁ κ) z u) l = Lg-rd₁ lW b (u ≤rf lW) l
Lg-rd₁ lW b (nc (inj₂ _) () u) l
Lg-rd₁ lW b (nw p x) l = Lg-rd₁ (lgW≤ p lW) b x l
Lg-rdp₁ lW b d l zero = l
Lg-rdp₁ lW b d l (suc n) = Lg-rd₁ lW (rdp₁ lW b d n) (d n) (Lg-rdp₁ lW b d l n)
```

## §4 第 1 层不看新种类的分量

```agda
drp₁ : ∀ {w₀ x y} → LgW L₀ (w₀ , x) → D (hs hz) (w₀ , x) → D (hs hz) (w₀ , y)
drp₁ l n0 = n0
drp₁ l n1 = n1
drp₁ l (a ⨾ b) = drp₁ l a ⨾ drp₁ l b
drp₁ l (nl d) = nl (λ n → drp₁ l (d n))
drp₁ {x = x} l (ni (ss hself) u) =
  ni (ss hself) (λ {W″} q lW″ z → drp₁ (proj₁ lW″ , proj₂ l) (u {proj₁ W″ , x} (proj₁ q , hself) (proj₁ lW″ , proj₂ l) (drp z)))
drp₁ {x = x} l (nc (inj₁ κ) z u) =
  nc (inj₁ κ) z (λ {W″} q lW″ → drp₁ (proj₁ lW″ , proj₂ l) (u {proj₁ W″ , x} (proj₁ q , hself) (proj₁ lW″ , proj₂ l)))
drp₁ l (nc (inj₂ _) () u)
drp₁ l (nw p t) = nw (proj₁ p , hself) (drp₁ (lgW≤ p l) t)
```

## §5 第 2 层读成 `Ht`

```agda
toD₁ : ∀ {W} → H₀ → D (hs hz) W
toD₁ hz = n0
toD₁ (hs y) = toD₁ y ⨾ n1
toD₁ (hl f) = nl (λ n → toD₁ (f n))
toD₁ (hΩ tt h) = ni (ss hself) (λ _ _ z → toD₁ (h (sum azero z)))

-- 新种类的闭包在第 2 层读成 κH 的 Ω-结点: 坐标 y : H₀ 处的分支取在新种类的界升到 (界 ⊞ encH y) 的世界里.
-- encH 对一切 y (不论合法) 给出合法的高度 (Ω-结点取底坐标的分支, ℕ-极限取部分和).
cumT : (ℕ → HB T) → ℕ → HB T
cumT g zero = g 0
cumT g (suc n) = cumT g n ⊞ g (suc n)

encH : H₀ → HB T
encH hz = hz
encH (hs y) = hs (encH y)
encH (hl f) = hl (cumT (λ n → encH (f n)))
encH (hΩ tt h) = encH (h azero)

Lg-cumT : ∀ g → (∀ n → LgB (g n)) → ∀ n → LgB (cumT g n)
Lg-cumT g l zero = l 0
Lg-cumT g l (suc n) = Lg-⊞ (cumT g n) (g (suc n)) (Lg-cumT g l n) (l (suc n))

Lg-encH : ∀ y → LgB (encH y)
Lg-encH hz = tt
Lg-encH (hs y) = Lg-encH y
Lg-encH (hl f) = (λ n → ⊞-fst (cumT (λ k → encH (f k)) n) (encH (f (suc n)))) , Lg-cumT (λ k → encH (f k)) (λ k → Lg-encH (f k))
Lg-encH (hΩ tt h) = Lg-encH (h azero)

qy : ∀ {W} (y : H₀) → W ≤ (proj₁ W , proj₂ W ⊞ encH y)
qy {W} y = ≤w-rf T , ⊞-fst (proj₂ W) (encH y)

lWy : ∀ {W} → LgW L₀ W → (y : H₀) → LgW L₀ (proj₁ W , proj₂ W ⊞ encH y)
lWy lW y = proj₁ lW , Lg-⊞ _ (encH y) (proj₂ lW) (Lg-encH y)

D₂ : Wd L₀ → Set
D₂ = D (hs (hs hz))

rd₂  : ∀ {W} → LgW L₀ W → Ht → D₂ W → Ht
rdp₂ : ∀ {W} → LgW L₀ W → Ht → (ℕ → D₂ W) → ℕ → Ht
rd₂ lW b n0 = b
rd₂ lW b n1 = hs b
rd₂ lW b (x ⨾ y) = rd₂ lW (rd₂ lW b x) y
rd₂ lW b (nl d) = hl (rdp₂ lW b d)
rd₂ lW b (ni (ss hself) u) = hΩ (inj₂ tt) (nbᴮ b (λ y h → rd₂ lW h (u ≤rf lW (toD₁ y))))
rd₂ lW b (ni (ss (hsuc hself)) u) = hΩ (inj₁ tt) (nbA b (λ c h → rd₂ lW h (u ≤rf lW (toD₀ c))))
rd₂ lW b (nc (inj₁ κ) z u) = rd₂ lW b (u ≤rf lW)
rd₂ {W} lW b (nc (inj₂ tt) z u) = hΩ (inj₂ tt) (nbᴮ b (λ y h → rd₂ (lWy lW y) h (u (qy {W} y) (lWy lW y))))
rd₂ lW b (nw p x) = rd₂ (lgW≤ p lW) b x
rdp₂ lW b d zero = b
rdp₂ lW b d (suc n) = rd₂ lW (rdp₂ lW b d n) (d n)

rd₂-fst : ∀ {W} (lW : LgW L₀ W) b (x : D₂ W) {w} → b ⊲[ w ] rd₂ lW b x
rd₂-fst lW b n0 = hself
rd₂-fst lW b n1 = hsuc hself
rd₂-fst lW b (x ⨾ y) = ⊲ᴮ-tr (rd₂-fst lW b x) (rd₂-fst lW (rd₂ lW b x) y)
rd₂-fst lW b (nl d) = hlim 0 hself
rd₂-fst lW b (ni (ss hself) u) {w} = hLim {S₁} {κ = inj₂ tt} {c = hz} (z⊲ᴮ (proj₂ w)) hself
rd₂-fst lW b (ni (ss (hsuc hself)) u) {w} = hLim {S₁} {κ = inj₁ tt} {c = azero} (z⊲ (proj₁ w)) hself
rd₂-fst lW b (nc (inj₁ κ) z u) = rd₂-fst lW b (u ≤rf lW)
rd₂-fst lW b (nc (inj₂ tt) z u) {w} = hLim {S₁} {κ = inj₂ tt} {c = hz} (z⊲ᴮ (proj₂ w)) hself
rd₂-fst lW b (nw p x) = rd₂-fst (lgW≤ p lW) b x

Lg-rd₂  : ∀ {W} (lW : LgW L₀ W) b (x : D₂ W) → LgB b → LgB (rd₂ lW b x)
Lg-rdp₂ : ∀ {W} (lW : LgW L₀ W) b (d : ℕ → D₂ W) → LgB b → ∀ n → LgB (rdp₂ lW b d n)
Lg-rd₂ lW b n0 l = l
Lg-rd₂ lW b n1 l = l
Lg-rd₂ lW b (x ⨾ y) l = Lg-rd₂ lW (rd₂ lW b x) y (Lg-rd₂ lW b x l)
Lg-rd₂ lW b (nl d) l = (λ n → rd₂-fst lW (rdp₂ lW b d n) (d n)) , Lg-rdp₂ lW b d l
Lg-rd₂ lW b (ni (ss hself) u) l =
  cont→Lg (nb-contB l (λ y h → rd₂-fst lW h (u ≤rf lW (toD₁ y))) (λ y h lh → Lg-rd₂ lW h (u ≤rf lW (toD₁ y)) lh))
Lg-rd₂ lW b (ni (ss (hsuc hself)) u) l =
  (λ lw e e′ p → nbA-mono fs p) , (λ c lc → Lg-nbA fs l (λ c h lh → Lg-rd₂ lW h (u ≤rf lW (toD₀ c)) lh) c lc)
  where
  fs : ∀ c h {w} → h ⊲[ w ] rd₂ lW h (u ≤rf lW (toD₀ c))
  fs c h = rd₂-fst lW h (u ≤rf lW (toD₀ c))
Lg-rd₂ lW b (nc (inj₁ κ) z u) l = Lg-rd₂ lW b (u ≤rf lW) l
Lg-rd₂ {W} lW b (nc (inj₂ tt) z u) l =
  cont→Lg (nb-contB l (λ y h → rd₂-fst (lWy lW y) h (u (qy {W} y) (lWy lW y))) (λ y h lh → Lg-rd₂ (lWy lW y) h (u (qy {W} y) (lWy lW y)) lh))
Lg-rd₂ lW b (nw p x) l = Lg-rd₂ (lgW≤ p lW) b x l
Lg-rdp₂ lW b d l zero = l
Lg-rdp₂ lW b d l (suc n) = Lg-rd₂ lW (rdp₂ lW b d n) (d n) (Lg-rdp₂ lW b d l n)
```
