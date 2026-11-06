# 族增量世界上的真折叠 (四): 对一切级的读回

> 不含记号. 入口 [FamFold](FamFold.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> 两种种类的折叠在第 $n+1$ 层目标上的输出 `D (ly (suc n))` 读成 `HB (Sk n)` (`HtTowerFRead.rd` 是 $n=0$, `HtTowerNRead.rd₂` 是 $n=1$, `FamFoldTwo.rd₃` 是 $n=2$ 的手写版本). 对一切 $n$ 一条定义, 对 $n$ 结构递归: 记录 `Pkg n` 装着一切 $i\le n$ 级的读回 `R` 与高度到树的翻译 `tr`, `pkg (suc n)` 只用 `pkg n`.
>
> - **翻译** `trN P x`: `HB (Sk (suc n))` 的高度读成第 $n+2$ 层的树. 种类按级 (`trK`): 第 0 级 ↦ 闭包 `nκ`, 第 1 级 ↦ 闭包 `nμ`, 第 $j\ge2$ 级 ↦ 过第 $j$ 层的节点, 输入 (第 $j$ 层的树) 经第 $j-1$ 级的读回读成坐标.
> - **读回** `rdN P`: 过第 $m\le n+1$ 层的节点读成第 $m$ 级种类的连续分支 (`FamFoldLift.node`), 坐标 $x$ 喂第 $m$ 层的树 (`toDk`: $m=0$ 时 `toD`, 否则第 $m-1$ 级的翻译); 闭包 `nκ`, `nμ` 读成第 0, 1 级的分支. **合法由形状给出** (`lgN`, 只要底合法), 底是第一位置 (`fstN`), 证明对一切级一条 (`FamFoldLift.Lg-node`, `fst-node`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.FamFoldRead where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; Lg)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree
  using (H₀; Ht; Wd₂; LgW₂; D; StH; ss; n0; n1; _⨾_; nl; ni; nκ; nμ; nw; ≤rf; lgW≤; nz⊲; inC; outC)
open import OCF.Align.HtTowerFRead using (toD; rd; rd-fst; Lg-rd; lwκ; pwκ)
open import OCF.Align.HtTowerNRead using (toD₁; xμ; lxμ; ≤μ)
open import OCF.Align.FamFoldIf using (Sk)
open import OCF.Align.FamFoldLift
```

## §1 层与包

```agda
ly : ℕ → Ht
ly zero = hz
ly (suc k) = hs (ly k)

record Rdr (n : ℕ) : Set where
  field
    rdr : ∀ {W} → LgW₂ W → HB (Sk n) → D (ly (suc n)) W → HB (Sk n)
    fst : ∀ {W} (lW : LgW₂ W) b (x : D (ly (suc n)) W) {w} → b ⊲[ w ] rdr lW b x
    lgr : ∀ {W} (lW : LgW₂ W) b (x : D (ly (suc n)) W) → LgB b → LgB (rdr lW b x)
open Rdr public

record Pkg (n : ℕ) : Set where
  field
    R  : ∀ {i} → Le i n → Rdr i
    tr : ∀ {i} → Le i n → ∀ {W} → HB (Sk i) → D (ly (suc i)) W
open Pkg public

R₀ : Rdr 0
R₀ = record { rdr = rd ; fst = rd-fst ; lgr = Lg-rd }
```

## §2 翻译: 高度读成树

```agda
module _ {n} (P : Pkg n) where
  trK : ∀ {m} → Le m (suc n) → (κ : K (Sk m)) → ∀ {L′} → (∀ {W} → ly m ⊲[ W ] L′) →
        (E (Sk m) κ → (W : Wd₂) → D (hs L′) W) → (W : Wd₂) → D (hs L′) W
  trK {m = zero} le tt Q g W = nκ tt (λ {c} _ _ → g c (c , proj₂ W))
  trK {m = suc zero} le (inj₂ tt) Q g W = nμ (nz⊲ (Q {W}) tt) (λ {W′} _ _ → g (proj₂ W′) W′)
  trK {m = suc (suc i)} le (inj₂ tt) Q g W =
    ni (ss (Q {W})) (λ {W′} _ lW′ y → g (rdr (R P (pdL le)) lW′ hz (outC (Q {W}) y)) W′)
  trK {m = suc m} le (inj₁ κ) Q g W = trK (prL le) κ (λ {W′} → ⊲ᴮ-tr (hsuc hself) (Q {W′})) g W

  trN : HB (Sk (suc n)) → (W : Wd₂) → D (ly (suc (suc n))) W
  trN hz W = n0
  trN (hs x) W = trN x W ⨾ n1
  trN (hl f) W = nl (λ k → trN (f k) W)
  trN (hΩ κ h) W = trK ≤r κ hself (λ c W′ → trN (h c) W′) W
```

## §3 读回

```agda
  toDk : ∀ {k′} → Le k′ (suc n) → Co k′ → ∀ {W} → D (ly k′) W
  toDk {k′ = zero} le c = toD c
  toDk {k′ = suc j} le x = tr P (pdL le) x

  rdNode : ∀ {W} {k′} → Le k′ (suc n) → ∀ {j} → j ⊲[ W ] ly k′ → HB (Sk (suc n)) →
           (D j W → HB (Sk (suc n)) → HB (Sk (suc n))) → HB (Sk (suc n))
  rdNode {k′ = zero} le hself b s = node le b (λ x h → s (toDk le x) h)
  rdNode {k′ = suc j} le hself b s = node le b (λ x h → s (toDk le x) h)
  rdNode {k′ = suc j} le (hsuc Q) b s = rdNode (prL le) Q b s

  fstNode : ∀ {W} {k′} (le : Le k′ (suc n)) {j} (Q : j ⊲[ W ] ly k′) b s {w} → b ⊲[ w ] rdNode le Q b s
  fstNode {k′ = zero} le hself b s = fst-node le b _
  fstNode {k′ = suc j} le hself b s = fst-node le b _
  fstNode {k′ = suc j} le (hsuc Q) b s = fstNode (prL le) Q b s

  lgNode : ∀ {W} {k′} (le : Le k′ (suc n)) {j} (Q : j ⊲[ W ] ly k′) {b s} →
           (∀ y h {w} → h ⊲[ w ] s y h) → LgB b → (∀ y h → LgB h → LgB (s y h)) → LgB (rdNode le Q b s)
  lgNode {k′ = zero} le hself fs lb ls = Lg-node le (λ x h → fs _ h) lb (λ x h → ls _ h)
  lgNode {k′ = suc j} le hself fs lb ls = Lg-node le (λ x h → fs _ h) lb (λ x h → ls _ h)
  lgNode {k′ = suc j} le (hsuc Q) fs lb ls = lgNode (prL le) Q fs lb ls

  rdN  : ∀ {W} → LgW₂ W → HB (Sk (suc n)) → D (ly (suc (suc n))) W → HB (Sk (suc n))
  rdpN : ∀ {W} → LgW₂ W → HB (Sk (suc n)) → (ℕ → D (ly (suc (suc n))) W) → ℕ → HB (Sk (suc n))
  rdN lW b n0 = b
  rdN lW b n1 = hs b
  rdN lW b (x ⨾ y) = rdN lW (rdN lW b x) y
  rdN lW b (nl d) = hl (rdpN lW b d)
  rdN lW b (ni (ss Q) u) = rdNode ≤r Q b (λ y h → rdN lW h (u ≤rf lW (inC Q y)))
  rdN {W} lW b (nκ _ u) =
    node (le0 (suc n)) b (λ c h → rdN (lwκ c (proj₁ lW) , proj₂ lW) h (u (pwκ (proj₁ W) c) (lwκ c (proj₁ lW))))
  rdN lW b (nμ _ u) =
    node (le1 n) b (λ x h → rdN (proj₁ lW , lxμ lW x) h (u (≤μ lW x) (proj₁ lW , lxμ lW x)))
  rdN lW b (nw p x) = rdN (lgW≤ p lW) b x
  rdpN lW b d zero = b
  rdpN lW b d (suc k) = rdN lW (rdpN lW b d k) (d k)

  fstN : ∀ {W} (lW : LgW₂ W) b (x : D (ly (suc (suc n))) W) {w} → b ⊲[ w ] rdN lW b x
  fstN lW b n0 = hself
  fstN lW b n1 = hsuc hself
  fstN lW b (x ⨾ y) = ⊲ᴮ-tr (fstN lW b x) (fstN lW (rdN lW b x) y)
  fstN lW b (nl d) = hlim 0 hself
  fstN lW b (ni (ss Q) u) = fstNode ≤r Q b _
  fstN lW b (nκ _ u) = fst-node (le0 (suc n)) b _
  fstN lW b (nμ _ u) = fst-node (le1 n) b _
  fstN lW b (nw p x) = fstN (lgW≤ p lW) b x

  lgN  : ∀ {W} (lW : LgW₂ W) b (x : D (ly (suc (suc n))) W) → LgB b → LgB (rdN lW b x)
  lgpN : ∀ {W} (lW : LgW₂ W) b (d : ℕ → D (ly (suc (suc n))) W) → LgB b → ∀ k → LgB (rdpN lW b d k)
  lgN lW b n0 l = l
  lgN lW b n1 l = l
  lgN lW b (x ⨾ y) l = lgN lW (rdN lW b x) y (lgN lW b x l)
  lgN lW b (nl d) l = (λ k → fstN lW (rdpN lW b d k) (d k)) , lgpN lW b d l
  lgN lW b (ni (ss Q) u) l =
    lgNode ≤r Q (λ y h → fstN lW h (u ≤rf lW (inC Q y))) l (λ y h lh → lgN lW h (u ≤rf lW (inC Q y)) lh)
  lgN {W} lW b (nκ _ u) l =
    Lg-node (le0 (suc n)) (λ c h → fstN (lwκ c (proj₁ lW) , proj₂ lW) h (u (pwκ (proj₁ W) c) (lwκ c (proj₁ lW)))) l
            (λ c h lh → lgN (lwκ c (proj₁ lW) , proj₂ lW) h (u (pwκ (proj₁ W) c) (lwκ c (proj₁ lW))) lh)
  lgN lW b (nμ _ u) l =
    Lg-node (le1 n) (λ x h → fstN (proj₁ lW , lxμ lW x) h (u (≤μ lW x) (proj₁ lW , lxμ lW x))) l
            (λ x h lh → lgN (proj₁ lW , lxμ lW x) h (u (≤μ lW x) (proj₁ lW , lxμ lW x)) lh)
  lgN lW b (nw p x) l = lgN (lgW≤ p lW) b x l
  lgpN lW b d l zero = l
  lgpN lW b d l (suc k) = lgN lW (rdpN lW b d k) (d k) (lgpN lW b d l k)

  Rnew : Rdr (suc n)
  Rnew = record { rdr = rdN ; fst = fstN ; lgr = lgN }
```

## §4 对一切级

```agda
pkg : ∀ n → Pkg n
pkg zero = record { R = λ { ≤r → R₀ } ; tr = λ { ≤r → λ x → toD₁ x } }
pkg (suc n) = record
  { R  = λ { ≤r → Rnew (pkg n) ; (≤s p) → R (pkg n) p }
  ; tr = λ { ≤r {W} x → trN (pkg n) x W ; (≤s p) → tr (pkg n) p } }

-- 第 n 级的读回: 第 n+1 层的树读成 HB (Sk n), 合法由形状给出
Rd : ∀ n → Rdr n
Rd n = R (pkg n) ≤r
```
