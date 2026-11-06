# 读回包 (二): 对坐标推广的读回包, 有限级, ω, ω+1

> 不含记号. 入口 [LvRd](LvRd.lagda.md), 接口 [LvRdIf](LvRdIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> [FamFoldRead](FamFoldRead.lagda.md) 的读回 `rdN` 只对 `HB (Sk (n+1))` 写. 这里把读回拆成两半:
>
> - **结点的解释** `NdI T L`: 层 $L$ 的树里过某层的结点 (`ni r u`) 读成 `HB T` 的什么结点 (`ndR r`), 外加两个嵌入 `eA`, `eM` 给闭包 `nκ`, `nμ` 的种类. 一步定理 `fsR` (底是第一位置), `lgR` (保合法) 是解释的字段.
> - **对一切 `NdI` 一条读回** `RG.rdG` (与 `rdN` 同形, 结点交给解释), `fstG`, `lgG`: 合法由形状给出.
>
> 解释由 [LvRdEmb](LvRdEmb.lagda.md) 的嵌入给出. 过第 $j$ 层的结点 (在第 $n+1$ 支之下) 读成第 $j$ 级种类经 `lePE` 再经外层嵌入 `o` 的结点 (`NF.ndF`), 坐标喂第 $j$ 层的树要第 $j-1$ 级的翻译 `tr`. 外层嵌入:
>
> | 级 (坐标 $c$) | 层 $L$ | `HB T` | 过 $\lhd$ 第 $n+1$ 支的结点 | 新种类 |
> |---|---|---|---|---|
> | 有限 $n+1$ | `ly (n+2)` | `Sk (n+1)` | `idE` | 由 `lePE ≤r` |
> | $\omega$ | `lyω` | `Gω` | `ιE (n+1)` (并的第 $n+1$ 个分量) | 无 |
> | $\omega+1$ | `lyω1` | `Gω1` | `ιE (n+1)` 再 `inj₁E` | 过第 $\omega$ 层: 坐标 `HB Gω`, 喂 `trω` |
>
> 翻译 (高度读成树) `trKg`: 第 $m$ 级种类在任意层 $L''$ 里, 只要给出过第 $m$ 层的结点证据 `R : StH W (ly m) L''` (`FamFoldRead.trK` 把它写死成 `ss Q`, 所以输出只能在后继层; 第 $\omega$ 层是极限, 要 `sl`). 包 `pkgF n` 对 $n$ 递归 (同 `FamFoldRead.pkg`); $\omega$ 的包是对角: 第 $n+1$ 支的结点用 `pkgF n`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvRdPkg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; Lg)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree
  using (Ht; Wd₂; LgW₂; D; StH; ss; sl; sL; Vs; n0; n1; _⨾_; nl; ni; nκ; nμ; nw; ≤rf; lgW≤; NZ₁; NZ-S; nz⊲; inC; outS; S→⊲)
  renaming (Sk to SkH)
open import OCF.Align.HtTowerFRead using (toD; rd; rd-fst; Lg-rd; lwκ; pwκ)
open import OCF.Align.HtTowerNRead using (toD₁; lxμ; ≤μ)
open import OCF.Align.FamFoldIf using (Sk)
open import OCF.Align.FamFoldLift using (Le; ≤r; ≤s; prL; pdL; le0; le1)
open import OCF.Align.FamFoldRead using (ly)
open import OCF.Align.LvRdIf using (Gω; Gω1; lyω; lyω1; RdC; PkgΩ)
open RdC public
open import OCF.Align.LvRdEmb
```

## §1 结点的解释与对一切解释的读回

```agda
record NdI (T : KS) (L : Ht) : Set where
  field
    ndR : ∀ {W k} (r : StH W k L) → HB T → (Vs L r W → HB T → HB T) → HB T
    fsR : ∀ {W k} (r : StH W k L) b s {w} → b ⊲[ w ] ndR r b s
    lgR : ∀ {W k} (r : StH W k L) {b s} → (∀ y h {w} → h ⊲[ w ] s y h) → LgB b →
          (∀ y h → LgB h → LgB (s y h)) → LgB (ndR r b s)
    eA  : Emb S₀ T
    eM  : Emb (step S₀) T

module RG {T L} (N : NdI T L) where
  open NdI N

  rdG  : ∀ {W} → LgW₂ W → HB T → D L W → HB T
  rdpG : ∀ {W} → LgW₂ W → HB T → (ℕ → D L W) → ℕ → HB T
  rdG lW b n0 = b
  rdG lW b n1 = hs b
  rdG lW b (x ⨾ y) = rdG lW (rdG lW b x) y
  rdG lW b (nl d) = hl (rdpG lW b d)
  rdG lW b (ni r u) = ndR r b (λ y h → rdG lW h (u ≤rf lW y))
  rdG {W} lW b (nκ _ u) =
    nodeA eA b (λ c h → rdG (lwκ c (proj₁ lW) , proj₂ lW) h (u (pwκ (proj₁ W) c) (lwκ c (proj₁ lW))))
  rdG lW b (nμ _ u) = nodeH eM b (λ x h → rdG (proj₁ lW , lxμ lW x) h (u (≤μ lW x) (proj₁ lW , lxμ lW x)))
  rdG lW b (nw p x) = rdG (lgW≤ p lW) b x
  rdpG lW b d zero = b
  rdpG lW b d (suc k) = rdG lW (rdpG lW b d k) (d k)

  fstG : ∀ {W} (lW : LgW₂ W) b (x : D L W) {w} → b ⊲[ w ] rdG lW b x
  fstG lW b n0 = hself
  fstG lW b n1 = hsuc hself
  fstG lW b (x ⨾ y) = ⊲ᴮ-tr (fstG lW b x) (fstG lW (rdG lW b x) y)
  fstG lW b (nl d) = hlim 0 hself
  fstG lW b (ni r u) = fsR r b _
  fstG lW b (nκ _ u) = fst-nodeA eA b _
  fstG lW b (nμ _ u) = fst-nodeH eM b _
  fstG lW b (nw p x) = fstG (lgW≤ p lW) b x

  lgG  : ∀ {W} (lW : LgW₂ W) b (x : D L W) → LgB b → LgB (rdG lW b x)
  lgpG : ∀ {W} (lW : LgW₂ W) b (d : ℕ → D L W) → LgB b → ∀ k → LgB (rdpG lW b d k)
  lgG lW b n0 l = l
  lgG lW b n1 l = l
  lgG lW b (x ⨾ y) l = lgG lW (rdG lW b x) y (lgG lW b x l)
  lgG lW b (nl d) l = (λ k → fstG lW (rdpG lW b d k) (d k)) , lgpG lW b d l
  lgG lW b (ni r u) l = lgR r (λ y h → fstG lW h (u ≤rf lW y)) l (λ y h lh → lgG lW h (u ≤rf lW y) lh)
  lgG {W} lW b (nκ _ u) l =
    Lg-nodeA eA (λ c h → fstG (lwκ c (proj₁ lW) , proj₂ lW) h (u (pwκ (proj₁ W) c) (lwκ c (proj₁ lW)))) l
      (λ c h lh → lgG (lwκ c (proj₁ lW) , proj₂ lW) h (u (pwκ (proj₁ W) c) (lwκ c (proj₁ lW))) lh)
  lgG lW b (nμ _ u) l =
    Lg-nodeH eM (λ x h → fstG (proj₁ lW , lxμ lW x) h (u (≤μ lW x) (proj₁ lW , lxμ lW x))) l
      (λ x h lh → lgG (proj₁ lW , lxμ lW x) h (u (≤μ lW x) (proj₁ lW , lxμ lW x)) lh)
  lgG lW b (nw p x) l = lgG (lgW≤ p lW) b x l
  lgpG lW b d l zero = l
  lgpG lW b d l (suc k) = lgG lW (rdpG lW b d k) (d k) (lgpG lW b d l k)

mkRd : ∀ {T L} → NdI T L → (∀ {W} → HB T → D L W) → RdC T L
mkRd N t = record { rdr = RG.rdG N ; fst = RG.fstG N ; lgr = RG.lgG N ; tr = t }
```

## §2 包与翻译

```agda
record PkgF (n : ℕ) : Set where
  field
    RR : ∀ {i} → Le i n → RdC (Sk i) (ly (suc i))
open PkgF public

nz₁S : ∀ {W L} → StH W (ly 1) L → NZ₁ L
nz₁S (ss P) = nz⊲ P tt
nz₁S (sl n P) = tt
nz₁S (sL e P) = tt

-- 第 m 级种类在任意层 L″ 里: 给出过第 m 层的结点证据
trKg : ∀ {n} → PkgF n → ∀ {m} → Le m (suc n) → (κ : K (Sk m)) → ∀ {L″} → (∀ {W} → StH W (ly m) L″) →
       (E (Sk m) κ → (W : Wd₂) → D L″ W) → (W : Wd₂) → D L″ W
trKg P {m = zero} le tt R g W = nκ (NZ-S (R {W})) (λ {c} _ _ → g c (c , proj₂ W))
trKg P {m = suc zero} le (inj₂ tt) R g W = nμ (nz₁S (R {W})) (λ {W′} _ _ → g (proj₂ W′) W′)
trKg P {m = suc (suc i)} le (inj₂ tt) R g W =
  ni (R {W}) (λ {W′} _ lW′ y → g (rdr (RR P (pdL le)) lW′ hz (outS (R {W}) y)) W′)
trKg P {m = suc m} le (inj₁ κ) R g W = trKg P (prL le) κ (λ {W′} → SkH (ss hself) (S→⊲ (R {W′}))) g W

module TF {n} (P : PkgF n) where
  trNF : HB (Sk (suc n)) → (W : Wd₂) → D (ly (suc (suc n))) W
  trNF hz W = n0
  trNF (hs x) W = trNF x W ⨾ n1
  trNF (hl f) W = nl (λ k → trNF (f k) W)
  trNF (hΩ κ h) W = trKg P ≤r κ (ss hself) (λ c W′ → trNF (h c) W′) W
```

## §3 过第 $j\le n+1$ 层的结点, 经外层嵌入

```agda
module NF {n} (P : PkgF n) {T : KS} (o : Emb (Sk (suc n)) T) where
  ndF : ∀ {W} {k′} → Le k′ (suc n) → ∀ {j} → j ⊲[ W ] ly k′ → HB T → (D j W → HB T → HB T) → HB T
  ndF {k′ = zero} le hself b s = nodeA (compE (lePE le) o) b (λ c h → s (toD c) h)
  ndF {k′ = suc i} le hself b s = nodeH (compE (lePE le) o) b (λ x h → s (tr (RR P (pdL le)) x) h)
  ndF {k′ = suc i} le (hsuc Q) b s = ndF (prL le) Q b s

  fsF : ∀ {W} {k′} (le : Le k′ (suc n)) {j} (Q : j ⊲[ W ] ly k′) b s {w} → b ⊲[ w ] ndF le Q b s
  fsF {k′ = zero} le hself b s = fst-nodeA (compE (lePE le) o) b _
  fsF {k′ = suc i} le hself b s = fst-nodeH (compE (lePE le) o) b _
  fsF {k′ = suc i} le (hsuc Q) b s = fsF (prL le) Q b s

  lgF : ∀ {W} {k′} (le : Le k′ (suc n)) {j} (Q : j ⊲[ W ] ly k′) {b s} →
        (∀ y h {w} → h ⊲[ w ] s y h) → LgB b → (∀ y h → LgB h → LgB (s y h)) → LgB (ndF le Q b s)
  lgF {k′ = zero} le hself fs lb ls = Lg-nodeA (compE (lePE le) o) (λ c h → fs _ h) lb (λ c h → ls _ h)
  lgF {k′ = suc i} le hself fs lb ls = Lg-nodeH (compE (lePE le) o) (λ x h → fs _ h) lb (λ x h → ls _ h)
  lgF {k′ = suc i} le (hsuc Q) fs lb ls = lgF (prL le) Q fs lb ls
```

## §4 有限级的包

```agda
module FinI (n : ℕ) (P : PkgF n) where
  L₂ : Ht
  L₂ = ly (suc (suc n))

  ndR : ∀ {W k} (r : StH W k L₂) → HB (Sk (suc n)) → (Vs L₂ r W → HB (Sk (suc n)) → HB (Sk (suc n))) → HB (Sk (suc n))
  ndR (ss Q) b s = NF.ndF P (idE _) ≤r Q b (λ y h → s (inC Q y) h)

  fsR : ∀ {W k} (r : StH W k L₂) b s {w} → b ⊲[ w ] ndR r b s
  fsR (ss Q) b s = NF.fsF P (idE _) ≤r Q b _

  lgR : ∀ {W k} (r : StH W k L₂) {b s} → (∀ y h {w} → h ⊲[ w ] s y h) → LgB b →
        (∀ y h → LgB h → LgB (s y h)) → LgB (ndR r b s)
  lgR (ss Q) fs lb ls = NF.lgF P (idE _) ≤r Q (λ y h → fs (inC Q y) h) lb (λ y h → ls (inC Q y) h)

  ndi : NdI (Sk (suc n)) L₂
  ndi = record { ndR = ndR ; fsR = fsR ; lgR = lgR ; eA = lePE (le0 (suc n)) ; eM = lePE (le1 n) }

R₀ : RdC S₀ (ly 1)
R₀ = record { rdr = rd ; fst = rd-fst ; lgr = Lg-rd ; tr = toD₁ }

pkgF : ∀ n → PkgF n
RnF  : ∀ n → RdC (Sk (suc n)) (ly (suc (suc n)))
pkgF zero = record { RR = λ { ≤r → R₀ } }
pkgF (suc n) = record { RR = λ { ≤r → RnF n ; (≤s p) → RR (pkgF n) p } }
RnF n = mkRd (FinI.ndi n (pkgF n)) (λ {W} x → TF.trNF (pkgF n) x W)

-- 第 n 级的读回包
RdF : ∀ n → RdC (Sk n) (ly (suc n))
RdF n = RR (pkgF n) ≤r
```

## §5 ω 的包 (对角)

第 $\omega$ 层 `lyω = hl (n ↦ ly (n+1))` 的结点都在某一支 $n$ 之下 (`sl n Q`), 读成并 `Gω` 的第 $n+1$ 个分量里的结点, 用第 $n$ 级的包 `pkgF n`. 闭包 `nκ`, `nμ` 读成第 0, 1 个分量的种类.

```agda
module OmI where
  ndR : ∀ {W k} (r : StH W k lyω) → HB Gω → (Vs lyω r W → HB Gω → HB Gω) → HB Gω
  ndR (sl n Q) b s = NF.ndF (pkgF n) (ιE {F = Sk} (suc n)) ≤r Q b (λ y h → s (inC Q y) h)

  fsR : ∀ {W k} (r : StH W k lyω) b s {w} → b ⊲[ w ] ndR r b s
  fsR (sl n Q) b s = NF.fsF (pkgF n) (ιE {F = Sk} (suc n)) ≤r Q b _

  lgR : ∀ {W k} (r : StH W k lyω) {b s} → (∀ y h {w} → h ⊲[ w ] s y h) → LgB b →
        (∀ y h → LgB h → LgB (s y h)) → LgB (ndR r b s)
  lgR (sl n Q) fs lb ls =
    NF.lgF (pkgF n) (ιE {F = Sk} (suc n)) ≤r Q (λ y h → fs (inC Q y) h) lb (λ y h → ls (inC Q y) h)

  ndi : NdI Gω lyω
  ndi = record { ndR = ndR ; fsR = fsR ; lgR = lgR ; eA = ιE {F = Sk} 0 ; eM = ιE {F = Sk} 1 }

-- 混合高度读成第 ω 层的树: 种类 (m, κ) 交给第 m 级的翻译, 结点过第 m 层.
-- m = m′+1 时在第 m′ 支 (ly m) 上字面地是该支 (hself), 读回落回同一个分量 m; m = 0 只用到层非零.
trOm : (κ : K Gω) → ∀ {L″} → (∀ {W} m → StH W (ly (suc m)) L″) →
       (E Gω κ → (W : Wd₂) → D L″ W) → (W : Wd₂) → D L″ W
trOm (zero , κ) R g W = trKg (pkgF 0) (≤s ≤r) κ (λ {W′} → SkH (ss hself) (S→⊲ (R {W′} 0))) g W
trOm (suc m , κ) R g W = trKg (pkgF m) ≤r κ (R m) g W

trω : HB Gω → (W : Wd₂) → D lyω W
trω hz W = n0
trω (hs x) W = trω x W ⨾ n1
trω (hl f) W = nl (λ k → trω (f k) W)
trω (hΩ κ h) W = trOm κ (λ m → sl m hself) (λ c W′ → trω (h c) W′) W

RdΩ : RdC Gω lyω
RdΩ = mkRd OmI.ndi (λ {W} x → trω x W)
```

## §6 ω+1 的包

第 $\omega+1$ 层 `lyω1 = hs lyω`: 过第 $\omega$ 层的结点 (`ss hself`) 是新种类, 坐标 `HB Gω` 喂 `trω`; 过第 $n+1$ 支之下的结点 (`ss (hlim n Q)`) 是旧种类, 嵌入多一步 `inj₁E`.

```agda
module Om1I where
  ndR : ∀ {W k} (r : StH W k lyω1) → HB Gω1 → (Vs lyω1 r W → HB Gω1 → HB Gω1) → HB Gω1
  ndR {W} (ss hself) b s = nodeH (idE Gω1) b (λ x h → s (trω x W) h)
  ndR (ss (hlim n Q)) b s = NF.ndF (pkgF n) (compE (ιE {F = Sk} (suc n)) (inj₁E Gω)) ≤r Q b (λ y h → s (inC Q y) h)

  fsR : ∀ {W k} (r : StH W k lyω1) b s {w} → b ⊲[ w ] ndR r b s
  fsR (ss hself) b s = fst-nodeH (idE Gω1) b _
  fsR (ss (hlim n Q)) b s = NF.fsF (pkgF n) (compE (ιE {F = Sk} (suc n)) (inj₁E Gω)) ≤r Q b _

  lgR : ∀ {W k} (r : StH W k lyω1) {b s} → (∀ y h {w} → h ⊲[ w ] s y h) → LgB b →
        (∀ y h → LgB h → LgB (s y h)) → LgB (ndR r b s)
  lgR {W} (ss hself) fs lb ls = Lg-nodeH (idE Gω1) (λ x h → fs (trω x W) h) lb (λ x h → ls (trω x W) h)
  lgR (ss (hlim n Q)) fs lb ls =
    NF.lgF (pkgF n) (compE (ιE {F = Sk} (suc n)) (inj₁E Gω)) ≤r Q (λ y h → fs (inC Q y) h) lb (λ y h → ls (inC Q y) h)

  ndi : NdI Gω1 lyω1
  ndi = record { ndR = ndR ; fsR = fsR ; lgR = lgR
               ; eA = compE (ιE {F = Sk} 0) (inj₁E Gω) ; eM = compE (ιE {F = Sk} 1) (inj₁E Gω) }

trΩ1 : HB Gω1 → (W : Wd₂) → D lyω1 W
trΩ1 hz W = n0
trΩ1 (hs x) W = trΩ1 x W ⨾ n1
trΩ1 (hl f) W = nl (λ k → trΩ1 (f k) W)
trΩ1 (hΩ (inj₂ tt) h) W = ni (ss hself) (λ {W′} _ lW′ y → trΩ1 (h (rdr RdΩ lW′ hz y)) W′)
trΩ1 (hΩ (inj₁ κ) h) W = trOm κ (λ m → ss (hlim m hself)) (λ c W′ → trΩ1 (h c) W′) W

RdΩ1 : RdC Gω1 lyω1
RdΩ1 = mkRd Om1I.ndi (λ {W} x → trΩ1 x W)

-- 接口 §2 的实例
pkgΩ : PkgΩ
pkgΩ = RdF , RdΩ , RdΩ1
```
