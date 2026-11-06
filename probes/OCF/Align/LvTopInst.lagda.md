# 整座塔加对角 (二): 用现有构造实例化 `FoldAt`, 截断版闭项, 全塔版闭项

> 不含记号. 入口 [LvTop](LvTop.lagda.md), 接口 [LvTopIf](LvTopIf.lagda.md), 塔 [LvTopTower](LvTopTower.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> - **§1 槽的搬运.** 第 $n$ 级在两处有两种写法: 坐标 `fin n` 处的 `Lev (fin n)` (塔用它) 与 `Sk n` (`LvRd` 的折叠用它); 二者命题相等 (`levFin`), 对变量 $n$ 不定义相等. 第 $\omega$ 级是 `sup ℕ (Lev ∘ f)` 对 `Gω = sup ℕ Sk`; 族之间只有逐点相等, 搬运整个族要函数外延. 所以这里写一个对树的结构映射 `Cvt.cvt` (逐结点搬种类与坐标, 不搬族) 与它保合法 (`Lg-cvt`, 世界反向逐分量搬). 这是脚手架: 序数值不需要, 是两种写法不一致带来的 (翻译账).
> - **§2 有限码与 ω 码上的 `FoldAt`.** `foldFin : FoldAt CovF` (码目标字面地等于某个 `fin n`): 目标 $0$ 时级顶就是 `Ωtop S₀` (`LvRdFold.Hn 0`, 不折叠); 目标 $m+1$ 时用 `LvRdFold.FF m` 在码 `kfin (m+1)` 上折叠, 世界是 `v₀` 在这个码上升高输入的槽, 再用 `dnF m` 降到 `Ht`. `foldω : FoldAt CovΩ` (目标字面地是 `hl f` 且逐项 `f n ≡ fin n`): 用 `LvRdFold.FΩ` (第 $\omega+1$ 级折叠) 在码 `kω` 上, 世界是 `v₀` 在 `kω` 上升高输入的槽, 用 `dω` 降. 合并 `foldTr : FoldAt (CovF ⊎ CovΩ)`.
>   **覆盖到哪里.** 码目标 $n$ (每个有限 $n$) 与 $\omega$, 即第 $1,2,\dots$ 级与第 $\omega+1$ 级的级顶. 码目标 $\omega+1$ (第 $\omega+2$ 级) 没有: `LvRd` 写了第 $\omega+1$ 层的读回 `RdΩ1`, 没有写第 $\omega+2$ 级的折叠 (`LvRd` 接手清单第 2 条).
> - **§3 截断版 (无条件).** 读法取常数 $1$ (`one₀`, 即 `LvRdWk.lvShape₁` 的读法): 各站的界 $B_s$ 就是 `fin s` (`B-fin`), 都在 `foldFin` 的覆盖之内; 极限界 `Bω = hl psum` 逐项等于 `fin n` (`covL`), 在 `foldω` 的覆盖之内. 塔走到: 第 $1,2,3,\dots$ 级 (一切有限站), 对角, 再加极限站 (第 $\omega+1$ 级). 闭项 `Ttr∞ = T⁺ Λ∞` (只有有限站的对角, 对照 `LvRdFold.T∞F`) 与 `Ttr = T⁺ (Λ∞ ⊞ Hω)` (对照 `LvRdFold.T∞ω1`). **这一版的 "层号由回灌给出" 是空的**: 读法是常数, 层号不读输出.
> - **§4 全塔版 (条件).** 以 `F : FoldAll` (一切码上的 `FoldAt`) 为模块参数, 读法取 `LvRdWk.σ₀` (`lvShapeδ` 的读法): `FullΛ F`. 闭项 `FullΛ.TΛ∞` (本接口下的候选: 部分和塔加对角) 与 `FullΛ.TΛ∞ω`. 读法是判断, 见入口: 层号是 `HB S₀` 的树, 判断读法低于 ψ₀Λ (上界约 $\psi_0(\Omega_{\Omega_2})$); **不是 ψ₀Λ 已写出**. 缺的那一条就是 `F`: 在码目标含 $\Omega$-结点的坐标上的折叠 (`LvOm` 一路在做的 "带世界的层证据与可能含 Ω-结点的坐标上的折叠"); 在只有后继与 ℕ-极限的一般坐标上的折叠本路也没有 (`LvRd` 只写了有限与 $\omega$).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvTopInst where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.CumReadCF using (A; azero; Lg)
import OCF.Free.Level as FLv
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop; Lg-Ωtop)
open import OCF.Align.HtTowerFTree using (Ht)
open import OCF.Align.HtTowerFClosed using (ord)
open import OCF.Align.FamFoldIf using (Sk)
open import OCF.Align.AdmWCoh using (fin)
open import OCF.Align.LvFbCode using (tgt)
open import OCF.Align.LvRdIf using (Gω; kω; kfin)
open import OCF.Align.LvRdWorld using (raise; v₀)
open import OCF.Align.LvRdFold using (module FF; module FΩ; dnF; dω; layΩ; Lg-layΩ)
open import OCF.Align.LvRdWk using (σ₀; lσ₀)
open import OCF.Align.LvTopIf
open import OCF.Align.LvTopTower
```

## §1 槽的搬运

```agda
levFin : ∀ n → Lev {S₀} (fin n) ≡ Sk n
levFin zero = refl
levFin (suc n) = cong step (levFin n)

toS : ∀ {S T : KS} → S ≡ T → HB S → HB T
toS e x = subst HB e x

lg-toS : ∀ {S T : KS} (e : S ≡ T) x → LgB x → LgB (toS e x)
lg-toS refl x l = l

-- 一个种类结构相等时, 种类, 坐标, 世界, 界, 第一位置, 合法的逐项搬运 (对 e 用 J)
tK : ∀ {S T : KS} → S ≡ T → K S → K T
tK refl κ = κ

bE : ∀ {S T : KS} (e : S ≡ T) κ → E T (tK e κ) → E S κ
bE refl κ c = c

fE : ∀ {S T : KS} (e : S ≡ T) κ → E S κ → E T (tK e κ)
fE refl κ c = c

bfE : ∀ {S T : KS} (e : S ≡ T) κ c → bE e κ (fE e κ c) ≡ c
bfE refl κ c = refl

bW : ∀ {S T : KS} → S ≡ T → Wd T → Wd S
bW refl w = w

bLgW : ∀ {S T : KS} (e : S ≡ T) w → LgW T w → LgW S (bW e w)
bLgW refl w l = l

bBd : ∀ {S T : KS} (e : S ≡ T) κ c w → Bd T (tK e κ) c w → Bd S κ (bE e κ c) (bW e w)
bBd refl κ c w b = b

fBd : ∀ {S T : KS} (e : S ≡ T) κ c w → Bd S κ c (bW e w) → Bd T (tK e κ) (fE e κ c) w
fBd refl κ c w b = b

bPr : ∀ {S T : KS} (e : S ≡ T) κ w c c′ → Pr T (tK e κ) w c c′ → Pr S κ (bW e w) (bE e κ c) (bE e κ c′)
bPr refl κ w c c′ p = p

bLgE : ∀ {S T : KS} (e : S ≡ T) κ c → LgE T (tK e κ) c → LgE S κ (bE e κ c)
bLgE refl κ c l = l

-- 两个族逐点相等时, 并上的树的结构映射 (不搬族本身, 不要外延)
module Cvt (F G : ℕ → KS) (e : ∀ n → F n ≡ G n) where
  cvt : HB (sup ℕ F) → HB (sup ℕ G)
  cvt hz = hz
  cvt (hs x) = hs (cvt x)
  cvt (hl f) = hl (λ n → cvt (f n))
  cvt (hΩ (n , κ) g) = hΩ (n , tK (e n) κ) (λ c → cvt (g (bE (e n) κ c)))

  bWs : Wd (sup ℕ G) → Wd (sup ℕ F)
  bWs w i = bW (e i) (w i)

  cvt-⊲ : ∀ {a b} {w : Wd (sup ℕ G)} → a ⊲[ bWs w ] b → cvt a ⊲[ w ] cvt b
  cvt-⊲ hself = hself
  cvt-⊲ (hsuc p) = hsuc (cvt-⊲ p)
  cvt-⊲ (hlim n p) = hlim n (cvt-⊲ p)
  cvt-⊲ {a = a} {w = w} (hLim {κ = (n , κ)} {g = g} {c = c} bd p) =
    hLim (fBd (e n) κ c (w n) bd) (subst (λ z → cvt a ⊲[ w ] cvt (g z)) (sym (bfE (e n) κ c)) (cvt-⊲ p))

  Lg-cvt : ∀ x → LgB x → LgB (cvt x)
  Lg-cvt hz l = tt
  Lg-cvt (hs x) l = Lg-cvt x l
  Lg-cvt (hl f) (st , l) = (λ {w} n → cvt-⊲ (st {bWs w} n)) , (λ n → Lg-cvt (f n) (l n))
  Lg-cvt (hΩ (n , κ) g) (mo , l) =
    (λ {w} {c} {c′} lw bd bd′ pr →
       cvt-⊲ (mo {bWs w} {bE (e n) κ c} {bE (e n) κ c′} (λ i → bLgW (e i) (w i) (lw i))
                 (bBd (e n) κ c (w n) bd) (bBd (e n) κ c′ (w n) bd′) (bPr (e n) κ (w n) c c′ pr))) ,
    (λ c lc → Lg-cvt (g (bE (e n) κ c)) (l _ (bLgE (e n) κ c lc)))
```

## §2 有限码与 ω 码上的 `FoldAt`

```agda
-- 覆盖: 码目标字面地等于某个 fin n
CovF : HB S₀ → Set
CovF t = Σ ℕ (λ n → t ≡ fin n)

eF : ∀ {t n} → t ≡ fin n → Lev {S₀} t ≡ Sk n
eF {n = n} e = trans (cong (Lev {S₀}) e) (levFin n)

-- 码目标 m+1: 第 m+2 级的级顶在码 kfin (m+1) 上折叠, 世界 = v₀ 在这个码上升高槽 x, 读回到第 m+1 级
outF : ∀ m → HB (Sk (suc m)) → HB (Sk (suc m))
outF m x = FF.lay m (dnF m) (FF.fold m (dnF m) (raise v₀ (kfin (suc m)) x) (Ωtop (Sk (suc m))))

loutF : ∀ m x → LgB (outF m x)
loutF m x = FF.Lg-lay m (dnF m) (FF.fold m (dnF m) (raise v₀ (kfin (suc m)) x) (Ωtop (Sk (suc m))))

rtF : ∀ {b} → LgB b → (c : Cod b) → CovF (tgt c) → (w : Wb b) → LgWb w → HB (Lev (tgt c))
rtF lb c (zero , e) w lw = hz
rtF lb c (suc m , e) w lw = toS (sym (eF e)) (outF m (toS (eF e) (w c)))

lrtF : ∀ {b} (lb : LgB b) c (cv : CovF (tgt c)) w (lw : LgWb w) → LgB (rtF lb c cv w lw)
lrtF lb c (zero , e) w lw = tt
lrtF lb c (suc m , e) w lw = lg-toS (sym (eF e)) (outF m (toS (eF e) (w c))) (loutF m (toS (eF e) (w c)))

HF : ∀ {b} → LgB b → (c : Cod b) → CovF (tgt c) → (w : Wb b) → LgWb w → Ht
HF lb c (zero , e) w lw = Ωtop S₀
HF lb c (suc m , e) w lw = proj₁ (dnF m) (outF m (toS (eF e) (w c)))

lgHF : ∀ {b} (lb : LgB b) c (cv : CovF (tgt c)) w (lw : LgWb w) → LgB (HF lb c cv w lw)
lgHF lb c (zero , e) w lw = Lg-Ωtop S₀
lgHF lb c (suc m , e) w lw = proj₂ (dnF m) (outF m (toS (eF e) (w c))) (loutF m (toS (eF e) (w c)))

foldFin : FoldAt CovF
foldFin = record { rt = rtF ; lrt = lrtF ; H = HF ; lgH = lgHF }

-- 覆盖: 码目标字面地是 hl f, 且逐项 f n ≡ fin n
CovΩ : HB S₀ → Set
CovΩ t = Σ (ℕ → HB S₀) (λ f → (t ≡ hl f) × (∀ n → f n ≡ fin n))

toG : ∀ {t} → CovΩ t → HB (Lev t) → HB Gω
toG (f , e , ef) x = Cvt.cvt (λ n → Lev (f n)) Sk (λ n → eF (ef n)) (tpL e x)

ofG : ∀ {t} → CovΩ t → HB Gω → HB (Lev t)
ofG (f , e , ef) y = tpL (sym e) (Cvt.cvt Sk (λ n → Lev (f n)) (λ n → sym (eF (ef n))) y)

lg-ofG : ∀ {t} (cv : CovΩ t) y → LgB y → LgB (ofG cv y)
lg-ofG (f , e , ef) y l = lg-tpL (sym e) _ (Cvt.Lg-cvt Sk (λ n → Lev (f n)) (λ n → sym (eF (ef n))) y l)

-- 码目标 ω: 第 ω+1 级的级顶在码 kω 上折叠 (LvRdFold.FΩ), 世界 = v₀ 在 kω 上升高槽 x, 读回到第 ω 级
outΩ : HB Gω → HB Gω
outΩ x = layΩ (FΩ.fold (raise v₀ kω x) (Ωtop Gω))

loutΩ : ∀ x → LgB (outΩ x)
loutΩ x = Lg-layΩ (FΩ.fold (raise v₀ kω x) (Ωtop Gω))

foldω : FoldAt CovΩ
foldω = record
  { rt = λ lb c cv w lw → ofG cv (outΩ (toG cv (w c)))
  ; lrt = λ lb c cv w lw → lg-ofG cv (outΩ (toG cv (w c))) (loutΩ (toG cv (w c)))
  ; H = λ lb c cv w lw → proj₁ dω (outΩ (toG cv (w c)))
  ; lgH = λ lb c cv w lw → proj₂ dω (outΩ (toG cv (w c))) (loutΩ (toG cv (w c))) }

-- 合并: 有限码与 ω 码
foldTr : FoldAt (λ t → CovF t ⊎ CovΩ t)
foldTr = record { rt = rt′ ; lrt = lrt′ ; H = H′ ; lgH = lgH′ }
  where
  rt′ : ∀ {b} → LgB b → (c : Cod b) → CovF (tgt c) ⊎ CovΩ (tgt c) → (w : Wb b) → LgWb w → HB (Lev (tgt c))
  rt′ lb c (inj₁ cv) = rtF lb c cv
  rt′ lb c (inj₂ cv) = FoldAt.rt foldω lb c cv
  lrt′ : ∀ {b} (lb : LgB b) c (cv : CovF (tgt c) ⊎ CovΩ (tgt c)) w (lw : LgWb w) → LgB (rt′ lb c cv w lw)
  lrt′ lb c (inj₁ cv) = lrtF lb c cv
  lrt′ lb c (inj₂ cv) = FoldAt.lrt foldω lb c cv
  H′ : ∀ {b} → LgB b → (c : Cod b) → CovF (tgt c) ⊎ CovΩ (tgt c) → (w : Wb b) → LgWb w → Ht
  H′ lb c (inj₁ cv) = HF lb c cv
  H′ lb c (inj₂ cv) = FoldAt.H foldω lb c cv
  lgH′ : ∀ {b} (lb : LgB b) c (cv : CovF (tgt c) ⊎ CovΩ (tgt c)) w (lw : LgWb w) → LgB (H′ lb c cv w lw)
  lgH′ lb c (inj₁ cv) = lgHF lb c cv
  lgH′ lb c (inj₂ cv) = FoldAt.lgH foldω lb c cv
```

## §3 截断版: 读法取常数 1, 无条件

```agda
one₀ : Ht → HB S₀
one₀ _ = hs hz

covS1 : ∀ t h → CovF t → CovF (t ⊞ one₀ h)
covS1 t h (n , e) = suc n , cong hs e

module Tr = Tower CovF foldFin one₀ (λ _ → tt) hz tt (zero , refl) covS1

-- 各站的界就是有限级的坐标
B-fin : ∀ s → Tr.B s ≡ fin s
B-fin zero = refl
B-fin (suc s) = cong hs (B-fin s)

-- 极限界逐项等于 fin n: 在 ω 码的覆盖之内
covL : CovΩ Tr.Bω
covL = Tr.PS.psum , refl , (λ n → trans (Tr.psum≡B n) (B-fin n))

module TrL = Tr.Lim CovΩ foldω covL

-- 只有有限站的对角
Ttr∞ : A
Ttr∞ = Tr.TΛ∞

Lg-Ttr∞ : Lg Ttr∞
Lg-Ttr∞ = Tr.Lg-TΛ∞

-- 有限站的对角加极限站 (第 ω+1 级): 截断版闭项
Ttr : A
Ttr = TrL.TΛ∞ω

Lg-Ttr : Lg Ttr
Lg-Ttr = TrL.Lg-TΛ∞ω

fghTr : ℕ → ℕ
fghTr = FLv.FGH (ord Ttr)
```

## §4 全塔版: 以一切码上的 `FoldAt` 为前提

```agda
module FullΛ (F : FoldAll) (b₀ : HB S₀) (lb₀ : LgB b₀) where
  open Full F σ₀ lσ₀ b₀ lb₀ public
  -- 闭项 (条件): TΛ∞ (ψ₀Λ 的候选), TΛ∞ω (加极限站); 证书 Lg-TΛ∞, Lg-TΛ∞ω; FGH fghΛ∞, fghΛ∞ω
```
