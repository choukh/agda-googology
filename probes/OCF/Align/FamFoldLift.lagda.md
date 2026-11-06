# 族增量世界上的真折叠 (三): 塔上的种类提升与连续分支

> 不含记号. 入口 [FamFold](FamFold.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> 第一级与第二级 ([FamFoldOne](FamFoldOne.lagda.md), [FamFoldTwo](FamFoldTwo.lagda.md)) 的差别只在读回: 第 $k+1$ 层的树读成 `HB (Sk k)` 时, 过第 $m\le k$ 层的节点读成第 $m$ 级种类的 $\Omega$-分支, 分支对坐标 (`Co m`: $m=0$ 时 `A`, 否则 `HB (Sk (m-1))`) 连续递归 (`nbA₂`, `nbH₂`, `nbᴮ` 各写了一遍). 本篇对一切 $m\le k$ 一条定义:
>
> - `Le m k`: $m\le k$ 的证据; `liftK p`: `Sk m` 的种类经 `inj₁` 搬进 `Sk k`. 坐标, 界, 第一位置, 世界, 合法都沿 `p` 逐步换 (`cvE`, `vcE`, `pwL`, `bd→`, `bd←`, `pr→`, `lw→`, `le→`), 每一步是定义相等 (`step` 的旧种类原样), 一般的 $p$ 上只有命题相等 `cv-vc`, `pw-pr`.
> - `nbC p b s`: 坐标 `Co m` 上的连续递归, 坐标里的 $\Omega$-节点 (种类 $\kappa$) 读成 `liftK (prL p) κ` 的节点. `node p b s = hΩ (liftK p (top m)) (nbC p b s ∘ …)`.
> - **一步定理 `Lg-node`**: 底合法, 每步是第一位置且保合法, 则 `node p b s` 合法; **`fst-node`**: 底是它的第一位置 (在一切世界). 对一切 $m\le k$, 一条证明 (对坐标的路径归纳, 界与世界沿 `p` 搬).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.FamFoldLift where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.FamFoldIf using (Sk)
```

## §1 级与种类的提升

```agda
-- 第 m 级新种类的坐标
Co : ℕ → Set
Co zero = A
Co (suc m) = HB (Sk m)

top : ∀ m → K (Sk m)
top zero = tt
top (suc m) = inj₂ tt

topC : ∀ m → E (Sk m) (top m) → Co m
topC zero c = c
topC (suc m) c = c

Ctop : ∀ m → Co m → E (Sk m) (top m)
Ctop zero c = c
Ctop (suc m) c = c

data Le : ℕ → ℕ → Set where
  ≤r : ∀ {m} → Le m m
  ≤s : ∀ {m k} → Le m k → Le m (suc k)

prL : ∀ {m k} → Le (suc m) k → Le m k
prL ≤r = ≤s ≤r
prL (≤s p) = ≤s (prL p)

-- Le (suc a) (suc b) → Le a b
pdL : ∀ {a b} → Le (suc a) (suc b) → Le a b
pdL ≤r = ≤r
pdL (≤s p) = prL p

le0 : ∀ k → Le 0 k
le0 zero = ≤r
le0 (suc k) = ≤s (le0 k)

le1 : ∀ k → Le 1 (suc k)
le1 zero = ≤r
le1 (suc k) = ≤s (le1 k)

liftK : ∀ {m k} → Le m k → K (Sk m) → K (Sk k)
liftK ≤r κ = κ
liftK (≤s p) κ = inj₁ (liftK p κ)

cvE : ∀ {m k} (p : Le m k) {κ} → E (Sk k) (liftK p κ) → E (Sk m) κ
cvE ≤r c = c
cvE (≤s p) c = cvE p c

vcE : ∀ {m k} (p : Le m k) {κ} → E (Sk m) κ → E (Sk k) (liftK p κ)
vcE ≤r c = c
vcE (≤s p) c = vcE p c

cv-vc : ∀ {m k} (p : Le m k) {κ} (c : E (Sk m) κ) → cvE p {κ} (vcE p c) ≡ c
cv-vc ≤r c = refl
cv-vc (≤s p) c = cv-vc p c

pwL : ∀ {m k} → Le m k → Wd (Sk k) → Wd (Sk m)
pwL ≤r w = w
pwL (≤s p) w = pwL p (proj₁ w)

pw-pr : ∀ {m k} (p : Le (suc m) k) (w : Wd (Sk k)) → pwL (prL p) w ≡ proj₁ (pwL p w)
pw-pr ≤r w = refl
pw-pr (≤s p) w = pw-pr p (proj₁ w)

bd→ : ∀ {m k} (p : Le m k) {κ c w} → Bd (Sk k) (liftK p κ) c w → Bd (Sk m) κ (cvE p c) (pwL p w)
bd→ ≤r e = e
bd→ (≤s p) e = bd→ p e

bd← : ∀ {m k} (p : Le m k) {κ c w} → Bd (Sk m) κ c (pwL p w) → Bd (Sk k) (liftK p κ) (vcE p c) w
bd← ≤r e = e
bd← (≤s p) e = bd← p e

pr→ : ∀ {m k} (p : Le m k) {κ c c′ w} → Pr (Sk k) (liftK p κ) w c c′ → Pr (Sk m) κ (pwL p w) (cvE p c) (cvE p c′)
pr→ ≤r e = e
pr→ (≤s p) e = pr→ p e

lw→ : ∀ {m k} (p : Le m k) {w} → LgW (Sk k) w → LgW (Sk m) (pwL p w)
lw→ ≤r l = l
lw→ (≤s p) l = lw→ p (proj₁ l)

le→ : ∀ {m k} (p : Le m k) {κ c} → LgE (Sk k) (liftK p κ) c → LgE (Sk m) κ (cvE p c)
le→ ≤r l = l
le→ (≤s p) l = le→ p l
```

## §2 坐标上的连续递归

```agda
nbA′ : ∀ {k} → Le zero k → HB (Sk k) → (A → HB (Sk k) → HB (Sk k)) → A → HB (Sk k)
nbA′ p b s azero = b
nbA′ p b s (asuc c) = s c (nbA′ p b s c)
nbA′ p b s (alim f) = hl (λ n → nbA′ p b s (f n))

nbH′ : ∀ {m k} → Le (suc m) k → HB (Sk k) → (HB (Sk m) → HB (Sk k) → HB (Sk k)) → HB (Sk m) → HB (Sk k)
nbH′ p b s hz = b
nbH′ p b s (hs x) = s x (nbH′ p b s x)
nbH′ p b s (hl f) = hl (λ n → nbH′ p b s (f n))
nbH′ p b s (hΩ κ h) = hΩ (liftK (prL p) κ) (λ c → nbH′ p b s (h (cvE (prL p) c)))

nbC : ∀ {m k} → Le m k → HB (Sk k) → (Co m → HB (Sk k) → HB (Sk k)) → Co m → HB (Sk k)
nbC {m = zero} = nbA′
nbC {m = suc m} = nbH′

node : ∀ {m k} → Le m k → HB (Sk k) → (Co m → HB (Sk k) → HB (Sk k)) → HB (Sk k)
node {m} p b s = hΩ (liftK p (top m)) (λ c → nbC p b s (topC m (cvE p c)))
```

**单调.** 坐标是 `A` 时对 `A` 的路径; 坐标是 `HB (Sk m)` 时对它的路径, 走进坐标的 $\Omega$-极限 (种类 $\kappa$, 界的证据 $e$) 时输出走进 `liftK (prL p) κ` 的节点, 坐标取 `vcE`, 界沿 `bd←` 搬, 世界与坐标的对应用 `pw-pr`, `cv-vc` (命题相等, 用 `subst`).

```agda
module _ {k} (p : Le zero k) {b : HB (Sk k)} {s : A → HB (Sk k) → HB (Sk k)} (fs : ∀ c h {w} → h ⊲[ w ] s c h) where
  nbC₀-mono : ∀ {c c′} → c ⊲ c′ → ∀ {w} → nbA′ p b s c ⊲[ w ] nbA′ p b s c′
  nbC₀-mono C.self = hself
  nbC₀-mono (C.suc q) = ⊲ᴮ-tr (nbC₀-mono q) (fs _ _)
  nbC₀-mono (C.lim n q) = hlim n (nbC₀-mono q)

  Lg-nbC₀ : LgB b → (∀ c h → LgB h → LgB (s c h)) → ∀ c → Lg c → LgB (nbA′ p b s c)
  Lg-nbC₀ lb ls azero _ = lb
  Lg-nbC₀ lb ls (asuc c) l = ls c _ (Lg-nbC₀ lb ls c l)
  Lg-nbC₀ lb ls (alim f) (st , l) = (λ n → nbC₀-mono (st n)) , (λ n → Lg-nbC₀ lb ls (f n) (l n))

module _ {m k} (p : Le (suc m) k) {b : HB (Sk k)} {s : HB (Sk m) → HB (Sk k) → HB (Sk k)} (fs : ∀ x h {w} → h ⊲[ w ] s x h) where
  nbC-mono : ∀ {x y : HB (Sk m)} {w : Wd (Sk k)} → x ⊲[ proj₁ (pwL p w) ] y → nbH′ p b s x ⊲[ w ] nbH′ p b s y
  nbC-mono hself = hself
  nbC-mono (hsuc q) = ⊲ᴮ-tr (nbC-mono q) (fs _ _)
  nbC-mono (hlim n q) = hlim n (nbC-mono q)
  nbC-mono {x} {w = w} (hLim {κ = κ} {g = h} {c = c} e q) =
    hLim {κ = liftK (prL p) κ} {c = vcE (prL p) c}
      (bd← (prL p) (subst (Bd (Sk m) κ c) (sym (pw-pr p w)) e))
      (subst (λ z → nbH′ p b s x ⊲[ w ] nbH′ p b s (h z)) (sym (cv-vc (prL p) c)) (nbC-mono q))

  Lg-nbC : LgB b → (∀ x h → LgB h → LgB (s x h)) → ∀ x → LgB x → LgB (nbH′ p b s x)
  Lg-nbC lb ls hz _ = lb
  Lg-nbC lb ls (hs x) l = ls x _ (Lg-nbC lb ls x l)
  Lg-nbC lb ls (hl f) (st , l) = (λ {w} n → nbC-mono {w = w} (st n)) , (λ n → Lg-nbC lb ls (f n) (l n))
  Lg-nbC lb ls (hΩ κ h) (mo , l) =
    (λ {w} {c} {c′} lw e e′ r →
       nbC-mono {w = w}
         (subst (λ z → h (cvE (prL p) c) ⊲[ z ] h (cvE (prL p) c′)) (pw-pr p w)
           (mo (lw→ (prL p) lw) (bd→ (prL p) e) (bd→ (prL p) e′) (pr→ (prL p) r)))) ,
    (λ c lc → Lg-nbC lb ls (h (cvE (prL p) c)) (l _ (le→ (prL p) lc)))
```

## §3 一步定理: 节点合法, 底是第一位置

```agda
Lg-node : ∀ {m k} (p : Le m k) {b : HB (Sk k)} {s : Co m → HB (Sk k) → HB (Sk k)} →
          (∀ x h {w} → h ⊲[ w ] s x h) → LgB b → (∀ x h → LgB h → LgB (s x h)) → LgB (node p b s)
Lg-node {m = zero} p fs lb ls =
  (λ lw e e′ r → nbC₀-mono p fs (pr→ p r)) , (λ c lc → Lg-nbC₀ p fs lb ls (cvE p c) (le→ p lc))
Lg-node {m = suc m} p fs lb ls =
  (λ {w} lw e e′ r → nbC-mono p fs {w = w} (pr→ p r)) , (λ c lc → Lg-nbC p fs lb ls (cvE p c) (le→ p lc))

fst-node : ∀ {m k} (p : Le m k) (b : HB (Sk k)) (s : Co m → HB (Sk k) → HB (Sk k)) {w} → b ⊲[ w ] node p b s
fst-node {m = zero} p b s {w} =
  hLim {κ = liftK p tt} {c = vcE p azero} (bd← p (z⊲ (pwL p w)))
    (subst (λ z → b ⊲[ w ] nbC p b s z) (sym (cv-vc p azero)) hself)
fst-node {m = suc m} p b s {w} =
  hLim {κ = liftK p (inj₂ tt)} {c = vcE p hz} (bd← p (z⊲ᴮ (proj₂ (pwL p w))))
    (subst (λ z → b ⊲[ w ] nbC p b s z) (sym (cv-vc p hz)) hself)
```
