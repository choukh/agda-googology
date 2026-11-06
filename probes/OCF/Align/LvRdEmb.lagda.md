# 读回包 (一): 种类的嵌入与对坐标连续的结点

> 不含记号. 入口 [LvRd](LvRd.lagda.md), 接口 [LvRdIf](LvRdIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> [FamFoldLift](FamFoldLift.lagda.md) 的 `node p b s` 把第 $m$ 级的种类经 `Le m k` 搬进 `Sk k`, 输出在 `HB (Sk k)` 里. 读第 $\omega$ 层的树时输出在 `HB Gω` (`Gω = sup ℕ Sk`) 里, 种类要经 `Le` 再经并的第 $n$ 个分量; 读第 $\omega+1$ 层时还要再经 `inj₁`. 本篇把 "种类怎样搬" 抽成一个记录 **`Emb U T`** (种类映射, 坐标往返, 世界投影, 界与第一位置与合法沿投影传), 对任意 `Emb` 一条定义, 一条合法证明:
>
> - `nodeA e b s` (`e : Emb S₀ T`): 坐标是 `A` 的结点, 分支对坐标连续递归.
> - `nodeH e b s` (`e : Emb (step U) T`): 坐标是 `HB U` 的结点 (新种类 `inj₂ tt` 搬过去), 坐标里的 $\Omega$-结点 (种类 $\kappa$) 读成 `lk e (inj₁ κ)` 的结点.
> - **一步定理** `Lg-nodeA`, `Lg-nodeH`: 底合法, 每步是第一位置且保合法, 则结点合法; `fst-nodeA`, `fst-nodeH`: 底是结点的第一位置 (在一切世界).
> - 实例: `idE`, `inj₁E` (旧种类进 `step`), `ιE i` (第 $i$ 个分量进 `sup`), 复合 `compE`, 由 `Le` 给出的 `lePE` (就是 `liftK` 那一串). 每个字段都是定义相等或已有字段的复合, 不用 `FamFoldLift` 的 `pw-pr` (内层种类取 `lk (inj₁ κ)`, 世界沿同一个投影).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvRdEmb where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.FamFoldIf using (Sk)
open import OCF.Align.FamFoldLift using (Le; ≤r; ≤s)
```

## §1 嵌入

```agda
record Emb (U T : KS) : Set where
  field
    lk    : K U → K T
    cv    : ∀ {κ} → E T (lk κ) → E U κ
    vc    : ∀ {κ} → E U κ → E T (lk κ)
    cv-vc : ∀ {κ} (c : E U κ) → cv {κ} (vc c) ≡ c
    π     : Wd T → Wd U
    bd→   : ∀ {κ c w} → Bd T (lk κ) c w → Bd U κ (cv c) (π w)
    bd←   : ∀ {κ c w} → Bd U κ c (π w) → Bd T (lk κ) (vc c) w
    pr→   : ∀ {κ c c′ w} → Pr T (lk κ) w c c′ → Pr U κ (π w) (cv c) (cv c′)
    lw→   : ∀ {w} → LgW T w → LgW U (π w)
    le→   : ∀ {κ c} → LgE T (lk κ) c → LgE U κ (cv c)
open Emb public

idE : ∀ S → Emb S S
idE S = record { lk = λ κ → κ ; cv = λ c → c ; vc = λ c → c ; cv-vc = λ c → refl ; π = λ w → w
               ; bd→ = λ e → e ; bd← = λ e → e ; pr→ = λ r → r ; lw→ = λ l → l ; le→ = λ l → l }

inj₁E : ∀ S → Emb S (step S)
inj₁E S = record { lk = inj₁ ; cv = λ c → c ; vc = λ c → c ; cv-vc = λ c → refl ; π = proj₁
                 ; bd→ = λ e → e ; bd← = λ e → e ; pr→ = λ r → r ; lw→ = proj₁ ; le→ = λ l → l }

ιE : ∀ {I : Set} {F : I → KS} (i : I) → Emb (F i) (sup I F)
ιE i = record { lk = λ κ → i , κ ; cv = λ c → c ; vc = λ c → c ; cv-vc = λ c → refl ; π = λ w → w i
              ; bd→ = λ e → e ; bd← = λ e → e ; pr→ = λ r → r ; lw→ = λ l → l i ; le→ = λ l → l }

compE : ∀ {U T V} → Emb U T → Emb T V → Emb U V
compE e f = record
  { lk = λ κ → lk f (lk e κ) ; cv = λ c → cv e (cv f c) ; vc = λ c → vc f (vc e c)
  ; cv-vc = λ c → trans (cong (cv e) (cv-vc f (vc e c))) (cv-vc e c)
  ; π = λ w → π e (π f w)
  ; bd→ = λ q → bd→ e (bd→ f q) ; bd← = λ q → bd← f (bd← e q) ; pr→ = λ r → pr→ e (pr→ f r)
  ; lw→ = λ l → lw→ e (lw→ f l) ; le→ = λ l → le→ e (le→ f l) }

lePE : ∀ {m k} → Le m k → Emb (Sk m) (Sk k)
lePE {m} ≤r = idE (Sk m)
lePE {k = suc k} (≤s p) = compE (lePE p) (inj₁E (Sk k))
```

## §2 坐标是 `A` 的结点

```agda
module _ {T : KS} where
  nbAG : HB T → (A → HB T → HB T) → A → HB T
  nbAG b s azero = b
  nbAG b s (asuc c) = s c (nbAG b s c)
  nbAG b s (alim f) = hl (λ n → nbAG b s (f n))

  module _ {b : HB T} {s : A → HB T → HB T} (fs : ∀ c h {w} → h ⊲[ w ] s c h) where
    nbAG-mono : ∀ {c c′} → c ⊲ c′ → ∀ {w} → nbAG b s c ⊲[ w ] nbAG b s c′
    nbAG-mono C.self = hself
    nbAG-mono (C.suc q) = ⊲ᴮ-tr (nbAG-mono q) (fs _ _)
    nbAG-mono (C.lim n q) = hlim n (nbAG-mono q)

    Lg-nbAG : LgB b → (∀ c h → LgB h → LgB (s c h)) → ∀ c → Lg c → LgB (nbAG b s c)
    Lg-nbAG lb ls azero _ = lb
    Lg-nbAG lb ls (asuc c) l = ls c _ (Lg-nbAG lb ls c l)
    Lg-nbAG lb ls (alim f) (st , l) = (λ n → nbAG-mono (st n)) , (λ n → Lg-nbAG lb ls (f n) (l n))

  nodeA : Emb S₀ T → HB T → (A → HB T → HB T) → HB T
  nodeA e b s = hΩ (lk e tt) (λ c → nbAG b s (cv e c))

  Lg-nodeA : ∀ (e : Emb S₀ T) {b s} → (∀ c h {w} → h ⊲[ w ] s c h) → LgB b → (∀ c h → LgB h → LgB (s c h)) →
             LgB (nodeA e b s)
  Lg-nodeA e fs lb ls = (λ lw q q′ r → nbAG-mono fs (pr→ e r)) , (λ c lc → Lg-nbAG fs lb ls (cv e c) (le→ e lc))

  fst-nodeA : ∀ (e : Emb S₀ T) b s {w} → b ⊲[ w ] nodeA e b s
  fst-nodeA e b s {w} =
    hLim {κ = lk e tt} {c = vc e azero} (bd← e (z⊲ (π e w)))
      (subst (λ z → b ⊲[ w ] nbAG b s z) (sym (cv-vc e azero)) hself)
```

## §3 坐标是高度的结点

```agda
module _ {U T : KS} (e : Emb (step U) T) where
  nbHG : HB T → (HB U → HB T → HB T) → HB U → HB T
  nbHG b s hz = b
  nbHG b s (hs x) = s x (nbHG b s x)
  nbHG b s (hl f) = hl (λ n → nbHG b s (f n))
  nbHG b s (hΩ κ h) = hΩ (lk e (inj₁ κ)) (λ c → nbHG b s (h (cv e c)))

  module _ {b : HB T} {s : HB U → HB T → HB T} (fs : ∀ x h {w} → h ⊲[ w ] s x h) where
    nbHG-mono : ∀ {x y : HB U} {w : Wd T} → x ⊲[ proj₁ (π e w) ] y → nbHG b s x ⊲[ w ] nbHG b s y
    nbHG-mono hself = hself
    nbHG-mono (hsuc q) = ⊲ᴮ-tr (nbHG-mono q) (fs _ _)
    nbHG-mono (hlim n q) = hlim n (nbHG-mono q)
    nbHG-mono {x} {w = w} (hLim {κ = κ} {g = h} {c = c} q₀ q) =
      hLim {κ = lk e (inj₁ κ)} {c = vc e c} (bd← e {κ = inj₁ κ} q₀)
        (subst (λ z → nbHG b s x ⊲[ w ] nbHG b s (h z)) (sym (cv-vc e {inj₁ κ} c)) (nbHG-mono q))

    Lg-nbHG : LgB b → (∀ x h → LgB h → LgB (s x h)) → ∀ x → LgB x → LgB (nbHG b s x)
    Lg-nbHG lb ls hz _ = lb
    Lg-nbHG lb ls (hs x) l = ls x _ (Lg-nbHG lb ls x l)
    Lg-nbHG lb ls (hl f) (st , l) = (λ {w} n → nbHG-mono {w = w} (st n)) , (λ n → Lg-nbHG lb ls (f n) (l n))
    Lg-nbHG lb ls (hΩ κ h) (mo , l) =
      (λ {w} lw q q′ r →
         nbHG-mono {w = w} (mo (proj₁ (lw→ e lw)) (bd→ e {κ = inj₁ κ} q) (bd→ e {κ = inj₁ κ} q′) (pr→ e {κ = inj₁ κ} r))) ,
      (λ c lc → Lg-nbHG lb ls (h (cv e c)) (l _ (le→ e {κ = inj₁ κ} lc)))

  nodeH : HB T → (HB U → HB T → HB T) → HB T
  nodeH b s = hΩ (lk e (inj₂ tt)) (λ c → nbHG b s (cv e c))

  Lg-nodeH : ∀ {b s} → (∀ x h {w} → h ⊲[ w ] s x h) → LgB b → (∀ x h → LgB h → LgB (s x h)) → LgB (nodeH b s)
  Lg-nodeH fs lb ls =
    (λ {w} lw q q′ r → nbHG-mono fs {w = w} (pr→ e r)) , (λ c lc → Lg-nbHG fs lb ls (cv e c) (le→ e lc))

  fst-nodeH : ∀ b s {w} → b ⊲[ w ] nodeH b s
  fst-nodeH b s {w} =
    hLim {κ = lk e (inj₂ tt)} {c = vc e hz} (bd← e (z⊲ᴮ (proj₂ (π e w))))
      (subst (λ z → b ⊲[ w ] nbHG b s z) (sym (cv-vc e hz)) hself)
```
