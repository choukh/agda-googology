# 有内容的下降 (四): 第 1 站的层号搬进 `Ht` (`μ′`, 有损, 保合法)

> 不含记号. 入口 [DnFold](DnFold.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> 第 1 站的层号在 `HB (Kc 1)`, `Kc 1 = sup (⊤ ⊎ H₀) (FN S₀)`. 它的种类分两类 (`Kd1`, 对种类的构造子分情形, 不判定任何高度的序):
>
> - **保留** (坐标是 `A` 或 `H₀`): `(inj₁ tt, tt)`, `(inj₂ 0, tt)`, `(inj₂ 1, inj₁ tt)` 读成 `Ht` 的 κA; `(inj₂ 1, inj₂ tt)` (坐标 `H₀`) 读成 κH. 第 1 站层号 `B 1` 的种类全在这里 (`KcFoldTower.One.B1-shape`).
> - **丢掉** (`Oth c`: 层号 $c\ge2$ 或含极限的级, 坐标是更高的高度): 只走底支.
>
> `μ′ b` 是 $1\boxplus$ (逐构造子) 搬过去的结果 (`μ′ hz = 1`), 所以第 1 层总是它的第一位置 (`one⊲`). **合法由世界的翻译给出** (`Lg-μ′`): `ωW W` 把 `Ht` 的世界 $W$ 翻成 `Kc 1` 的世界 (保留的分量取 $W$ 或 $W_A$, 丢掉的分量取码的基世界 `w0`); 在基世界里丢掉的种类只有底坐标可入 (`basebot`), 所以经过丢掉的结点的路径只走底支 (`μ-⊲`). 只用到合法层号的单调性, 不判定.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.DnFoldMu where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (S₁; H₀; Ht; Wd₂; LgW₂; κA; κH)
open import OCF.Align.LvKtCode using (CdK; cdLev; w0; lw0)
open import OCF.Align.LvKtIf using (Kc; ckc; FN)
```

## §1 种类的分类

```agda
K1 : KS
K1 = Kc 1

data Oth : H₀ → Set where
  o₁ : ∀ c → Oth (hs (hs c))
  o₂ : ∀ f → Oth (hs (hl f))
  o₃ : ∀ k h → Oth (hs (hΩ k h))
  o₄ : ∀ f → Oth (hl f)
  o₅ : ∀ k h → Oth (hΩ k h)

data Kd1 : K K1 → Set where
  kA₁ : Kd1 (inj₁ tt , tt)
  kA₂ : Kd1 (inj₂ hz , tt)
  kA₃ : Kd1 (inj₂ (hs hz) , inj₁ tt)
  kH  : Kd1 (inj₂ (hs hz) , inj₂ tt)
  kO  : ∀ {c} κ → Oth c → Kd1 (inj₂ c , κ)

kd1 : ∀ κ → Kd1 κ
kd1 (inj₁ tt , tt) = kA₁
kd1 (inj₂ hz , tt) = kA₂
kd1 (inj₂ (hs hz) , inj₁ tt) = kA₃
kd1 (inj₂ (hs hz) , inj₂ tt) = kH
kd1 (inj₂ (hs (hs c)) , κ) = kO κ (o₁ c)
kd1 (inj₂ (hs (hl f)) , κ) = kO κ (o₂ f)
kd1 (inj₂ (hs (hΩ k h)) , κ) = kO κ (o₃ k h)
kd1 (inj₂ (hl f) , κ) = kO κ (o₄ f)
kd1 (inj₂ (hΩ k h) , κ) = kO κ (o₅ k h)
```

## §2 层号的搬运

```agda
μΩ : ∀ κ → Kd1 κ → (E K1 κ → Ht) → Ht
μΩ _ kA₁ r = hΩ κA r
μΩ _ kA₂ r = hΩ κA r
μΩ _ kA₃ r = hΩ κA r
μΩ _ kH r = hΩ κH r
μΩ _ (kO {c} κ o) r = r (bot K1 (inj₂ c , κ))

μ′ : HB K1 → Ht
μ′ hz = hs hz
μ′ (hs b) = hs (μ′ b)
μ′ (hl f) = hl (λ n → μ′ (f n))
μ′ (hΩ κ g) = μΩ κ (kd1 κ) (λ x → μ′ (g x))
```

## §3 世界的翻译与基世界

```agda
ωW : Wd₂ → Wd K1
ωW W (inj₁ tt) = proj₁ W
ωW W (inj₂ hz) = proj₁ W
ωW W (inj₂ (hs hz)) = W
ωW W (inj₂ (hs (hs c))) = w0 (cdLev (hs (hs c)))
ωW W (inj₂ (hs (hl f))) = w0 (cdLev (hs (hl f)))
ωW W (inj₂ (hs (hΩ k h))) = w0 (cdLev (hs (hΩ k h)))
ωW W (inj₂ (hl f)) = w0 (cdLev (hl f))
ωW W (inj₂ (hΩ k h)) = w0 (cdLev (hΩ k h))

lωW : ∀ {W} → LgW₂ W → LgW K1 (ωW W)
lωW lW (inj₁ tt) = proj₁ lW
lωW lW (inj₂ hz) = proj₁ lW
lωW lW (inj₂ (hs hz)) = lW
lωW lW (inj₂ (hs (hs c))) = lw0 (cdLev (hs (hs c)))
lωW lW (inj₂ (hs (hl f))) = lw0 (cdLev (hs (hl f)))
lωW lW (inj₂ (hs (hΩ k h))) = lw0 (cdLev (hs (hΩ k h)))
lωW lW (inj₂ (hl f)) = lw0 (cdLev (hl f))
lωW lW (inj₂ (hΩ k h)) = lw0 (cdLev (hΩ k h))

-- 丢掉的分量取的是基世界
eO : ∀ {W c} → Oth c → ∀ {κ x} → Bd (Lev c) κ x (ωW W (inj₂ c)) → Bd (Lev c) κ x (w0 (cdLev c))
eO (o₁ c) e = e
eO (o₂ f) e = e
eO (o₃ k h) e = e
eO (o₄ f) e = e
eO (o₅ k h) e = e

-- 基世界里只有底坐标可入
basebot : ∀ (c : H₀) κ x → Bd (Lev c) κ x (w0 (cdLev c)) → x ≡ bot (Lev c) κ
basebot hz tt x C.self = refl
basebot (hs c) (inj₁ κ) x e = basebot c κ x e
basebot (hs c) (inj₂ tt) x hself = refl
basebot (hl f) (n , κ) x e = basebot (f n) κ x e
basebot (hΩ k g) (y , κ) x e = basebot (g y) κ x e
```

## §4 保第一位置与合法

```agda
μΩ-⊲ : ∀ {W : Wd₂} κ (k : Kd1 κ) (g : E K1 κ → HB K1) x → Bd K1 κ x (ωW W) →
       ∀ {t} → t ⊲[ W ] μ′ (g x) → t ⊲[ W ] μΩ κ k (λ y → μ′ (g y))
μΩ-⊲ _ kA₁ g x e q = hLim {κ = κA} {c = x} e q
μΩ-⊲ _ kA₂ g x e q = hLim {κ = κA} {c = x} e q
μΩ-⊲ _ kA₃ g x e q = hLim {κ = κA} {c = x} e q
μΩ-⊲ _ kH g x e q = hLim {κ = κH} {c = x} e q
μΩ-⊲ {W} _ (kO {c} κ o) g x e {t} q = subst (λ z → t ⊲[ W ] μ′ (g z)) (basebot c κ x (eO {W} o e)) q

μ-⊲ : ∀ {W : Wd₂} {a b : HB K1} → a ⊲[ ωW W ] b → μ′ a ⊲[ W ] μ′ b
μ-⊲ hself = hself
μ-⊲ (hsuc p) = hsuc (μ-⊲ p)
μ-⊲ (hlim n p) = hlim n (μ-⊲ p)
μ-⊲ (hLim {κ = κ} {g = g} {c = x} e p) = μΩ-⊲ κ (kd1 κ) g x e (μ-⊲ p)

LgΩ : ∀ κ (k : Kd1 κ) (g : E K1 κ → HB K1) →
      (∀ {w c c′} → LgW K1 w → Bd K1 κ c w → Bd K1 κ c′ w → Pr K1 κ w c c′ → g c ⊲[ w ] g c′) →
      (∀ x → LgE K1 κ x → LgB (μ′ (g x))) → LgB (μΩ κ k (λ x → μ′ (g x)))
LgΩ _ kA₁ g mo rec = (λ lw e e′ pr → μ-⊲ (mo (lωW lw) e e′ pr)) , rec
LgΩ _ kA₂ g mo rec = (λ lw e e′ pr → μ-⊲ (mo (lωW lw) e e′ pr)) , rec
LgΩ _ kA₃ g mo rec = (λ lw e e′ pr → μ-⊲ (mo (lωW lw) e e′ pr)) , rec
LgΩ _ kH g mo rec = (λ lw e e′ pr → μ-⊲ (mo (lωW lw) e e′ pr)) , rec
LgΩ _ (kO {c} κ o) g mo rec =
  rec (bot K1 (inj₂ c , κ)) (lgBd K1 {κ = inj₂ c , κ} {c = bot K1 (inj₂ c , κ)} {w = w0 (ckc 1)} (botBd K1 (inj₂ c , κ) (w0 (ckc 1))) (lw0 (ckc 1)))

Lg-μ′ : ∀ b → LgB b → LgB (μ′ b)
Lg-μ′ hz _ = tt
Lg-μ′ (hs b) l = Lg-μ′ b l
Lg-μ′ (hl f) (st , l) = (λ {w} n → μ-⊲ (st {ωW w} n)) , (λ n → Lg-μ′ (f n) (l n))
Lg-μ′ (hΩ κ g) (mo , l) = LgΩ κ (kd1 κ) g mo (λ x lx → Lg-μ′ (g x) (l x lx))
```

## §5 第 1 层总是第一位置

```agda
oneΩ : ∀ {w : Wd₂} κ (k : Kd1 κ) (g : E K1 κ → HB K1) → hs hz ⊲[ w ] μ′ (g (bot K1 κ)) →
       hs hz ⊲[ w ] μΩ κ k (λ x → μ′ (g x))
oneΩ {w} _ kA₁ g q = hLim (botBd S₁ κA w) q
oneΩ {w} _ kA₂ g q = hLim (botBd S₁ κA w) q
oneΩ {w} _ kA₃ g q = hLim (botBd S₁ κA w) q
oneΩ {w} _ kH g q = hLim (botBd S₁ κH w) q
oneΩ _ (kO κ o) g q = q

one⊲ : ∀ b {w : Wd₂} → hs hz ⊲[ w ] μ′ b
one⊲ hz = hself
one⊲ (hs b) = hsuc (one⊲ b)
one⊲ (hl f) = hlim 0 (one⊲ (f 0))
one⊲ (hΩ κ g) = oneΩ κ (kd1 κ) g (one⊲ (g (bot K1 κ)))
```
