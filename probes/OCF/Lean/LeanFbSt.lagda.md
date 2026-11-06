# LeanFb (一): 站以 ℕ 为下标; 塔, 对角, 一个站的头的升界

> 不含记号. 入口 [LeanFb](LeanFb.lagda.md), 接口 [LeanFbIf](LeanFbIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> 在 [LeanTLv](LeanTLv.lagda.md) 的一次封闭层号 `LH`/`Lv` 上重写 [Fab2SLs](../Align/Fab2SLs.lagda.md) §1, §3 (只读参考, 不导入 `OCF.Align`): 第 $n$ 站的层号 `st n = ofHB (tw n)`, 种类结构 `FS n = step (Lv (st n))`, 站并成 `SLs = sup ℕ FS`. 头种类 `νS n` 的坐标字面就是 `HB (Lv (st n))`. 塔 $t_{n+1}=\sup_c (t_n\boxplus c)$ ($c$ 过第 $n$ 站头的坐标), 对角 $\Lambda_s=\sup_n(1\boxplus t_n)$, 折叠的最高层 `ΛF = up Λs`.
>
> 站的世界以 $\mathbb N$ 为下标, 所以一个站的头可以单独升 (`upd`, 对站号与分量号同时递归): 接口的 `Up` 只有一个成员 (`headUp n`), 升的是第 $n$ 站世界的第二分量, 别的站原样 (`upd-keep`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.LeanFbSt where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Lean.LeanTBase
open import OCF.Lean.LeanTLv
open import OCF.Lean.LeanFbIf
```

## §1 站, 塔, 对角

```agda
st : ℕ → LH
st n = ofHB (tw n)

FS : ℕ → KS
FS n = FL (st n)

SLs : KS
SLs = sup ℕ FS

νS : ℕ → K SLs
νS n = n , inj₂ tt

ιS : ∀ n → HB (FS n) → HB SLs
ιS n = ι {ℕ} {FS} n

tws : ℕ → HB SLs
tws zero = hz
tws (suc n) = hΩ (νS n) (λ c → tws n ⊞ ιS n (up c))

tws-st : ∀ {W} n → tws n ⊲[ W ] tws (suc n)
tws-st {W} n = hLim (botBd SLs (νS n) W) (⊞-fst (tws n) hz)

Lg-tws : ∀ n → LgB (tws n)
Lg-tws zero = tt
Lg-tws (suc n) =
  (λ {W} lw e e′ p → ⊞-⊲ (tws n) (ι-⊲ {ℕ} {FS} {n} {w = W} (up-⊲ p))) ,
  (λ {W} {c} lw e → Lg-⊞ (tws n) (ιS n (up c)) (Lg-tws n)
     (Lg-ι n (up c) (Lg-up c (lgB⊲ e (proj₁ (lw n)) (proj₂ (lw n))))))

Λs : HB SLs
Λs = hl (λ n → hs hz ⊞ tws n)

ΛF : HB (step SLs)
ΛF = up Λs

lΛF : LgB ΛF
lΛF = Lg-up Λs ((λ n → ⊞-⊲ (hs hz) (tws-st n)) , (λ n → Lg-⊞ (hs hz) (tws n) tt (Lg-tws n)))

oneF : ∀ {w} → hs hz ⊲[ w ] ΛF
oneF = hlim 0 hself

-- 第 n 站的层是最高层的字面第一位置, 对一切世界
stage-fst : ∀ n {w} → up (hs hz ⊞ tws n) ⊲[ w ] ΛF
stage-fst n = hlim n hself
```

## §2 ℕ 下标上的点更新

```agda
upd : ∀ {P : ℕ → Set} → ((m : ℕ) → P m) → (n : ℕ) → P n → (m : ℕ) → P m
upd w zero x zero = x
upd w zero x (suc m) = w (suc m)
upd w (suc n) x zero = w zero
upd {P} w (suc n) x (suc m) = upd {λ k → P (suc k)} (λ k → w (suc k)) n x m

upd-R : ∀ {P : ℕ → Set} (R : ∀ m → P m → P m → Set) (w : (m : ℕ) → P m) n (x : P n) →
        (∀ m → R m (w m) (w m)) → R n (w n) x → ∀ m → R m (w m) (upd {P} w n x m)
upd-R R w zero x rf r zero = r
upd-R R w zero x rf r (suc m) = rf (suc m)
upd-R R w (suc n) x rf r zero = rf zero
upd-R {P} R w (suc n) x rf r (suc m) =
  upd-R {λ k → P (suc k)} (λ k → R (suc k)) (λ k → w (suc k)) n x (λ k → rf (suc k)) r m

upd-Q : ∀ {P : ℕ → Set} (Q : ∀ m → P m → Set) (w : (m : ℕ) → P m) n (x : P n) →
        (∀ m → Q m (w m)) → Q n x → ∀ m → Q m (upd {P} w n x m)
upd-Q Q w zero x qw qx zero = qx
upd-Q Q w zero x qw qx (suc m) = qw (suc m)
upd-Q Q w (suc n) x qw qx zero = qw zero
upd-Q {P} Q w (suc n) x qw qx (suc m) =
  upd-Q {λ k → P (suc k)} (λ k → Q (suc k)) (λ k → w (suc k)) n x (λ k → qw (suc k)) qx m

upd-at : ∀ {P : ℕ → Set} (w : (m : ℕ) → P m) n (x : P n) → upd {P} w n x n ≡ x
upd-at w zero x = refl
upd-at {P} w (suc n) x = upd-at {λ k → P (suc k)} (λ k → w (suc k)) n x

upd-keep : ∀ {P : ℕ → Set} (w : (m : ℕ) → P m) n (x : P n) m → ¬ (n ≡ m) → upd {P} w n x m ≡ w m
upd-keep w zero x zero ne = ⊥-elim (ne refl)
upd-keep w zero x (suc m) ne = refl
upd-keep w (suc n) x zero ne = refl
upd-keep {P} w (suc n) x (suc m) ne = upd-keep {λ k → P (suc k)} (λ k → w (suc k)) n x m (λ e → ne (cong suc e))
```

## §3 一个站的头: 只有一个成员的 `Up`

升第 $n$ 站的头: 把第 $n$ 站世界的第二分量 $\beta$ 换成 $\beta\boxplus\delta$.

```agda
WS : Set
WS = Wd SLs

bumpH : ∀ n → HB (Lv (st n)) → WS → WS
bumpH n δ w = upd {λ m → Wd (FS m)} w n (proj₁ (w n) , proj₂ (w n) ⊞ δ)

headUp : ∀ n → Up SLs (Lv (st n))
headUp n = record
  { J = ⊤ ; κJ = λ _ → νS n ; co = λ _ e → e
  ; rz = bumpH n
  ; rz≤ = λ δ w → upd-R {λ m → Wd (FS m)} (λ m → _≤w_ (FS m)) w n _ (λ m → ≤w-rf (FS m)) (≤w-rf (Lv (st n)) , ⊞-fst _ δ)
  ; rzLg = λ {δ} {w} lδ lw → upd-Q {λ m → Wd (FS m)} (λ m → LgW (FS m)) w n _ lw (proj₁ (lw n) , Lg-⊞ _ δ (proj₂ (lw n)) lδ)
  ; rz-top = λ _ δ w → cong proj₂ (upd-at {λ m → Wd (FS m)} w n (proj₁ (w n) , proj₂ (w n) ⊞ δ)) }

-- 升第 n 站的头, 别的站原样 (ℕ 上的 "留别份")
head-keep : ∀ n δ (w : WS) m → ¬ (n ≡ m) → bumpH n δ w m ≡ w m
head-keep n δ w m ne = upd-keep {λ k → Wd (FS k)} w n _ m ne
```
