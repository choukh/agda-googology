# 可数层的对角 (二): 有限级里按位置存界

> 不含记号. 入口 [DiagK](DiagK.lagda.md). 有限级 `Sn k = stepᵏ S₀` ([HtTowerU](HtTowerU.lagda.md)): 种类是 $k+1$ 个位置, 世界是嵌套的对 $(((A\times H_0)\times H_1)\cdots)$. 协调者转来的两个陷阱在这里都不出现, 都是定理:
>
> 1. **改一层不要判定** (对照 `CohWUpd.upd→wdec`): 每个种类的界是世界里一个存着的值 (`bnd`), 界关系就是 "坐标是这个值的第一位置" (`bd≡pr`, `refl` 的递归). 改一个种类的界、其余不动 (`upd`, 律 `at`, `off`) 对位置结构递归写出, `off` 的证明不看 $\kappa\ne\kappa'$ 以外的任何东西. 种类相等本身可判定 (`decK`). `upd` 在界变大时是世界的变大 (`upd-≤`), 保合法 (`lg-upd`).
> 2. **没有拷贝** (对照 `CohWNeg.no-cross`): 种类由读回位置 `rl` 唯一决定 (`rl-inj`); 低级嵌进高级 (`kmS`, 投影 `proj₁`) 在任意多级上界定义相等 (`wmS`, 一条对级差 $d$ 的递归), 且同一位置的界就是同一个分量 (`bnd-up`, 坐标经 `to`, 每级是恒等), 读回位置不变 (`rl-up`).
>
> **范围.** 只对 `Sn` 这样的有限级 (种类有限多, 按位置); 对含 `Lev` 的级见 [DiagKLev](DiagKLev.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.DiagKPos where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n)
open import Data.Nat.Properties using (m≤n⇒m≤1+n; ≤-refl; 1+n≰n)
open import Data.Empty using (⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerU using (Sn)
open import OCF.Align.HtTowerFNeed using (KMatch; km; to; fr; fr-to)
open import OCF.Align.HtTowerNStage using (kmComp; WMatch; wm; bd→; bd←; lgw)
```

## §1 界是存着的值

```agda
Kn : ℕ → Set
Kn k = K (Sn k)

-- 读回位置: 底种类在 0, 第 j 级的新种类在 j
rl : ∀ k → Kn k → ℕ
rl zero tt = zero
rl (suc k) (inj₁ κ) = rl k κ
rl (suc k) (inj₂ tt) = suc k

bnd : ∀ k (κ : Kn k) → Wd (Sn k) → E (Sn k) κ
bnd zero tt w = w
bnd (suc k) (inj₁ κ) (w , b) = bnd k κ w
bnd (suc k) (inj₂ tt) (w , b) = b

bd≡pr : ∀ k (κ : Kn k) c w → Bd (Sn k) κ c w ≡ Pr (Sn k) κ w c (bnd k κ w)
bd≡pr zero tt c w = refl
bd≡pr (suc k) (inj₁ κ) c (w , b) = bd≡pr k κ c w
bd≡pr (suc k) (inj₂ tt) c (w , b) = refl
```

## §2 改一个种类的界

```agda
upd : ∀ k (κ : Kn k) → E (Sn k) κ → Wd (Sn k) → Wd (Sn k)
upd zero tt c w = c
upd (suc k) (inj₁ κ) c (w , b) = upd k κ c w , b
upd (suc k) (inj₂ tt) c (w , b) = w , c

at : ∀ k (κ : Kn k) c w → bnd k κ (upd k κ c w) ≡ c
at zero tt c w = refl
at (suc k) (inj₁ κ) c (w , b) = at k κ c w
at (suc k) (inj₂ tt) c (w , b) = refl

inj₁-inj : ∀ {X Y : Set} {a b : X} → _≡_ {A = X ⊎ Y} (inj₁ a) (inj₁ b) → a ≡ b
inj₁-inj refl = refl

off : ∀ k (κ κ′ : Kn k) c w → ¬ (κ ≡ κ′) → bnd k κ′ (upd k κ c w) ≡ bnd k κ′ w
off zero tt tt c w ne with ne refl
... | ()
off (suc k) (inj₁ κ) (inj₁ κ′) c (w , b) ne = off k κ κ′ c w (λ e → ne (cong inj₁ e))
off (suc k) (inj₁ κ) (inj₂ tt) c (w , b) ne = refl
off (suc k) (inj₂ tt) (inj₁ κ′) c (w , b) ne = refl
off (suc k) (inj₂ tt) (inj₂ tt) c (w , b) ne with ne refl
... | ()

decK : ∀ k (κ κ′ : Kn k) → Dec (κ ≡ κ′)
decK zero tt tt = yes refl
decK (suc k) (inj₁ κ) (inj₁ κ′) with decK k κ κ′
... | yes refl = yes refl
... | no ne = no (λ e → ne (inj₁-inj e))
decK (suc k) (inj₁ κ) (inj₂ tt) = no (λ ())
decK (suc k) (inj₂ tt) (inj₁ κ′) = no (λ ())
decK (suc k) (inj₂ tt) (inj₂ tt) = yes refl
```

**`upd` 是世界的变大.** 新界在旧界之上 (旧界是新界的第一位置) 时, 改后的世界在原世界之上; 坐标合法时保合法.

```agda
upd-≤ : ∀ k (κ : Kn k) c w → Pr (Sn k) κ w (bnd k κ w) c → _≤w_ (Sn k) w (upd k κ c w)
upd-≤ zero tt c w p = p
upd-≤ (suc k) (inj₁ κ) c (w , b) p = upd-≤ k κ c w p , hself
upd-≤ (suc k) (inj₂ tt) c (w , b) p = ≤w-rf (Sn k) , p

lg-upd : ∀ k (κ : Kn k) c w → LgW (Sn k) w → LgE (Sn k) κ c → LgW (Sn k) (upd k κ c w)
lg-upd zero tt c w lw lc = lc
lg-upd (suc k) (inj₁ κ) c (w , b) (lw , lb) lc = lg-upd k κ c w lw lc , lb
lg-upd (suc k) (inj₂ tt) c (w , b) (lw , lb) lc = lw , lc
```

## §3 没有拷贝

每个读回位置恰有一个种类 (`rl-inj`).

```agda
rl-bd : ∀ k (κ : Kn k) → rl k κ ≤ k
rl-bd zero tt = z≤n
rl-bd (suc k) (inj₁ κ) = m≤n⇒m≤1+n (rl-bd k κ)
rl-bd (suc k) (inj₂ tt) = ≤-refl

rl-inj : ∀ k (κ κ′ : Kn k) → rl k κ ≡ rl k κ′ → κ ≡ κ′
rl-inj zero tt tt e = refl
rl-inj (suc k) (inj₁ κ) (inj₁ κ′) e = cong inj₁ (rl-inj k κ κ′ e)
rl-inj (suc k) (inj₁ κ) (inj₂ tt) e = ⊥-elim (1+n≰n (subst (λ m → m ≤ k) e (rl-bd k κ)))
rl-inj (suc k) (inj₂ tt) (inj₁ κ′) e = ⊥-elim (1+n≰n (subst (λ m → m ≤ k) (sym e) (rl-bd k κ′)))
rl-inj (suc k) (inj₂ tt) (inj₂ tt) e = refl
```

**低级嵌进高级.** 一级是 `kmStep` 与投影 `proj₁` (界定义相等); $d$ 级是它的复合. 同一个种类在高级里的界就是低级里那个分量 (`bnd-up`): 只有一条路, 一个分量.

```agda
kmId : ∀ {S} → KMatch S S
kmId = record { km = λ κ → κ ; to = λ κ c → c ; fr = λ κ c → c ; fr-to = λ κ c → refl }

kmStep′ : ∀ {S} → KMatch S (step S)
kmStep′ = record { km = inj₁ ; to = λ κ c → c ; fr = λ κ c → c ; fr-to = λ κ c → refl }

wmId : ∀ {S} → WMatch S S kmId
wmId = record { wm = λ w → w ; bd→ = λ e → e ; bd← = λ e → e ; lgw = λ l → l }

wmStep : ∀ {S} → WMatch S (step S) kmStep′
wmStep = record { wm = proj₁ ; bd→ = λ e → e ; bd← = λ e → e ; lgw = proj₁ }

wmComp : ∀ {S S′ S″} {M : KMatch S S′} {N : KMatch S′ S″} → WMatch S S′ M → WMatch S′ S″ N → WMatch S S″ (kmComp M N)
wmComp P Q = record
  { wm = λ w → wm P (wm Q w)
  ; bd→ = λ e → bd→ P (bd→ Q e)
  ; bd← = λ e → bd← Q (bd← P e)
  ; lgw = λ l → lgw P (lgw Q l) }

kmS : ∀ d k → KMatch (Sn k) (Sn (d + k))
kmS zero k = kmId
kmS (suc d) k = kmComp (kmS d k) kmStep′

wmS : ∀ d k → WMatch (Sn k) (Sn (d + k)) (kmS d k)
wmS zero k = wmId
wmS (suc d) k = wmComp (wmS d k) wmStep

bnd-up : ∀ d k (κ : Kn k) w → bnd (d + k) (km (kmS d k) κ) w ≡ to (kmS d k) κ (bnd k κ (wm (wmS d k) w))
bnd-up zero k κ w = refl
bnd-up (suc d) k κ (w , b) = bnd-up d k κ w

rl-up : ∀ d k (κ : Kn k) → rl (d + k) (km (kmS d k) κ) ≡ rl k κ
rl-up zero k κ = refl
rl-up (suc d) k κ = rl-up d k κ
```
