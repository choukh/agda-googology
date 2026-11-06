# X₁ 上叠层, 否定一路 (七): `leg` 对字面第一位置不单调

> 不含记号. 入口 [NegX1Up](NegX1Up.lagda.md). 对 PathOut 的实例 [PathOutX1](PathOutX1.lagda.md) 的 `leg` (只读导入) 写. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **问题.** 接口 [X1UpIf](X1UpIf.lagda.md) 文首的判断: "实例的 `shift` ($B\boxplus\mathrm{leg}\,c$) 对坐标的字面第一位置不单调 (`leg` 取部分和), 所以 'shift 单调' 一类的律实例满足不了; 未编译反例, 只是判断." 本篇把 `leg` 那一半写成定理.
>
> **结果.**
>
> 1. **`leg-not-mono` (定理).** 坐标 $c=\lim(1,1,\dots)$, $c'=\lim(1, c, c, \dots)$, 都合法 (`Lg-c₁`, `Lg-c′`), $c\lhd c'$ (`c⊲c′`), 但 $\mathrm{leg}\,c\not\lhd\mathrm{leg}\,c'$ (任一世界). 原因同 `NegTySupMono.Φ-not-mono`: $\mathrm{leg}\,c=\lim(1,2,3,\dots)$ (记作 $\hat\omega$), $\mathrm{leg}\,c'=\lim(1,\ 1\boxplus\hat\omega,\ 1\boxplus\hat\omega\boxplus\hat\omega,\dots)$, $\hat\omega$ 不是任何部分和的字面第一位置.
>
> **前提实例.** $c$, $c'$ 合法, $c\lhd c'$, 都在本篇给出.
>
> **只否定什么.** 只否定 "`leg` 保字面第一位置". **不否定**: `shift` $=B\boxplus\mathrm{leg}$ 在合法世界 $B$ 上的单调 (要 "$B\boxplus x\lhd B\boxplus y\Rightarrow x\lhd y$" 一类的消去, 本篇没写; 判断: 同样不单调); `leg` 保值 (没有值的定理); `adm-shift` 与 `Lg-leg` (构造一路的定理). 接口本身不要求 `shift` 单调, 本篇不否定接口. 本篇没有关闭任何路线.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegX1UpLeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy using (S⊥)
open import OCF.Align.TySupC using (Cd)
open import OCF.Align.PathOutX1 using (leg; Σ₀)
```

## §1 $\hat\omega$ 不在部分和下面

```agda
one : Cd
one = hs hz

c₁ : Cd
c₁ = hl (λ _ → one)

ω̂ : Cd
ω̂ = hl (Σ₀ (λ _ → one))

leg-c₁ : leg c₁ ≡ ω̂
leg-c₁ = refl

at : Cd → ℕ → Cd
at (hl f) n = f n
at x n = x

hs-inj : ∀ {x y : Cd} → hs x ≡ hs y → x ≡ y
hs-inj refl = refl

-- Y ⊞ Σ₀ (λ _ → one) k = hs^(k+1) Y
strip : ∀ {w} k {Y : Cd} → ω̂ ⊲[ w ] Y ⊞ Σ₀ (λ _ → one) k → ω̂ ⊲[ w ] Y
strip zero (hsuc p) = p
strip (suc k) (hsuc p) = strip k p

key : ∀ {w a b} (Y : Cd) → a ⊲[ w ] b → a ≡ ω̂ → b ≡ Y ⊞ ω̂ → ¬ (Y ≡ hz) → ¬ (ω̂ ⊲[ w ] Y) → ⊥
key Y hself ea eb nz nY = nz (sym (hs-inj (cong (λ h → at h 0) (trans (sym ea) eb))))
key Y (hsuc p) ea ()
key {w} {a} Y (hlim n p) ea eb nz nY =
  nY (strip n (subst (λ z → z ⊲[ w ] Y ⊞ Σ₀ (λ _ → one) n) ea (subst (λ z → a ⊲[ w ] z) (cong (λ h → at h n) eb) p)))
key Y (hLim {κ = ()} e p) ea eb
```

## §2 坐标与反例

```agda
f′ : ℕ → Cd
f′ zero = one
f′ (suc _) = c₁

c′ : Cd
c′ = hl f′

Lg-c₁ : LgB c₁
Lg-c₁ = (λ _ → hself) , (λ _ → tt)

Lg-c′ : LgB c′
Lg-c′ = st , lg
  where
  st : ∀ {w} n → f′ n ⊲[ w ] f′ (suc n)
  st zero = hlim 0 hself
  st (suc n) = hself
  lg : ∀ n → LgB (f′ n)
  lg zero = tt
  lg (suc n) = Lg-c₁

c⊲c′ : ∀ {w} → c₁ ⊲[ w ] c′
c⊲c′ = hlim 1 hself

G : ℕ → Cd
G = Σ₀ (λ m → leg (f′ m))

no-hz : ∀ {w} → ¬ (ω̂ ⊲[ w ] hz)
no-hz ()

s≢z : ∀ {x : Cd} → ¬ (hs x ≡ hz)
s≢z ()

l≢z : ∀ {f : ℕ → Cd} → ¬ (hl f ≡ hz)
l≢z ()

nzG : ∀ m → ¬ (G m ≡ hz)
nzG zero = s≢z
nzG (suc m) = l≢z

notG : ∀ {w} m → ¬ (ω̂ ⊲[ w ] G m)
notG zero p = no-hz (strip 0 {hz} p)
notG (suc m) p = key (G m) p refl refl (nzG m) (notG m)

leg-not-mono : ∀ {w} → ¬ (leg c₁ ⊲[ w ] leg c′)
leg-not-mono {w} p = go p refl refl
  where
  s≢l : ∀ {x : Cd} {f : ℕ → Cd} → ¬ (hs x ≡ hl f)
  s≢l ()
  go : ∀ {a b} → a ⊲[ w ] b → a ≡ ω̂ → b ≡ hl G → ⊥
  go hself ea eb = s≢l (cong (λ h → at h 1) (trans (sym ea) eb))
  go (hsuc p) ea ()
  go {a} (hlim n p) ea eb = notG n (subst (λ z → z ⊲[ w ] G n) ea (subst (λ z → a ⊲[ w ] z) (cong (λ h → at h n) eb) p))
  go (hLim {κ = ()} e p) ea eb
```

## 结论 (按档)

- **[定理]** `leg-c₁`, `strip`, `key`, `Lg-c₁`, **`Lg-c′`**, **`c⊲c′`**, `notG`, **`leg-not-mono`**.
- **[判断]** `shift` 在合法世界上同样不单调 (要消去引理, 未写).
