# 改 "在上" 的折法, 否定一路 (四): 接口有一个折出 1 的实例 (盲定理)

> 不含记号. 入口 [NegFold1](NegFold1.lagda.md). 导入接口 [Fold1If](Fold1If.lagda.md), [CRwBase](CRwBase.lagda.md), [NegFold1Base](NegFold1Base.lagda.md), [NegFold1If](NegFold1If.lagda.md) (`Clauses`). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **定理 `Ibl` (接口的一个实例).** 折叠在 $\Omega$-结点处**不坍缩**, 只取最小坐标处的分支: $\Phi(\Omega\{g\})=\Phi(g\,\bot)$; 零, 后继, ℕ-极限三个子句照接口. 输入一侧的世界 `Win` 把每一层新种类的界都取作 $0$, 所以第一位置只经过坐标 $0$ 处的分支 (`zbd`), 单调对一切输入成立 (`Pick.mono`, 不读合法); 合法 `Lg` 取 "ℕ-极限在 `Win` 里步进, $\Omega$-结点只看坐标 $\bot$ 处的分支". 接口的十二个字段全部满足.
>
> **盲 (`Ibl-Ω₁`, `refl`).** 这个实例把第 $1$ 层的地板 $\Omega_1$ 折到第 $0$ 层得 $1$. 所以接口的律 (含 `Φ-lg`, `Φ-mono`, `Φ-≤`, `Φ-l11`) 不推出任何强度: 强度只能由实例自己的值定理给出. 两处具体的盲: (a) `Win` 由实例选, 界取 $0$ 时 `Φ-mono` 只说坐标 $0$ 处的分支; (b) `Lg` 由实例选, 可以只看一个分支.
>
> **对 [NegFold1If](NegFold1If.lagda.md) 的意义.** 那里 `no-val-ext`, `Lg-not-total`, `Φ-indep` 是 "对一切实例" 的定理; `Ibl` 说明实例存在, 它们不是空真的.
>
> **只否定什么.** 只否定: "接口的律推出强度" (或推出 $\Omega$-结点被坍缩). **不否定**: 构造一路的实例的强度 (由它自己的值定理决定); 接口本身的合理性 (律都成立, 只是弱).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegFold1Blind where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If
open import OCF.Lean.NegFold1Base
open import OCF.Lean.NegFold1If using (module Clauses)
```

## §1 只取最小坐标的折叠, 对一切种类结构

`LgZ w h`: ℕ-极限在世界 $w$ 里步进, $\Omega$-结点只看坐标 $\bot$ 处的分支.

```agda
module _ {S : KS} (w : Wd S) where
  LgZ : HB S → Set
  LgZ hz = ⊤
  LgZ (hs h) = LgZ h
  LgZ (hl f) = (∀ n → f n ⊲[ w ] f (suc n)) × (∀ n → LgZ (f n))
  LgZ (hΩ κ g) = LgZ (g (bot S κ))

  LgZ-⊞ : ∀ a b → LgZ a → LgZ b → LgZ (a ⊞ b)
  LgZ-⊞ a hz la lb = la
  LgZ-⊞ a (hs b) la lb = LgZ-⊞ a b la lb
  LgZ-⊞ a (hl f) la (st , l) = (λ n → ⊞-⊲ a (st n)) , (λ n → LgZ-⊞ a (f n) la (l n))
  LgZ-⊞ a (hΩ κ g) la lb = LgZ-⊞ a (g (bot S κ)) la lb

  LgZ-mul : ∀ x → LgZ x → ∀ n → LgZ (mul x n)
  LgZ-mul x l zero = l
  LgZ-mul x l (suc n) = LgZ-⊞ (mul x n) x (LgZ-mul x l n) l

module Pick {S S′ : KS} (w : Wd S) (zb : ∀ {κ c} → Bd S κ c w → c ≡ bot S κ) where
  F : HB S → HB S′
  F hz = hs hz
  F (hs h) = hl (mul (F h))
  F (hl f) = hl (λ n → F (f n))
  F (hΩ κ g) = F (g (bot S κ))

  mono : ∀ {a c} {w′ : Wd S′} → a ⊲[ w ] c → F a ⊲[ w′ ] F c
  mono hself = hself
  mono (hsuc p) = ⊲ᴮ-tr (mono p) (hlim 0 hself)
  mono (hlim n p) = hlim n (mono p)
  mono {a} {w′ = w′} (hLim {κ = κ} {g = g} e p) = subst (λ z → F a ⊲[ w′ ] F (g z)) (zb e) (mono p)

  F-lg : ∀ (w′ : Wd S′) h → LgZ w h → LgZ w′ (F h)
  F-lg w′ hz l = tt
  F-lg w′ (hs h) l = (λ n → ⊞-fst (mul (F h) n) (F h)) , LgZ-mul w′ (F h) (F-lg w′ h l)
  F-lg w′ (hl f) (st , l) = (λ n → mono (st n)) , (λ n → F-lg w′ (f n) (l n))
  F-lg w′ (hΩ κ g) l = F-lg w′ (g (bot S κ)) l
```

## §2 世界: 每层新种类的界取 $0$

```agda
Win₀ : ∀ m → Wd (Lv m)
Win₀ hz = tt
Win₀ (hs x) = Win₀ x , hz
Win₀ (hl f) = λ n → Win₀ (f n)
Win₀ (hΩ () _)

zbd : ∀ m {κ c} → Bd (Lv m) κ c (Win₀ m) → c ≡ bot (Lv m) κ
zbd hz {κ = ()}
zbd (hs x) {κ = inj₁ κ} e = zbd x e
zbd (hs x) {κ = inj₂ _} hself = refl
zbd (hl f) {κ = n , κ} e = zbd (f n) e
zbd (hΩ () _)

ι-⊲ : ∀ {F : ℕ → KS} {n} {a b : HB (F n)} {w : Wd (sup ℕ F)} → a ⊲[ w n ] b → ι {F = F} n a ⊲[ w ] ι n b
ι-⊲ hself = hself
ι-⊲ (hsuc p) = hsuc (ι-⊲ p)
ι-⊲ (hlim n p) = hlim n (ι-⊲ p)
ι-⊲ (hLim e p) = hLim e (ι-⊲ p)

LgZ-ι : ∀ {F : ℕ → KS} {w : Wd (sup ℕ F)} n (x : HB (F n)) → LgZ {S = F n} (w n) x → LgZ {S = sup ℕ F} w (ι {F = F} n x)
LgZ-ι n hz l = tt
LgZ-ι n (hs x) l = LgZ-ι n x l
LgZ-ι n (hl f) (st , l) = (λ k → ι-⊲ (st k)) , (λ k → LgZ-ι n (f k) (l k))
LgZ-ι {F} n (hΩ κ g) l = LgZ-ι n (g (bot (F n) κ)) l

lg-top₀ : ∀ m → LgZ (Win₀ m) (top m)
lg-ΣT : ∀ f n → LgZ (Win₀ (hl f)) (ΣT S⊥ hz f n)
lg-top₀ hz = tt
lg-top₀ (hs x) = tt
lg-top₀ (hl f) = (λ n → ⊞-fst (ΣT S⊥ hz f n) (ι {F = λ k → Lv (f k)} (suc n) (topT S⊥ hz (f (suc n))))) , lg-ΣT f
lg-top₀ (hΩ () _)
lg-ΣT f zero = LgZ-ι {F = λ k → Lv (f k)} 0 (top (f 0)) (lg-top₀ (f 0))
lg-ΣT f (suc n) = LgZ-⊞ (Win₀ (hl f)) (ΣT S⊥ hz f n) (ι {F = λ k → Lv (f k)} (suc n) (top (f (suc n)))) (lg-ΣT f n) (LgZ-ι {F = λ k → Lv (f k)} (suc n) (top (f (suc n))) (lg-top₀ (f (suc n))))

lg₀Z : ∀ (h : Cd) → LgZ tt h → LgB h
lg₀Z hz l = tt
lg₀Z (hs h) l = lg₀Z h l
lg₀Z (hl f) (st , l) = (λ n → st n) , (λ n → lg₀Z (f n) (l n))
lg₀Z (hΩ () _) l
```

## §3 实例

```agda
ΦZ : (m : Cd) → LgB m → (t : Cd) → t ⊲ m → HB (Lv t) → HB (Lv m) → HB (Lv t)
ΦZ m lm t pt b = Pick.F {S = Lv m} {S′ = Lv t} (Win₀ m) (zbd m)

Ibl : Fold1If
Ibl = record
  { Φ = ΦZ
  ; Φ-z = λ m lm t pt b → refl
  ; Φ-s = λ m lm t pt b h → refl
  ; Φ-pt = λ m lm t pt b f → refl
  ; Lg = λ m → LgZ (Win₀ m)
  ; lg₀ = lg₀Z
  ; lg-top = λ m lm → lg-top₀ m
  ; Φ-lg = λ m lm t pt b lb h l → Pick.F-lg (Win₀ m) (zbd m) (Win₀ t) h l
  ; Win = λ m lm b → Win₀ m
  ; Φ-mono = λ m lm pt lb lc p → Pick.mono (Win₀ m) (zbd m) p
  ; Φ-≤ = λ m lm t pt b → Clauses.F-≤ (ΦZ m lm t pt b) refl (λ h → refl) (λ f → refl)
  ; Φ-l11 = λ m lm t pt b → Clauses.F-l11 (ΦZ m lm t pt b) refl (λ h → refl) (λ f → refl)
  }
```

**盲.** 第 $1$ 层的地板 $\Omega_1$ 折到第 $0$ 层得 $1$; 第 $2$ 层的地板 $\Omega_2$ 也得 $1$.

```agda
Ibl-Ω₁ : Fold1If.Φ Ibl (hs hz) tt hz (hsuc hself) hz (top (hs hz)) ≡ hs hz
Ibl-Ω₁ = refl

Ibl-Ω₂ : Fold1If.Φ Ibl (hs (hs hz)) tt hz (hsuc (hsuc hself)) hz (top (hs (hs hz))) ≡ hs hz
Ibl-Ω₂ = refl
```

## 结论 (按档)

- **[定理]** `LgZ`, `LgZ-⊞`, `LgZ-mul`; `Pick.F`, **`Pick.mono`** (对一切输入, 不读合法), `Pick.F-lg`; `Win₀`, `zbd`, `ι-⊲`, `LgZ-ι`, `lg-top₀`, `lg₀Z`; **`Ibl : Fold1If`**; **`Ibl-Ω₁`**, `Ibl-Ω₂` (`refl`).
- **[判断]** 接口要说强度, 至少要约束 `Win` (界不能取 $0$, 例如要求界是合法世界里的界) 并加一条关于 $\Omega$-结点的值的律 (带界). 这是建议, 不是定理.
