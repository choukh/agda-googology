# NegSameV (四): 对接口 `LvMor`: 分量 0 被保持, 本身不会碰到拷贝; $\omega_1+1\to\omega_2+1$ 的实例

> 不含记号. 入口 [NegSameV](NegSameV.lagda.md). 对构造一路 SameV 的接口 [SameVIf](SameVIf.lagda.md) (定稿 2026-11-06 21:03, 本路不改它). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **问题 (构造一路的请求 (2)).** `NegValXSelf.self≰copy` 说 $\Omega_1$ 本身 (分量 $0$, 回灌并移动世界) 不能比成拷贝 (分量 $c\ne0$, 不动世界). 跨分量比较沿层号搬运 $c\mapsto\mathrm{im}\,c$ 时, 会不会把分量 $0$ 与分量 $c\neq0$ 配上.
>
> **定理.**
>
> 1. **`im-nz`, `im-zero-iff`.** 对一切 `M : LvMor m m′`, 一切位置 $c\lhd m$: $\mathrm{im}\,c=0$ 当且仅当 $c=0$ (字面). 所以沿 `M` 比较的分量, 分量 $0$ 只配分量 $0$: **本身只配本身, 拷贝只配拷贝** (`self-safe`), `self≰copy` 不被触发. 这是对请求 (2) 的回答; 是正面结果.
> 2. **`M₁₂`.** $\omega_1+1\to\omega_2+1$ 上有满足接口全部律的搬运 (位置按树的形状读, 协调是 `refl`). 这是 `floor-block` 那一对层号的实例, 说明接口的 `LvMor` 在这一对上可满足.
>
> **前提实例.** 1: 一切 `M`, 例如 `M₁₂`.
>
> **只否定什么.** 1 没有否定任何东西, 只说明 `self≰copy` 不挡沿 `LvMor` 的比较; 它不说 `Ω≤Ω` 的跨分量版本已成立. 2 只给一对层号的实例, 不说一般的 `LeAt` 推导能造出协调的搬运.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegSameVMor where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (I₁)
open import OCF.Lean.CRwFold I₁
open import OCF.Lean.ValCRel I₁
open import OCF.Lean.SameVIf
open import OCF.Lean.NegSameVSpine using (nat; ω₁; ω₂; Lg-ω₁)
```

## §1 分量 0

位置 $c\ne0$ 时 $0$ 真包含于 $c$ (`Pp hz c`).

```agda
pp-z : ∀ c → ¬ (c ≡ hz) → Pp hz c
pp-z hz ne = ⊥-elim (ne refl)
pp-z (hs c) ne = pps (z⊲ᴮ c)
pp-z (hl f) ne = ppl 0 (z⊲ᴮ (f 0))
pp-z (hΩ () _) ne

no-pp-z : ∀ {a} → ¬ Pp a hz
no-pp-z ()

module _ {m m′ : Cd} (M : LvMor m m′) where
  im-nz : ∀ {c} (q : c ⊲ m) → ¬ (c ≡ hz) → ¬ (im M q ≡ hz)
  im-nz {c} q ne e = no-pp-z (subst (Pp (im M (z⊲ᴮ m))) e
    (im-pp M (z⊲ᴮ m) q (pp-z c ne)))

  -- 左边: 像是 0 ⟹ 坐标是 0 的 Pp 里, `im (z⊲ᴮ m)` 是 0
  im-zero-iff : ∀ {c} (q : c ⊲ m) → ((c ≡ hz) → im M q ≡ hz) × (im M q ≡ hz → ¬ ¬ (c ≡ hz))
  im-zero-iff {c} q = (λ e → lem c q e) , (λ e ne → im-nz q ne e)
    where
    lem : ∀ c (q : c ⊲ m) → c ≡ hz → im M q ≡ hz
    lem .hz q refl = im-z M q

  self-safe : ∀ {c} (q : c ⊲ m) → (c ≡ hz → im M q ≡ hz) × (¬ (c ≡ hz) → ¬ (im M q ≡ hz))
  self-safe q = proj₁ (im-zero-iff q) , im-nz q
```

## §2 一个非平凡的搬运: $\omega_1+1\to\omega_2+1$

`f` 按树的形状读: 有限树不动, ℕ-极限送到 $\omega_2$. 像只看位置, 不看证明, 所以协调 (`im-irr`) 是 `refl`.

```agda
f : Cd → Cd
f hz = hz
f (hs x) = hs (f x)
f (hl _) = ω₂
f (hΩ () _)

data Fn : Cd → Set where
  fz : Fn hz
  fs : ∀ {x} → Fn x → Fn (hs x)

fn-nat : ∀ n → Fn (nat n)
fn-nat zero = fz
fn-nat (suc n) = fs (fn-nat n)

fn⊲ : ∀ {a b} → Fn b → a ⊲ b → Fn a
fn⊲ fb hself = fb
fn⊲ (fs fb) (hsuc p) = fn⊲ fb p

f-fin : ∀ {x} → Fn x → f x ≡ x
f-fin fz = refl
f-fin (fs fx) = cong hs (f-fin fx)

-- 有限树都在 ω₂ 的某一项之下
fin⊲n : ∀ {x} → Fn x → Σ ℕ (λ k → x ⊲ nat (suc k))
fin⊲n fz = 0 , hsuc hself
fin⊲n {hs x} (fs fx) with fin⊲n fx
... | k , q = suc k , up⊲ k q
  where
  up⊲ : ∀ {y} n → y ⊲ nat (suc n) → hs y ⊲ nat (suc (suc n))
  up⊲ n hself = hself
  up⊲ zero (hsuc hself) = hsuc hself
  up⊲ (suc n) (hsuc q) = hsuc (up⊲ n q)

f⊲n : ∀ {x} → Fn x → Σ ℕ (λ k → f x ⊲ nat (suc k))
f⊲n {x} fx = proj₁ (fin⊲n fx) , subst (λ z → z ⊲ nat (suc (proj₁ (fin⊲n fx)))) (sym (f-fin fx)) (proj₂ (fin⊲n fx))

f⊲ω : ∀ {x} → Fn x → f x ⊲ ω₂
f⊲ω fx = hlim (proj₁ (f⊲n fx)) (proj₂ (f⊲n fx))

f⊲fin : ∀ {t u} → Fn u → t ⊲ u → f t ⊲ f u
f⊲fin fu hself = hself
f⊲fin (fs fu) (hsuc p) = hsuc (f⊲fin fu p)

m₁ m₂ : Cd
m₁ = hs ω₁
m₂ = hs ω₂

data Pos : Cd → Set where
  pT : Pos m₁
  pL : Pos ω₁
  pF : ∀ {t} → Fn t → Pos t

cls : ∀ {t} → t ⊲ m₁ → Pos t
cls hself = pT
cls (hsuc hself) = pL
cls (hsuc (hlim n r)) = pF (fn⊲ (fn-nat n) r)

noL : ¬ Fn ω₁
noL ()

noT : ¬ Fn m₁
noT (fs ())

im⊲₁ : ∀ {t} → Pos t → f t ⊲ m₂
im⊲₁ pT = hself
im⊲₁ pL = hsuc hself
im⊲₁ (pF ft) = hsuc (f⊲ω ft)

mon : ∀ {t u} → Pos t → Pos u → t ⊲ u → f t ⊲ f u
mon pT pT p = hself
mon pT pL p = ⊥-elim (nos p)
mon pT (pF fu) p = ⊥-elim (noT (fn⊲ fu p))
mon pL pT p = hsuc hself
mon pL pL p = hself
mon pL (pF fu) p = ⊥-elim (noL (fn⊲ fu p))
mon (pF ft) pT p = hsuc (f⊲ω ft)
mon (pF ft) pL p = f⊲ω ft
mon (pF ft) (pF fu) p = f⊲fin fu p

ppm : ∀ {t u} → Pos t → Pos u → Pp t u → Pp (f t) (f u)
ppm pT pT (pps q) = ⊥-elim (nos q)
ppm pL pT (pps q) = pps hself
ppm (pF ft) pT (pps q) = pps (f⊲ω ft)
ppm pT pL (ppl n q) = ⊥-elim (noT (fn⊲ (fn-nat n) q))
ppm pL pL (ppl n q) = ⊥-elim (noL (fn⊲ (fn-nat n) q))
ppm (pF ft) pL (ppl n q) = ppl (proj₁ (f⊲n ft)) (proj₂ (f⊲n ft))
ppm pT (pF (fs fu)) (pps q) = ⊥-elim (noT (fn⊲ fu q))
ppm pL (pF (fs fu)) (pps q) = ⊥-elim (noL (fn⊲ fu q))
ppm (pF ft) (pF (fs fu)) (pps q) = pps (f⊲fin fu q)

lem₁₂ : LeAt hz ω₁ ω₂
lem₁₂ = Rel.l≤l (λ n → n) (L.idInc hz) (λ n → Rel.≤s (L.≤-refl hz (nat n)))

lef : ∀ {t} → Pos t → LeAt hz t (f t)
lef pT = Rel.s≤s lem₁₂
lef pL = lem₁₂
lef {t} (pF ft) = subst (λ z → LeAt hz t z) (sym (f-fin ft)) (L.≤-refl hz t)

M₁₂ : LvMor m₁ m₂
M₁₂ = record
  { im = λ {t} _ → f t
  ; im⊲ = λ q → im⊲₁ (cls q)
  ; im-irr = λ q q′ → refl
  ; im-z = λ q → refl
  ; im-⊲ = λ q r p → mon (cls q) (cls r) p
  ; im-s = λ q r p → mon (cls (⊲ᴮ-tr p r)) (cls r) p
  ; im-pp = λ q r p → ppm (cls q) (cls r) p
  ; im-le = λ q → lef (cls q) }

im-top : im M₁₂ hself ≡ m₂
im-top = refl

im-ω : im M₁₂ (hsuc hself) ≡ ω₂
im-ω = refl
```

## 结论 (按档)

- **[定理, 不用 UIP]** `pp-z`, **`im-nz`**, `im-zero-iff`, **`self-safe`**; `M₁₂` ($\omega_1+1\to\omega_2+1$ 的搬运, 接口的全部律), `im-top`, `im-ω`, `cls`, `mon`, `ppm`, `lef`.
- **[判断]** 由 `self-safe`, 沿 `LvMor` 的跨分量比较不会把本身配到拷贝.
