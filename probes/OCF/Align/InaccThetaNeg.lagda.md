# 全部 $\theta$ 的证书: 一个原始的 `S` 不能对全部层号正确

> 不含记号. 结论写在 [InaccTheta](InaccTheta.lagda.md). `no-uniform`: 如果一个判决 `S` (拿到的是原始的层号对) 对一切 `Ordᴵ` 层号的链都语义正确 (`LvT`), 就有 WLPO. 没有用函数外延性. 所以第 5 站的前提 `HE` 不能对全部世界一次性兑现. 它与 `<ᴵ-dec` 不矛盾: 每个层号自己带证据时比较是定理, 下面的反例族**不能**一致地给出证据, 只能在 "全假" 与 "第 $n$ 位真" 两种假设下分别给出. **`S` 能否对单个固定的世界 $\ell$ 正确, 没有解决.**

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.InaccThetaNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Align.InaccTreeBase using (Lv; zero; suc; lim; limᴼ; Ordᴸ; Pre; at; toLv; Verdict; pen; rise; Tree; up; Ω)
open import OCF.Align.InaccFloorTree using (Sib; natL; lt)
open import OCF.Align.InaccFloorBase using (em; ≅→⊑ᴵ)
open import OCF.Align.InaccSingularBase using (WLPO)
open import OCF.Align.InaccThetaEq using (module Eqv)
open import OCF.Align.Level using
  (Ordᴵ; _<ᴵ_; _≅ᴵ_; _⊑ᴵ_; zero; suc; lim; z≅; s≅; l≅; z⊑; s⊑; l⊑; natᴵ; natᴵ-step; ωᴵ; ≅ᴵ-refl)
```

## §1 反例族

`i s` 是极限 $0,1,\dots$; 第一个真位之后变成常值 $\omega+2$. 全假时它 $\cong^\mathsf{I}\omega$, 否则真正大于 $\omega+1$. 层 `κ s` 的第 0 项有路径到 $\omega+1$, 第 1 项有路径到 `suc (i s)`. 它的步进证据要分情况 (`tF`, `tT`), 但步进证据不进入层号: 两种证据给同一个 `κ s`.

```agda
flag : (ℕ → Bool) → ℕ → Bool
flag s zero    = s zero
flag s (suc n) = flag s n ∨ s (suc n)

ω₂ : Ordᴵ
ω₂ = suc (suc ωᴵ)

sel : Bool → ℕ → Ordᴵ
sel true  n = ω₂
sel false n = natᴵ n

nat⊑ω₂ : ∀ n → natᴵ n ⊑ᴵ ω₂
nat⊑ω₂ zero    = z⊑
nat⊑ω₂ (suc n) = s⊑ (≅ᴵ-refl _) (suc (suc (lim (suc n) zero)))

⊑-refl : ∀ a → a ⊑ᴵ a
⊑-refl a = ≅→⊑ᴵ (≅ᴵ-refl a)

sel-step : ∀ b c n → sel b n ⊑ᴵ sel (b ∨ c) (suc n)
sel-step true  c     n = ⊑-refl ω₂
sel-step false true  n = nat⊑ω₂ n
sel-step false false n = natᴵ-step n

g : (ℕ → Bool) → ℕ → Ordᴵ
g s n = sel (flag s n) n

i : (ℕ → Bool) → Ordᴵ
i s = lim (g s) (λ n → sel-step (flag s n) (s (suc n)) n)

G : (ℕ → Bool) → ℕ → Ordᴵ
G s zero    = ω₂
G s (suc n) = suc (suc (i s))

flag-false : ∀ s → (∀ n → s n ≡ false) → ∀ n → flag s n ≡ false
flag-false s h zero = h zero
flag-false s h (suc n) rewrite flag-false s h n | h (suc n) = refl

flag-true : ∀ s n → s n ≡ true → flag s n ≡ true
flag-true s zero p = p
flag-true s (suc n) p rewrite p = ∨-true (flag s n) where
  ∨-true : ∀ b → (b ∨ true) ≡ true
  ∨-true true  = refl
  ∨-true false = refl

ω≅i : ∀ s → (∀ n → s n ≡ false) → ωᴵ ≅ᴵ i s
ω≅i s h = l≅ λ n → subst (λ b → natᴵ n ≅ᴵ sel b n) (sym (flag-false s h n)) (≅ᴵ-refl _)

tail⊑ : ∀ s n → G s (suc n) ⊑ᴵ G s (suc (suc n))
tail⊑ s n = ⊑-refl _

tF : ∀ s → (∀ n → s n ≡ false) → ∀ n → G s n ⊑ᴵ G s (suc n)
tF s h zero    = s⊑ (s≅ (ω≅i s h)) zero
tF s h (suc n) = tail⊑ s n

ω₁<sel : ∀ b n → b ≡ true → suc ωᴵ <ᴵ sel b n
ω₁<sel _ n refl = zero

tT : ∀ s n → s n ≡ true → ∀ m → G s m ⊑ᴵ G s (suc m)
tT s n p zero    = s⊑ (≅ᴵ-refl _) (suc (suc (lim n (ω₁<sel (flag s n) n (flag-true s n p)))))
tT s n p (suc m) = tail⊑ s m

E : Ordᴵ → Lv
E a = toLv (em a)

κ : (ℕ → Bool) → Lv
κ s = lim (λ n → E (G s n))

_ : ∀ s h → E (lim (G s) (tF s h)) ≡ κ s
_ = λ s h → refl

_ : ∀ s n p → E (lim (G s) (tT s n p)) ≡ κ s
_ = λ s n p → refl
```

## §2 判决读出来

```agda
at-natE : ∀ n (r : Pre (E (natᴵ n))) → Σ ℕ λ m → at (E (natᴵ n)) r ≡ natL m
at-natE (suc n) (inj₁ _) = n , lem n where
  lem : ∀ n → E (natᴵ n) ≡ natL n
  lem zero    = refl
  lem (suc n) = cong Lv.suc (lem n)
at-natE (suc n) (inj₂ r) = at-natE n r

module Neg (S : Sib) (B₀ : Ordᴸ zero → Set) where
  open Eqv S B₀

  J : Lv
  J = E (suc ωᴵ)

  I : (ℕ → Bool) → Lv
  I s = E (suc (i s))

  read : ∀ s → LvT (κ s) → CV (S J (I s))
  read s w with proj₁ w (1 , inj₁ tt) tt
  ... | inj₂ (ok , _) = proj₁ ok (0 , inj₁ tt) tt

  natL≢ : ∀ m {f : ℕ → Lv} → natL m ≡ Lv.suc (Lv.lim f) → ⊥
  natL≢ zero ()
  natL≢ (suc zero) ()
  natL≢ (suc (suc m)) ()

  -- 全假: 目标里没有字面的 J
  no-pen : ∀ s → (∀ n → s n ≡ false) → ∀ (r : Pre (I s)) → at (I s) r ≡ J → ⊥
  no-pen s h (inj₁ _) ()
  no-pen s h (inj₂ (n , r)) e = go (flag s n) (flag-false s h n) r e where
    go : ∀ b → b ≡ false → (r : Pre (E (sel b n))) → at (E (sel b n)) r ≡ J → ⊥
    go _ refl r e with at-natE n r
    ... | m , e′ = natL≢ m (trans (sym e′) e)

  -- 第 n 位真: 目标里有字面的 J
  yes-path : ∀ b n → b ≡ true → Σ (Pre (E (sel b n))) λ r → AdmB (E (sel b n)) r × at (E (sel b n)) r ≈ᴮ J
  yes-path _ n refl = inj₁ tt , tt , ≈ᴮ-refl J

  dec : ∀ s (v : Verdict J (I s)) → ((∀ n → s n ≡ false) → CV v) → (∀ n → s n ≡ true → CV v) →
        (∀ n → s n ≡ false) ⊎ ((∀ n → s n ≡ false) → ⊥)
  dec s (pen r b) c₁ c₂ = inj₂ λ h → absurd h (c₁ h) where
    absurd : (∀ n → s n ≡ false) → CV (pen r b) → ⊥
    absurd h (cvp _ e _) = no-pen s h r e
  dec s rise c₁ c₂ = inj₁ λ n → go n (s n) refl where
    go : ∀ n b → s n ≡ b → s n ≡ false
    go n false p = p
    go n true  p with c₂ n p
    ... | cvr k with yes-path (flag s n) n (flag-true s n p)
    ...   | r , d , e = ⊥-elim (k (inj₂ (n , r)) d e)

  no-uniform : (∀ a → LvT (E a)) → WLPO
  no-uniform H s = dec s (S J (I s))
    (λ h → read s (H (lim (G s) (tF s h))))
    (λ n p → read s (H (lim (G s) (tT s n p))))

  no-uniformG : (∀ a → LvG (E a)) → WLPO
  no-uniformG H = no-uniform (λ a → proj₂ (H (suc a)))

  -- 下标含参数层 1 的 `limᴼ`: $\\Omega_{\\Omega_2}$ 的层号要求原始分支上全部正确
  no-Ω₂ : LvG (toLv (Ω (natL 2))) → WLPO
  no-Ω₂ w = no-uniformG (λ a → proj₂ (proj₂ w) (up tt (em a)) tt)
```

叶子取 `⊤` 时, 第 5 站的**输入** $\Omega_\Omega$ 的层号本身就要全部原始分支上正确 (`no-Ωᵀ`). 这是叶子改成 `≈ᴮ` 的编译理由: 只有嵌套的下标才碰到它, 第 5 站自己用 `Station5` 绕开了.

```agda
module NegT (S : Sib) where
  open Eqv S (λ _ → ⊤) using (LvG)
  open Neg S (λ _ → ⊤) using (no-uniformG)

  no-Ωᵀ : LvG (toLv (Ω (natL 1))) → WLPO
  no-Ωᵀ w = no-uniformG (λ a → proj₂ (proj₂ w) (em a) tt)
```
