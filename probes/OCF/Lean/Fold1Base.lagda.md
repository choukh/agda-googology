# Fold1 (一): 合法 `Lg*`, 塔的合法结构, 路径上的搬运

> 不含记号. 入口 [Fold1](Fold1.lagda.md), 接口 [Fold1If](Fold1If.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延. 只导入 stdlib, [CRwBase](CRwBase.lagda.md), [Fold1If](Fold1If.lagda.md).
>
> **这一篇做什么.** (1) 合法 `Lg*`: 与 `CRwBase.LgB` 逐构造子相同, 只把 ℕ-极限的步进改成 "在一切**合法**世界里" (同 [Fab3Typed](../Align/Fab3Typed.lagda.md) §1, 那里是对 `HtTowerTy` 写的, 类型不同, 这里对 `CRwBase` 重写). 合法结构 `LS` 有三个字段; `step*` 同 Fab3Typed, 新增 `sup*` (并的合法结构), 于是塔的每一层有合法结构 `ℓT m` (§2). (2) 路径 $x\lhd t$ 上的搬运 (§3): 种类上提 `liftK`, 坐标 `frK`/`toK`, 子世界 `sub`, 界与第一位置与坐标合法的搬运. (3) 地板合法 `lg-top`, 地板世界 `Wi` (每个种类的界取它那一层的地板). (4) 值关系 `≤ᵛ` 的引理 (§5).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.Fold1Base where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If
```

## §1 合法 `Lg*` (对一切种类结构)

```agda
record LS (S : KS) : Set₁ where
  field
    LgW*  : Wd S → Set
    LgE*  : (κ : K S) → E S κ → Set
    lgBd* : ∀ {κ c w} → Bd S κ c w → LgW* w → LgE* κ c
open LS public

module _ {S : KS} (ℓ : LS S) where
  Lg* : HB S → Set
  Lg* hz = ⊤
  Lg* (hs h) = Lg* h
  Lg* (hl f) = (∀ {w} → LgW* ℓ w → ∀ n → f n ⊲[ w ] f (suc n)) × (∀ n → Lg* (f n))
  Lg* (hΩ κ g) =
    (∀ {w c c′} → LgW* ℓ w → Bd S κ c w → Bd S κ c′ w → Pr S κ w c c′ → g c ⊲[ w ] g c′) ×
    (∀ c → LgE* ℓ κ c → Lg* (g c))

  lg*⊲ : ∀ {a b w} → a ⊲[ w ] b → LgW* ℓ w → Lg* b → Lg* a
  lg*⊲ hself lw l = l
  lg*⊲ (hsuc p) lw l = lg*⊲ p lw l
  lg*⊲ (hlim n p) lw l = lg*⊲ p lw (proj₂ l n)
  lg*⊲ (hLim e p) lw l = lg*⊲ p lw (proj₂ l _ (lgBd* ℓ e lw))

  Lg*-⊞ : ∀ a b → Lg* a → Lg* b → Lg* (a ⊞ b)
  Lg*-⊞ a hz la lb = la
  Lg*-⊞ a (hs b) la lb = Lg*-⊞ a b la lb
  Lg*-⊞ a (hl f) la (st , l) = (λ lw n → ⊞-⊲ a (st lw n)) , (λ n → Lg*-⊞ a (f n) la (l n))
  Lg*-⊞ a (hΩ κ g) la (mo , l) = (λ lw e e′ p → ⊞-⊲ a (mo lw e e′ p)) , (λ c lc → Lg*-⊞ a (g c) la (l c lc))

  Lg*-mul : ∀ x → Lg* x → ∀ n → Lg* (mul x n)
  Lg*-mul x l zero = l
  Lg*-mul x l (suc n) = Lg*-⊞ (mul x n) x (Lg*-mul x l n) l
```

## §2 底, 一步, 并; 塔的合法结构

```agda
ls⊥ : LS S⊥
ls⊥ = record { LgW* = λ _ → ⊤ ; LgE* = λ () ; lgBd* = λ {κ} → ⊥-elim κ }

step* : ∀ {T} → LS T → LS (step T)
step* {T} ℓ = record { LgW* = λ w → LgW* ℓ (proj₁ w) × Lg* ℓ (proj₂ w) ; LgE* = LE ; lgBd* = λ {κ} → lB {κ} }
  where
  LE : (κ : K (step T)) → E (step T) κ → Set
  LE (inj₁ κ) = LgE* ℓ κ
  LE (inj₂ _) = Lg* ℓ
  lB : ∀ {κ c w} → Bd (step T) κ c w → LgW* ℓ (proj₁ w) × Lg* ℓ (proj₂ w) → LE κ c
  lB {inj₁ κ} e (lw , lb) = lgBd* ℓ e lw
  lB {inj₂ _} e (lw , lb) = lg*⊲ ℓ e lw lb

sup* : ∀ {F : ℕ → KS} → (∀ n → LS (F n)) → LS (sup ℕ F)
sup* ℓ = record { LgW* = λ w → ∀ i → LgW* (ℓ i) (w i) ; LgE* = λ κ → LgE* (ℓ (proj₁ κ)) (proj₂ κ)
                ; lgBd* = λ {κ} e lw → lgBd* (ℓ (proj₁ κ)) e (lw (proj₁ κ)) }

ℓT : ∀ m → LS (Lv m)
ℓT hz = ls⊥
ℓT (hs x) = step* (ℓT x)
ℓT (hl f) = sup* (λ n → ℓT (f n))
ℓT (hΩ () _)

-- 第 0 层: Lg* 就是 LgB
lgB⊥ : ∀ h → Lg* ls⊥ h → LgB h
lgB⊥ hz l = tt
lgB⊥ (hs h) l = lgB⊥ h l
lgB⊥ (hl f) (st , l) = (λ {w} n → st {w} tt n) , (λ n → lgB⊥ (f n) (l n))
lgB⊥ (hΩ () _) l
```

`up`, `ι` 保第一位置与 `Lg*`; 地板合法.

```agda
module _ {T : KS} where
  up-⊲ : ∀ {a b w β} → a ⊲[ w ] b → up a ⊲[ _,_ {B = λ _ → HB T} w β ] up b
  up-⊲ hself = hself
  up-⊲ (hsuc p) = hsuc (up-⊲ p)
  up-⊲ (hlim n p) = hlim n (up-⊲ p)
  up-⊲ (hLim e p) = hLim e (up-⊲ p)

  Lg*-up : (ℓ : LS T) → ∀ a → Lg* ℓ a → Lg* (step* ℓ) (up a)
  Lg*-up ℓ hz l = tt
  Lg*-up ℓ (hs a) l = Lg*-up ℓ a l
  Lg*-up ℓ (hl f) (st , l) = (λ lw n → up-⊲ (st (proj₁ lw) n)) , (λ n → Lg*-up ℓ (f n) (l n))
  Lg*-up ℓ (hΩ κ g) (mo , l) = (λ lw e e′ p → up-⊲ (mo (proj₁ lw) e e′ p)) , (λ c lc → Lg*-up ℓ (g c) (l c lc))

module _ {F : ℕ → KS} where
  ι-⊲ : ∀ {i a b} {w : Wd (sup ℕ F)} → a ⊲[ w i ] b → ι {ℕ} {F} i a ⊲[ w ] ι i b
  ι-⊲ hself = hself
  ι-⊲ (hsuc p) = hsuc (ι-⊲ p)
  ι-⊲ (hlim n p) = hlim n (ι-⊲ p)
  ι-⊲ (hLim e p) = hLim e (ι-⊲ p)

  Lg*-ι : (ℓ : ∀ n → LS (F n)) → ∀ i a → Lg* (ℓ i) a → Lg* (sup* ℓ) (ι i a)
  Lg*-ι ℓ i hz l = tt
  Lg*-ι ℓ i (hs a) l = Lg*-ι ℓ i a l
  Lg*-ι ℓ i (hl f) (st , l) = (λ lw n → ι-⊲ (st (lw i) n)) , (λ n → Lg*-ι ℓ i (f n) (l n))
  Lg*-ι ℓ i (hΩ κ g) (mo , l) = (λ lw e e′ p → ι-⊲ (mo (lw i) e e′ p)) , (λ c lc → Lg*-ι ℓ i (g c) (l c lc))

lg-top* : ∀ m → Lg* (ℓT m) (top m)
lg-ΣT : ∀ (f : ℕ → Cd) n → Lg* (ℓT (hl f)) (ΣT S⊥ hz f n)
lg-top* hz = tt
lg-top* (hs x) = (λ lw e e′ p → up-⊲ p) , (λ c lc → Lg*-up (ℓT x) c lc)
lg-top* (hl f) = (λ lw n → ⊞-fst (ΣT S⊥ hz f n) _) , lg-ΣT f
lg-top* (hΩ () _)
lg-ΣT f zero = Lg*-ι (λ n → ℓT (f n)) 0 _ (lg-top* (f 0))
lg-ΣT f (suc n) = Lg*-⊞ (ℓT (hl f)) _ _ (lg-ΣT f n) (Lg*-ι (λ n → ℓT (f n)) (suc n) _ (lg-top* (f (suc n))))
```

**地板世界** `Wi m`: 每个种类的界取它那一层的地板 (第 $x+1$ 层的新种类, 界是 `top x`). 合法.

```agda
Wi : ∀ m → Wd (Lv m)
Wi hz = tt
Wi (hs x) = Wi x , top x
Wi (hl f) = λ n → Wi (f n)
Wi (hΩ () _)

lgWi : ∀ m → LgW* (ℓT m) (Wi m)
lgWi hz = tt
lgWi (hs x) = lgWi x , lg-top* x
lgWi (hl f) = λ n → lgWi (f n)
lgWi (hΩ () _)
```

## §3 路径 $x\lhd t$ 上的搬运

`liftK q`: 第 $x$ 层的种类看成第 $t$ 层的种类 (沿路径的拷贝); `frK`/`toK`: 坐标 (每步都是恒等); `sub q v`: 第 $t$ 层的世界沿路径取到第 $x$ 层. 界, `Pr`, 坐标合法都沿路径原样搬运 (每步是定义上的等式).

```agda
liftK : ∀ {x t} → x ⊲ t → K (Lv x) → K (Lv t)
liftK hself κ = κ
liftK (hsuc q) κ = inj₁ (liftK q κ)
liftK (hlim n q) κ = n , liftK q κ
liftK (hLim {κ = ()} _ _) _

frK : ∀ {x t} (q : x ⊲ t) κ → E (Lv t) (liftK q κ) → E (Lv x) κ
frK hself κ d = d
frK (hsuc q) κ d = frK q κ d
frK (hlim n q) κ d = frK q κ d
frK (hLim {κ = ()} _ _) _ _

toK : ∀ {x t} (q : x ⊲ t) κ → E (Lv x) κ → E (Lv t) (liftK q κ)
toK hself κ d = d
toK (hsuc q) κ d = toK q κ d
toK (hlim n q) κ d = toK q κ d
toK (hLim {κ = ()} _ _) _ _

ftK : ∀ {x t} (q : x ⊲ t) κ c → frK q κ (toK q κ c) ≡ c
ftK hself κ c = refl
ftK (hsuc q) κ c = ftK q κ c
ftK (hlim n q) κ c = ftK q κ c
ftK (hLim {κ = ()} _ _) _ _

sub : ∀ {x t} → x ⊲ t → Wd (Lv t) → Wd (Lv x)
sub hself v = v
sub (hsuc q) v = sub q (proj₁ v)
sub (hlim n q) v = sub q (v n)
sub (hLim {κ = ()} _ _) _

bdDn : ∀ {x t} (q : x ⊲ t) κ {d v} → Bd (Lv t) (liftK q κ) d v → Bd (Lv x) κ (frK q κ d) (sub q v)
bdDn hself κ b = b
bdDn (hsuc q) κ b = bdDn q κ b
bdDn (hlim n q) κ b = bdDn q κ b
bdDn (hLim {κ = ()} _ _) _ _

bdUp : ∀ {x t} (q : x ⊲ t) κ {c v} → Bd (Lv x) κ c (sub q v) → Bd (Lv t) (liftK q κ) (toK q κ c) v
bdUp hself κ b = b
bdUp (hsuc q) κ b = bdUp q κ b
bdUp (hlim n q) κ b = bdUp q κ b
bdUp (hLim {κ = ()} _ _) _ _

prDn : ∀ {x t} (q : x ⊲ t) κ {d d′ v} → Pr (Lv t) (liftK q κ) v d d′ → Pr (Lv x) κ (sub q v) (frK q κ d) (frK q κ d′)
prDn hself κ p = p
prDn (hsuc q) κ p = prDn q κ p
prDn (hlim n q) κ p = prDn q κ p
prDn (hLim {κ = ()} _ _) _ _

lgDn : ∀ {x t} (q : x ⊲ t) κ {d} → LgE* (ℓT t) (liftK q κ) d → LgE* (ℓT x) κ (frK q κ d)
lgDn hself κ l = l
lgDn (hsuc q) κ l = lgDn q κ l
lgDn (hlim n q) κ l = lgDn q κ l
lgDn (hLim {κ = ()} _ _) _ _

lgSub : ∀ {x t} (q : x ⊲ t) {v} → LgW* (ℓT t) v → LgW* (ℓT x) (sub q v)
lgSub hself l = l
lgSub (hsuc q) l = lgSub q (proj₁ l)
lgSub (hlim n q) l = lgSub q (l n)
lgSub (hLim {κ = ()} _ _) _

-- 第一位置只经界读世界: 界逐种类可推, 则第一位置可推
trW : ∀ (S : KS) {w w′ : Wd S} → (∀ κ c → Bd S κ c w → Bd S κ c w′) → ∀ {a b : HB S} → a ⊲[ w ] b → a ⊲[ w′ ] b
trW S h hself = hself
trW S h (hsuc p) = hsuc (trW S h p)
trW S h (hlim n p) = hlim n (trW S h p)
trW S h (hLim {κ = κ} {c = c} e p) = hLim (h κ c e) (trW S h p)
```

## §4 改世界的一个分量

```agda
open import Data.Nat using (_≟_)
open import Relation.Nullary using (yes; no)

updAt : ∀ {A : ℕ → Set} → (∀ i → A i) → ∀ k → A k → ∀ i → A i
updAt w k a i with i ≟ k
... | yes refl = a
... | no _ = w i

updAt-P : ∀ {A : ℕ → Set} (P : ∀ i → A i → Set) {w : ∀ i → A i} {k a} → P k a → (∀ i → P i (w i)) → ∀ i → P i (updAt w k a i)
updAt-P P {k = k} pa pw i with i ≟ k
... | yes refl = pa
... | no _ = pw i
```

## §5 值关系的引理 (不带世界)

```agda
module _ {S : KS} where
  ≤-refl : ∀ a → _≤ᵛ_ {S} a a
  ≤-refl hz = z≤
  ≤-refl (hs a) = s≤s (≤-refl a)
  ≤-refl (hl f) = l≤ (λ n → ≤l n (≤-refl (f n)))
  ≤-refl (hΩ κ g) = Ω≤Ω (λ c → ≤-refl (g c))

  ≤-trans : ∀ {a b c : HB S} → a ≤ᵛ b → b ≤ᵛ c → a ≤ᵛ c
  ≤-trans z≤ q = z≤
  ≤-trans (l≤ h) q = l≤ (λ n → ≤-trans (h n) q)
  ≤-trans p (≤l n q) = ≤l n (≤-trans p q)
  ≤-trans p (≤Ω c q) = ≤Ω c (≤-trans p q)
  ≤-trans p (≤s q) = ≤s (≤-trans p q)
  ≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)
  ≤-trans (≤s p) (s≤s q) = ≤s (≤-trans p q)
  ≤-trans (≤l n p) (l≤ h) = ≤-trans p (h n)
  ≤-trans (≤Ω c p) (Ω≤Ω H) = ≤Ω c (≤-trans p (H c))
  ≤-trans (Ω≤Ω H) (Ω≤Ω H′) = Ω≤Ω (λ c → ≤-trans (H c) (H′ c))

  ≤⊞ : ∀ a b → _≤ᵛ_ {S} a (a ⊞ b)
  ≤⊞ a hz = ≤-refl a
  ≤⊞ a (hs b) = ≤s (≤⊞ a b)
  ≤⊞ a (hl f) = ≤l 0 (≤⊞ a (f 0))
  ≤⊞ a (hΩ κ g) = ≤Ω (bot S κ) (≤⊞ a (g (bot S κ)))

  ⊞-≤ˡ : ∀ {a a′ : HB S} → a ≤ᵛ a′ → ∀ b → a ⊞ b ≤ᵛ a′ ⊞ b
  ⊞-≤ˡ p hz = p
  ⊞-≤ˡ p (hs b) = s≤s (⊞-≤ˡ p b)
  ⊞-≤ˡ p (hl f) = l≤ (λ n → ≤l n (⊞-≤ˡ p (f n)))
  ⊞-≤ˡ p (hΩ κ g) = Ω≤Ω (λ c → ⊞-≤ˡ p (g c))

  ⊞-≤ʳ : ∀ a {b b′ : HB S} → b ≤ᵛ b′ → a ⊞ b ≤ᵛ a ⊞ b′
  ⊞-≤ʳ a {b′ = b′} z≤ = ≤⊞ a b′
  ⊞-≤ʳ a (s≤s p) = s≤s (⊞-≤ʳ a p)
  ⊞-≤ʳ a (≤s p) = ≤s (⊞-≤ʳ a p)
  ⊞-≤ʳ a (l≤ h) = l≤ (λ n → ⊞-≤ʳ a (h n))
  ⊞-≤ʳ a (≤l n p) = ≤l n (⊞-≤ʳ a p)
  ⊞-≤ʳ a (≤Ω c p) = ≤Ω c (⊞-≤ʳ a p)
  ⊞-≤ʳ a (Ω≤Ω H) = Ω≤Ω (λ c → ⊞-≤ʳ a (H c))

  mul-≤ : ∀ {x y : HB S} → x ≤ᵛ y → ∀ n → mul x n ≤ᵛ mul y n
  mul-≤ p zero = p
  mul-≤ {y = y} p (suc n) = ≤-trans (⊞-≤ˡ (mul-≤ p n) _) (⊞-≤ʳ (mul y n) p)
```
