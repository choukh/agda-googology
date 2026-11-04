# 读回, $\Omega$, 合法性的闭包定理

> 不含记号. 结论写在 [LevelFix](LevelFix.lagda.md). `up` 把第 $y$ 层的值读成层号, `em` 被它一步消掉. `Ω̂` 是一个定义, 三行归约 (`Ω̂-suc`, `Ω̂-lim`, `Ω̂-lc`). **`Legal x → Legal (Ω̂ x)` 对一切 `x`, 不按阶段, 一步 (`Legal-Ω̂`).** 这是 [EBOTopRaw](EBOTopRaw.lagda.md) 的 `G-good` 要的形状, 只是在 `Legal` 上, 不是在 `HS` 上.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LevelFixVal where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Free.Level using (Ordᴵ)
import OCF.Free.Level as Lvl
open import OCF.Align.LevelFixCore
```

## §1 读回

```agda
up : (y : LF) → Raw y → LF
upT : LF → LF
cO : (k : LF) → Raw k
upK : (y : LF) (i : Kid y) → KidR y i → LF
upN : (y : LF) (r : Pre y) (c : Low y r) (t : LF) (g : (η : Low y r) → GdL y r c η → LF) → LF

upN (suc k) (inj₁ _) c t g = lc k c t g
upN (suc k) (inj₂ r) c t g = upN k r c t g
upN (lim f) (n , r) c t g = upN (f n) r c t g
upN (lc k c₀ t₀ g₀) (inj₁ (inj₁ _)) c t g = lc k c t g
upN (lc k c₀ t₀ g₀) (inj₁ (inj₂ r)) c t g = upN k r c t g
upN (lc k c₀ t₀ g₀) (inj₂ (inj₁ r)) c t g = upN t₀ r c t g
upN (lc k c₀ t₀ g₀) (inj₂ (inj₂ (η , e , r))) c t g = upN (g₀ η e) r c t g

up y G.zero = zero
up y (G.suc a) = suc (up y a)
up y (G.lim f) = lim (λ n → up y (f n))
up y (G.lc r c t g) = upN y r c (up y t) (λ η e → up y (g η e))
up y (G.em i T) = upK y i T
up y G.top = upT y

upK (suc k) _ T = up k T
upK (lim f) n T = up (f n) T
upK (lc k c t g) (inj₁ _) T = up k T
upK (lc k c t g) (inj₂ (inj₁ _)) T = up t T
upK (lc k c t g) (inj₂ (inj₂ (η , e))) T = up (g η e) T
```

## §2 $\Omega$: 一个定义

`top` 形式地是 $\Omega_y$, `upT` 把它展开. 后继的节点就在前驱这一层, 下界 `cO k`, 极限逐项, 闭包的节点不变. **下面三条都是 `refl`, 所以这就是 `EBOTopRaw` 的 `next` 的形状, 没有折叠.** `cO zero` 用字面的 $1$: 第 0 层的值里 `top` 就是 1, 用字面的才能走到 `suc (suc zero)`.

```agda
cO zero = G.suc G.zero
cO (suc k) = G.top
cO (lim f) = G.top
cO (lc k c t g) = G.top

upT zero = suc zero
upT (suc k) = lc k (cO k) (upT k) (λ η e → up k η)
upT (lim f) = lim (λ n → upT (f n))
upT (lc k c t g) = lc k c (upT t) (λ η e → upT (g η e))

Ω̂ : LF → LF
Ω̂ = upT

Ω̂-zero : Ω̂ zero ≡ suc zero
Ω̂-zero = refl

Ω̂-suc : ∀ k → Ω̂ (suc k) ≡ lc k (cO k) (Ω̂ k) (λ η e → up k η)
Ω̂-suc k = refl

Ω̂-lim : ∀ f → Ω̂ (lim f) ≡ lim (λ n → Ω̂ (f n))
Ω̂-lim f = refl

Ω̂-lc : ∀ k c t g → Ω̂ (lc k c t g) ≡ lc k c (Ω̂ t) (λ η e → Ω̂ (g η e))
Ω̂-lc k c t g = refl

natF : ℕ → LF
natF zero = zero
natF (suc n) = suc (natF n)

infixl 6 _+ᴸ_
_+ᴸ_ : LF → LF → LF
a +ᴸ zero = a
a +ᴸ suc b = suc (a +ᴸ b)
a +ᴸ lim f = lim (λ n → a +ᴸ f n)
a +ᴸ lc k c t g = lc k c (a +ᴸ t) (λ η e → a +ᴸ g η e)

tw : ℕ → LF
tw zero = zero
tw (suc n) = Ω̂ (tw n)

Λ : LF
Λ = lim tw

-- 验收目标 1 的值. 都是同一个类型, 同一个定义.
Ω₁ Ω₂ Ω₃ Ωω : LF
Ω₁ = Ω̂ (natF 1)
Ω₂ = Ω̂ (natF 2)
Ω₃ = Ω̂ (natF 3)
Ωω = Ω̂ (lim natF)

Ω₁+1 Ω₁·2 ΩΩ₂ : LF
Ω₁+1 = suc Ω₁
Ω₁·2 = Ω₁ +ᴸ Ω₁
ΩΩ₂ = Ω̂ Ω₂

-- Ω_{Ω_η}, η 是任意层号, 不限于可数
ΩΩ : LF → LF
ΩΩ η = Ω̂ (Ω̂ η)

Λ-form : Λ ≡ lim tw
Λ-form = refl

fix-form : Ω̂ Λ ≡ lim (λ n → tw (suc n))
fix-form = refl

tw-2 : tw 2 ≡ lc zero (G.suc G.zero) (suc zero) (λ η e → up zero η)
tw-2 = refl

-- 任何层号的 Ω_{x+1} 都有分支: 下界的后继
ofI : Ordᴵ → LF
ofI Lvl.zero = zero
ofI (Lvl.suc a) = suc (ofI a)
ofI (Lvl.lim f s) = lim (λ n → ofI (f n))

ΩΩᴵ : Ordᴵ → LF
ΩΩᴵ η = Ω̂ (Ω̂ (ofI η))
```

`Ω̂ Λ` 与 `Λ` 差一个头 (`fix-form`): 同一个序列去掉第 0 项. 这正是 `EBOTopRaw` 的不动点 (`fixpoint`) 的形状.

## §3 层号上的第一位置与合法性

`CP a b`: $a$ 字面地是 $b$ 的第一位置. **这里可以直接对 `LF` 写数据类型**, 因为它不进 `lc` 的负位置. `Legal` 是块外的谓词, 它不进定义: 树不读它, 闭包定理才读.

```agda
data CP : LF → LF → Set where
  self : ∀ {a} → CP a a
  suc  : ∀ {a b} → CP a b → CP a (suc b)
  lim  : ∀ {a f} n → CP a (f n) → CP a (lim f)
  fst  : ∀ {a k c t g} → CP a t → CP a (lc k c t g)

CP-tr : ∀ {a b d} → CP a b → CP b d → CP a d
CP-tr p self = p
CP-tr p (suc q) = suc (CP-tr p q)
CP-tr p (lim n q) = lim n (CP-tr p q)
CP-tr p (fst q) = fst (CP-tr p q)

Legal : LF → Set
Legal zero = ⊤
Legal (suc k) = Legal k
Legal (lim f) = (∀ n → CP (f n) (f (suc n))) × (∀ n → Legal (f n))
Legal (lc k c t g) =
  Legal k ×
  (∀ η e → CP t (g η e)) ×
  (∀ η e η′ e′ → Gd k η η′ → CP (g η e) (g η′ e′)) ×
  (∀ η e e′ → g η e ≡ g η e′) ×
  Legal t × (∀ η e → Legal (g η e))
```

## §4 块里的证据读到层号上

```agda
fstN : ∀ y r c t g {a} → CP a t → CP a (upN y r c t g)
fstN (suc k) (inj₁ _) c t g p = fst p
fstN (suc k) (inj₂ r) c t g p = fstN k r c t g p
fstN (lim f) (n , r) c t g p = fstN (f n) r c t g p
fstN (lc k c₀ t₀ g₀) (inj₁ (inj₁ _)) c t g p = fst p
fstN (lc k c₀ t₀ g₀) (inj₁ (inj₂ r)) c t g p = fstN k r c t g p
fstN (lc k c₀ t₀ g₀) (inj₂ (inj₁ r)) c t g p = fstN t₀ r c t g p
fstN (lc k c₀ t₀ g₀) (inj₂ (inj₂ (η , e , r))) c t g p = fstN (g₀ η e) r c t g p

cp→CP : ∀ y {a b} → Cp y a b → CP (up y a) (up y b)
dn→CP : ∀ y {a} b → Dn y a b → CP (up y a) (up y b)
dnk→CP : ∀ y i i′ {a b} → DnK y i i′ a b → CP (upK y i a) (upK y i′ b)

cp→CP y (inj₁ refl) = self
cp→CP y {b = b} (inj₂ p) = dn→CP y b p

dn→CP y (G.suc b) p = suc (cp→CP y p)
dn→CP y (G.lim f) (n , p) = lim n (cp→CP y p)
dn→CP y (G.lc r c t g) p = fstN y r c _ _ (cp→CP y p)
dn→CP y {a = G.em i′ _} (G.em i T) p = dnk→CP y i′ i p
dn→CP (suc k) {G.em _ _} G.top p = fst (cp→CP k p)
dn→CP (lc k c t g) {G.em (inj₂ (inj₁ _)) _} G.top p = fst (cp→CP t p)

dnk→CP (suc k) _ _ {b = b} p = dn→CP k b p
dnk→CP (lim f) n .n {b = b} (refl , p) = dn→CP (f n) b p
dnk→CP (lc k c t g) (inj₁ _) (inj₁ _) {b = b} p = dn→CP k b p
dnk→CP (lc k c t g) (inj₂ (inj₁ _)) (inj₂ (inj₁ _)) {b = b} p = dn→CP t b p
dnk→CP (lc k c t g) (inj₂ (inj₂ (η , e))) (inj₂ (inj₂ .(η , e))) {b = b} (refl , p) = dn→CP (g η e) b p

legalN : ∀ y r c t g → Legal y →
  (∀ η e → CP t (g η e)) →
  (∀ η e η′ e′ → GdL y r η η′ → CP (g η e) (g η′ e′)) →
  (∀ η e e′ → g η e ≡ g η e′) →
  Legal t → (∀ η e → Legal (g η e)) → Legal (upN y r c t g)
legalN (suc k) (inj₁ _) c t g L a b i u v = L , a , b , i , u , v
legalN (suc k) (inj₂ r) c t g L a b i u v = legalN k r c t g L a b i u v
legalN (lim f) (n , r) c t g L a b i u v = legalN (f n) r c t g (proj₂ L n) a b i u v
legalN (lc k c₀ t₀ g₀) (inj₁ (inj₁ _)) c t g L a b i u v = proj₁ L , a , b , i , u , v
legalN (lc k c₀ t₀ g₀) (inj₁ (inj₂ r)) c t g L a b i u v = legalN k r c t g (proj₁ L) a b i u v
legalN (lc k c₀ t₀ g₀) (inj₂ (inj₁ r)) c t g (_ , _ , _ , _ , lt , _) a b i u v = legalN t₀ r c t g lt a b i u v
legalN (lc k c₀ t₀ g₀) (inj₂ (inj₂ (η , e , r))) c t g (_ , _ , _ , _ , _ , lg) a b i u v = legalN (g₀ η e) r c t g (lg η e) a b i u v
```

## §5 闭包定理: 对一切层号, 一步

**定理 `Ω̂-CP`, `Legal-Ω̂`, `lgl→Legal`.** 第一位置被 $\Omega$ 保持 (`Ω_{b+1}` 的第一支字面是 `Ω_b`). 合法性被 $\Omega$ 保持. 块里的证据读到层号上: 读到 `top` 时要 `Legal y`, 这就是 `Legal-Ω̂` 自己. 对 `x` 结构递归, 没有阶段, 没有世界, 没有判决.

```agda
cO-CP : ∀ k {η} → Cp k (cO k) η → CP (Ω̂ k) (up k η)
cO-CP zero p = cp→CP zero p
cO-CP (suc k) p = cp→CP (suc k) p
cO-CP (lim f) p = cp→CP (lim f) p
cO-CP (lc k c t g) p = cp→CP (lc k c t g) p

Ω̂-CP : ∀ {a b} → CP a b → CP (Ω̂ a) (Ω̂ b)
Ω̂-CP self = self
Ω̂-CP (suc p) = fst (Ω̂-CP p)
Ω̂-CP (lim n p) = lim n (Ω̂-CP p)
Ω̂-CP (fst p) = fst (Ω̂-CP p)

Legal-Ω̂ : ∀ x → Legal x → Legal (Ω̂ x)
lgl→Legal : ∀ y → Legal y → ∀ T → Lgl y T → Legal (up y T)
lglK→Legal : ∀ y → Legal y → ∀ i T → LglK y i T → Legal (upK y i T)

Legal-Ω̂ zero w = tt
Legal-Ω̂ (suc k) w =
  w ,
  (λ η e → cO-CP k (proj₁ e)) ,
  (λ η e η′ e′ d → cp→CP k (proj₁ d)) ,
  (λ η e e′ → refl) ,
  Legal-Ω̂ k w ,
  (λ η e → lgl→Legal k w η (proj₂ e))
Legal-Ω̂ (lim f) (st , w) = (λ n → Ω̂-CP (st n)) , (λ n → Legal-Ω̂ (f n) (w n))
Legal-Ω̂ (lc k c t g) (Lk , tg , dir , irr , wt , wg) =
  Lk ,
  (λ η e → Ω̂-CP (tg η e)) ,
  (λ η e η′ e′ d → Ω̂-CP (dir η e η′ e′ d)) ,
  (λ η e e′ → cong Ω̂ (irr η e e′)) ,
  Legal-Ω̂ t wt ,
  (λ η e → Legal-Ω̂ (g η e) (wg η e))

lgl→Legal y L G.zero w = tt
lgl→Legal y L (G.suc a) w = lgl→Legal y L a w
lgl→Legal y L (G.lim f) (st , w) = (λ n → cp→CP y (st n)) , (λ n → lgl→Legal y L (f n) (w n))
lgl→Legal y L (G.lc r c t g) (tg , dir , irr , lt , lg) =
  legalN y r c (up y t) (λ η e → up y (g η e)) L
    (λ η e → cp→CP y (tg η e))
    (λ η e η′ e′ d → cp→CP y (dir η e η′ e′ d))
    (λ η e e′ → cong (up y) (irr η e e′))
    (lgl→Legal y L t lt)
    (λ η e → lgl→Legal y L (g η e) (lg η e))
lgl→Legal y L (G.em i T) w = lglK→Legal y L i T w
lgl→Legal y L G.top w = Legal-Ω̂ y L

lglK→Legal (suc k) L _ T w = lgl→Legal k L T w
lglK→Legal (lim f) L n T w = lgl→Legal (f n) (proj₂ L n) T w
lglK→Legal (lc k c t g) L (inj₁ _) T w = lgl→Legal k (proj₁ L) T w
lglK→Legal (lc k c t g) (_ , _ , _ , _ , lt , _) (inj₂ (inj₁ _)) T w = lgl→Legal t lt T w
lglK→Legal (lc k c t g) (_ , _ , _ , _ , _ , lg) (inj₂ (inj₂ (η , e))) T w = lgl→Legal (g η e) (lg η e) T w

Lgl-cO : ∀ k → Lgl k (cO k)
Lgl-cO zero = tt
Lgl-cO (suc k) = tt
Lgl-cO (lim f) = tt
Lgl-cO (lc k c t g) = tt

-- 分支不空: 对一切 k, 下界的后继过守卫
branch : ∀ k → Gd k (cO k) (G.suc (cO k))
branch k = inj₂ (inj₁ refl) , Lgl-cO k
```

**推论: 塔与极限.** $x_{n+1}=\Omega_{x_n}$ 全部合法, 相邻字面第一位置, 所以 $\Lambda$ 合法, $\Omega_\Lambda$ 也合法. 这里 `Legal` 只说层号的形状合法: **它不说 $\psi_0$ 的输出是序数, 也不说树正确.**

```agda
tw-step : ∀ n → CP (tw n) (tw (suc n))
tw-step zero = suc self
tw-step (suc n) = Ω̂-CP (tw-step n)

Legal-tw : ∀ n → Legal (tw n)
Legal-tw zero = tt
Legal-tw (suc n) = Legal-Ω̂ (tw n) (Legal-tw n)

Legal-Λ : Legal Λ
Legal-Λ = tw-step , Legal-tw

Legal-ΩΛ : Legal (Ω̂ Λ)
Legal-ΩΛ = Legal-Ω̂ Λ Legal-Λ

natF-step : ∀ n → CP (natF n) (natF (suc n))
natF-step n = suc self

Legal-nat : ∀ n → Legal (natF n)
Legal-nat zero = tt
Legal-nat (suc n) = Legal-nat n

Legal-ω : Legal (lim natF)
Legal-ω = natF-step , Legal-nat

Legal-Ωω : Legal Ωω
Legal-Ωω = Legal-Ω̂ (lim natF) Legal-ω

Legal-Ω₂ : Legal Ω₂
Legal-Ω₂ = Legal-Ω̂ (natF 2) tt

Legal-ΩΩ₂ : Legal ΩΩ₂
Legal-ΩΩ₂ = Legal-Ω̂ Ω₂ Legal-Ω₂

Legal-ΩΩ : ∀ η → Legal η → Legal (ΩΩ η)
Legal-ΩΩ η w = Legal-Ω̂ (Ω̂ η) (Legal-Ω̂ η w)

-- ofI 对一切 η 有值 (ΩΩᴵ η 是闭项); 合法性要 Ordᴵ 的步进是字面的第一位置. Ordᴵ 的 lim 只带 ⊑ᴵ, 所以这是条件.
Legal-ΩΩᴵ : ∀ η → Legal (ofI η) → Legal (ΩΩᴵ η)
Legal-ΩΩᴵ η w = Legal-ΩΩ (ofI η) w

add-CP : ∀ x {a b} → CP a b → CP (x +ᴸ a) (x +ᴸ b)
add-CP x self = self
add-CP x (suc p) = suc (add-CP x p)
add-CP x (lim n p) = lim n (add-CP x p)
add-CP x (fst p) = fst (add-CP x p)

Legal-add : ∀ x a → Legal x → Legal a → Legal (x +ᴸ a)
Legal-add x zero w u = w
Legal-add x (suc a) w u = Legal-add x a w u
Legal-add x (lim f) w (st , u) = (λ n → add-CP x (st n)) , (λ n → Legal-add x (f n) w (u n))
Legal-add x (lc k c t g) w (Lk , tg , dir , irr , wt , wg) =
  Lk ,
  (λ η e → add-CP x (tg η e)) ,
  (λ η e η′ e′ d → add-CP x (dir η e η′ e′ d)) ,
  (λ η e e′ → cong (x +ᴸ_) (irr η e e′)) ,
  Legal-add x t w wt ,
  (λ η e → Legal-add x (g η e) w (wg η e))
```
