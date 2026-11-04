# 累加读回: 字面合法由构造给出, 第一位置不被保持

> 不含记号. 结论写在 [CumRead](CumRead.lagda.md).
>
> - `cumA`: 第 0 层的树读成层, 每个 `lim` 累加: $\lim f\mapsto\lim(g_0,\ g_0+(g_1+1),\ \dots)$, $g_i$ 是 $f_i$ 的读回. **`Lg-cum`: 对一切树, 无条件, 字面合法.** 这是 [NoKCertNeg](NoKCertNeg.lagda.md) 的 `no-HS→Lgl` 绕过去的办法: 读回不要求被读的树合法.
> - `ordᴸ`: 同样的读回放到 `LF` 上. `lc` 的分支逐点读. `Legal-ordᴸ`: 没有闭包的层上无条件合法.
> - `no-cum-⊲`: **累加不保字面第一位置.** $\omega$ 是 $\lim(1,\omega,\omega,\dots)$ 的字面第一位置, 读回之后不是. `no-Legal-ordᴸ`: 所以 `lc` 的分支逐点读过不去: `tw 2` (也就是 $\Omega_1$) 合法, 它的 `ordᴸ` 不合法, `Legal` 的 `dir` 那一条在 $\eta$ 跨过极限的第 1 项时断了.
> - `overshootᴬ`: **累加确实改值:** $\omega\cdot3$ 在 `cumA` $(\omega\cdot2)$ 之下. 与 [Cumsum](Cumsum.lagda.md) 的 `overshoot` 同形, 这里是字面路径.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CumReadBase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)
open import OCF.Free.Level using (Ordᶜ; _≺_; _⊑⁰_; HS; hz; hs; hl)
import OCF.Free.Level as FL
open import OCF.Align.LevelFixCore using (LF; zero; suc; lim; lc; Gd; Raw; module G)
open import OCF.Align.LevelFixVal using (CP; self; suc; lim; fst; Legal; _+ᴸ_; add-CP; Legal-add; up; tw; Legal-tw)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; Lg; ⊲-tr; ≪∘)
import OCF.Align.CumReadCF as C
```

## §1 层上的加法

```agda
infixl 6 _⊞_
_⊞_ : A → A → A
a ⊞ azero = a
a ⊞ asuc b = asuc (a ⊞ b)
a ⊞ alim f = alim (λ n → a ⊞ f n)

⊞-fst : ∀ a b → a ⊲ a ⊞ b
⊞-fst a azero = C.self
⊞-fst a (asuc b) = C.suc (⊞-fst a b)
⊞-fst a (alim f) = C.lim 0 (⊞-fst a (f 0))

⊞-⊲ : ∀ a {b b′} → b ⊲ b′ → a ⊞ b ⊲ a ⊞ b′
⊞-⊲ a C.self = C.self
⊞-⊲ a (C.suc p) = C.suc (⊞-⊲ a p)
⊞-⊲ a (C.lim n p) = C.lim n (⊞-⊲ a p)

⊞-≪ : ∀ a {b b′} → b ≪ b′ → a ⊞ b ≪ a ⊞ b′
⊞-≪ a C.zero = C.zero
⊞-≪ a (C.suc p) = C.suc (⊞-≪ a p)
⊞-≪ a (C.lim n p) = C.lim n (⊞-≪ a p)

Lg-⊞ : ∀ a b → Lg a → Lg b → Lg (a ⊞ b)
Lg-⊞ a azero u v = u
Lg-⊞ a (asuc b) u v = Lg-⊞ a b u v
Lg-⊞ a (alim f) u (st , v) = (λ n → ⊞-⊲ a (st n)) , (λ n → Lg-⊞ a (f n) u (v n))
```

## §2 累加

```agda
cs : (ℕ → A) → ℕ → A
cs g zero = g 0
cs g (suc n) = cs g n ⊞ asuc (g (suc n))

cs-step : ∀ g n → cs g n ⊲ cs g (suc n)
cs-step g n = ⊞-fst (cs g n) (asuc (g (suc n)))

Lg-cs : ∀ g → (∀ n → Lg (g n)) → ∀ n → Lg (cs g n)
Lg-cs g w zero = w 0
Lg-cs g w (suc n) = Lg-⊞ (cs g n) (asuc (g (suc n))) (Lg-cs g w n) (w (suc n))

Ord₀ : Set
Ord₀ = Ordᶜ FL.zero

cumA : Ord₀ → A
cumA FL.zero = azero
cumA (FL.suc a) = asuc (cumA a)
cumA (FL.lim f) = alim (cs (λ n → cumA (f n)))
cumA (FL.limᵢ () f)
cumA (FL.up () x)

Lg-cum : ∀ y → Lg (cumA y)
Lg-cum FL.zero = tt
Lg-cum (FL.suc a) = Lg-cum a
Lg-cum (FL.lim f) = cs-step (λ n → cumA (f n)) , Lg-cs (λ n → cumA (f n)) (λ n → Lg-cum (f n))
Lg-cum (FL.limᵢ () f)
Lg-cum (FL.up () x)
```

**链.** 下一个下标把上一个输出接在上面: $\eta'=\eta+(\lceil y\rceil+1)$. **字面第一位置由构造给出** (`next-⊲`), 合法性也是 (`Lg-next`). 这是 [CrossMNode](CrossMNode.lagda.md) 的累加链 `C` 落到层上的形状. 这也回答了 `chain-stuck` 那个点: 下界 $c$ 不需要在链点的第一路径上, 因为第一个下标就是 $c+(\lceil y_0\rceil+1)$.

```agda
next : A → Ord₀ → A
next η y = η ⊞ asuc (cumA y)

next-⊲ : ∀ η y → η ⊲ next η y
next-⊲ η y = ⊞-fst η (asuc (cumA y))

Lg-next : ∀ η y → Lg η → Lg (next η y)
Lg-next η y w = Lg-⊞ η (asuc (cumA y)) w (Lg-cum y)
```

## §3 改值: $\omega\cdot3$ 在 $\lceil\omega\cdot2\rceil$ 之下

```agda
natO : ℕ → Ord₀
natO zero = FL.zero
natO (suc n) = FL.suc (natO n)

ω₁ : Ord₀
ω₁ = FL.lim natO

_+₀_ : Ord₀ → ℕ → Ord₀
a +₀ zero = a
a +₀ suc n = FL.suc (a +₀ n)

ω·2 : Ord₀
ω·2 = FL.lim (λ n → ω₁ +₀ n)

ωA : A
ωA = cumA ω₁

overshootᴬ : (ωA ⊞ asuc (asuc ωA)) ⊞ ωA ≪ cumA ω·2
overshootᴬ = C.lim 2 (⊞-≪ (ωA ⊞ asuc (asuc ωA)) (C.suc (C.suc C.zero)))
```

## §4 累加不保第一位置

$b=\lim(1,\omega,\omega,\dots)$. $\omega$ 是它的字面第一位置 (相邻项也是), 但 $\lceil\omega\rceil$ 不是 $\lceil b\rceil$ 的第一位置: `cs` 的每一项都以 $1$ 打头, 所以 $\lceil b\rceil$ 里的极限的第 0 项都不是 $0$, 而 $\lceil\omega\rceil$ 的第 0 项是 $0$.

```agda
hb : ℕ → Ord₀
hb zero = natO 1
hb (suc _) = ω₁

b₀ : Ord₀
b₀ = FL.lim hb

NZ : A → Set
NZ azero = ⊥
NZ (asuc _) = ⊤
NZ (alim f) = NZ (f 0)

NZ-⊞ : ∀ a b → NZ a → NZ (a ⊞ b)
NZ-⊞ a azero u = u
NZ-⊞ a (asuc b) u = tt
NZ-⊞ a (alim f) u = NZ-⊞ a (f 0) u

I : A → Set
I azero = ⊤
I (asuc a) = I a
I (alim f) = NZ (f 0) × (∀ n → I (f n))

I-⊞ : ∀ a b → NZ a → I a → I b → I (a ⊞ b)
I-⊞ a azero n u v = u
I-⊞ a (asuc b) n u v = I-⊞ a b n u v
I-⊞ a (alim f) n u (_ , v) = NZ-⊞ a (f 0) n , (λ k → I-⊞ a (f k) n u (v k))

I-⊲ : ∀ {a b} → a ⊲ b → I b → I a
I-⊲ C.self u = u
I-⊲ (C.suc p) u = I-⊲ p u
I-⊲ (C.lim n p) (_ , u) = I-⊲ p (u n)

natA-I : ∀ n → I (cumA (natO n))
natA-I zero = tt
natA-I (suc n) = natA-I n

-- ωA 的项
gωA : ℕ → A
gωA k = cumA (natO k)

ωA-I′ : ∀ n → I (cs gωA (suc n))
ωA-I′ zero = natA-I 1
ωA-I′ (suc n) = I-⊞ (cs gωA (suc n)) (asuc (gωA (suc (suc n)))) tt (ωA-I′ n) (natA-I (suc (suc n)))

csb : ℕ → A
csb = cs (λ n → cumA (hb n))

NZ-csb : ∀ n → NZ (csb n)
NZ-csb zero = tt
NZ-csb (suc n) = tt

ωA-terms : ∀ n → I (cs gωA n)
ωA-terms zero = tt
ωA-terms (suc n) = ωA-I′ n
```

`ωA` 的第 0 项是 $0$, 所以它自己不满足 `I`. `csb` 的每一项满足 `I`: 新接上的 `asuc ωA` 经 `I-⊞` 变成以 `csb n` 打头.

```agda
I-add-ω : ∀ a → NZ a → I a → I (a ⊞ ωA)
I-add-ω a n u = NZ-⊞ a (cs gωA 0) n , (λ k → I-⊞ a (cs gωA k) n u (ωA-terms k))

I-csb : ∀ n → I (csb n)
I-csb zero = tt
I-csb (suc n) = I-add-ω (csb n) (NZ-csb n) (I-csb n)

no-I-ωA : I ωA → ⊥
no-I-ωA (() , _)

no-cum-⊲ : ωA ⊲ cumA b₀ → ⊥
no-cum-⊲ p = no-I-ωA (I-⊲ p (NZ-csb 0 , I-csb))
```

对照: 在树上 $\omega$ 确实是 $b_0$ 的第一位置 (`hb 1`), 所以 `no-cum-⊲` 不是读错了第一位置.

```agda
data _◁_ : Ord₀ → Ord₀ → Set where
  self : ∀ {a} → a ◁ a
  suc  : ∀ {a b} → a ◁ b → a ◁ FL.suc b
  lim  : ∀ {a f} n → a ◁ f n → a ◁ FL.lim f

ω◁b₀ : ω₁ ◁ b₀
ω◁b₀ = lim 1 self
```

## §5 `LF` 上

`lim` 累加, `lc` 逐点. **没有闭包的层上无条件合法; 有闭包的层上逐点读不合法.**

```agda
csL : (ℕ → LF) → ℕ → LF
csL g zero = g 0
csL g (suc n) = csL g n +ᴸ suc (g (suc n))

+ᴸ-fst : ∀ a b → CP a (a +ᴸ b)
+ᴸ-fst a zero = self
+ᴸ-fst a (suc b) = suc (+ᴸ-fst a b)
+ᴸ-fst a (lim f) = lim 0 (+ᴸ-fst a (f 0))
+ᴸ-fst a (lc k c t g) = fst (+ᴸ-fst a t)

csL-step : ∀ g n → CP (csL g n) (csL g (suc n))
csL-step g n = +ᴸ-fst (csL g n) (suc (g (suc n)))

Legal-csL : ∀ g → (∀ n → Legal (g n)) → ∀ n → Legal (csL g n)
Legal-csL g w zero = w 0
Legal-csL g w (suc n) = Legal-add (csL g n) (suc (g (suc n))) (Legal-csL g w n) (w (suc n))

ordᴸ : LF → LF
ordᴸ zero = zero
ordᴸ (suc a) = suc (ordᴸ a)
ordᴸ (lim f) = lim (csL (λ n → ordᴸ (f n)))
ordᴸ (lc k c t g) = lc k c (ordᴸ t) (λ η e → ordᴸ (g η e))

NoLc : LF → Set
NoLc zero = ⊤
NoLc (suc a) = NoLc a
NoLc (lim f) = ∀ n → NoLc (f n)
NoLc (lc k c t g) = ⊥

Legal-ordᴸ : ∀ y → NoLc y → Legal (ordᴸ y)
Legal-ordᴸ zero h = tt
Legal-ordᴸ (suc a) h = Legal-ordᴸ a h
Legal-ordᴸ (lim f) h = csL-step (λ n → ordᴸ (f n)) , Legal-csL (λ n → ordᴸ (f n)) (λ n → Legal-ordᴸ (f n) (h n))
Legal-ordᴸ (lc k c t g) ()
```

**`no-Legal-ordᴸ`.** `tw 2` 的分支是 $\eta\mapsto$ `up 0 η`. 取 $\eta=\lceil\omega\rceil$ 的字面值, $\eta'=\lim(1,\omega,\omega,\dots)$ 的字面值, 两个都合法, 前者是后者的第一位置, 而 `ordᴸ` 之后不是. 这里的值是 `Raw 0` 里的值, `up 0` 把它搬到 `LF`.

```agda
rd₀ : Ord₀ → Raw zero
rd₀ FL.zero = G.zero
rd₀ (FL.suc a) = G.suc (rd₀ a)
rd₀ (FL.lim f) = G.lim (λ n → rd₀ (f n))
rd₀ (FL.limᵢ () f)
rd₀ (FL.up () x)

NZL : LF → Set
NZL zero = ⊥
NZL (suc _) = ⊤
NZL (lim f) = NZL (f 0)
NZL (lc k c t g) = NZL t

NZ-+ᴸ : ∀ a b → NZL a → NZL (a +ᴸ b)
NZ-+ᴸ a zero u = u
NZ-+ᴸ a (suc b) u = tt
NZ-+ᴸ a (lim f) u = NZ-+ᴸ a (f 0) u
NZ-+ᴸ a (lc k c t g) u = NZ-+ᴸ a t u

IL : LF → Set
IL zero = ⊤
IL (suc a) = IL a
IL (lim f) = NZL (f 0) × (∀ n → IL (f n))
IL (lc k c t g) = IL t

IL-+ᴸ : ∀ a b → NoLc b → NZL a → IL a → IL b → IL (a +ᴸ b)
IL-+ᴸ a zero h n u v = u
IL-+ᴸ a (suc b) h n u v = IL-+ᴸ a b h n u v
IL-+ᴸ a (lim f) h n u (_ , v) = NZ-+ᴸ a (f 0) n , (λ k → IL-+ᴸ a (f k) (h k) n u (v k))
IL-+ᴸ a (lc k c t g) () n u v

IL-CP : ∀ {a b} → CP a b → IL b → IL a
IL-CP self u = u
IL-CP (suc p) u = IL-CP p u
IL-CP (lim n p) (_ , u) = IL-CP p (u n)
IL-CP (fst p) u = IL-CP p u

natL : ℕ → LF
natL zero = zero
natL (suc n) = suc (natL n)

up-nat : ∀ n → up zero (rd₀ (natO n)) ≡ natL n
up-nat zero = refl
up-nat (suc n) = cong suc (up-nat n)

-- ⌈ω⌉ 与 ⌈b₀⌉ 的 LF 版本
ωL : LF
ωL = ordᴸ (up zero (rd₀ ω₁))

bL : LF
bL = ordᴸ (up zero (rd₀ b₀))

ordᴸ-nat : ∀ n → NoLc (ordᴸ (up zero (rd₀ (natO n))))
ordᴸ-nat zero = tt
ordᴸ-nat (suc n) = ordᴸ-nat n

IL-nat : ∀ n → IL (ordᴸ (up zero (rd₀ (natO n))))
IL-nat zero = tt
IL-nat (suc n) = IL-nat n

gω : ℕ → LF
gω n = ordᴸ (up zero (rd₀ (natO n)))

NoLc-+ᴸ : ∀ a b → NoLc a → NoLc b → NoLc (a +ᴸ b)
NoLc-+ᴸ a zero u v = u
NoLc-+ᴸ a (suc b) u v = NoLc-+ᴸ a b u v
NoLc-+ᴸ a (lim f) u v = λ n → NoLc-+ᴸ a (f n) u (v n)
NoLc-+ᴸ a (lc k c t g) u ()

NoLc-gω : ∀ n → NoLc (csL gω n)
NoLc-gω zero = tt
NoLc-gω (suc n) = NoLc-+ᴸ _ (suc (gω (suc n))) (NoLc-gω n) (ordᴸ-nat (suc n))

IL-gω : ∀ n → IL (csL gω n)
IL-gω zero = tt
IL-gω (suc zero) = tt
IL-gω (suc (suc n)) = IL-+ᴸ (csL gω (suc n)) (suc (gω (suc (suc n)))) (ordᴸ-nat (suc (suc n))) tt (IL-gω (suc n)) (IL-nat (suc (suc n)))

gb : ℕ → LF
gb n = ordᴸ (up zero (rd₀ (hb n)))

csb-NZ : ∀ n → NZL (csL gb n)
csb-NZ zero = tt
csb-NZ (suc n) = tt

ωL-noLc : NoLc ωL
ωL-noLc = NoLc-gω

IL-add-ω : ∀ a → NZL a → IL a → IL (a +ᴸ ωL)
IL-add-ω a n u = NZ-+ᴸ a (csL gω 0) n , (λ k → IL-+ᴸ a (csL gω k) (NoLc-gω k) n u (IL-gω k))

IL-csb : ∀ n → IL (csL gb n)
IL-csb zero = tt
IL-csb (suc n) = IL-add-ω (csL gb n) (csb-NZ n) (IL-csb n)

no-IL-ω : IL ωL → ⊥
no-IL-ω (() , _)

no-CP-ω : CP ωL bL → ⊥
no-CP-ω p = no-IL-ω (IL-CP p (csb-NZ 0 , IL-csb))
```

现在落到 `tw 2`. 它的分支在 `Gd zero (suc zero) η` 上. 两个下标 $\eta_1,\eta_2$ 都以 $1$ 为字面第一位置, $\eta_1$ 是 $\eta_2$ 的字面第一位置, 都合法.

```agda
open import OCF.Align.LevelFixCore using (Cp; Dn; Lgl)

one : Raw zero
one = G.suc G.zero

η₁ η₂ : Raw zero
η₁ = rd₀ ω₁
η₂ = rd₀ b₀

nat-step : ∀ n → Cp zero (rd₀ (natO n)) (rd₀ (natO (suc n)))
nat-step n = inj₂ (inj₁ refl)

one⊑nat : ∀ n → Cp zero one (rd₀ (natO (suc n)))
one⊑nat zero = inj₁ refl
one⊑nat (suc n) = inj₂ (one⊑nat n)

Lgl-nat : ∀ n → Lgl zero (rd₀ (natO n))
Lgl-nat zero = tt
Lgl-nat (suc n) = Lgl-nat n

Lgl-η₁ : Lgl zero η₁
Lgl-η₁ = nat-step , Lgl-nat

Cp-one-η₁ : Cp zero one η₁
Cp-one-η₁ = inj₂ (1 , inj₁ refl)

step-b : ∀ n → Cp zero (rd₀ (hb n)) (rd₀ (hb (suc n)))
step-b zero = Cp-one-η₁
step-b (suc n) = inj₁ refl

Lgl-hb : ∀ n → Lgl zero (rd₀ (hb n))
Lgl-hb zero = tt
Lgl-hb (suc n) = Lgl-η₁

Lgl-η₂ : Lgl zero η₂
Lgl-η₂ = step-b , Lgl-hb

Cp-η₁-η₂ : Cp zero η₁ η₂
Cp-η₁-η₂ = inj₂ (1 , inj₁ refl)

Cp-one-η₂ : Cp zero one η₂
Cp-one-η₂ = inj₂ (0 , inj₁ refl)

no-Legal-ordᴸ : Legal (ordᴸ (tw 2)) → ⊥
no-Legal-ordᴸ (_ , _ , dir , _ , _ , _) =
  no-CP-ω (dir η₁ (Cp-one-η₁ , Lgl-η₁) η₂ (Cp-one-η₂ , Lgl-η₂) (Cp-η₁-η₂ , Lgl-η₂))

-- 前提可满足: tw 2 本身合法
Legal-tw2 : Legal (tw 2)
Legal-tw2 = Legal-tw 2
```

## §6 值: 不低于, 与吸收

`toO`: 层读回第 0 层的树. `_≼_`: Brouwer 序. **`dom-cum`: $y\preceq\lceil y\rceil$, 无条件.** `absorb`: 如果 $y$ 对加法封闭, 项的读回都在 $y$ 之下, 那么 $\lceil y\rceil\preceq y$: 这时累加不改值. 这是条件定理, 前提写明了. `absorb-ω`: $\omega$ 上前提成立, $\lceil\omega\rceil$ 与 $\omega$ 互相 $\preceq$. 对比 `overshootᴬ`: $\omega\cdot2$ 不是加法主数, 值变了.

`no-⊞-left`: 左边的第一位置不被 `⊞` 保持. 这是 [CumReadW](CumReadW.lagda.md) 里 "同一个闭包在两个世界算出的链字面不可比" 的根.

```agda
toO : A → Ord₀
toO azero = FL.zero
toO (asuc a) = FL.suc (toO a)
toO (alim f) = FL.lim (λ n → toO (f n))

infix 4 _≼_
data _≼_ : Ord₀ → Ord₀ → Set where
  z≼  : ∀ {b} → FL.zero ≼ b
  s≼  : ∀ {a b} → a ≼ b → FL.suc a ≼ FL.suc b
  s≼ʳ : ∀ {a b} → a ≼ b → a ≼ FL.suc b
  l≼  : ∀ {f b} → (∀ n → f n ≼ b) → FL.lim f ≼ b
  l≼ʳ : ∀ {a f} n → a ≼ f n → a ≼ FL.lim f

≼-refl : ∀ a → a ≼ a
≼-refl FL.zero = z≼
≼-refl (FL.suc a) = s≼ (≼-refl a)
≼-refl (FL.lim f) = l≼ (λ n → l≼ʳ n (≼-refl (f n)))
≼-refl (FL.limᵢ () f)
≼-refl (FL.up () x)

≼-trans : ∀ {a b c} → a ≼ b → b ≼ c → a ≼ c
≼-trans z≼ y = z≼
≼-trans (s≼ x) (s≼ y) = s≼ (≼-trans x y)
≼-trans (s≼ x) (s≼ʳ y) = s≼ʳ (≼-trans (s≼ x) y)
≼-trans (s≼ x) (l≼ʳ n y) = l≼ʳ n (≼-trans (s≼ x) y)
≼-trans (s≼ʳ x) (s≼ y) = s≼ʳ (≼-trans x y)
≼-trans (s≼ʳ x) (s≼ʳ y) = s≼ʳ (≼-trans (s≼ʳ x) y)
≼-trans (s≼ʳ x) (l≼ʳ n y) = l≼ʳ n (≼-trans (s≼ʳ x) y)
≼-trans (l≼ h) y = l≼ (λ n → ≼-trans (h n) y)
≼-trans (l≼ʳ n x) (l≼ h) = ≼-trans x (h n)
≼-trans (l≼ʳ n x) (s≼ʳ y) = s≼ʳ (≼-trans (l≼ʳ n x) y)
≼-trans (l≼ʳ n x) (l≼ʳ k y) = l≼ʳ k (≼-trans (l≼ʳ n x) y)

-- b ≼ a + b, 左加数不减值
⊞-dom : ∀ a b → toO b ≼ toO (a ⊞ b)
⊞-dom a azero = z≼
⊞-dom a (asuc b) = s≼ (⊞-dom a b)
⊞-dom a (alim f) = l≼ (λ n → l≼ʳ n (⊞-dom a (f n)))

cs-dom : ∀ g n → toO (g n) ≼ toO (cs g n)
cs-dom g zero = ≼-refl _
cs-dom g (suc n) = s≼ʳ (⊞-dom (cs g n) (g (suc n)))

dom-cum : ∀ y → y ≼ toO (cumA y)
dom-cum FL.zero = z≼
dom-cum (FL.suc a) = s≼ (dom-cum a)
dom-cum (FL.lim f) = l≼ (λ n → l≼ʳ n (≼-trans (dom-cum (f n)) (cs-dom (λ k → cumA (f k)) n)))
dom-cum (FL.limᵢ () f)
dom-cum (FL.up () x)

-- 上界: y 对 ⊞ 封闭
record Closed (y : Ord₀) : Set where
  field
    cl-add : ∀ a b → FL.suc (toO a) ≼ y → FL.suc (toO b) ≼ y → FL.suc (toO (a ⊞ b)) ≼ y
    cl-suc : ∀ {a} → FL.suc a ≼ y → FL.suc (FL.suc a) ≼ y
open Closed public

absorb : ∀ {f : ℕ → Ord₀} → Closed (FL.lim f) → (∀ n → FL.suc (toO (cumA (f n))) ≼ FL.lim f) → toO (cumA (FL.lim f)) ≼ FL.lim f
absorb {f} c h = l≼ (λ n → ≼-pred (go n))
  where
  ≼-pred : ∀ {a b} → FL.suc a ≼ b → a ≼ b
  ≼-pred (s≼ x) = s≼ʳ x
  ≼-pred (s≼ʳ x) = s≼ʳ (≼-pred x)
  ≼-pred (l≼ʳ n x) = l≼ʳ n (≼-pred x)
  go : ∀ n → FL.suc (toO (cs (λ k → cumA (f k)) n)) ≼ FL.lim f
  go zero = h 0
  go (suc n) = cl-add c (cs (λ k → cumA (f k)) n) (asuc (cumA (f (suc n)))) (go n) (cl-suc c (h (suc n)))

-- ω 上: 有限的和还是有限的
Fin : Ord₀ → Set
Fin x = Σ ℕ λ m → x ≼ natO m

-- 数字
NA : A → Set
NA azero = ⊤
NA (asuc a) = NA a
NA (alim f) = ⊥

fin-⊞ : ∀ a b → NA b → Fin (toO a) → Σ ℕ λ m → (toO (a ⊞ b) ≼ natO m)
fin-⊞ a azero h u = u
fin-⊞ a (asuc b) h u with fin-⊞ a b h u
... | k , q = suc k , s≼ q
fin-⊞ a (alim f) () u

NA-nat : ∀ n → NA (cumA (natO n))
NA-nat zero = tt
NA-nat (suc n) = NA-nat n

fin-cs : ∀ n → Fin (toO (cs gωA n))
fin-cs zero = 0 , z≼
fin-cs (suc n) = fin-⊞ (cs gωA n) (asuc (gωA (suc n))) (NA-nat (suc n)) (fin-cs n)

≼-upper : toO ωA ≼ ω₁
≼-upper = l≼ (λ n → ≼-tr′ (fin-cs n))
  where
  ≼-tr′ : ∀ {a} → Fin a → a ≼ ω₁
  ≼-tr′ (m , p) = l≼ʳ m p

absorb-ω : (ω₁ ≼ toO ωA) × (toO ωA ≼ ω₁)
absorb-ω = dom-cum ω₁ , ≼-upper

-- ⊞ 不保左边的第一位置
no-⊞-left : (∀ a a′ b → a ⊲ a′ → a ⊞ b ⊲ a′ ⊞ b) → ⊥
no-⊞-left h = no-zero (I-⊲ (h azero (asuc azero) ωA (C.suc C.self)) (I-add-ω (asuc azero) tt tt))
  where
  no-zero : I (azero ⊞ ωA) → ⊥
  no-zero (() , _)
```
