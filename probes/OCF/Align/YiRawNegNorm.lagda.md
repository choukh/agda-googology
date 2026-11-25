# YiRawNeg 第 3 项 (ii)：只在链上归一，链点与原来的累计是什么关系

**判决：编译定理。值的序是本文件自己在第 0 层的树上定义的 (`_≼_`)，没有对参照验收。** 字面上不成立：`ω` 不是 `cum ω` 的第一位置 (`cum-not-first`)，链点同理 (`point-not-first`)。
值上成立：`v ≼ cum v`，`c + v ≼ c + cum v`；分支值按值单调时，不归一的链的第 n 点 `≼` 归一的链的第 n 点 (`raw≼pt`)。反向不成立：`cum (ω + ω)` 严格高于 `ω + ω` (`inflate`)。
证书一侧 (正面)：归一的链点的证书由树算出并且一致 (`cum-coh`)，链的定义不调用分支值的合法性引理；根合法只要分支值沿限制单调 (`NormRoot.root-legal`)。
不否定链上归一；它改了链的行，值可以变高。上一步的部件在 [YiLvNegCum](YiLvNegCum.lagda.md)，不归一的链在 [YiRawNegChain](YiRawNegChain.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiRawNegNorm where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; subst)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck
open import OCF.Align.YiIrrIf
open import OCF.Align.YiIrrFoldBase using (add-legal; add-cp)
open import OCF.Align.YiLvNegCum
  using (psum; cum; weak; psum-legal; cum-legal; num; ω; ω-lgl; cum-add-weak)
open import OCF.Align.YiLvNegRestrict using (restrict; restrict-add; Coh; add-coh)
open import OCF.Align.YiRawNegModel using (lim-body)
```

## 1 字面上：累计不是归一后的第一位置

`cum ω` 的各项是有限的部分和，第 1 项是 2，而 `ω` 的第 1 项是 1；极限也不在有限的树之下。`ω` 是合法的 (`YiLvNegCum.ω-lgl`)。

```agda
Finite : R → Set
Finite G.zero = ⊤
Finite (G.suc a) = Finite a
Finite (G.lim f) = ⊥
Finite (G.lc () c t g)
Finite (G.em () T)
Finite G.top = ⊤

no-lim-below : ∀ y → Finite y → ∀ {f} → Cp zero (G.lim f) y → ⊥
no-lim-below G.zero h (inj₁ ())
no-lim-below G.zero h (inj₂ ())
no-lim-below (G.suc y) h (inj₁ ())
no-lim-below (G.suc y) h (inj₂ p) = no-lim-below y h p
no-lim-below (G.lim g) () p
no-lim-below (G.lc () c t g) h p
no-lim-below (G.em () T) h p
no-lim-below G.top h (inj₁ ())
no-lim-below G.top h (inj₂ ())

add-finite : ∀ x y → Finite x → Finite y → Finite (x +ʳ y)
add-finite x G.zero hx hy = hx
add-finite x (G.suc y) hx hy = add-finite x y hx hy
add-finite x (G.lim f) hx ()
add-finite x (G.lc () c t g) hx hy
add-finite x (G.em () T) hx hy
add-finite x G.top hx hy = hx

psum-finite : ∀ (g : ℕ → R) → (∀ n → Finite (g n)) → ∀ n → Finite (psum g n)
psum-finite g h zero = h zero
psum-finite g h (suc n) = add-finite (psum g n) (G.suc (g (suc n))) (psum-finite g h n) (h (suc n))

cum-num-finite : ∀ k → Finite (cum (num k))
cum-num-finite zero = tt
cum-num-finite (suc k) = cum-num-finite k

differ₁ : num 1 ≡ psum (λ k → cum (num k)) 1 → ⊥
differ₁ ()

cum-not-first : Cp zero ω (cum ω) → ⊥
cum-not-first (inj₁ e) = differ₁ (cong (λ x → lim-body x 1) e)
cum-not-first (inj₂ (n , p)) =
  no-lim-below (psum (λ k → cum (num k)) n) (psum-finite _ cum-num-finite n) p

differ₂ : one +ʳ num 1 ≡ one +ʳ psum (λ k → cum (num k)) 1 → ⊥
differ₂ ()

-- 链点的形式: 下界 1, 累计 ω.
point-not-first : Cp zero (one +ʳ ω) (one +ʳ cum ω) → ⊥
point-not-first (inj₁ e) = differ₂ (cong (λ x → lim-body x 1) e)
point-not-first (inj₂ (n , p)) =
  no-lim-below (one +ʳ psum (λ k → cum (num k)) n)
    (add-finite one _ tt (psum-finite _ cum-num-finite n)) p
```

## 2 第 0 层的树上值的序

布劳威尔树通常的序，写成两个互归纳的关系。`top` 在第 0 层读作 1 (`x +ʳ top = suc x`)。这是树侧的定义，不引用记号，也没有对参照的值验收。

```agda
infix 4 _≼_ _≺_
data _≼_ : R → R → Set
data _≺_ : R → R → Set

data _≼_ where
  z≼ : ∀ {b} → G.zero ≼ b
  s≼ : ∀ {a b} → a ≺ b → G.suc a ≼ b
  l≼ : ∀ {f b} → (∀ n → f n ≼ b) → G.lim f ≼ b
  t≼ : ∀ {b} → G.zero ≺ b → G.top ≼ b

data _≺_ where
  ≺s : ∀ {a b} → a ≼ b → a ≺ G.suc b
  ≺l : ∀ {a g} n → a ≺ g n → a ≺ G.lim g
  ≺t : ∀ {a} → a ≼ G.zero → a ≺ G.top

≼-lim : ∀ {a g} n → a ≼ g n → a ≼ G.lim g
≼-lim n z≼ = z≼
≼-lim n (s≼ p) = s≼ (≺l n p)
≼-lim n (l≼ h) = l≼ (λ m → ≼-lim n (h m))
≼-lim n (t≼ p) = t≼ (≺l n p)

≼-refl : ∀ a → a ≼ a
≼-refl G.zero = z≼
≼-refl (G.suc a) = s≼ (≺s (≼-refl a))
≼-refl (G.lim f) = l≼ (λ n → ≼-lim n (≼-refl (f n)))
≼-refl (G.lc () c t g)
≼-refl (G.em () T)
≼-refl G.top = t≼ (≺t z≼)

≼-bot : ∀ {a} b → a ≼ G.zero → a ≼ b
≼-bot b z≼ = z≼
≼-bot b (s≼ ())
≼-bot b (l≼ h) = l≼ (λ n → ≼-bot b (h n))
≼-bot b (t≼ ())

≼-suc : ∀ {a b} → a ≼ b → a ≼ G.suc b
≺→≼ : ∀ {a b} → a ≺ b → a ≼ b
≼-suc z≼ = z≼
≼-suc (s≼ p) = s≼ (≺s (≺→≼ p))
≼-suc (l≼ h) = l≼ (λ n → ≼-suc (h n))
≼-suc (t≼ p) = t≼ (≺s z≼)
≺→≼ (≺s p) = ≼-suc p
≺→≼ (≺l n p) = ≼-lim n (≺→≼ p)
≺→≼ (≺t p) = ≼-bot G.top p

≼-trans : ∀ {a b c} → a ≼ b → b ≼ c → a ≼ c
≺≼-trans : ∀ {a b c} → a ≺ b → b ≼ c → a ≺ c
≼≺-trans : ∀ {a b c} → a ≼ b → b ≺ c → a ≺ c
≼-trans z≼ q = z≼
≼-trans (s≼ p) q = s≼ (≺≼-trans p q)
≼-trans (l≼ h) q = l≼ (λ n → ≼-trans (h n) q)
≼-trans (t≼ p) q = t≼ (≺≼-trans p q)
≺≼-trans (≺s p) (s≼ q) = ≼≺-trans p q
≺≼-trans (≺l n p) (l≼ h) = ≺≼-trans p (h n)
≺≼-trans (≺t p) (t≼ q) = ≼≺-trans p q
≼≺-trans p (≺s q) = ≺s (≼-trans p q)
≼≺-trans p (≺l n q) = ≺l n (≼≺-trans p q)
≼≺-trans p (≺t q) = ≺t (≼-trans p q)

≺-irrefl : ∀ a → a ≺ a → ⊥
≺-irrefl G.zero ()
≺-irrefl (G.suc a) (≺s (s≼ p)) = ≺-irrefl a p
≺-irrefl (G.lim f) (≺l n p) = ≺-irrefl (f n) (≼≺-trans (≼-lim n (≼-refl (f n))) p)
≺-irrefl (G.lc () c t g) p
≺-irrefl (G.em () T) p
≺-irrefl G.top (≺t (t≼ ()))
```

加法对这个序的几条：两个加数都在和之下，对两个加数都单调，结合律的一个方向。

```agda
add-left : ∀ x y → x ≼ x +ʳ y
add-left x G.zero = ≼-refl x
add-left x (G.suc y) = ≼-suc (add-left x y)
add-left x (G.lim f) = ≼-lim zero (add-left x (f zero))
add-left x (G.lc () c t g)
add-left x (G.em () T)
add-left x G.top = ≼-suc (≼-refl x)

add-right : ∀ x y → y ≼ x +ʳ y
add-right x G.zero = z≼
add-right x (G.suc y) = s≼ (≺s (add-right x y))
add-right x (G.lim f) = l≼ (λ n → ≼-lim n (add-right x (f n)))
add-right x (G.lc () c t g)
add-right x (G.em () T)
add-right x G.top = t≼ (≺s z≼)

add-monoʳ : ∀ x {y y′} → y ≼ y′ → x +ʳ y ≼ x +ʳ y′
add-monoʳ≺ : ∀ x {y y′} → y ≺ y′ → x +ʳ y ≺ x +ʳ y′
add-monoʳ x {y′ = y′} z≼ = add-left x y′
add-monoʳ x (s≼ p) = s≼ (add-monoʳ≺ x p)
add-monoʳ x (l≼ h) = l≼ (λ n → add-monoʳ x (h n))
add-monoʳ x (t≼ p) = s≼ (add-monoʳ≺ x p)
add-monoʳ≺ x (≺s p) = ≺s (add-monoʳ x p)
add-monoʳ≺ x (≺l n p) = ≺l n (add-monoʳ≺ x p)
add-monoʳ≺ x (≺t p) = ≺s (add-monoʳ x p)

add-monoˡ : ∀ {x x′} → x ≼ x′ → ∀ y → x +ʳ y ≼ x′ +ʳ y
add-monoˡ p G.zero = p
add-monoˡ p (G.suc y) = s≼ (≺s (add-monoˡ p y))
add-monoˡ p (G.lim f) = l≼ (λ n → ≼-lim n (add-monoˡ p (f n)))
add-monoˡ p (G.lc () c t g)
add-monoˡ p (G.em () T)
add-monoˡ p G.top = s≼ (≺s p)

add-assoc : ∀ c a y → (c +ʳ a) +ʳ y ≼ c +ʳ (a +ʳ y)
add-assoc c a G.zero = ≼-refl (c +ʳ a)
add-assoc c a (G.suc y) = s≼ (≺s (add-assoc c a y))
add-assoc c a (G.lim f) = l≼ (λ n → ≼-lim n (add-assoc c a (f n)))
add-assoc c a (G.lc () c′ t g)
add-assoc c a (G.em () T)
add-assoc c a G.top = ≼-refl (G.suc (c +ʳ a))
```

## 3 值上：归一压得住累计，并且可以严格更高

```agda
psum-above : ∀ (g : ℕ → R) n → g n ≼ psum g n
psum-above g zero = ≼-refl (g zero)
psum-above g (suc n) =
  ≼-trans (≼-suc (≼-refl (g (suc n)))) (add-right (psum g n) (G.suc (g (suc n))))

cum-above : ∀ v → v ≼ cum v
cum-above G.zero = z≼
cum-above (G.suc v) = s≼ (≺s (cum-above v))
cum-above (G.lim f) =
  l≼ (λ n → ≼-lim n (≼-trans (cum-above (f n)) (psum-above (λ k → cum (f k)) n)))
cum-above (G.lc () c t g)
cum-above (G.em () T)
cum-above G.top = ≼-refl G.top

point-above : ∀ c v → c +ʳ v ≼ c +ʳ cum v
point-above c v = add-monoʳ c (cum-above v)

-- 只在一个极限处取部分和: 值不降; 在常值列 (合法, 相邻项相等) 上严格升高.
lim≼psum : ∀ (g : ℕ → R) → G.lim g ≼ G.lim (psum g)
lim≼psum g = l≼ (λ n → ≼-lim n (psum-above g n))

psum-inflates : G.lim (λ _ → one) ≺ G.lim (psum (λ _ → one))
psum-inflates = ≺l 1 (≺s (l≼ (λ n → ≼-suc (≼-refl one))))

-- 归一与加法: 先归一再加, 不超过先加再归一.
cum-add : ∀ v y → cum v +ʳ y ≼ cum (v +ʳ y)
cum-add v G.zero = ≼-refl (cum v)
cum-add v (G.suc y) = s≼ (≺s (cum-add v y))
cum-add v (G.lim f) =
  l≼ (λ n → ≼-lim n (≼-trans (cum-add v (f n)) (psum-above (λ k → cum (v +ʳ f k)) n)))
cum-add v (G.lc () c t g)
cum-add v (G.em () T)
cum-add v G.top = ≼-refl (G.suc (cum v))
```

两条链。`raw`：下一点是这一点加上这一点的分支值。`pt`：累计 `tot` 不归一地加，链点取 `c + cum tot`
(`YiLvNegCum.norm-guard` 的形状)。分支值在这里只是坐标的函数，按值单调是前提；它对真的折叠没有证。

```agda
module Compare (E : R → R) (E-mono : ∀ {a b} → a ≼ b → E a ≼ E b) (c : R) where

  raw : ℕ → R
  raw zero = c
  raw (suc n) = raw n +ʳ E (raw n)

  tot : ℕ → R
  tot zero = G.zero
  tot (suc n) = tot n +ʳ E (c +ʳ cum (tot n))

  pt : ℕ → R
  pt n = c +ʳ cum (tot n)

  raw≼pt : ∀ n → raw n ≼ pt n
  raw≼pt zero = ≼-refl c
  raw≼pt (suc n) =
    ≼-trans (add-monoˡ (raw≼pt n) (E (raw n)))
      (≼-trans (add-monoʳ (pt n) (E-mono (raw≼pt n)))
        (≼-trans (add-assoc c (cum (tot n)) (E (pt n)))
          (add-monoʳ c (cum-add (tot n) (E (pt n))))))

-- 归一把 ω + ω 的值严格抬高: 第 1 个部分和已经是 (cum ω + cum ω) + 2.
double : (ω +ʳ ω) ≼ (cum ω +ʳ cum ω)
double = ≼-trans (add-monoˡ (cum-above ω) ω) (add-monoʳ (cum ω) (cum-above ω))

inflate : (ω +ʳ ω) ≺ cum (ω +ʳ ω)
inflate = ≺l 1 (≺s (≼-suc double))

cum-not-below : cum (ω +ʳ ω) ≼ (ω +ʳ ω) → ⊥
cum-not-below p = ≺-irrefl (ω +ʳ ω) (≺≼-trans inflate p)

-- 前提的实例, 也是两条链不等值的实例: 分支值取常值 ω, 下界取零, 第 2 点.
module Const = Compare (λ _ → ω) (λ _ → ≼-refl ω) G.zero

const-strict : Const.raw 2 ≺ Const.pt 2
const-strict = ≺l 1 (≺s (≼-suc
  (≼-trans
    (≼-trans (add-monoˡ (cum-above (G.zero +ʳ ω)) ω)
      (add-monoʳ (cum (G.zero +ʳ ω)) (≼-trans (add-right G.zero ω) (cum-above (G.zero +ʳ ω)))))
    (add-right G.zero (cum (G.zero +ʳ ω) +ʳ cum (G.zero +ʳ ω))))))

const-not-back : Const.pt 2 ≼ Const.raw 2 → ⊥
const-not-back p = ≺-irrefl (Const.raw 2) (≺≼-trans const-strict p)
```

## 4 证书一侧：归一的链不调用分支值的合法性引理

`cum-legal` 造出的证书是一致的 (`Coh`)，并且沿链的一步限制回来就是前一点的证书。所以归一的链上，链点的证书由树算出；
根合法只要分支值沿限制单调，加上分支值各自合法。`tot` 的定义里没有 `E-legal`。

```agda
restrict-weak : ∀ x y (lx : Lgl zero x) (ly : Lgl zero y) →
  restrict (weak x y) (add-legal x y lx ly) ≡ lx
restrict-weak x G.zero lx ly = refl
restrict-weak x (G.suc y) lx ly = restrict-weak x y lx ly
restrict-weak x (G.lim f) lx (st , lf) = restrict-weak x (f zero) lx (lf zero)
restrict-weak x (G.lc () c t g) lx ly
restrict-weak x (G.em () T) lx ly
restrict-weak x G.top lx ly = refl

psum-coh : ∀ (g : ℕ → R) (lg : ∀ n → Lgl zero (g n)) → (∀ n → Coh (g n) (lg n)) →
  ∀ n → Coh (psum g n) (psum-legal g lg n)
psum-coh g lg ch zero = ch zero
psum-coh g lg ch (suc n) =
  add-coh (psum g n) (G.suc (g (suc n))) (psum-legal g lg n) (lg (suc n))
    (psum-coh g lg ch n) (ch (suc n))

cum-coh : ∀ a → Coh (cum a) (cum-legal a)
cum-coh G.zero = tt
cum-coh (G.suc a) = cum-coh a
cum-coh (G.lim f) =
  (λ n → restrict-weak (psum (λ k → cum (f k)) n) (G.suc (cum (f (suc n))))
    (psum-legal (λ k → cum (f k)) (λ k → cum-legal (f k)) n) (cum-legal (f (suc n)))) ,
  psum-coh (λ k → cum (f k)) (λ k → cum-legal (f k)) (λ k → cum-coh (f k))
cum-coh (G.lc () c t g)
cum-coh (G.em () T)
cum-coh G.top = tt

cum-restrict : ∀ v y → restrict (cum-add-weak v y) (cum-legal (v +ʳ y)) ≡ cum-legal v
cum-restrict v G.zero = refl
cum-restrict v (G.suc y) = cum-restrict v y
cum-restrict v (G.lim f) = cum-restrict v (f zero)
cum-restrict v (G.lc () c t g)
cum-restrict v (G.em () T)
cum-restrict v G.top = refl

module NormRoot (E : (η : R) → Lgl zero η → R) (c : R) (l₀ : Lgl zero c) where

  cert : ∀ v → Lgl zero (c +ʳ cum v)
  cert v = add-legal c (cum v) l₀ (cum-legal v)

  val : R → R
  val v = E (c +ʳ cum v) (cert v)

  tot : ℕ → R
  tot zero = G.zero
  tot (suc n) = tot n +ʳ val (tot n)

  root : R
  root = G.lim (λ n → val (tot n))

  cert-restrict : ∀ v y →
    restrict (add-cp c (cum-add-weak v y)) (cert (v +ʳ y)) ≡ cert v
  cert-restrict v y =
    trans (restrict-add c (cum (v +ʳ y)) (cum-add-weak v y) l₀ (cum-legal (v +ʳ y)))
      (cong (add-legal c (cum v) l₀) (cum-restrict v y))

  cert-coh : Coh c l₀ → ∀ v → Coh (c +ʳ cum v) (cert v)
  cert-coh ch v = add-coh c (cum v) l₀ (cum-legal v) ch (cum-coh v)

  -- 合法性引理无前提时.
  root-legal :
    (∀ η η′ (p : Cp zero η η′) (l′ : Lgl zero η′) → Cp zero (E η (restrict p l′)) (E η′ l′)) →
    (∀ η l → Lgl zero (E η l)) → Lgl zero root
  root-legal rm E-legal =
    (λ n → subst (λ z → Cp zero (E (c +ʳ cum (tot n)) z) (val (tot (suc n))))
      (cert-restrict (tot n) (val (tot n)))
      (rm (c +ʳ cum (tot n)) (c +ʳ cum (tot (suc n)))
        (add-cp c (cum-add-weak (tot n) (val (tot n)))) (cert (tot (suc n))))) ,
    (λ n → E-legal (c +ʳ cum (tot n)) (cert (tot n)))

  -- 合法性引理与限制形式都只对一致的证书给出时: 不需要 "输出证书一致".
  root-legalᶜ : Coh c l₀ →
    (∀ η η′ (p : Cp zero η η′) (l′ : Lgl zero η′) → Coh η′ l′ →
      Cp zero (E η (restrict p l′)) (E η′ l′)) →
    (∀ η l → Coh η l → Lgl zero (E η l)) → Lgl zero root
  root-legalᶜ ch rm E-legal =
    (λ n → subst (λ z → Cp zero (E (c +ʳ cum (tot n)) z) (val (tot (suc n))))
      (cert-restrict (tot n) (val (tot n)))
      (rm (c +ʳ cum (tot n)) (c +ʳ cum (tot (suc n)))
        (add-cp c (cum-add-weak (tot n) (val (tot n)))) (cert (tot (suc n)))
        (cert-coh ch (tot (suc n))))) ,
    (λ n → E-legal (c +ʳ cum (tot n)) (cert (tot n)) (cert-coh ch (tot n)))

-- 前提的实例: 分支值就是坐标.
plain-norm-legal : Lgl zero (NormRoot.root (λ η l → η) one tt)
plain-norm-legal = NormRoot.root-legal (λ η l → η) one tt (λ η η′ p l′ → p) (λ η l → l)

plain-norm-legalᶜ : Lgl zero (NormRoot.root (λ η l → η) one tt)
plain-norm-legalᶜ =
  NormRoot.root-legalᶜ (λ η l → η) one tt tt (λ η η′ p l′ ch → p) (λ η l ch → l)
```

范围。§3 的 `raw≼pt` 以 "分支值只读坐标且按值单调" 为前提，前提的实例是常值；真的折叠的分支值读证书，并且按值单调没有证。
`inflate`、`const-strict` 说两条链的值可以不同；折叠的输出是不是总落在归一不改值的那一类树上，没有判定。
§4 与 [YiRawNegChain](YiRawNegChain.lagda.md) §3 对照：不归一的链在 "合法性引理带一致性前提" 时要 `E-coh`，归一的链不要。
