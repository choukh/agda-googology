# 序数高度的世界: 数据树, $\Omega$, 加法

> 不含记号, 不含累加. 结论写在 [CumHt](CumHt.lagda.md). 与 [CumUpW](CumUpW.lagda.md) 同形, 差别:
>
> - `𝓞 H a u`: 高度 `H` $=\langle r,p\rangle$, $p:A$. 定义按 $(r,p,a)$ 字典序递归, 三个分开的参数, 终止检查自己看得出来.
> - **低高度的节点 `od`, 嵌入 `oL` 多带一个证据:** 路径里自由的那一位 (`fd`) 在世界之下. $r$ 位下降时 $p$ 位是自由的, 没有这个证据就比不了.
> - **$\Omega$ 的新情形.** $(r,p+1,0)$: 闭包, 第一支 $(r,p,1)$, 分支 $(r,p,v)$. $(r,\lim f,0)$: $\omega$-极限. $(r+1,0,0)$: 闭包, 第一支 $(r,1,0)$, 分支 $(r,v,0)$, **$v$ 跑遍一切世界.** 与 $(r,p+1,0)$ 同一个构造子 `oc`.
> - `mx`: 世界 $\max(u,\ \text{目标两位},\ \text{项两位})$, 字面比较, 运行世界只作证据. 由两两比较折叠.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CumHtTree where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Free.Level as FL
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; Strict; ss; sl; Lg; ⊲-tr; lg⊲; z⊲; ≪∘; ≪S; ≪⊲; S→⊲; cmpF)
import OCF.Align.CumReadCF as C
open import OCF.Align.CumHtBase
```

## §1 数据树

`𝓞 H a u`: 高度 $H$, 层 $a$, 世界 $u$. `V`: 同高度低层的元素, 走路径 (`≪`). `Lw`: 低高度的元素, 对一切 `A` 下标.

```agda
data Stp : ∀ {a L} → Strict a L → Set where
  es : ∀ {b} → Stp {b} {asuc b} (ss C.self)
  el : ∀ {f} n → Stp {f n} {alim f} (sl n C.self)

module _ (H : Ht) (a : A) (V : ∀ {b} → Strict b a → A → Set) (Lw : ∀ {h} → h <ᴴ H → A → A → Set) where
  data O₊ : A → Set where
    o0 : ∀ {u} → O₊ u
    os : ∀ {u} → O₊ u → O₊ u
    ol : ∀ {u} → (ℕ → O₊ u) → O₊ u
    oi : ∀ {u k} (r : k ≪ a) → (∀ {v} → u ⊲ v → Gw v → V (≪S r) v → O₊ v) → O₊ u
    od : ∀ {u h} (i : h <ᴴ H) (k : A) → Rd (fd i) k u → (∀ {v} → u ⊲ v → Gw v → Lw i k v → O₊ v) → O₊ u
    oc : ∀ {u} → O₊ u → (∀ {v} → u ⊲ v → Gw v → O₊ v) → O₊ u
    oe : ∀ {u b} {R : Strict b a} → Stp R → V R u → O₊ u
    oL : ∀ {u h} (i : h <ᴴ H) (k : A) → D⊲ (fd i) k u → Lw i k u → O₊ u
    ow : ∀ {u v} → u ⊲ v → Gw u → O₊ u → O₊ v

-- 盒子: 让 `x : Low …` 的类型头是数据. `--without-K` 下类型头卡住的函数参数不参与终止检查,
-- CumUp 靠隐式的 p 下降过关, 这里 r 位下降时 p 位自由, 字面的 ⟨ s , p′ ⟩ 比不过 ⟨ suc s , p ⟩.
data Bx (L : Set) : Set where
  bx : L → Bx L

𝓞′  : ℕ → A → A → A → Set
Vs′ : ∀ r p a {b} → Strict b a → A → Set
Vc′ : ∀ r p a {b} → b ⊲ a → A → Set
Low′ : ∀ r p {h} → h <ᴴ ⟨ r , p ⟩ → A → A → Set
𝓞′ r p a = O₊ ⟨ r , p ⟩ a (Vs′ r p a) (λ i k u → Bx (Low′ r p i k u))
Vs′ r p (asuc b) (ss P) u = Vc′ r p b P u
Vs′ r p (alim f) (sl n P) u = Vc′ r p (f n) P u
Vc′ r p a C.self u = 𝓞′ r p a u
Vc′ r p (asuc b) (C.suc P) u = Vc′ r p b P u
Vc′ r p (alim f) (C.lim n P) u = Vc′ r p (f n) P u
Low′ r _ (hs0 {b = b}) k u = 𝓞′ r b k u
Low′ r _ (hl0 {f = f} n) k u = 𝓞′ r (f n) k u
Low′ _ _ (hr0 {s = s} {p′ = p′}) k u = 𝓞′ s p′ k u
Low′ r _ (hsS {b = b} i) k u = Low′ r b i k u
Low′ r _ (hlS {f = f} n i) k u = Low′ r (f n) i k u
Low′ _ _ (hrS {s = s} i) k u = Low′ s azero i k u

𝓞 : Ht → A → A → Set
𝓞 H a u = 𝓞′ (rr H) (pp H) a u

Vs : ∀ H a {b} → Strict b a → A → Set
Vs H = Vs′ (rr H) (pp H)

Vc : ∀ H a {b} → b ⊲ a → A → Set
Vc H = Vc′ (rr H) (pp H)

Low : ∀ H {h} → h <ᴴ H → A → A → Set
Low H i k u = Bx (Low′ (rr H) (pp H) i k u)

outC : ∀ {p a b u} (P : b ⊲ a) → Vc p a P u → 𝓞 p b u
outC C.self x = x
outC (C.suc P) x = outC P x
outC (C.lim n P) x = outC P x

inC : ∀ {p a b u} (P : b ⊲ a) → 𝓞 p b u → Vc p a P u
inC C.self x = x
inC (C.suc P) x = inC P x
inC (C.lim n P) x = inC P x

outS : ∀ {p a b u} (R : Strict b a) → Vs p a R u → 𝓞 p b u
outS (ss P) x = outC P x
outS (sl n P) x = outC P x

inS : ∀ {p a b u} (R : Strict b a) → 𝓞 p b u → Vs p a R u
inS (ss P) x = inC P x
inS (sl n P) x = inC P x

outL : ∀ {p h k u} (i : h <ᴴ p) → Low p i k u → 𝓞 h k u
outL hs0 (bx x) = x
outL (hl0 n) (bx x) = x
outL hr0 (bx x) = x
outL (hsS i) x = outL i x
outL (hlS n i) x = outL i x
outL (hrS i) x = outL i x

inL : ∀ {p h k u} (i : h <ᴴ p) → 𝓞 h k u → Low p i k u
inL hs0 x = bx x
inL (hl0 n) x = bx x
inL hr0 x = bx x
inL (hsS i) x = inL i x
inL (hlS n i) x = inL i x
inL (hrS i) x = inL i x

out-inC : ∀ {p a b u} (P : b ⊲ a) (x : 𝓞 p b u) → outC P (inC P x) ≡ x
out-inC C.self x = refl
out-inC (C.suc P) x = out-inC P x
out-inC (C.lim n P) x = out-inC P x

out-inS : ∀ {p a b u} (R : Strict b a) (x : 𝓞 p b u) → outS R (inS R x) ≡ x
out-inS (ss P) x = out-inC P x
out-inS (sl n P) x = out-inC P x

out-inL : ∀ {p h k u} (i : h <ᴴ p) (x : 𝓞 h k u) → outL i (inL i x) ≡ x
out-inL hs0 x = refl
out-inL (hl0 n) x = refl
out-inL hr0 x = refl
out-inL (hsS i) x = out-inL i x
out-inL (hlS n i) x = out-inL i x
out-inL (hrS i) x = out-inL i x
```

## §2 $\Omega$

`Ω̇ H a`: 闭的元素, 世界是 $1$. 高度的 $p$ 不进世界: 它在路径 (`hs0`, `hl0`) 里, 由折叠时项的证据管. 只有 $r$ 位下降时自由的 $p$ 位要证据 (`hr0` 的第一支在世界 $1$, 分支 $v$ 在世界 $v$).

```agda
Ω̇′ : ∀ r p a → 𝓞′ r p a one
Ω̇′ r p (asuc c) = oi C.zero (λ q g z → oe es z)
Ω̇′ r p (alim f) = ol (λ n → oe (el n) (Ω̇′ r p (f n)))
Ω̇′ r (asuc b) azero =
  oc (oL hs0 one (z⊲ one ,ᵈ C.self) (bx (Ω̇′ r b one)))
     (λ {v} q g → oL hs0 v (z⊲ v ,ᵈ C.self) (bx (ow (pos g) g₀ (Ω̇′ r b v))))
Ω̇′ r (alim f) azero = ol (λ n → oL (hl0 n) azero (z⊲ one ,ᵈ z⊲ one) (bx (Ω̇′ r (f n) azero)))
Ω̇′ zero azero azero = os o0
Ω̇′ (suc s) azero azero =
  oc (oL hr0 azero (C.self ,ᵈ z⊲ one) (bx (Ω̇′ s one azero)))
     (λ {v} q g → oL (hr0 {p′ = v}) azero (C.self ,ᵈ z⊲ v) (bx (ow (pos g) g₀ (Ω̇′ s v azero))))

Ω̇ : ∀ H a → 𝓞 H a one
Ω̇ H a = Ω̇′ (rr H) (pp H) a

Ω̇at : ∀ p a {v} → Gw v → 𝓞 p a v
Ω̇at p a g = ow (pos g) g₀ (Ω̇ p a)
```

## §3 世界的 $\max$

两两比较折叠. `is` 记着 $m$ 是哪一个, 用来证 $m$ 模 `≈ᴬ` 与证据无关 (`m≈`).

```agda
data Mis (m u x₁ x₂ y₁ y₂ : A) : Set where
  iu : m ≡ u → Mis m u x₁ x₂ y₁ y₂
  ix₁ : m ≡ x₁ → Mis m u x₁ x₂ y₁ y₂
  ix₂ : m ≡ x₂ → Mis m u x₁ x₂ y₁ y₂
  iy₁ : m ≡ y₁ → Mis m u x₁ x₂ y₁ y₂
  iy₂ : m ≡ y₂ → Mis m u x₁ x₂ y₁ y₂

-- 数据, 不是记录: 否则 mx 不等比较就展开成投影, with 抽象不到
data M₂ (u x v : A) : Set where
  m2 : (m₂ : A) → Gw m₂ → u ⊲ m₂ → x ⊲ m₂ → m₂ ⊲ v → (m₂ ≡ u) ⊎ (m₂ ≡ x) → M₂ u x v

mx₂ : ∀ {u x v} → Gw u → Gw v → u ⊲ v → x ⊲ v → M₂ u x v
mx₂ {u} {x} gu gv uv xv with cmpF uv xv (lgw gv)
... | inj₁ x⊲u = m2 u gu C.self x⊲u uv (inj₁ refl)
... | inj₂ u⊲x = m2 x (gw (lg⊲ xv (lgw gv)) (⊲-tr (pos gu) u⊲x)) u⊲x C.self xv (inj₂ refl)

record Mx (u x₁ x₂ y₁ y₂ v : A) : Set where
  constructor mx′
  field
    m   : A
    gm  : Gw m
    um  : u ⊲ m
    tm  : D⊲ x₁ x₂ m
    am  : D⊲ y₁ y₂ m
    mv  : m ⊲ v
    is  : Mis m u x₁ x₂ y₁ y₂

mx : ∀ {u x₁ x₂ y₁ y₂ v} → Gw u → Gw v → u ⊲ v → D⊲ x₁ x₂ v → D⊲ y₁ y₂ v → Mx u x₁ x₂ y₁ y₂ v
mx {u} {x₁} {x₂} {y₁} {y₂} {v} gu gv uv tv av with mx₂ gu gv uv (d₁ tv)
... | m2 m₁ g₁ u₁ a₁ v₁ i₁ with mx₂ g₁ gv v₁ (d₂ tv)
...   | m2 m₂ g₂ u₂ a₂ v₂ i₂ with mx₂ g₂ gv v₂ (d₁ av)
...     | m2 m₃ g₃ u₃ a₃ v₃ i₃ with mx₂ g₃ gv v₃ (d₂ av)
...       | m2 m₄ g₄ u₄ a₄ v₄ i₄ =
  mx′ m₄ g₄ (⊲-tr u₁ (⊲-tr u₂ (⊲-tr u₃ u₄)))
    (⊲-tr a₁ (⊲-tr u₂ (⊲-tr u₃ u₄)) ,ᵈ ⊲-tr a₂ (⊲-tr u₃ u₄))
    (⊲-tr a₃ u₄ ,ᵈ a₄) v₄ (fold i₁ i₂ i₃ i₄)
  where
  fold : ∀ {m₁ m₂ m₃ m₄} → (m₁ ≡ u) ⊎ (m₁ ≡ x₁) → (m₂ ≡ m₁) ⊎ (m₂ ≡ x₂) → (m₃ ≡ m₂) ⊎ (m₃ ≡ y₁) → (m₄ ≡ m₃) ⊎ (m₄ ≡ y₂) → Mis m₄ u x₁ x₂ y₁ y₂
  fold p q r (inj₂ s) = iy₂ s
  fold p q (inj₂ r) (inj₁ refl) = iy₁ r
  fold p (inj₂ q) (inj₁ refl) (inj₁ refl) = ix₂ q
  fold (inj₁ p) (inj₁ refl) (inj₁ refl) (inj₁ refl) = iu p
  fold (inj₂ p) (inj₁ refl) (inj₁ refl) (inj₁ refl) = ix₁ p

-- m 被对面的上界控制
ctrl : ∀ {m u x₁ x₂ y₁ y₂ m′ u′ x₁′ x₂′ y₁′ y₂′} → Mis m u x₁ x₂ y₁ y₂ → u′ ⊲ m′ → D⊲ x₁′ x₂′ m′ → D⊲ y₁′ y₂′ m′ →
       u ≈ᴬ u′ → D≈ x₁ x₂ x₁′ x₂′ → D≈ y₁ y₂ y₁′ y₂′ → Σ A (λ x′ → (x′ ⊲ m′) × (m ≈ᴬ x′))
ctrl {u′ = u′} (iu refl) p t a e f h = u′ , p , e
ctrl {x₁′ = z} (ix₁ refl) p t a e f h = z , d₁ t , e₁ f
ctrl {x₂′ = z} (ix₂ refl) p t a e f h = z , d₂ t , e₂ f
ctrl {y₁′ = z} (iy₁ refl) p t a e f h = z , d₁ a , e₁ h
ctrl {y₂′ = z} (iy₂ refl) p t a e f h = z , d₂ a , e₂ h

m≈ : ∀ {m u x₁ x₂ y₁ y₂ m′ u′ x₁′ x₂′ y₁′ y₂′} → Mis m u x₁ x₂ y₁ y₂ → Mis m′ u′ x₁′ x₂′ y₁′ y₂′ →
     u ⊲ m → D⊲ x₁ x₂ m → D⊲ y₁ y₂ m → u′ ⊲ m′ → D⊲ x₁′ x₂′ m′ → D⊲ y₁′ y₂′ m′ →
     u ≈ᴬ u′ → D≈ x₁ x₂ x₁′ x₂′ → D≈ y₁ y₂ y₁′ y₂′ → m ≈ᴬ m′
m≈ is is′ p₁ p₂ p₃ p₁′ p₂′ p₃′ e₁ e₂ e₃ with ctrl is p₁′ p₂′ p₃′ e₁ e₂ e₃ | ctrl is′ p₁ p₂ p₃ (≈ᴬ-sym e₁) (D≈-sym e₂) (D≈-sym e₃)
... | x′ , xp , xe | y , yp , ye = ≈ᴬ-sym (≈ᴬ-trans ye (anti yp xp (≈ᴬ-sym ye) xe))
```

## §4 加法

右边元素的层 $(p',b)$ 怎么放进左边的层 $(p,a)$: 同高度走第一位置, 低高度只要下标和路径自由的那一位在世界之下. `fw`, `bw`: 这两位.

```agda
data Rel : Ht → A → Ht → A → Set where
  sa : ∀ {p a b} → b ⊲ a → Rel p b p a
  lw : ∀ {h p b a} → h <ᴴ p → Rel h b p a

fw : ∀ {p′ b p a} → Rel p′ b p a → A
fw (sa P) = azero
fw (lw i) = fd i

bw : ∀ {p′ b p a} → Rel p′ b p a → A
bw (sa P) = azero
bw {b = b} (lw i) = b

-- 证据搬到 od 的路径
Dfd : ∀ {h₀ h₁ p k m} (j : h₀ <ᴴ h₁) (i : h₁ <ᴴ p) → D⊲ (fd j) k m → fd i ⊲ m → D⊲ (fd (<tr j i)) k m
Dfd j i e f = fd-tr j i (d₁ e) f ,ᵈ d₂ e

-- W + x: 左边不动, 世界是 max(u₀, u′, 两位). 与运行世界无关
add  : ∀ {p a p′ b u₀ u′} → 𝓞 p a u₀ → Gw u₀ → (R : Rel p′ b p a) → 𝓞 p′ b u′ → Gw u′ → ∀ v → Gw v → u₀ ⊲ v → u′ ⊲ v → D⊲ (fw R) (bw R) v → 𝓞 p a v
add⁰ : ∀ {p a p′ b u₀ u′} → 𝓞 p a u₀ → Gw u₀ → (R : Rel p′ b p a) → 𝓞 p′ b u′ → Gw u′ → ∀ m → Gw m → u₀ ⊲ m → u′ ⊲ m → D⊲ (fw R) (bw R) m → 𝓞 p a m
addL : ∀ {p a p′ h k u₀ u′} → 𝓞 p a u₀ → Gw u₀ → (t : h <ᴴ p) → (j : h <ᴴ p′) → Low p′ j k u′ → Gw u′ → ∀ m → Gw m → u₀ ⊲ m → u′ ⊲ m → D⊲ (fd t) k m → 𝓞 p a m

add W gu₀ R x gx v gv u₀v xv bv with mx gu₀ gv u₀v (Dzr xv) bv
... | mx′ m gm um tm am mv _ = ow mv gm (add⁰ W gu₀ R x gx m gm um (d₂ tm) am)

add⁰ W gu₀ R o0 gx m gm um tm am = ow um gu₀ W
add⁰ W gu₀ R (os x) gx m gm um tm am = os (add W gu₀ R x gx m gm um tm am)
add⁰ W gu₀ R (ol F) gx m gm um tm am = ol (λ n → add W gu₀ R (F n) gx m gm um tm am)
add⁰ W gu₀ (sa P) (oi r h) gx m gm um tm am =
  oi (≪∘ r P) (λ {v} q g y → add W gu₀ (sa P) (h (⊲-tr tm q) g (inS (≪S r) (outS (≪S (≪∘ r P)) y))) g v g (⊲-tr um q) C.self (Dz v))
add⁰ W gu₀ (lw i) (oi {k = k} r h) gx m gm um tm am =
  od i k (rd (d₁ am) (≪∘ r (d₂ am))) (λ {v} q g y → add W gu₀ (lw i) (h (⊲-tr tm q) g (inS (≪S r) (outL i y))) g v g (⊲-tr um q) C.self (D-tr am q))
add⁰ W gu₀ (sa P) (od j k r h) gx m gm um tm am =
  od j k (Rd-tr r tm) (λ {v} q g y → add W gu₀ (sa P) (h (⊲-tr tm q) g (inL j (outL j y))) g v g (⊲-tr um q) C.self (Dz v))
add⁰ W gu₀ (lw i) (od j k r h) gx m gm um tm am =
  od (<tr j i) k (rd (fd-tr j i (r₁ (Rd-tr r tm)) (d₁ am)) (r₂ (Rd-tr r tm))) (λ {v} q g y → add W gu₀ (lw i) (h (⊲-tr tm q) g (inL j (outL (<tr j i) y))) g v g (⊲-tr um q) C.self (D-tr am q))
add⁰ W gu₀ R (oc x h) gx m gm um tm am =
  oc (add W gu₀ R x gx m gm um tm am) (λ {v} q g → add W gu₀ R (h (⊲-tr tm q) g) g v g (⊲-tr um q) C.self (D-tr am q))
add⁰ W gu₀ (sa P) (oe es x) gx m gm um tm am = add W gu₀ (sa (⊲-tr (C.suc C.self) P)) x gx m gm um tm am
add⁰ W gu₀ (lw i) (oe es x) gx m gm um tm am = add W gu₀ (lw i) x gx m gm um tm (Dr (C.suc C.self) am)
add⁰ W gu₀ (sa P) (oe (el n) x) gx m gm um tm am = add W gu₀ (sa (⊲-tr (C.lim n C.self) P)) x gx m gm um tm am
add⁰ W gu₀ (lw i) (oe (el n) x) gx m gm um tm am = add W gu₀ (lw i) x gx m gm um tm (Dr (C.lim n C.self) am)
add⁰ W gu₀ (sa P) (oL j k e x) gx m gm um tm am = addL W gu₀ j j x gx m gm um tm (D-tr e tm)
add⁰ W gu₀ (lw i) (oL j k e x) gx m gm um tm am = addL W gu₀ (<tr j i) j x gx m gm um tm (Dfd j i (D-tr e tm) (d₁ am))
add⁰ W gu₀ R (ow p′ g′ x) gx m gm um tm am = add W gu₀ R x g′ m gm um (⊲-tr p′ tm) am

addL W gu₀ t hs0 (bx x) gx m gm um tm km = add W gu₀ (lw t) x gx m gm um tm km
addL W gu₀ t (hl0 n) (bx x) gx m gm um tm km = add W gu₀ (lw t) x gx m gm um tm km
addL W gu₀ t hr0 (bx x) gx m gm um tm km = add W gu₀ (lw t) x gx m gm um tm km
addL W gu₀ t (hsS j) x gx m gm um tm km = addL W gu₀ t j x gx m gm um tm km
addL W gu₀ t (hlS n j) x gx m gm um tm km = addL W gu₀ t j x gx m gm um tm km
addL W gu₀ t (hrS j) x gx m gm um tm km = addL W gu₀ t j x gx m gm um tm km

rep : ∀ {p a u} → 𝓞 p a u → Gw u → ℕ → 𝓞 p a u
rep y g zero = o0
rep y g (suc zero) = y
rep {u = u} y g (suc (suc m)) = add (rep y g (suc m)) g (sa C.self) y g u g C.self C.self (Dz u)

chainᵒ : ∀ {p k u} → Gw u → (𝓞 p k u → 𝓞 p k u) → ℕ → 𝓞 p k u
chainᵒ {p} {k} g f zero = Ω̇at p k g
chainᵒ g f (suc n) = f (chainᵒ g f n)
```

## §5 第 0 层

```agda
H₀ : Ht
H₀ = ⟨ zero , azero ⟩

em : ∀ {u} → Ord₀ → 𝓞 H₀ azero u
em FL.zero = o0
em (FL.suc a) = os (em a)
em (FL.lim f) = ol (λ n → em (f n))
em (FL.limᵢ () f)
em (FL.up () x)
```
