# 不累加的下标: 字面化

> 不含记号. `rd`: 第 0 层的树逐点读成下标, 不累加. 上一轮的 `no-rd`, `no-HS→Lgl` 说这个读出对 `HS` 树不一定字面合法. 这里的定理说: **对字面第一位置模 $\cong$ 的树 (`Lit₀`, 比 `HS` 强), 有一个逐点 $\approx$ 于读出的字面合法的副本** (`lit`), 而且可以指定它以另一个副本为第一位置 (`graft₀`).
>
> - 副本与 `rd y` 只差逐点相等的函数, 所以基本列的每一项值都相同: **没有前缀, 没有累加, 没有 $+1$.**
> - 不用函数外延, 不搬运层. 办法是嫁接: 把 $P$ 接到 $y$ 的第一位置 $x$ 上 ($P\approx x$), 极限 $K$ 在 $x\triangleleft K_n$ 处, 第 $n$ 项换成嫁接的结果, 第 $n+1$ 项往上逐项重新嫁接 (`Lg` 给了第一位置), 第 $n$ 项往下逐项取投影 (`proj`).
> - **代价: 要证据.** `lit` 读 `Lit₀ y`. 这与 `toLevel` 读 `HS` 同类, 定义依赖证书.
>
> 全文 `--safe --without-K --lossy-unification`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NoCumLit where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
import OCF.Free.Level as FL
open FL using (Ordᶜ; _≅_; z≅; s≅; l≅; lᵢ≅; upˡ; upʳ; _⊑⁰_; ≺s; ≺l; ≅→⊑; HS; hz; hs; hl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; lg⊲)
import OCF.Align.CumReadCF as C

Ord₀ : Set
Ord₀ = Ordᶜ FL.zero
```

## §1 结构等价, 投影

```agda
infix 4 _≈ᴬ_
data _≈ᴬ_ : A → A → Set where
  z≈ : azero ≈ᴬ azero
  s≈ : ∀ {a b} → a ≈ᴬ b → asuc a ≈ᴬ asuc b
  l≈ : ∀ {f g} → (∀ n → f n ≈ᴬ g n) → alim f ≈ᴬ alim g

≈ᴬ-refl : ∀ a → a ≈ᴬ a
≈ᴬ-refl azero = z≈
≈ᴬ-refl (asuc a) = s≈ (≈ᴬ-refl a)
≈ᴬ-refl (alim f) = l≈ (λ n → ≈ᴬ-refl (f n))

≈ᴬ-sym : ∀ {a b} → a ≈ᴬ b → b ≈ᴬ a
≈ᴬ-sym z≈ = z≈
≈ᴬ-sym (s≈ e) = s≈ (≈ᴬ-sym e)
≈ᴬ-sym (l≈ h) = l≈ (λ n → ≈ᴬ-sym (h n))

≈ᴬ-trans : ∀ {a b c} → a ≈ᴬ b → b ≈ᴬ c → a ≈ᴬ c
≈ᴬ-trans z≈ z≈ = z≈
≈ᴬ-trans (s≈ e) (s≈ d) = s≈ (≈ᴬ-trans e d)
≈ᴬ-trans (l≈ h) (l≈ k) = l≈ (λ n → ≈ᴬ-trans (h n) (k n))

record Pj (x g : A) : Set where
  constructor pj
  field
    p  : A
    pe : p ≈ᴬ x
    pa : p ⊲ g
open Pj public

proj : ∀ {x y g} → x ⊲ y → g ≈ᴬ y → Pj x g
proj {g = g} C.self e = pj g e C.self
proj (C.suc q) (s≈ e) = let r = proj q e in pj (p r) (pe r) (C.suc (pa r))
proj (C.lim n q) (l≈ h) = let r = proj q (h n) in pj (p r) (pe r) (C.lim n (pa r))
```

## §2 嫁接

```agda
record El (y : A) : Set where
  constructor el
  field
    g  : A
    eq : g ≈ᴬ y
    lg : Lg g
open El public

record Gr (y P : A) : Set where
  constructor gr
  field
    gE : El y
    at : P ⊲ g gE
open Gr public

record Sq (K : ℕ → A) (f : ℕ → ℕ) (P : A) (n : ℕ) : Set where
  field
    G   : ℕ → A
    eqG : ∀ m → G m ≈ᴬ K (f m)
    lgG : ∀ m → Lg (G m)
    stG : ∀ m → G m ⊲ G (suc m)
    atG : P ⊲ G n
open Sq

graftA : ∀ y {x} → x ⊲ y → Lg y → (P : A) → Lg P → P ≈ᴬ x → Gr y P
graftAt : (K : ℕ → A) (f : ℕ → ℕ) (n : ℕ) → (∀ m → K (f m) ⊲ K (f (suc m))) → (∀ m → Lg (K (f m))) →
          ∀ {x} → x ⊲ K (f n) → (P : A) → Lg P → P ≈ᴬ x → Sq K f P n

graftA y C.self wy P wP e = gr (el P e wP) C.self
graftA (asuc y) (C.suc q) w P wP e =
  let r = graftA y q w P wP e in gr (el (asuc (g (gE r))) (s≈ (eq (gE r))) (lg (gE r))) (C.suc (at r))
graftA (alim K) (C.lim n q) (st , w) P wP e =
  let r = graftAt K (λ m → m) n st w q P wP e in
  gr (el (alim (G r)) (l≈ (eqG r)) (stG r , lgG r)) (C.lim n (atG r))

graftAt K f zero st w {x} q P wP e = record { G = λ m → g (U m) ; eqG = λ m → eq (U m) ; lgG = λ m → lg (U m) ; stG = step ; atG = at r₀ }
  where
  r₀ = graftA (K (f 0)) q (w 0) P wP e
  U : ∀ m → El (K (f m))
  U zero = gE r₀
  U (suc m) = gE (graftA (K (f (suc m))) (st m) (w (suc m)) (g (U m)) (lg (U m)) (eq (U m)))
  step : ∀ m → g (U m) ⊲ g (U (suc m))
  step m = at (graftA (K (f (suc m))) (st m) (w (suc m)) (g (U m)) (lg (U m)) (eq (U m)))
graftAt K f (suc n) st w q P wP e = record { G = G′ ; eqG = eq′ ; lgG = lg′ ; stG = st′ ; atG = atG r }
  where
  r = graftAt K (λ m → f (suc m)) n (λ m → st (suc m)) (λ m → w (suc m)) q P wP e
  b = proj (st 0) (eqG r 0)
  G′ : ℕ → A
  G′ zero = p b
  G′ (suc m) = G r m
  eq′ : ∀ m → G′ m ≈ᴬ K (f m)
  eq′ zero = pe b
  eq′ (suc m) = eqG r m
  lg′ : ∀ m → Lg (G′ m)
  lg′ zero = lg⊲ (pa b) (lgG r 0)
  lg′ (suc m) = lgG r m
  st′ : ∀ m → G′ m ⊲ G′ (suc m)
  st′ zero = pa b
  st′ (suc m) = stG r m
```

## §3 字面第一位置模 $\cong$

```agda
data _⊴₀_ : Ord₀ → Ord₀ → Set where
  r0 : ∀ {a b} → a ≅ b → a ⊴₀ b
  s0 : ∀ {a b} → a ⊴₀ b → a ⊴₀ FL.suc b
  l0 : ∀ {a f} n → a ⊴₀ f n → a ⊴₀ FL.lim f

⊴₀→⊑⁰ : ∀ {a b} → a ⊴₀ b → a ⊑⁰ b
⊴₀→⊑⁰ (r0 e) = ≅→⊑ e
⊴₀→⊑⁰ (s0 d) c = ≺s (⊴₀→⊑⁰ d c)
⊴₀→⊑⁰ (l0 n d) c = ≺l n (⊴₀→⊑⁰ d c)

Lit₀ : Ord₀ → Set
Lit₀ FL.zero = ⊤
Lit₀ (FL.suc a) = Lit₀ a
Lit₀ (FL.lim f) = (∀ n → f n ⊴₀ f (suc n)) × (∀ n → Lit₀ (f n))
Lit₀ (FL.limᵢ () f)
Lit₀ (FL.up () x)

HS₀ : ∀ a → Lit₀ a → HS a
HS₀ FL.zero u = hz
HS₀ (FL.suc a) u = hs (HS₀ a u)
HS₀ (FL.lim f) (st , u) = hl (λ n → HS₀ (f n) (u n)) (λ n → ⊴₀→⊑⁰ (st n))
HS₀ (FL.limᵢ () f) u
HS₀ (FL.up () x) u

rd : Ord₀ → A
rd FL.zero = azero
rd (FL.suc a) = asuc (rd a)
rd (FL.lim f) = alim (λ n → rd (f n))
rd (FL.limᵢ () f)
rd (FL.up () x)

≅→≈ : ∀ {a b : Ord₀} → a ≅ b → rd a ≈ᴬ rd b
≅→≈ z≅ = z≈
≅→≈ (s≅ e) = s≈ (≅→≈ e)
≅→≈ (l≅ h) = l≈ (λ n → ≅→≈ (h n))
≅→≈ (lᵢ≅ {p = ()} e h)
≅→≈ (upˡ {r = ()} e)
≅→≈ (upʳ {r = ()} e)

tr⊴ : ∀ {a b g} → a ⊴₀ b → g ≈ᴬ rd b → Pj (rd a) g
tr⊴ {g = g} (r0 e) d = pj g (≈ᴬ-trans d (≈ᴬ-sym (≅→≈ e))) C.self
tr⊴ (s0 x) (s≈ d) = let r = tr⊴ x d in pj (p r) (pe r) (C.suc (pa r))
tr⊴ (l0 n x) (l≈ h) = let r = tr⊴ x (h n) in pj (p r) (pe r) (C.lim n (pa r))

-- 把 P 接到 G 上: 结果 ≈ rd b, 以 P 为第一位置
graft₀ : ∀ {a b} → a ⊴₀ b → El (rd b) → (P : El (rd a)) → Gr (rd b) (g P)
graft₀ d G P =
  let r = tr⊴ d (eq G)
      s = graftA (g G) (pa r) (lg G) (g P) (lg P) (≈ᴬ-trans (eq P) (≈ᴬ-sym (pe r)))
  in gr (el (g (gE s)) (≈ᴬ-trans (eq (gE s)) (eq G)) (lg (gE s))) (at s)

lit : ∀ y → Lit₀ y → El (rd y)
lit FL.zero u = el azero z≈ tt
lit (FL.suc a) u = let r = lit a u in el (asuc (g r)) (s≈ (eq r)) (lg r)
lit (FL.lim f) (st , u) = el (alim (λ n → g (F n))) (l≈ (λ n → eq (F n))) ((λ n → at (Fs n)) , (λ n → lg (F n)))
  where
  F  : ∀ n → El (rd (f n))
  Fs : ∀ n → Gr (rd (f (suc n))) (g (F n))
  F zero = lit (f 0) (u 0)
  F (suc n) = gE (Fs n)
  Fs n = graft₀ (st n) (lit (f (suc n)) (u (suc n))) (F n)
lit (FL.limᵢ () f) u
lit (FL.up () x) u
```
