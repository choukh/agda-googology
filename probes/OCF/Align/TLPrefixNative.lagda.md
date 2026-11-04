# 前缀 (五): 合法性做进定义, 到哪一步

> 入口 [TLPrefix](TLPrefix.lagda.md). **判决: PARTIAL.** 不含记号, 不读证书. 这是作者的理想形态的探针: 不累加, 没有单独的合法性证明, 证据就在树的 `lim` 里.
>
> **编译过的.**
>
> - `A`, `_⊲_`: 下标的极限自带字面第一位置, 没有 `Lg`. `from`, `Lg-from`: 读成带 `Lg` 的下标.
> - `Str`, `O`: 数据树分层定义, `ol` 带 `⊴`, `oi` 带分支单调和分支同余. 过了正性和停机检查. 朴素的写法过不了, 报错在 [TLPrefix](TLPrefix.lagda.md).
> - `Ω̇`, `Ω⊴`, `Ω≈`: 证据和树一起造, 互递归. `Ω̇ (alim f st)` 的步进就是 `Ω⊴ (st n)`. 对照 `Certified.Ω-not-step`: 那里相邻两项不 `⊑`, 这里是 `⊴`, 不是同一个关系.
> - `ord`, `HS-ord`: **第 0 层的 `HS` 不要 `WF`.** 证据就在 `ol` 里.
>
> **没有的: 折叠 `ψ`.** 骨架的停机报错在 [TLPrefix](TLPrefix.lagda.md). 未走通, 不是否定.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLPrefixNative where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
import OCF.Free.Level as FL
open FL using (HS; hz; hs; hl; _⊑⁰_; _≅_; ≺s; ≺l; z≅; s≅; l≅; ≅→⊑; Ordᶜ)
import OCF.Align.CumReadCF as C
```

## §1 下标

```agda
data A : Set
data _⊲_ : A → A → Set
data A where
  azero : A
  asuc  : A → A
  alim  : (f : ℕ → A) → (∀ n → f n ⊲ f (suc n)) → A
data _⊲_ where
  self : ∀ {a} → a ⊲ a
  suc  : ∀ {a b} → a ⊲ b → a ⊲ asuc b
  lim  : ∀ {a f s} n → a ⊲ f n → a ⊲ alim f s

data _≪_ : A → A → Set where
  zero : ∀ {a} → a ≪ asuc a
  suc  : ∀ {a b} → a ≪ b → a ≪ asuc b
  lim  : ∀ {a f s} n → a ≪ f n → a ≪ alim f s

data Strict (a : A) : A → Set where
  ss : ∀ {b} → a ⊲ b → Strict a (asuc b)
  sl : ∀ {f st} n → a ⊲ f n → Strict a (alim f st)

≪⊲ : ∀ {a b} → a ≪ b → a ⊲ b
≪⊲ zero = suc self
≪⊲ (suc r) = suc (≪⊲ r)
≪⊲ (lim n r) = lim n (≪⊲ r)

≪S : ∀ {a b} → a ≪ b → Strict a b
≪S zero = ss self
≪S (suc r) = ss (≪⊲ r)
≪S (lim n r) = sl n (≪⊲ r)

```

## §2 分层的数据树

证据的关系是参数, 所以正性检查只看到参数, 看不到低层的 `O` 在箭头左边.

```agda
module Str (L : A) (V : ∀ {a} → Strict a L → Set)
  (Ωv : ∀ {k} (r : k ≪ L) → V (≪S r))
  (LeV : ∀ {a b} (R : Strict a L) (R′ : Strict b L) → V R → V R′ → Set)
  (EqV : ∀ {a b} (R : Strict a L) (R′ : Strict b L) → V R → V R′ → Set) where
  data O₊ : Set
  data _⊴₊_ : O₊ → O₊ → Set
  _≈₊_ : O₊ → O₊ → Set
  data O₊ where
    o0 : O₊
    os : O₊ → O₊
    ol : (F : ℕ → O₊) → (∀ n → F n ⊴₊ F (suc n)) → O₊
    oi : ∀ {k} (r : k ≪ L) (h : V (≪S r) → O₊) →
         (∀ y y′ → LeV (≪S r) (≪S r) y y′ → h y ⊴₊ h y′) → (∀ y y′ → EqV (≪S r) (≪S r) y y′ → h y ≈₊ h y′) → O₊
    oe : ∀ {a} (R : Strict a L) → V R → O₊
  data _⊴₊_ where
    rf : ∀ {x y} → x ≈₊ y → x ⊴₊ y
    s  : ∀ {x y} → x ⊴₊ y → x ⊴₊ os y
    l  : ∀ {x F st} n → x ⊴₊ F n → x ⊴₊ ol F st
    nd : ∀ {x k} {r : k ≪ L} {h m c} → x ⊴₊ h (Ωv r) → x ⊴₊ oi r h m c
    ee : ∀ {a b} {R : Strict a L} {R′ : Strict b L} {x x′} → LeV R R′ x x′ → oe R x ⊴₊ oe R′ x′
  o0 ≈₊ o0 = ⊤
  os x ≈₊ os y = x ≈₊ y
  ol F _ ≈₊ ol G _ = ∀ n → F n ≈₊ G n
  oi {k = k} r h _ _ ≈₊ oi {k = k′} r′ h′ _ _ = (k ≡ k′) × (∀ y y′ → EqV (≪S r) (≪S r′) y y′ → h y ≈₊ h′ y′)
  oe R x ≈₊ oe R′ x′ = EqV R R′ x x′
  _ ≈₊ _ = ⊥
open Str using (o0; os; ol; oi; oe; rf; s; l; nd; ee)

```

## §3 层, 关系, $\Omega$

```agda
O : A → Set
Vs : ∀ L {a} → Strict a L → Set
Vc : ∀ b {a} → a ⊲ b → Set
Ωvs : ∀ L {k} (r : k ≪ L) → Vs L (≪S r)
Ωvc : ∀ b {k} (P : k ⊲ b) → Vc b P
LeS : ∀ L {a b} (R : Strict a L) (R′ : Strict b L) → Vs L R → Vs L R′ → Set
EqS : ∀ L {a b} (R : Strict a L) (R′ : Strict b L) → Vs L R → Vs L R′ → Set
LeR : ∀ L {b} (R′ : Strict b L) {a} → O a → Vs L R′ → Set
LeC : ∀ c {b} (P : b ⊲ c) {a} → O a → Vc c P → Set
EqR : ∀ L {b} (R′ : Strict b L) {a} → O a → Vs L R′ → Set
EqC : ∀ c {b} (P : b ⊲ c) {a} → O a → Vc c P → Set
Ω̇ : ∀ L → O L
_⊴_ : ∀ {L} → O L → O L → Set
_≈_ : ∀ {L} → O L → O L → Set
outS : ∀ {b a} (R : Strict a b) → Vs b R → O a
outC : ∀ {b a} (P : a ⊲ b) → Vc b P → O a
inS : ∀ {b a} (R : Strict a b) → O a → Vs b R
inC : ∀ {b a} (P : a ⊲ b) → O a → Vc b P
upP : ∀ {a b} → a ⊲ b → O a → O b
Ω⊴ : ∀ {a b} (P : a ⊲ b) → upP P (Ω̇ a) ⊴ Ω̇ b
Ω≈ : ∀ a → Ω̇ a ≈ Ω̇ a
out-inC : ∀ {b a} (P : a ⊲ b) (x : O a) → outC P (inC P x) ≡ x

O L = Str.O₊ L (Vs L) (Ωvs L) (LeS L) (EqS L)
_⊴_ {L} = Str._⊴₊_ L (Vs L) (Ωvs L) (LeS L) (EqS L)
_≈_ {L} = Str._≈₊_ L (Vs L) (Ωvs L) (LeS L) (EqS L)
Vs (asuc b) (ss P) = Vc b P
Vs (alim f st) (sl n P) = Vc (f n) P
Vc a self = O a
Vc (asuc b) (suc P) = Vc b P
Vc (alim f st) (lim n P) = Vc (f n) P
Ωvs (asuc b) {k} zero = Ω̇ b
Ωvs (asuc b) (suc r) = Ωvc b (≪⊲ r)
Ωvs (alim f st) (lim n r) = Ωvc (f n) (≪⊲ r)
Ωvc a self = Ω̇ a
Ωvc (asuc b) (suc P) = Ωvc b P
Ωvc (alim f st) (lim n P) = Ωvc (f n) P
outC self x = x
outC (suc P) x = outC P x
outC (lim n P) x = outC P x
inC self x = x
inC (suc P) x = inC P x
inC (lim n P) x = inC P x
outS (ss P) x = outC P x
outS (sl n P) x = outC P x
inS (ss P) x = inC P x
inS (sl n P) x = inC P x
out-inC self x = refl
out-inC (suc P) x = out-inC P x
out-inC (lim n P) x = out-inC P x
upP self x = x
upP (suc P) x = oe (ss P) (inC P x)
upP (lim n P) x = oe (sl n P) (inC P x)
LeS L R R′ x x′ = LeR L R′ (outS R x) x′
EqS L R R′ x x′ = EqR L R′ (outS R x) x′
LeR (asuc c) (ss P) x x′ = LeC c P x x′
LeR (alim f st) (sl n P) x x′ = LeC (f n) P x x′
LeC c {b = b} self {a = a} x x′ = Σ (a ⊲ b) λ P → upP P x ⊴ x′
LeC (asuc c) (suc P) x x′ = LeC c P x x′
LeC (alim f st) (lim n P) x x′ = LeC (f n) P x x′
EqR (asuc c) (ss P) x x′ = EqC c P x x′
EqR (alim f st) (sl n P) x x′ = EqC (f n) P x x′
EqC c {b = b} self {a = a} x x′ = Σ (a ⊲ b) λ P → upP P x ≈ x′
EqC (asuc c) (suc P) x x′ = EqC c P x x′
EqC (alim f st) (lim n P) x x′ = EqC (f n) P x x′
Ω̇ azero = os o0
Ω̇ (asuc a) = oi zero (λ z → oe (ss self) z) (λ y y′ d → ee d) (λ y y′ d → d)
Ω̇ (alim f st) = ol (λ n → oe (sl n self) (Ω̇ (f n))) (λ n → ee (st n , Ω⊴ (st n)))
Ω⊴ {a} self = rf (Ω≈ a)
Ω⊴ {a} (suc {b = b} P) = nd (ee (P , subst (λ z → upP P z ⊴ Ω̇ b) (sym (out-inC P (Ω̇ a))) (Ω⊴ P)))
Ω⊴ {a} (lim {f = f} n P) = l n (ee (P , subst (λ z → upP P z ⊴ Ω̇ (f n)) (sym (out-inC P (Ω̇ a))) (Ω⊴ P)))
Ω≈ azero = tt
Ω≈ (asuc a) = refl , (λ y y′ d → d)
Ω≈ (alim f st) = λ n → self , Ω≈ (f n)

```

## §4 第 0 层: 合法由定义保证

`O azero` 只有 `o0`, `os`, `ol`. 它就是证据在 `lim` 里的第 0 层树.

```agda
Ord₀ : Set
Ord₀ = Ordᶜ FL.zero

ord : O azero → Ord₀
ord o0 = FL.zero
ord (os x) = FL.suc (ord x)
ord (ol F st) = FL.lim (λ n → ord (F n))
ord (oi () h m c)
ord (oe () x)

≈→≅ : (x y : O azero) → x ≈ y → ord x ≅ ord y
≈→≅ o0 o0 e = z≅
≈→≅ (os x) (os y) e = s≅ (≈→≅ x y e)
≈→≅ (ol F st) (ol G st′) e = l≅ (λ n → ≈→≅ (F n) (G n) (e n))
≈→≅ (oi () h m c) y e
≈→≅ (oe () x) y e
≈→≅ o0 (oi () h m c) e
≈→≅ o0 (oe () y) e
≈→≅ (os x) (oi () h m c) e
≈→≅ (os x) (oe () y) e
≈→≅ (ol F st) (oi () h m c) e
≈→≅ (ol F st) (oe () y) e

⊴→⊑⁰ : {x y : O azero} → x ⊴ y → ord x ⊑⁰ ord y
⊴→⊑⁰ {x} {y} (rf e) = ≅→⊑ (≈→≅ x y e)
⊴→⊑⁰ (s d) c = ≺s (⊴→⊑⁰ d c)
⊴→⊑⁰ (l n d) c = ≺l n (⊴→⊑⁰ d c)
⊴→⊑⁰ (nd {r = ()} d)
⊴→⊑⁰ (ee {R = ()} d)

-- 没有 WF: 证据就在树里
HS-ord : (x : O azero) → HS (ord x)
HS-ord o0 = hz
HS-ord (os x) = hs (HS-ord x)
HS-ord (ol F st) = hl (λ n → HS-ord (F n)) (λ n → ⊴→⊑⁰ (st n))
HS-ord (oi () h m c)
HS-ord (oe () x)
```

## §5 读成带 `Lg` 的下标

```agda
from : A → C.A
from⊲ : ∀ {a b} → a ⊲ b → from a C.⊲ from b
from azero = C.azero
from (asuc a) = C.asuc (from a)
from (alim f st) = C.alim (λ n → from (f n))
from⊲ self = C.self
from⊲ (suc P) = C.suc (from⊲ P)
from⊲ (lim n P) = C.lim n (from⊲ P)

Lg-from : ∀ a → C.Lg (from a)
Lg-from azero = tt
Lg-from (asuc a) = Lg-from a
Lg-from (alim f st) = (λ n → from⊲ (st n)) , (λ n → Lg-from (f n))
```
