# 层号判决的范数模: 规整树的走步定理 (不含记号)

> 底座, 结论在 [InaccModulus](InaccModulus.lagda.md). 本文件的导入链不含 `OCF.Align.EBO`. **`mod`, `Dᵐ`, `Fam`, `famReg`, `tri` 都只提树.**

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.InaccModulusBase where

open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; s≤s; z≤n; _⊔_; _≤′_; ≤′-refl; ≤′-step; _≤?_)
open import Data.Nat.Properties using (≤⇒≤′; ≤-trans; ≤-refl; <-trans; m≤m⊔n; m≤n⊔m; m≤n⇒m≤1+n; n≮n; <⇒≤; ≰⇒>)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Data.Maybe using (just)
open import OCF.Align.InaccTreeBase hiding (eq)
open import OCF.Align.InaccStrikeBase using (Funext; into-out; strip)
```

## §1 走步、节点与规整类

`wk x` 沿分支 1 一直走到 0 的步数. `Nd y x`: `y` **字面上**是 `x` 的前驱节点. `W y x`: `y` 在 `x` 的 1-走步上, 且严格 (至少走一步). `Reg x`: `x` 不含 `limᴼ`, 每个 `lim h` 节点满足 `h n` 在 `h (n+1)` 的 1-走步上. `Reg` 只提树, 不提记号.

选分支 1 而不是分支 0 不是任意的: EBO 的规则 `ψ_u(b+1)[n] = ψ_u(b)·n` 在 `n = 0` 处给 0, 0-走步把 `b` 整个丢掉, 走步长度读不出任何东西.

```agda
wk : Lv → ℕ
wk zero       = 0
wk (suc a)    = suc (wk a)
wk (lim f)    = suc (wk (f 1))
wk (limᴼ k g) = 0

Nd : Lv → Lv → Set
Nd y x = Σ (Pre x) λ r → at x r ≡ y

data W (y : Lv) : Lv → Set where
  ws0 : W y (suc y)
  ws  : ∀ {a} → W y a → W y (suc a)
  wl0 : ∀ {f} → f 1 ≡ y → W y (lim f)
  wl  : ∀ {f} → W y (f 1) → W y (lim f)

Reg : Lv → Set
Reg zero       = ⊤
Reg (suc a)    = Reg a
Reg (lim h)    = (∀ n → W (h n) (h (suc n))) × (∀ n → Reg (h n))
Reg (limᴼ _ _) = ⊥
```

## §2 基本引理

```agda
Nd-trans : ∀ {z y x} → Nd y x → Nd z y → Nd z x
Nd-trans {x = x} (r , refl) (s , e) with comp x r s
... | t , q = t , trans q e

W-trans : ∀ {z y x} → W y x → W z y → W z x
W-trans ws0     v = ws v
W-trans (ws w)  v = ws (W-trans w v)
W-trans (wl0 refl) v = wl v
W-trans (wl w)  v = wl (W-trans w v)

W-Nd : ∀ {y x} → Reg x → W y x → Nd y x
W-Nd _ ws0    = inj₁ tt , refl
W-Nd r (ws w) with W-Nd r w
... | s , e = inj₂ s , e
W-Nd {x = lim h} (st , rg) (wl0 refl) with W-Nd (rg 2) (st 1)
... | s , e = (2 , s) , e
W-Nd {x = lim h} (st , rg) (wl w) with Nd-trans (W-Nd (rg 2) (st 1)) (W-Nd (rg 1) w)
... | s , e = (2 , s) , e

wk-< : ∀ {y x} → W y x → wk y < wk x
wk-< ws0        = ≤-refl
wk-< (ws w)     = m≤n⇒m≤1+n (wk-< w)
wk-< (wl0 refl) = ≤-refl
wk-< (wl w)     = m≤n⇒m≤1+n (wk-< w)

module Chain {h : ℕ → Lv} (st : ∀ n → W (h n) (h (suc n))) where
  W-lt′ : ∀ {m n} → suc m ≤′ n → W (h m) (h n)
  W-lt′ ≤′-refl     = st _
  W-lt′ (≤′-step p) = W-trans (st _) (W-lt′ p)

  W-lt : ∀ {m n} → m < n → W (h m) (h n)
  W-lt p = W-lt′ (≤⇒≤′ p)

  wk-grow : ∀ n → n ≤ wk (h n)
  wk-grow zero    = z≤n
  wk-grow (suc n) = ≤-trans (s≤s (wk-grow n)) (wk-< (st n))
```

## §3 线性: 走步上的点把节点分成两边

`lin`: `y` 在 `a` 的走步上 (或就是 `a`), `x` 是 `a` 的节点, 则 `x` 等于 `y`, 或在 `y` 之下, 或 `y` 在 `x` 的走步上. 证明对 `a` 递归, 没有用任何算术: 这是整个判决的核心, 也是为什么 "规整" 比 "单调" 强.

```agda
lin : ∀ a → Reg a → ∀ {x y} → (y ≡ a ⊎ W y a) → Nd x a → (x ≡ y) ⊎ (Nd x y ⊎ W y x)
lin zero _ _ (() , _)
lin (suc b) r (inj₁ refl) n = inj₂ (inj₁ n)
lin (suc b) r (inj₂ ws0)     (inj₁ _ , e) = inj₁ (sym e)
lin (suc b) r (inj₂ ws0)     (inj₂ s , e) = inj₂ (inj₁ (s , e))
lin (suc b) r (inj₂ (ws w))  (inj₁ _ , refl) = inj₂ (inj₂ w)
lin (suc b) r (inj₂ (ws w))  (inj₂ s , e) = lin b r (inj₂ w) (s , e)
lin (lim h) r (inj₁ refl) n = inj₂ (inj₁ n)
lin (lim h) (st , rg) {x} {y} (inj₂ w) ((m , s) , e) = lin (h (suc (suc m))) (rg _) (inj₂ wy) nd
  where
    open Chain st
    1<t : 1 < suc (suc m)
    1<t = s≤s (s≤s z≤n)
    wy′ : W y (lim h) → W y (h (suc (suc m)))
    wy′ (wl0 refl) = W-lt 1<t
    wy′ (wl v)     = W-trans (W-lt 1<t) v
    wy : W y (h (suc (suc m)))
    wy = wy′ w
    nd : Nd x (h (suc (suc m)))
    nd = Nd-trans (W-Nd (rg _) (W-lt (m≤n⇒m≤1+n ≤-refl))) (s , e)
lin (limᴼ k g) () _ _
```

## §4 模定理

**`mod`: 在 `Reg` 的 `lim h` 上, `j` 若是某个 `h m` 的节点, 就是 `h (1 + wk j)` 的节点.** 模只由 `j` 的树读出, 与目标无关. 证明: 取 `m > 1 + wk j`, 对 `h m` 与走步点 `h (m-1)` 用 `lin`. `j` 若等于 `h (m-1)` 或 `h (m-1)` 在 `j` 的走步上, 都给出 `m-1 ≤ wk j`, 矛盾; 只剩 `j` 在 `h (m-1)` 之下, 下降.

```agda
module Mod {h : ℕ → Lv} (st : ∀ n → W (h n) (h (suc n))) (rg : ∀ n → Reg (h n)) where
  open Chain st

  Nd-up : ∀ {j m n} → m < n → Nd j (h m) → Nd j (h n)
  Nd-up p q = Nd-trans (W-Nd (rg _) (W-lt p)) q

  Nd-up≤ : ∀ {j m n} → m ≤ n → Nd j (h m) → Nd j (h n)
  Nd-up≤ {m = m} {n} p q with ≤⇒≤′ p
  ... | ≤′-refl   = q
  ... | ≤′-step r = Nd-up (s≤s (≤′⇒≤ r)) q
    where
      ≤′⇒≤ : ∀ {a b} → a ≤′ b → a ≤ b
      ≤′⇒≤ ≤′-refl     = ≤-refl
      ≤′⇒≤ (≤′-step r) = m≤n⇒m≤1+n (≤′⇒≤ r)

  mod : ∀ {j} m → Nd j (h m) → Nd j (h (suc (wk j)))
  mod zero    q = Nd-up≤ z≤n q
  mod {j} (suc m) q with suc m ≤? suc (wk j)
  ... | yes p = Nd-up≤ p q
  ... | no ¬p = go (lin (h (suc m)) (rg _) (inj₂ (st m)) q)
    where
      big : suc (wk j) ≤ m
      big with ≰⇒> ¬p
      ... | s≤s r = r
      go : (j ≡ h m) ⊎ (Nd j (h m) ⊎ W (h m) j) → Nd j (h (suc (wk j)))
      go (inj₁ refl)        = ⊥-elim (n≮n _ (≤-trans big (wk-grow m)))
      go (inj₂ (inj₁ q′))   = mod m q′
      go (inj₂ (inj₂ w))    = ⊥-elim (n≮n _ (≤-trans (≤-trans big (wk-grow m)) (<⇒≤ (wk-< w))))
```

## §5 判决 `Dᵐ`

`samᵐ` 与 `Dm` 都只走**一条**路径, 不搜索. `samᵐ` 在 `lim` 上取 `1 + wk a ⊔ wk b` 这一个分支. `Dm μ j` 在 `lim` 目标上进 `h μ`, `μ = 1 + wk j` 全程不变. 它们是 `Lv` 上的总函数; `limᴼ` 目标一律答 `rise`, 只对可数段声称正确.

```agda
samᵐ : Lv → Lv → Bool
samᵐ zero    zero    = true
samᵐ (suc a) (suc b) = samᵐ a b
samᵐ (lim f) (lim h) = samᵐ (f (suc (wk (lim f) ⊔ wk (lim h)))) (h (suc (wk (lim f) ⊔ wk (lim h))))
samᵐ _       _       = false

svᵐ : ∀ j i → Bool → Verdict j i → Verdict j (suc i)
svᵐ j i true  V         = pen (inj₁ tt) (cast i j)
svᵐ j i false (pen r b) = pen (inj₂ r) b
svᵐ j i false rise      = rise

lvᵐ : ∀ μ j (h : ℕ → Lv) → Verdict j (h μ) → Verdict j (lim h)
lvᵐ μ j h (pen r b) = pen (μ , r) b
lvᵐ μ j h rise      = rise

Dm : ℕ → (j i : Lv) → Verdict j i
Dm μ j zero       = rise
Dm μ j (suc i)    = svᵐ j i (samᵐ j i) (Dm μ j i)
Dm μ j (lim h)    = lvᵐ μ j h (Dm μ j (h μ))
Dm μ j (limᴼ k g) = rise

Dᵐ : Oracle
Dᵐ j i = Dm (suc (wk j)) j i
```

## §6 规整族 `Fam`: 判决正确所需的全部性质

`Fam F` 是树的性质: 类 `F` 对子树封闭, 不含 `limᴼ`, `lim h` 的项一个是下一个的节点, 且 `F` 内的节点落在 `h (1 + wk j)` 之下. **判决的正确性只用这五条.** `famReg` 说 `Reg` 是一个 `Fam`: 走步条件推出模 (`mod`).

```agda
record Fam (F : Lv → Set) : Set where
  field
    f-suc  : ∀ {a} → F (suc a) → F a
    f-lim  : ∀ {h} → F (lim h) → ∀ n → F (h n)
    f-no   : ∀ {k g} → F (limᴼ k g) → ⊥
    f-step : ∀ {h} → F (lim h) → ∀ n → Nd (h n) (h (suc n))
    f-mod  : ∀ {j h} → F j → F (lim h) → Nd j (lim h) → Nd j (h (suc (wk j)))

famReg : Fam Reg
famReg = record
  { f-suc  = λ r → r
  ; f-lim  = λ (_ , rg) n → rg n
  ; f-no   = λ ()
  ; f-step = λ (st , rg) n → W-Nd (rg _) (st n)
  ; f-mod  = λ { _ (st , rg) ((m , s) , e) → Mod.mod st rg m (s , e) }
  }

record PenOK {j i} (V : Verdict j i) : Set where
  field
    rr : Pre i
    bb : Ordᴸ (at i rr) → Ordᴸ j
    vq : V ≡ pen rr bb
    lb : at i rr ≡ j
    sb : ∀ y → strip (bb y) ≡ strip y

Nd-suc : ∀ {a b} → Nd (suc a) (suc b) → Nd a b
Nd-suc (inj₁ _ , refl) = inj₁ tt , refl
Nd-suc (inj₂ r , e)    = Nd-trans (r , e) (inj₁ tt , refl)

module OnFam {F : Lv → Set} (fam : Fam F) where
  open Fam fam

  up≤′ : ∀ {h j m n} → F (lim h) → m ≤′ n → Nd j (h m) → Nd j (h n)
  up≤′ fh ≤′-refl     q = q
  up≤′ fh (≤′-step p) q = Nd-trans (f-step fh _) (up≤′ fh p q)

  up≤ : ∀ {h j m n} → F (lim h) → m ≤ n → Nd j (h m) → Nd j (h n)
  up≤ fh p q = up≤′ fh (≤⇒≤′ p) q

  head-Nd : ∀ {f} → F (lim f) → ∀ μ → Nd (f μ) (lim f)
  head-Nd fl μ with f-step fl μ
  ... | s , e = (suc μ , s) , e

  irr : ∀ x → F x → Nd x x → ⊥
  irr zero fx (() , _)
  irr (suc a) fx n = irr a (f-suc fx) (Nd-suc n)
  irr (lim h) fx ((m , s) , e) = irr (h m) (f-lim fx m) (Nd-trans (s , e) (head-Nd fx m))
  irr (limᴼ _ _) fx _ = f-no fx

  sam-refl : ∀ x → F x → samᵐ x x ≡ true
  sam-refl zero    r = refl
  sam-refl (suc a) r = sam-refl a (f-suc r)
  sam-refl (lim f) r = sam-refl (f _) (f-lim r _)
  sam-refl (limᴼ _ _) r = ⊥-elim (f-no r)

  lim-μ : ∀ {f h} → F (lim f) → F (lim h) → ∀ μ → suc (wk (lim f)) ≤ μ → Nd (lim f) (lim h) → Nd (f μ) (h μ)
  lim-μ ff fh μ p n = Nd-trans (up≤ fh p (f-mod ff fh n)) (head-Nd ff μ)

  sam-lt : ∀ x y → F x → F y → Nd x y → samᵐ x y ≡ false
  sam-lt zero    zero    _ _ (() , _)
  sam-lt zero    (suc b) _ _ _ = refl
  sam-lt zero    (lim h) _ _ _ = refl
  sam-lt (suc a) zero    _ _ _ = refl
  sam-lt (suc a) (suc b) fa fb n = sam-lt a b (f-suc fa) (f-suc fb) (Nd-suc n)
  sam-lt (suc a) (lim h) _ _ _ = refl
  sam-lt (lim f) zero    _ _ _ = refl
  sam-lt (lim f) (suc b) _ _ _ = refl
  sam-lt (lim f) (lim h) ff fh n =
    sam-lt (f μ) (h μ) (f-lim ff μ) (f-lim fh μ) (lim-μ ff fh μ (s≤s (m≤m⊔n (wk (lim f)) (wk (lim h)))) n)
    where μ = suc (wk (lim f) ⊔ wk (lim h))
  sam-lt zero    (limᴼ _ _) _ fy _ = ⊥-elim (f-no fy)
  sam-lt (suc a) (limᴼ _ _) _ fy _ = ⊥-elim (f-no fy)
  sam-lt (lim f) (limᴼ _ _) _ fy _ = ⊥-elim (f-no fy)
  sam-lt (limᴼ _ _) _ fx _ _ = ⊥-elim (f-no fx)

  sam-gt : ∀ x y → F x → F y → Nd y x → samᵐ x y ≡ false
  sam-gt zero    zero    _ _ (() , _)
  sam-gt zero    (suc b) _ _ _ = refl
  sam-gt zero    (lim h) _ _ _ = refl
  sam-gt (suc a) zero    _ _ _ = refl
  sam-gt (suc a) (suc b) fa fb n = sam-gt a b (f-suc fa) (f-suc fb) (Nd-suc n)
  sam-gt (suc a) (lim h) _ _ _ = refl
  sam-gt (lim f) zero    _ _ _ = refl
  sam-gt (lim f) (suc b) _ _ _ = refl
  sam-gt (lim f) (lim h) ff fh n =
    sam-gt (f μ) (h μ) (f-lim ff μ) (f-lim fh μ) (lim-μ fh ff μ (s≤s (m≤n⊔m (wk (lim f)) (wk (lim h)))) n)
    where μ = suc (wk (lim f) ⊔ wk (lim h))
  sam-gt zero    (limᴼ _ _) _ fy _ = ⊥-elim (f-no fy)
  sam-gt (suc a) (limᴼ _ _) _ fy _ = ⊥-elim (f-no fy)
  sam-gt (lim f) (limᴼ _ _) _ fy _ = ⊥-elim (f-no fy)
  sam-gt (limᴼ _ _) _ fx _ _ = ⊥-elim (f-no fx)

  D-rise : ∀ μ j i → F j → F i → (∀ {x} → Nd x i → Nd x j) → Dm μ j i ≡ rise
  D-rise μ j zero       _ _ _ = refl
  D-rise μ j (suc i) fj fi n
    rewrite sam-gt j i fj (f-suc fi) (n (inj₁ tt , refl))
          | D-rise μ j i fj (f-suc fi) (λ { (s , e) → n (inj₂ s , e) }) = refl
  D-rise μ j (lim h) fj fi n
    rewrite D-rise μ j (h μ) fj (f-lim fi μ) (λ { (s , e) → n ((μ , s) , e) }) = refl
  D-rise μ j (limᴼ _ _) _ fi _ = ⊥-elim (f-no fi)

  Dᵐ-eq : ∀ j → F j → Dᵐ j j ≡ rise
  Dᵐ-eq j r = D-rise _ j j r r (λ n → n)

  Dᵐ-gt : ∀ {j i} → F j → F i → Nd i j → Dᵐ j i ≡ rise
  Dᵐ-gt {j} {i} fj fi n = D-rise _ j i fj fi (Nd-trans n)
```

## §7 `cast` 在族内是恒等

与 InaccStrikeNat 的 `Cast` 相同, 只把 `IsNat` 换成 `F`.

```agda
  module CastR (fe : Funext) where
    cast-id  : ∀ a → F a → (y : Ordᴸ a) → cast a a y ≡ y
    castP-id : ∀ a → F a → (r : Pre a) →
               Σ (Ordᴸ (at a r) → Ordᴸ (at a r)) λ bk → (castP a a r ≡ just (r , bk)) × (∀ y → bk y ≡ y)

    castP-id zero fa ()
    castP-id (suc a) fa (inj₁ _) = cast a a , refl , cast-id a (f-suc fa)
    castP-id (suc a) fa (inj₂ r) with castP a a r | castP-id a (f-suc fa) r
    ... | just _ | bk , refl , h = bk , refl , h
    castP-id (lim f) fa (n , r) with castP (f n) (f n) r | castP-id (f n) (f-lim fa n) r
    ... | just _ | bk , refl , h = bk , refl , h
    castP-id (limᴼ _ _) fa _ = ⊥-elim (f-no fa)

    cast-id a fa zero    = refl
    cast-id a fa (suc y) = cong Tree.suc (cast-id a fa y)
    cast-id a fa (lim g) = cong Tree.lim (fe (λ n → cast-id a fa (g n)))
    cast-id a fa (limᵢ r g) with castP a a r | castP-id a fa r
    ... | just _ | bk , refl , h = cong (Tree.limᵢ r) (fe λ y →
          trans (cast-id a fa (g (intoL a r (bk (outL a r y)))))
                (cong g (trans (cong (intoL a r) (h (outL a r y))) (into-out a r y))))
    cast-id (suc a) fa (up _ x) = cong (up tt) (cast-id a (f-suc fa) x)
    cast-id (lim f) fa (up n x) = cong (up n) (cast-id (f n) (f-lim fa n) x)
    cast-id (limᴼ _ _) fa (up _ _) = ⊥-elim (f-no fa)
```

## §8 判决的正确性: `pen`

`PenOK`: 判决是 `pen`, 路径字面命中, 搬运对 `strip` 是恒等. 这正是 `Commute` 的 `GV lt` 的内容, 这里陈述不提记号.

```agda
    D-pen : ∀ j i → F j → F i → Nd j i → PenOK (Dm (suc (wk j)) j i)
    D-pen j zero _ _ (() , _)
    D-pen j (suc i) fj fi (inj₁ _ , refl) rewrite sam-refl j fj =
      record { rr = inj₁ tt ; bb = cast j j ; vq = refl ; lb = refl ; sb = λ y → cong strip (cast-id j fj y) }
    D-pen j (suc i) fj fi (inj₂ s , e) rewrite sam-lt j i fj (f-suc fi) (s , e)
      with Dm (suc (wk j)) j i | D-pen j i fj (f-suc fi) (s , e)
    ... | V | record { rr = r ; bb = b ; vq = refl ; lb = l ; sb = q } =
      record { rr = inj₂ r ; bb = b ; vq = refl ; lb = l ; sb = q }
    D-pen j (lim h) fj fi n
      with Dm (suc (wk j)) j (h (suc (wk j))) | D-pen j (h (suc (wk j))) fj (f-lim fi _) (f-mod fj fi n)
    ... | V | record { rr = r ; bb = b ; vq = refl ; lb = l ; sb = q } =
      record { rr = suc (wk j) , r ; bb = b ; vq = refl ; lb = l ; sb = q }
    D-pen j (limᴼ _ _) _ fi _ = ⊥-elim (f-no fi)

    Dᵐ-lt : ∀ {j i} → F j → F i → Nd j i → PenOK (Dᵐ j i)
    Dᵐ-lt {j} {i} = D-pen j i
```

## §9 公共上界内的三歧

规整树本身不必可比: `lim [0,1,2,…]` 与 `lim [1,2,3,…]` 都规整, 互不为节点. 可比性来自公共上界: 同一棵规整树的两个节点必可比. 所以**类是 "规整树的有向族", 不是单棵规整树**.

```agda
tri : ∀ c → Reg c → ∀ {x y} → Nd x c → Nd y c → (x ≡ y) ⊎ (Nd x y ⊎ Nd y x)
tri zero _ (() , _) _
tri (suc b) r (inj₁ _ , refl) (inj₁ _ , refl) = inj₁ refl
tri (suc b) r (inj₁ _ , refl) (inj₂ s , e)    = inj₂ (inj₂ (s , e))
tri (suc b) r (inj₂ s , e)    (inj₁ _ , refl) = inj₂ (inj₁ (s , e))
tri (suc b) r (inj₂ s , e)    (inj₂ s′ , e′)  = tri b r (s , e) (s′ , e′)
tri (lim h) (st , rg) ((m , s) , e) ((n , s′) , e′) =
  tri (h (m ⊔ n)) (rg _) (Nd-up≤ (m≤m⊔n m n) (s , e)) (Nd-up≤ (m≤n⊔m m n) (s′ , e′))
  where open Mod st rg
tri (limᴼ _ _) () _ _
```
