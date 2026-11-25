# 统一值模拟: 带上下文帧的关系族

> 验收文件 (定义与引理). 归纳族 `J Γ X y`: 参照树 X 被 "上下文 Γ 里的深层树 y" 模拟; Γ 是嵌套 `up t c ·` 的帧, 链从顶层往下数. 槽位上的关系是参数 `Sl`, 按层号递归接上 (`Rel`, `SlOf`, `RelP`), 对一切层号 (含 ℕ 极限与 `Ωₗ`) 有定义.
> 编译定理 (对一切层号): 对搬运封闭 (`trRel`), 孩子层的推导搬进父层带一帧的上下文 (`emb`), 加法, 右加, `next`, 部分和 (`addL`, `cumR`, `nextL`, `inCum`), 第 0 层读成值序 (`r→≼`).
> 不涉及折叠 (折叠在 `YiUpSimFold`), 不否定什么.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiUpSimRel where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import OCF.Lean.YiFreshBlock renaming (L to LF)
open import OCF.Lean.YiFreshFold using (_+_; iter; next; cum)
open import OCF.Lean.YiFreshLegal using (_⊢_◃_; ◃s; ◃l; ◃w; ◃u; ◃c; ◃t; +-mono)
open import OCF.Lean.YiFreshValRead using (T₀; read; ◃⊑)
open import OCF.Lean.YiLeanValRel using (TRC; module Back)

import OCF.Align.Level as L
open L using (_≅ᴵ_; _<ᴵ_)
open import OCF.Align.Value using (_≼_; z≼; s≼s; l≼; u≼; ≼-trans; ⊑→≼)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using () renaming (iter to iterᴸ)
```

## 链与上下文

链 `Dc ℓ j` 从顶层 ℓ 逐次取孩子到 j, 顶端在前 (与 `YiUpBlock.Dn` 方向相反: 这里要从顶层剥帧). 帧在深端加 (`snocC`).

```agda
data Dc : LF → LF → Set where
  []  : ∀ {ℓ} → Dc ℓ ℓ
  _∷_ : ∀ {ℓ j} (c : Ch ℓ) → Dc (chL ℓ c) j → Dc ℓ j

snocD : ∀ {ℓ j} → Dc ℓ j → (c : Ch j) → Dc ℓ (chL j c)
snocD []       c = c ∷ []
snocD (c′ ∷ d) c = c′ ∷ snocD d c

data Ctx : (ℓ : LF) {j : LF} → Dc ℓ j → Set where
  []  : ∀ {ℓ} → Ctx ℓ {ℓ} []
  fr  : ∀ {ℓ j} (t : Tr ℓ) (c : Ch ℓ) {d : Dc (chL ℓ c) j} → Ctx (chL ℓ c) d → Ctx ℓ (c ∷ d)

snocC : ∀ {ℓ j} {d : Dc ℓ j} → Ctx ℓ d → Tr j → (c : Ch j) → Ctx ℓ (snocD d c)
snocC []            t c = fr t c []
snocC (fr t′ c′ Γ)  t c = fr t′ c′ (snocC Γ t c)
```

## 层号的对应

```agda
data Corr : L.Ordᴵ → LF → Set where
  cz : Corr L.zero zero
  cs : ∀ {a k} → Corr a k → Corr (L.suc a) (suc k)
  cl : ∀ {g s f} → (∀ n → Corr (g n) (f n)) → Corr (L.lim g s) (lim f)

Corr-≅ : ∀ {a b x} → a ≅ᴵ b → Corr b x → Corr a x
Corr-≅ L.z≅ cz = cz
Corr-≅ (L.s≅ e) (cs c) = cs (Corr-≅ e c)
Corr-≅ (L.l≅ h) (cl c) = cl (λ n → Corr-≅ (h n) (c n))

Corr-uniq : ∀ {a b x} → Corr a x → Corr b x → a ≅ᴵ b
Corr-uniq cz cz = L.z≅
Corr-uniq (cs c) (cs d) = L.s≅ (Corr-uniq c d)
Corr-uniq (cl c) (cl d) = L.l≅ (λ n → Corr-uniq (c n) (d n))
```

## 关系族

规则: 零在任何 (顶层) 树之下 `zr`; X 被前缀模拟则弹出帧 `pop`; 后继 `ss`; 沿第一位置序放宽 `wk`; 左边极限 `ll`; 结点对结点 `nd` (层号对应, 分支对一切被模拟的输入); 参照的提升透明 `ur`; 压入帧 `psh` (深层树是 y, 等于外层是 `up t c y`).

```agda
module Sim (ℓ : LF) (Sl : ∀ {j} → Dc ℓ j → (p : Pos j) → ∀ {i} → L.Ordᶜ i → Br j p → Set) where
  data J : ∀ {j} {d : Dc ℓ j} → Ctx ℓ d → ∀ {k} → L.Ordᶜ k → Tr j → Set where
    zr  : ∀ {k} {y : Tr ℓ} → J [] {k} L.zero y
    pop : ∀ {j d} {Γ : Ctx ℓ {j} d} {k} {X : L.Ordᶜ k} {t : Tr j} {c : Ch j} {y : Tr (chL j c)}
        → J Γ X t → J (snocC Γ t c) X y
    ss  : ∀ {j d} {Γ : Ctx ℓ {j} d} {k} {X : L.Ordᶜ k} {y : Tr j} → J Γ X y → J Γ (L.suc X) (suc y)
    wk  : ∀ {j d} {Γ : Ctx ℓ {j} d} {k} {X : L.Ordᶜ k} {y y′ : Tr j} → J Γ X y → j ⊢ y ◃ y′ → J Γ X y′
    ll  : ∀ {j d} {Γ : Ctx ℓ {j} d} {k} {F : ℕ → L.Ordᶜ k} {y : Tr j} → (∀ n → J Γ (F n) y) → J Γ (L.lim F) y
    nd  : ∀ {j d} {Γ : Ctx ℓ {j} d} {i K′} {q : i <ᴵ K′} {f : L.U i (L.<→◃ q) → L.Ordᶜ K′}
            {p : Pos j} {g : Br j p → Tr j}
        → Corr i (at j p)
        → (∀ (y₀ : L.Ordᶜ i) (c : Br j p) → Sl d p y₀ c → J Γ (f (L.into (L.<→◃ q) y₀)) (g c))
        → J Γ (L.limᵢ q f) (Ω p g)
    ur  : ∀ {j d} {Γ : Ctx ℓ {j} d} {k} {X : L.Ordᶜ k} {y : Tr j} → J Γ X y → J Γ (L.up {k = k} L.zero X) y
    psh : ∀ {j d} {Γ : Ctx ℓ {j} d} {k} {X : L.Ordᶜ k} {t : Tr j} {c : Ch j} {y : ChT j c}
        → J (snocC Γ t c) X (chT j c y) → J Γ X (up t c y)

open Sim public using (zr; pop; ss; wk; ll; nd; ur; psh)

Rel   : (ℓ : LF) → ∀ {k} → L.Ordᶜ k → Tr ℓ → Set
SlOf  : (ℓ : LF) → ∀ {j} → Dc ℓ j → (p : Pos j) → ∀ {i} → L.Ordᶜ i → Br j p → Set
RelP  : (ℓ : LF) (p : Pos ℓ) → ∀ {i} → L.Ordᶜ i → Br ℓ p → Set
RelP⁼ : (a : LF) (p : Pos⁼ a) → ∀ {i} → L.Ordᶜ i → Br⁼ a p → Set

Rel ℓ X y = Sim.J ℓ (SlOf ℓ) [] X y

SlOf ℓ        []       p = RelP ℓ p
SlOf zero     (() ∷ d) p
SlOf (suc a)  (_ ∷ d)  p = SlOf a d p
SlOf (lim g)  (n ∷ d)  p = SlOf (g n) d p
SlOf (Ωₗ k h) (c ∷ d)  p = SlOf (h c) d p

RelP (suc a)  t              = RelP⁼ a t
RelP (lim g)  (n , t)        = RelP⁼ (g n) t
RelP (Ωₗ k h) (inj₁ t)       = RelP⁼ k t
RelP (Ωₗ k h) (inj₂ (c , t)) = RelP⁼ (h c) t

RelP⁼ a (inj₁ _) = Rel a
RelP⁼ a (inj₂ p) = RelP a p
```

## 对层间搬运封闭

```agda
module TRJ (ℓ : LF) (Sl : ∀ {j} → Dc ℓ j → (p : Pos j) → ∀ {i} → L.Ordᶜ i → Br j p → Set)
  (ST : ∀ {j} (d : Dc ℓ j) (p : Pos j) → TRC (λ {i} → Sl d p {i})) where
  open Sim ℓ Sl using (J)

  TR⁻ : ∀ {a b} (e : a ≅ᴵ b) {j d} {Γ : Ctx ℓ {j} d} {y : L.Ordᶜ b} {η} → J Γ y η → J Γ (L.tr⁻ e y) η
  TR⁻ e zr = zr
  TR⁻ e (pop r) = pop (TR⁻ e r)
  TR⁻ e (ss r) = ss (TR⁻ e r)
  TR⁻ e (wk r d) = wk (TR⁻ e r) d
  TR⁻ e (ll h) = ll (λ n → TR⁻ e (h n))
  TR⁻ e (nd {d = d} {q = q} {f = f} {p = p} {g = g} lv h) =
    nd (Corr-≅ (L.≅ᴵ-sym (L.Restr.eq (L.res⁻ q e))) lv) (λ y a r →
      subst (λ w → J _ (L.tr⁻ e (f (L.into (L.<→◃ q) (L.Restr.back (L.res⁻ q e) w)))) (g a))
        (sym (L.out-into (L.<→◃ (L.Restr.lt (L.res⁻ q e))) y))
        (TR⁻ e (h (L.Restr.back (L.res⁻ q e) y) a (Back.back⁻ᴿ (ST d p) q e r))))
  TR⁻ (L.s≅ e) (ur r) = ur (TR⁻ e r)
  TR⁻ e (psh r) = psh (TR⁻ e r)

  TR⁺ : ∀ {a b} (e : a ≅ᴵ b) {j d} {Γ : Ctx ℓ {j} d} {y : L.Ordᶜ a} {η} → J Γ y η → J Γ (L.tr e y) η
  TR⁺ e zr = zr
  TR⁺ e (pop r) = pop (TR⁺ e r)
  TR⁺ e (ss r) = ss (TR⁺ e r)
  TR⁺ e (wk r d) = wk (TR⁺ e r) d
  TR⁺ e (ll h) = ll (λ n → TR⁺ e (h n))
  TR⁺ e (nd {d = d} {q = q} {f = f} {p = p} {g = g} lv h) =
    nd (Corr-≅ (L.≅ᴵ-sym (L.Restr.eq (L.res q e))) lv) (λ y a r →
      subst (λ w → J _ (L.tr e (f (L.into (L.<→◃ q) (L.Restr.back (L.res q e) w)))) (g a))
        (sym (L.out-into (L.<→◃ (L.Restr.lt (L.res q e))) y))
        (TR⁺ e (h (L.Restr.back (L.res q e) y) a (Back.backᴿ (ST d p) q e r))))
  TR⁺ (L.s≅ e) (ur r) = ur (TR⁺ e r)
  TR⁺ e (psh r) = psh (TR⁺ e r)

trRel : ∀ ℓ → TRC (λ {k} → Rel ℓ {k})
trSl  : ∀ ℓ {j} (d : Dc ℓ j) (p : Pos j) → TRC (λ {i} → SlOf ℓ d p {i})
trP   : ∀ ℓ (p : Pos ℓ) → TRC (λ {i} → RelP ℓ p {i})
trP⁼  : ∀ a (p : Pos⁼ a) → TRC (λ {i} → RelP⁼ a p {i})

trRel ℓ = record { tr⁻ᴿ = λ e r → TRJ.TR⁻ ℓ (SlOf ℓ) (trSl ℓ) e r ; trᴿ = λ e r → TRJ.TR⁺ ℓ (SlOf ℓ) (trSl ℓ) e r }

trSl ℓ        []       p = trP ℓ p
trSl zero     (() ∷ d) p
trSl (suc a)  (_ ∷ d)  p = trSl a d p
trSl (lim g)  (n ∷ d)  p = trSl (g n) d p
trSl (Ωₗ k h) (c ∷ d)  p = trSl (h c) d p

trP (suc a)  t              = trP⁼ a t
trP (lim g)  (n , t)        = trP⁼ (g n) t
trP (Ωₗ k h) (inj₁ t)       = trP⁼ k t
trP (Ωₗ k h) (inj₂ (c , t)) = trP⁼ (h c) t

trP⁼ a (inj₁ _) = trRel a
trP⁼ a (inj₂ p) = trP a p
```

## 孩子层的推导搬进父层

孩子层 a 空上下文的推导, 在父层 (这里写后继层; 另两种层号同文) 带一帧的上下文里仍是推导. 链顶端在前, 所以父层在孩子链上的槽位关系定义性地就是孩子层的, 不需要换型.

```agda
emb : ∀ {a} (t₀ : Tr (suc a)) {j} {d : Dc a j} {Δ : Ctx a d} {k} {X : L.Ordᶜ k} {y : Tr j}
  → Sim.J a (SlOf a) Δ X y → Sim.J (suc a) (SlOf (suc a)) (fr t₀ tt Δ) X y
emb t₀ zr       = pop {Γ = []} zr
emb t₀ (pop r)  = pop (emb t₀ r)
emb t₀ (ss r)   = ss (emb t₀ r)
emb t₀ (wk r d) = wk (emb t₀ r) d
emb t₀ (ll h)   = ll (λ n → emb t₀ (h n))
emb t₀ (nd c h) = nd c (λ y₀ c₀ sl → emb t₀ (h y₀ c₀ sl))
emb t₀ (ur r)   = ur (emb t₀ r)
emb t₀ (psh r)  = psh (emb t₀ r)
```

## 加法, 右加, `next`, 部分和

顶层前缀左加 b: 上下文空时加在深层树上, 否则加在最外一帧的前缀上 (加法不打开 `up`).

```agda
module Add (ℓ : LF) (Sl : ∀ {j} → Dc ℓ j → (p : Pos j) → ∀ {i} → L.Ordᶜ i → Br j p → Set) where
  open Sim ℓ Sl using (J)

  pre : Tr ℓ → ∀ {j} {d : Dc ℓ j} → Ctx ℓ d → Ctx ℓ d
  pre b []         = []
  pre b (fr t c Γ) = fr (b + t) c Γ

  prey : Tr ℓ → ∀ {j} {d : Dc ℓ j} → Ctx ℓ d → Tr j → Tr j
  prey b []         y = b + y
  prey b (fr t c Γ) y = y

  rpad : ∀ {k} {X : L.Ordᶜ k} {b : Tr ℓ} → J [] X b → (y : Tr ℓ) → J [] X (b + y)
  rpad r zero       = r
  rpad r (suc y)    = wk (rpad r y) ◃s
  rpad r (lim f)    = wk (rpad r (f zero)) (◃l zero)
  rpad r (Ω p g)    = wk (rpad r (g (fromBr ℓ p zero))) ◃w
  rpad r (up t c y) = psh (pop {Γ = []} (rpad r t))

  addL : ∀ {ka} {Xa : L.Ordᶜ ka} {b : Tr ℓ} → J [] Xa b
    → ∀ {j d} {Γ : Ctx ℓ {j} d} {k} {Xb : L.Ordᶜ k} {y : Tr j} → J Γ Xb y → (σ : L.Simᴵ k ka)
    → J (pre b Γ) (L.add Xa σ Xb) (prey b Γ y)
  addL sa zr σ = rpad sa _
  addL sa (pop {Γ = []} r) σ = pop {Γ = []} (addL sa r σ)
  addL sa (pop {Γ = fr t′ c′ Γ₁} r) σ = pop (addL sa r σ)
  addL sa {Γ = []} (ss r) σ = ss (addL sa r σ)
  addL sa {Γ = fr t c Γ} (ss r) σ = ss (addL sa r σ)
  addL {b = b} sa {Γ = []} (wk r e) σ = wk (addL sa r σ) (+-mono b e)
  addL sa {Γ = fr t c Γ} (wk r e) σ = wk (addL sa r σ) e
  addL sa {Γ = []} (ll h) σ = ll (λ n → addL sa (h n) σ)
  addL sa {Γ = fr t c Γ} (ll h) σ = ll (λ n → addL sa (h n) σ)
  addL {Xa = Xa} {b = b} sa {Γ = []} (nd {q = q} {f = f} {g = g} c h) σ =
    nd c (λ y₀ c₀ sl → subst (λ w → J [] (L.add Xa σ (f (L.into (L.<→◃ q) w))) (b + g c₀))
      (sym (L.out-into (L.<→◃ (σ q)) y₀)) (addL sa (h y₀ c₀ sl) σ))
  addL {Xa = Xa} {b = b} sa {Γ = fr t c′ Γ} (nd {q = q} {f = f} {g = g} c h) σ =
    nd c (λ y₀ c₀ sl → subst (λ w → J (fr (b + t) c′ Γ) (L.add Xa σ (f (L.into (L.<→◃ q) w))) (g c₀))
      (sym (L.out-into (L.<→◃ (σ q)) y₀)) (addL sa (h y₀ c₀ sl) σ))
  addL sa (ur r) σ = addL sa r (λ q → σ (L.suc q))
  addL sa (psh {Γ = []} r) σ = psh (addL sa r σ)
  addL sa (psh {Γ = fr t′ c′ Γ₁} r) σ = psh (addL sa r σ)

  cumR : (a : Tr ℓ) → ∀ {j d} {Γ : Ctx ℓ {j} d} {k} {X : L.Ordᶜ k} {y : Tr j} → J Γ X y
    → J (pre a Γ) X (prey a Γ y)
  cumR a zr = zr
  cumR a (pop {Γ = []} r) = pop {Γ = []} (cumR a r)
  cumR a (pop {Γ = fr t′ c′ Γ₁} r) = pop (cumR a r)
  cumR a {Γ = []} (ss r) = ss (cumR a r)
  cumR a {Γ = fr t c Γ} (ss r) = ss (cumR a r)
  cumR a {Γ = []} (wk r e) = wk (cumR a r) (+-mono a e)
  cumR a {Γ = fr t c Γ} (wk r e) = wk (cumR a r) e
  cumR a {Γ = []} (ll h) = ll (λ n → cumR a (h n))
  cumR a {Γ = fr t c Γ} (ll h) = ll (λ n → cumR a (h n))
  cumR a {Γ = []} (nd c h) = nd c (λ y₀ c₀ sl → cumR a (h y₀ c₀ sl))
  cumR a {Γ = fr t c′ Γ} (nd c h) = nd c (λ y₀ c₀ sl → cumR a (h y₀ c₀ sl))
  cumR a {Γ = []} (ur r) = ur (cumR a r)
  cumR a {Γ = fr t c Γ} (ur r) = ur (cumR a r)
  cumR a (psh {Γ = []} r) = psh (cumR a r)
  cumR a (psh {Γ = fr t′ c′ Γ₁} r) = psh (cumR a r)

  nextL : ∀ {k} {X : L.Ordᶜ k} {b : Tr ℓ} → J [] X b → J [] (L.lim (iterᴸ (X L.+_) L.zero)) (next b)
  nextL {X = X} {b = b} sa = ll λ where
      zero    → zr
      (suc n) → wk (go n) (◃l n)
    where
    go : ∀ n → J [] (iterᴸ (X L.+_) L.zero (suc n)) (iter (b +_) b n)
    go zero    = sa
    go (suc n) = addL sa (go n) (λ q → q)

  inCum : (F : ℕ → Tr ℓ) (n : ℕ) → ∀ {k} {X : L.Ordᶜ k} → J [] X (F n) → J [] X (lim (cum F))
  inCum F n r = wk (go n r) (◃l n)
    where
    go : ∀ n {k} {X : L.Ordᶜ k} → J [] X (F n) → J [] X (cum F n)
    go zero    r = r
    go (suc n) r = cumR (cum F n) r
```

## 第 0 层: 读成值序

```agda
read0 : ∀ {j} → Dc zero j → Tr j → T₀
read0 []       y = read y
read0 (() ∷ d) y

r0 : ∀ {j} {d : Dc zero j} {Γ : Ctx zero d} {k} {X : L.Ordᶜ k} {y : Tr j}
  → Sim.J zero (SlOf zero) Γ X y → X ≼ read0 d y
r0 zr = z≼
r0 (pop {d = []} {c = ()} r)
r0 (pop {d = () ∷ _} r)
r0 {d = []} (ss r) = s≼s (r0 r)
r0 {d = []} (wk {y = y} r e) = ≼-trans (r0 r) (⊑→≼ (read y) (◃⊑ e))
r0 {d = []} (ll h) = l≼ (λ n → r0 (h n))
r0 {d = []} (nd {p = ()} c h)
r0 {d = []} (ur r) = u≼ (r0 r)
r0 {d = []} (psh {c = ()} r)
r0 {d = () ∷ _} r

r→≼ : ∀ {k} {X : L.Ordᶜ k} {y : Tr zero} → Rel zero X y → X ≼ read y
r→≼ r = r0 r
```
