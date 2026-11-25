# YiIntr：有限规范 Ω 的构造环境

本篇不假定任意 LF 都有 Ω 闭包。World 保存候选 Ω 目标、
源到目标的路径及可数源的孩子环境；CanonicalWorld 另证环境按规范
零／后继／极限配方构造，Ready 指定一次 Ω 所需的环境。
Ω̂ 在 Ready 上定义，不能读作无条件的 LF → LF。
目标是实填 0、1、Ω₁ 的环境及 tw 0..3；不是全塔迁移。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiIntrFinite where

open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Align.YiIntrCore
open import OCF.Align.YiIntrRaw

reach-trans : ∀ {a b c} → Reach a b → Reach b c → Reach a c
reach-trans p here = p
reach-trans p (via-suc q) = via-suc (reach-trans p q)
reach-trans p (via-lim n q) = via-lim n (reach-trans p q)
reach-trans p (via-first q) = via-first (reach-trans p q)
reach-trans p (via-branch η e q) = via-branch η e (reach-trans p q)

cO : (k : LF) → Raw k
cO zero = G.suc G.zero
cO (suc k) = G.top
cO (lim f) = G.top
cO (lc k c w b t p g) = G.top

cO-Lgl : ∀ k → Lgl k (cO k)
cO-Lgl zero = tt
cO-Lgl (suc k) = tt
cO-Lgl (lim f) = tt
cO-Lgl (lc k c w b t p g) = tt

cO-Nested : ∀ k → Nested k (cO k)
cO-Nested zero = tt
cO-Nested (suc k) = tt
cO-Nested (lim f) = tt
cO-Nested (lc k c w b t p g) = tt

read0 : Raw zero → LF
read0 G.zero = zero
read0 (G.suc a) = suc (read0 a)
read0 (G.lim f) = lim (λ n → read0 (f n))
read0 (G.lc () c t g)
read0 (G.em () a)
read0 G.top = suc zero

data World : LF → Set
KidsW : LF → Set
data World where
  world : ∀ {k} (ω : LF) → Reach k ω → KidsW k → World k
KidsW zero = ⊤
KidsW (suc k) = World k
KidsW (lim f) = ∀ n → World (f n)
KidsW (lc k c w b t p g) = ⊥

omega : ∀ {k} → World k → LF
omega (world ω p cs) = ω

world-root : ∀ {k} (w : World k) → Reach k (omega w)
world-root (world ω p cs) = p

children : ∀ {k} → World k → KidsW k
children (world ω p cs) = cs

-- 在可数源的槽位重建 lc，根路径只用各部分。
nodeN : ∀ k → World k → (r : Pre k) (c : Low k r) →
  LglLow k r c → NestedLow k r c → (t : LF) → Reach k t →
  ((η : Low k r) → GdL k r c η → LF) →
  Σ LF (λ x → Reach t x)
nodeN zero w ()
nodeN (suc k) w (inj₁ _) c l b t p g =
  lc k c l b t p g , via-first here
nodeN (suc k) w (inj₂ r) c l b t p g =
  nodeN k (children w) r c l b t
    (reach-trans (via-suc here) p) g
nodeN (lim f) w (n , r) c l b t p g =
  nodeN (f n) (children w n) r c l b t
    (reach-trans (via-lim n here) p) g
nodeN (lc k c₀ l₀ b₀ t₀ p₀ g₀) (world ω p ()) r c l b t q g

no-top-em : ∀ k i a → Cp k G.top (G.em i a) → ⊥
no-top-em k i a (inj₁ ())
no-top-em k i a (inj₂ ())

down-top-above : ∀ k a → Dn k a G.top → Cp k G.top a → ⊥
down-top-above zero a () q
down-top-above (lim f) a () q
down-top-above (suc k) (G.em i a) p q = no-top-em (suc k) i a q
down-top-above (suc k) G.zero () q
down-top-above (suc k) (G.suc a) () q
down-top-above (suc k) (G.lim f) () q
down-top-above (suc k) (G.lc r c t g) () q
down-top-above (suc k) G.top () q
down-top-above (lc k c w b t p g) (G.em (inj₂ (inj₁ i)) a) d q =
  no-top-em (lc k c w b t p g) (inj₂ (inj₁ i)) a q
down-top-above (lc k c w b t p g) (G.em (inj₁ i) a) () q
down-top-above (lc k c w b t p g) (G.em (inj₂ (inj₂ i)) a) () q
down-top-above (lc k c w b t p g) G.zero () q
down-top-above (lc k c w b t p g) (G.suc a) () q
down-top-above (lc k c w b t p g) (G.lim f) () q
down-top-above (lc k c w b t p g) (G.lc r d u h) () q
down-top-above (lc k c w b t p g) G.top () q

below : ∀ k → World k → (a : Raw k) → Lgl k a → Nested k a →
  Cp k a G.top → LF
below k w .G.top l b (inj₁ refl) = omega w
below zero w a l b (inj₂ ())
below (lim f) w a l b (inj₂ ())
below (suc k) w (G.em i a) l b (inj₂ q) =
  below k (children w) a l b q
below (suc k) w G.zero l b (inj₂ ())
below (suc k) w (G.suc a) l b (inj₂ ())
below (suc k) w (G.lim f) l b (inj₂ ())
below (suc k) w (G.lc r c t g) l b (inj₂ ())
below (suc k) w G.top l b (inj₂ ())
below (lc k c w₀ b₀ t p g) (world ω root ()) a l b q

below-reach : ∀ k w a l b (q : Cp k a G.top) →
  Cp k G.top a → Reach (omega w) (below k w a l b q)
below-reach k w .G.top l b (inj₁ refl) d = here
below-reach k w a l b (inj₂ q) d = ⊥-elim (down-top-above k a q d)

up-to : ∀ k (f : ℕ → Raw k) →
  (∀ n → Cp k (f n) (f (suc n))) → ∀ j m → Cp k (f m) (f (j + m))
up-to k f st zero m = inj₁ refl
up-to k f st (suc j) m = Cp-tr k (up-to k f st j m) (st (j + m))

mutual
  above : ∀ k (w : World k) (a : Raw k) → Lgl k a → Nested k a →
    Cp k G.top a → Σ LF (λ x → Reach (omega w) x)
  above k w G.zero l b (inj₁ ())
  above k w G.zero l b (inj₂ ())
  above k w (G.suc a) l b (inj₁ ())
  above k w (G.suc a) l b (inj₂ q) =
    suc (proj₁ v) , via-suc (proj₂ v)
    where v = above k w a l b q
  above k w (G.lim f) (st , lf) bf (inj₁ ())
  above k w (G.lim f) (st , lf) bf (inj₂ (m , q)) =
    lim (λ j → proj₁ (col j)) , via-lim m (proj₂ (col m) q)
    where
    col : ∀ j → Σ LF (λ x → Cp k G.top (f j) → Reach (omega w) x)
    col j = mixed k w (f j) (lf j) (bf j)
      (cmpC k (f (j + m))
        (subst (λ z → Cp k (f j) (f z)) (+-comm m j)
          (up-to k f st m j))
        (Cp-tr k q (up-to k f st j m)) (lf (j + m)))
  above k w (G.lc r c t g) (tg , mono , irr , lt , lg)
    (lc₀ , bc , bt , bg) (inj₁ ())
  above k w (G.lc r c t g) (tg , mono , irr , lt , lg)
    (lc₀ , bc , bt , bg) (inj₂ q) =
    proj₁ node , reach-trans (proj₂ first) (proj₂ node)
    where
    first = above k w t lt bt q
    node = nodeN k w r c lc₀ bc (proj₁ first)
      (reach-trans (world-root w) (proj₂ first))
      (λ η e → proj₁ (above k w (g η e) (lg η e) (bg η e)
        (Cp-tr k q (tg η e))))
  above k w (G.em i a) l b (inj₁ ())
  above k w (G.em i a) l b (inj₂ ())
  above k w G.top l b q = omega w , here

  mixed : ∀ k (w : World k) (a : Raw k) → Lgl k a → Nested k a →
    (Cp k a G.top ⊎ Cp k G.top a) →
    Σ LF (λ x → Cp k G.top a → Reach (omega w) x)
  mixed k w a l b (inj₁ q) = below k w a l b q , below-reach k w a l b q
  mixed k w a l b (inj₂ q) = proj₁ v , (λ _ → proj₂ v)
    where v = above k w a l b q

readC : ∀ k → World k → (η : Raw k) → Gd k (cO k) η → LF
readC zero w η e = read0 η
readC (suc k) w η (p , l , b) = proj₁ (above (suc k) w η l b p)
readC (lim f) w η (p , l , b) = proj₁ (above (lim f) w η l b p)
readC (lc k c l₀ b₀ t p₀ g) (world ω root ()) η e

world0 : World zero
world0 = world (suc zero) (via-suc here) tt

sucWorld : ∀ {k} (w : World k) → Reach (suc k) (omega w) → World (suc k)
sucWorld {k} w p = world
  (lc k (cO k) (cO-Lgl k) (cO-Nested k) (omega w) p (readC k w))
  (via-first p) w

-- World 的路径条件本身不认证 Ω；另用归纳见证排除任意填目标。
data CanonicalWorld : ∀ {k} → World k → Set where
  cw-zero : CanonicalWorld world0
  cw-suc : ∀ {k} (w : World k) (p : Reach (suc k) (omega w)) →
    CanonicalWorld w → CanonicalWorld (sucWorld w p)
  cw-lim : ∀ {f} (ws : ∀ n → World (f n))
    (p : Reach (lim f) (lim (λ n → omega (ws n)))) →
    (∀ n → CanonicalWorld (ws n)) →
    CanonicalWorld (world (lim (λ n → omega (ws n))) p ws)

-- 一次 Ω：所有额外环境和根位置前提在类型中明列。
data Ready : LF → Set
Ω̂ : ∀ {x} → Ready x → LF
data Ready where
  r-zero : Ready zero
  r-suc : ∀ {k} (w : World k) → CanonicalWorld w →
    Reach (suc k) (omega w) → Ready (suc k)
  r-lim : ∀ {f} → (∀ n → Ready (f n)) → Ready (lim f)
  r-lc : ∀ {k c w b t p g} (dt : Ready t) →
    Reach (suc k) (Ω̂ dt) → (∀ η e → Ready (g η e)) →
    Ready (lc k c w b t p g)
Ω̂ r-zero = suc zero
Ω̂ (r-suc w cw p) = omega (sucWorld w p)
Ω̂ (r-lim d) = lim (λ n → Ω̂ (d n))
Ω̂ (r-lc {k} {c} {w} {b} {g = g} dt q dg) =
  lc k c w b (Ω̂ dt) q (λ η e → Ω̂ (dg η e))

raw1 : Raw zero
raw1 = G.suc G.zero

world1 : World (suc zero)
world1 = sucWorld world0 here

hub : LF
hub = omega world1

hub-branch : ∀ η (e : Gd zero raw1 η) → Reach (read0 η) hub
hub-branch η e = via-branch η e here

-- 第 0 层的所有坐标都没有嵌套 lc。
raw0-Nested : ∀ a → Nested zero a
raw0-Nested G.zero = tt
raw0-Nested (G.suc a) = raw0-Nested a
raw0-Nested (G.lim f) = λ n → raw0-Nested (f n)
raw0-Nested (G.lc () c t g)
raw0-Nested (G.em () a)
raw0-Nested G.top = tt

record CountResult (a : Raw zero) : Set where
  constructor result
  field
    ready : Ready (read0 a)
    kids : KidsW (read0 a)
    root : Reach (read0 a) (Ω̂ ready)
    canonical : CanonicalWorld (world (Ω̂ ready) root kids)
    from-hub : Cp zero raw1 a → Reach hub (Ω̂ ready)
open CountResult

worldOf : ∀ {a} → CountResult a → World (read0 a)
worldOf d = world (Ω̂ (ready d)) (root d) (kids d)

result0 : CountResult G.zero
result0 = result r-zero tt (via-suc here) cw-zero
  (λ { (inj₁ ()) ; (inj₂ ()) })

result1 : CountResult raw1
result1 = result (r-suc world0 cw-zero here) world0 (via-first here)
  (cw-suc world0 here cw-zero) (λ _ → here)

under1 : ∀ a → Cp zero a raw1 → CountResult a
under1 .raw1 (inj₁ refl) = result1
under1 .G.zero (inj₂ (inj₁ refl)) = result0
under1 a (inj₂ (inj₂ ()))

mutual
  positiveWorld : ∀ a → Lgl zero a → Cp zero raw1 a → CountResult a
  positiveWorld G.zero l (inj₁ ())
  positiveWorld G.zero l (inj₂ ())
  positiveWorld (G.suc a) l (inj₁ refl) = result1
  positiveWorld (G.suc a) l (inj₂ q) =
    result (r-suc (worldOf d) (canonical d) p) (worldOf d) (via-first p)
      (cw-suc (worldOf d) p (canonical d))
      (λ _ → via-first (from-hub d q))
    where
    d = positiveWorld a l q
    p : Reach (suc (read0 a)) (Ω̂ (ready d))
    p = reach-trans
      (hub-branch (G.suc a) (inj₂ q , l , raw0-Nested a)) (from-hub d q)
  positiveWorld (G.lim f) (st , lf) (inj₁ ())
  positiveWorld (G.lim f) (st , lf) (inj₂ (m , q)) =
    result (r-lim (λ j → ready (col j))) (λ j → worldOf (col j)) rt
      (cw-lim (λ j → worldOf (col j)) rt (λ j → canonical (col j)))
      (λ _ → h)
    where
    col : ∀ j → CountResult (f j)
    col j = mixedWorld (f j) (lf j)
      (cmpC zero (f (j + m))
        (subst (λ z → Cp zero (f j) (f z)) (+-comm m j)
          (up-to zero f st m j))
        (Cp-tr zero q (up-to zero f st j m)) (lf (j + m)))
    h : Reach hub (lim (λ j → Ω̂ (ready (col j))))
    h = via-lim m (from-hub (col m) q)
    rt : Reach (lim (λ j → read0 (f j))) (lim (λ j → Ω̂ (ready (col j))))
    rt = reach-trans (hub-branch (G.lim f)
      (inj₂ (m , q) , (st , lf) , raw0-Nested (G.lim f))) h
  positiveWorld (G.lc () c t g) l q
  positiveWorld (G.em () a) l q
  positiveWorld G.top l (inj₁ ())
  positiveWorld G.top l (inj₂ ())

  mixedWorld : ∀ a → Lgl zero a → (Cp zero a raw1 ⊎ Cp zero raw1 a) → CountResult a
  mixedWorld a l (inj₁ q) = under1 a q
  mixedWorld a l (inj₂ q) = positiveWorld a l q

tw₀ tw₁ tw₂ tw₃ : LF
tw₀ = zero
tw₁ = Ω̂ r-zero
tw₂ = Ω̂ (r-suc world0 cw-zero here)

ready₂ : Ready tw₂
ready₂ = r-lc (r-suc world0 cw-zero here) (via-first here)
  (λ η e → ready (positiveWorld η (proj₁ (proj₂ e)) (proj₁ e)))

tw₃ = Ω̂ ready₂

tw₃-form : tw₃ ≡
  lc zero raw1 tt tt tw₂ (via-first here)
    (λ η e → Ω̂ (ready (positiveWorld η (proj₁ (proj₂ e)) (proj₁ e))))
tw₃-form = refl
```

positiveWorld 量化全部合法 Raw 0 正坐标，包含弱合法常列；
它在极限中用同一个 f(j+m) 的两个 Cp 与 Lgl 比较，不使用裸下标比较。
构造环境来自真子坐标递归，CountResult 不把未知 Ω 输出当假设。
这里 Ω̂ 的定义仍承接原四行及读回模板；没有证明与旧 LF 序数值相同。
