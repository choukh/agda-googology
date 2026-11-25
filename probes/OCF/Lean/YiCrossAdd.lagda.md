# 加法与结点两行对跨层模拟 `Simʰ` 单调

验收文件. 编译定理, 无前提: `add-monoʰ` (一般层的加法对 `Simʰ` 的两个参数单调, 对接口的全部十二条规则), `plus-monoʰ`, `succ-monoʰ`, `psum-monoʰ`, 结点的两行 `ΨN-bbʰ`, `ΨN-nnʰ` (同为保留或同为折叠).
不涉及派发与折叠本身. 接口在 [YiCrossIface](YiCrossIface.lagda.md), 折叠的单调在 [YiCrossMono](YiCrossMono.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCrossAdd where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using
  (lev; Way; keep; fold; Ext; nodeAt; chain; Ψn; ΨN; succ; psum; ΩT)
open import OCF.Lean.YiCrossIface
```

## 1 造结点的办法的两条律

`BB`: 落在 `top` 那一支之下就在结点之下. `BN`: 两个位置的层号相等, 顶相关, 相关的下标上分支相关, 则两个结点相关.
`SimP` 先沿左边递归, 所以限制左边的造法时类型定义性不变; 限制右边时用 `pS`, `pL`, `pΩ` 搬运.

```agda
record BB {M′ k′ : LF} (M : LF) (B′ : Bld M′ k′) : Set where
  field
    bb : ∀ r′ {y : Raw M} {g′} → Simʰ M M′ y (g′ (Lay.tp (Lo k′ r′))) → Simʰ M M′ y (B′ r′ g′)
open BB

BN : ∀ {M k M′ k′} → Bld M k → Bld M′ k′ → Set
BN {M} {k} {M′} {k′} B B′ = ∀ r r′ {g g′} → lev k r ≡ lev k′ r′ →
  SimP k k′ r r′ (Lay.tp (Lo k r)) (Lay.tp (Lo k′ r′)) →
  (∀ η η′ → SimP k k′ r r′ η η′ → Simʰ M M′ (g η) (g′ η′)) → Simʰ M M′ (B r g) (B′ r′ g′)

bb-lc : ∀ {M M′} → BB {M′} {M′} M G.lc
bb-lc = record { bb = λ r′ h → bR h }

bn-lc : ∀ {M M′} → BN {M} {M} {M′} {M′} G.lc G.lc
bn-lc r r′ e p h = nN e p h

bb-s : ∀ {M M′ k′} {B′ : Bld M′ (suc k′)} → BB M B′ → BB {M′} {k′} M (λ r → B′ (inj₂ r))
bb-s ok = record { bb = λ r′ → bb ok (inj₂ r′) }

bb-l : ∀ {M M′ f′} {B′ : Bld M′ (lim f′)} → BB M B′ → ∀ n → BB {M′} {f′ n} M (λ r → B′ (n , r))
bb-l ok n = record { bb = λ r′ → bb ok (n , r′) }

bb-c : ∀ {M M′ j′ g′} {B′ : Bld M′ (lc j′ g′)} → BB M B′ → ∀ η l →
  BB {M′} {g′ η} M (λ r → B′ (η , l , r))
bb-c ok η l = record { bb = λ r′ → bb ok (η , l , r′) }

pS : ∀ K (r : Pre K) k′ (r′ : Pre k′) → SimP K (suc k′) r (inj₂ r′) ≡ SimP K k′ r r′
pS (suc k) (inj₁ _) k′ r′ = refl
pS (suc k) (inj₂ r) k′ r′ = pS k r k′ r′
pS (lim f) (n , r) k′ r′ = pS (f n) r k′ r′
pS (lc k g) (η , _ , r) k′ r′ = pS (g η) r k′ r′

pL : ∀ K (r : Pre K) f′ n (r′ : Pre (f′ n)) → SimP K (lim f′) r (n , r′) ≡ SimP K (f′ n) r r′
pL (suc k) (inj₁ _) f′ n r′ = refl
pL (suc k) (inj₂ r) f′ n r′ = pL k r f′ n r′
pL (lim f) (i , r) f′ n r′ = pL (f i) r f′ n r′
pL (lc k g) (η , _ , r) f′ n r′ = pL (g η) r f′ n r′

pΩ : ∀ K (r : Pre K) j′ g′ η′ l′ (r′ : Pre (g′ η′)) →
  SimP K (lc j′ g′) r (η′ , l′ , r′) ≡ SimP K (g′ η′) r r′
pΩ (suc k) (inj₁ _) j′ g′ η′ l′ r′ = refl
pΩ (suc k) (inj₂ r) j′ g′ η′ l′ r′ = pΩ k r j′ g′ η′ l′ r′
pΩ (lim f) (i , r) j′ g′ η′ l′ r′ = pΩ (f i) r j′ g′ η′ l′ r′
pΩ (lc k g) (η , _ , r) j′ g′ η′ l′ r′ = pΩ (g η) r j′ g′ η′ l′ r′

bn-Rs : ∀ {M k M′ k′} {B : Bld M k} {B′ : Bld M′ (suc k′)} → BN B B′ →
  BN {M} {k} {M′} {k′} B (λ r → B′ (inj₂ r))
bn-Rs {k = k} {k′ = k′} bn r r′ e p h = bn r (inj₂ r′) e
  (subst (λ P → P _ _) (sym (pS k r k′ r′)) p)
  (λ η η′ q → h η η′ (subst (λ P → P η η′) (pS k r k′ r′) q))

bn-Rl : ∀ {M k M′ f′} {B : Bld M k} {B′ : Bld M′ (lim f′)} → BN B B′ → ∀ n →
  BN {M} {k} {M′} {f′ n} B (λ r → B′ (n , r))
bn-Rl {k = k} {f′ = f′} bn n r r′ e p h = bn r (n , r′) e
  (subst (λ P → P _ _) (sym (pL k r f′ n r′)) p)
  (λ η η′ q → h η η′ (subst (λ P → P η η′) (pL k r f′ n r′) q))

bn-Rc : ∀ {M k M′ j′ g′} {B : Bld M k} {B′ : Bld M′ (lc j′ g′)} → BN B B′ → ∀ η′ l′ →
  BN {M} {k} {M′} {g′ η′} B (λ r → B′ (η′ , l′ , r))
bn-Rc {k = k} {j′ = j′} {g′ = g′} bn η′ l′ r r′ e p h = bn r (η′ , l′ , r′) e
  (subst (λ P → P _ _) (sym (pΩ k r j′ g′ η′ l′ r′)) p)
  (λ η η″ q → h η η″ (subst (λ P → P η η″) (pΩ k r j′ g′ η′ l′ r′) q))
```

## 2 加法

`add-wkʰ`: 左参数不高于和. `add-topʰ`: `suc x` 不高于 `x′ + top` (任意层). `add-monoʰ` 对推导归纳; `tT`, `cR`, `eL`, `eR` 处层号变小.

```agda
acc₂ʰ : ∀ {A A′ : Set} (Q : A → A′ → Set) {s : ℕ → A → A} {s′ : ℕ → A′ → A′} →
  (∀ n {y y′} → Q y y′ → Q (s n y) (s′ n y′)) → ∀ {x x′} → Q x x′ → ∀ n → Q (acc s x n) (acc s′ x′ n)
acc₂ʰ Q h q zero = q
acc₂ʰ Q h q (suc n) = h n (acc₂ʰ Q h q n)

add-wkʰ : ∀ {M M′} k′ (B′ : Bld M′ k′) → BB M B′ → ∀ {x x′} → Simʰ M M′ x x′ → ∀ a′ →
  Simʰ M M′ x (add k′ B′ x′ a′)
add-wkʰ k′ B′ ok h G.zero = h
add-wkʰ k′ B′ ok h (G.suc a) = wS (add-wkʰ k′ B′ ok h a)
add-wkʰ k′ B′ ok h (G.lim f) = lR 0 (add-wkʰ k′ B′ ok h (f 0))
add-wkʰ k′ B′ ok h (G.lc r g) = bb ok r (add-wkʰ k′ B′ ok h (g _))
add-wkʰ zero B′ ok h (G.em () a)
add-wkʰ (suc k′) B′ ok h (G.em _ a) = add-wkʰ k′ _ (bb-s ok) h a
add-wkʰ (lim f) B′ ok h (G.em n a) = add-wkʰ (f n) _ (bb-l ok n) h a
add-wkʰ (lc j g) B′ ok h (G.em (η , l) a) = add-wkʰ (g η) _ (bb-c ok η l) h a
add-wkʰ zero B′ ok h G.top = wS h
add-wkʰ (suc k′) B′ ok h G.top = bb ok (inj₁ tt) (add-wkʰ k′ _ (bb-s ok) h G.top)
add-wkʰ (lim f) B′ ok h G.top = lR 0 (add-wkʰ (f 0) _ (bb-l ok 0) h G.top)
add-wkʰ (lc j g) B′ ok h G.top = wS h

add-topʰ : ∀ {M M′} k′ (B′ : Bld M′ k′) → BB M B′ → ∀ {x x′} → Simʰ M M′ x x′ →
  Simʰ M M′ (G.suc x) (add k′ B′ x′ G.top)
add-topʰ zero B′ ok h = sS h
add-topʰ (suc k′) B′ ok h = bb ok (inj₁ tt) (add-topʰ k′ _ (bb-s ok) h)
add-topʰ (lim f) B′ ok h = lR 0 (add-topʰ (f 0) _ (bb-l ok 0) h)
add-topʰ (lc j g) B′ ok h = sS h

add-monoʰ : ∀ {M M′} k k′ (B : Bld M k) (B′ : Bld M′ k′) → BB M B′ → BN B B′ →
  ∀ {x x′} → Simʰ M M′ x x′ → ∀ {a a′} → Simʰ k k′ a a′ → Simʰ M M′ (add k B x a) (add k′ B′ x′ a′)
add-monoʰ k k′ B B′ ok bn h {a′ = a′} zS = add-wkʰ k′ B′ ok h a′
add-monoʰ k k′ B B′ ok bn h (sS d) = sS (add-monoʰ k k′ B B′ ok bn h d)
add-monoʰ k k′ B B′ ok bn h (wS d) = wS (add-monoʰ k k′ B B′ ok bn h d)
add-monoʰ k k′ B B′ ok bn h (lR n d) = lR n (add-monoʰ k k′ B B′ ok bn h d)
add-monoʰ k k′ B B′ ok bn h (lL f) = lL (λ n → add-monoʰ k k′ B B′ ok bn h (f n))
add-monoʰ k k′ B B′ ok bn h (bR {r′ = r′} d) = bb ok r′ (add-monoʰ k k′ B B′ ok bn h d)
add-monoʰ k k′ B B′ ok bn h (nN {r = r} {r′ = r′} e p f) =
  bn r r′ e p (λ η η′ q → add-monoʰ k k′ B B′ ok bn h (f η η′ q))
add-monoʰ zero k′ B B′ ok bn h (eL {i = ()} d)
add-monoʰ (suc k) k′ B B′ ok bn h (eL d) =
  add-monoʰ k k′ _ B′ ok (λ r r′ → bn (inj₂ r) r′) h d
add-monoʰ (lim f) k′ B B′ ok bn h (eL {i = n} d) =
  add-monoʰ (f n) k′ _ B′ ok (λ r r′ → bn (n , r) r′) h d
add-monoʰ (lc j g) k′ B B′ ok bn h (eL {i = (η , l)} d) =
  add-monoʰ (g η) k′ _ B′ ok (λ r r′ → bn (η , l , r) r′) h d
add-monoʰ k zero B B′ ok bn h (eR {i′ = ()} d)
add-monoʰ k (suc k′) B B′ ok bn h (eR d) =
  add-monoʰ k k′ B _ (bb-s ok) (bn-Rs bn) h d
add-monoʰ k (lim f′) B B′ ok bn h (eR {i′ = n} d) =
  add-monoʰ k (f′ n) B _ (bb-l ok n) (bn-Rl bn n) h d
add-monoʰ k (lc j′ g′) B B′ ok bn h (eR {i′ = (η′ , l′)} d) =
  add-monoʰ k (g′ η′) B _ (bb-c ok η′ l′) (bn-Rc bn η′ l′) h d
add-monoʰ zero k′ B B′ ok bn h (tT e) = add-topʰ k′ B′ ok h
add-monoʰ (suc k) zero B B′ ok bn h (tT ())
add-monoʰ (suc k) (suc k′) B B′ ok bn h (tT (e , t)) = bn (inj₁ tt) (inj₁ tt) e t
  (λ η η′ q → add-monoʰ k k′ _ _ (bb-s ok) (bn-Rs (λ r r′ → bn (inj₂ r) r′)) h q)
add-monoʰ (suc k) (lim f′) B B′ ok bn h (tT ())
add-monoʰ (suc k) (lc j′ g′) B B′ ok bn h (tT ())
add-monoʰ (lim f) zero B B′ ok bn h (tT ())
add-monoʰ (lim f) (suc k′) B B′ ok bn h (tT ())
add-monoʰ {M} {M′} (lim f) (lim f′) B B′ ok bn h (tT e) = lL (λ n → lR n
  (acc₂ʰ (Simʰ M M′)
    (λ i p → add-monoʰ (f i) (f′ i) _ _ (bb-l ok i) (bn-Rl (λ r r′ → bn (i , r) r′) i) p (e i))
    h (suc n)))
add-monoʰ (lim f) (lc j′ g′) B B′ ok bn h (tT ())
add-monoʰ (lc j g) zero B B′ ok bn h (tT ())
add-monoʰ (lc j g) (suc k′) B B′ ok bn h (tT ())
add-monoʰ (lc j g) (lim f′) B B′ ok bn h (tT ())
add-monoʰ (lc j g) (lc j′ g′) B B′ ok bn h (tT e) = sS h
add-monoʰ k zero B B′ ok bn h (cR {i′ = ()} c d)
add-monoʰ k (suc k′) B B′ ok bn h (cR c d) =
  bb ok (inj₁ tt) (add-monoʰ k k′ B _ (bb-s ok) (bn-Rs bn) h d)
add-monoʰ k (lim f′) B B′ ok bn h (cR refl d) =
  lR 0 (add-monoʰ k (f′ 0) B _ (bb-l ok 0) (bn-Rl bn 0) h d)
add-monoʰ k (lc j′ g′) B B′ ok bn h (cR () d)
add-monoʰ zero k′ B B′ ok bn h (t0 z) = sS (add-wkʰ k′ B′ ok h _)
add-monoʰ (suc k) k′ B B′ ok bn h (t0 ())
add-monoʰ (lim f) k′ B B′ ok bn h (t0 ())
add-monoʰ (lc j g) k′ B B′ ok bn h (t0 ())

plus-monoʰ : ∀ m m′ {x x′ a a′} → Simʰ m m′ x x′ → Simʰ m m′ a a′ →
  Simʰ m m′ (plus m x a) (plus m′ x′ a′)
plus-monoʰ m m′ h d = add-monoʰ m m′ G.lc G.lc bb-lc bn-lc h d

succ-monoʰ : ∀ m m′ {y y′} → Simʰ m m′ y y′ → Simʰ m m′ (succ m y) (succ m′ y′)
succ-monoʰ m m′ h = lL (λ n → lR n (acc₂ʰ (Simʰ m m′) (λ _ p → plus-monoʰ m m′ h p) h n))

psum-monoʰ : ∀ m m′ {h : ℕ → Raw m} {h′ : ℕ → Raw m′} → (∀ n → Simʰ m m′ (h n) (h′ n)) →
  Simʰ m m′ (G.lim (psum m h)) (G.lim (psum m′ h′))
psum-monoʰ m m′ q =
  lL (λ n → lR n (acc₂ʰ (Simʰ m m′) (λ i p → plus-monoʰ m m′ p (q (suc i))) (q 0) n))
```

## 3 结点的两行

`-bb`: 只动右边. `-nn`: 左右同为保留 (两个结点, 位置任意) 或同为折叠 (链逐点相关).

```agda
nodeAt-bbʰ : ∀ {M M′} m′ (p′ : Pre m′) (B′ : Bld M′ m′) → BB M B′ → ∀ {x} g′ →
  Simʰ M M′ x (g′ G.top) → Simʰ M M′ x (nodeAt m′ p′ B′ g′)
nodeAt-bbʰ (suc k) (inj₁ _) B′ ok g′ h = bb ok (inj₁ tt) h
nodeAt-bbʰ (suc k) (inj₂ p) B′ ok = nodeAt-bbʰ k p _ (bb-s ok)
nodeAt-bbʰ (lim f) (n , p) B′ ok = nodeAt-bbʰ (f n) p _ (bb-l ok n)
nodeAt-bbʰ (lc j g) (η , l , p) B′ ok = nodeAt-bbʰ (g η) p _ (bb-c ok η l)

nodeAt-bnQ : ∀ {M M′} j (N : (Raw j → Raw M) → Raw M) m′ (p′ : Pre m′) (B′ : Bld M′ m′) →
  (∀ r′ {g g′} → j ≡ lev m′ r′ → SimQ j m′ r′ G.top (Lay.tp (Lo m′ r′)) →
    (∀ η η′ → SimQ j m′ r′ η η′ → Simʰ M M′ (g η) (g′ η′)) → Simʰ M M′ (N g) (B′ r′ g′)) →
  ∀ {g g′} → j ≡ lev m′ p′ → Simʰ j (lev m′ p′) G.top G.top →
  (∀ η η′ → Simʰ j (lev m′ p′) η η′ → Simʰ M M′ (g η) (g′ η′)) → Simʰ M M′ (N g) (nodeAt m′ p′ B′ g′)
nodeAt-bnQ j N (suc k′) (inj₁ _) B′ rb e t h = rb (inj₁ tt) e t h
nodeAt-bnQ j N (suc k′) (inj₂ p′) B′ rb = nodeAt-bnQ j N k′ p′ _ (λ r′ → rb (inj₂ r′))
nodeAt-bnQ j N (lim f′) (n , p′) B′ rb = nodeAt-bnQ j N (f′ n) p′ _ (λ r′ → rb (n , r′))
nodeAt-bnQ j N (lc j′ g′) (η , l , p′) B′ rb = nodeAt-bnQ j N (g′ η) p′ _ (λ r′ → rb (η , l , r′))

nodeAt-bnʰ : ∀ {M M′} m (p : Pre m) (B : Bld M m) m′ (p′ : Pre m′) (B′ : Bld M′ m′) → BN B B′ →
  ∀ {g g′} → lev m p ≡ lev m′ p′ → Simʰ (lev m p) (lev m′ p′) G.top G.top →
  (∀ η η′ → Simʰ (lev m p) (lev m′ p′) η η′ → Simʰ M M′ (g η) (g′ η′)) →
  Simʰ M M′ (nodeAt m p B g) (nodeAt m′ p′ B′ g′)
nodeAt-bnʰ (suc k) (inj₁ _) B m′ p′ B′ bn = nodeAt-bnQ k (B (inj₁ tt)) m′ p′ B′ (λ r′ → bn (inj₁ tt) r′)
nodeAt-bnʰ (suc k) (inj₂ p) B m′ p′ B′ bn = nodeAt-bnʰ k p _ m′ p′ B′ (λ r r′ → bn (inj₂ r) r′)
nodeAt-bnʰ (lim f) (n , p) B m′ p′ B′ bn = nodeAt-bnʰ (f n) p _ m′ p′ B′ (λ r r′ → bn (n , r) r′)
nodeAt-bnʰ (lc j g) (η , l , p) B m′ p′ B′ bn =
  nodeAt-bnʰ (g η) p _ m′ p′ B′ (λ r r′ → bn (η , l , r) r′)

chain-monoʰ : ∀ j j′ {gk : Raw j → Raw j} {gk′ : Raw j′ → Raw j′} → Simʰ j j′ G.top G.top →
  (∀ η η′ → Simʰ j j′ η η′ → Simʰ j j′ (gk η) (gk′ η′)) →
  ∀ n → Simʰ j j′ (chain j gk n) (chain j′ gk′ n)
chain-monoʰ j j′ t h zero = t
chain-monoʰ j j′ t h (suc n) = plus-monoʰ j j′ (chain-monoʰ j j′ t h n) (h _ _ (chain-monoʰ j j′ t h n))

Ψn-bbʰ : ∀ {M} m′ j′ (w′ : Way m′ j′) gm′ gk′ {x : Raw M} → Simʰ M m′ x (gm′ G.top) →
  Simʰ M m′ x (Ψn m′ j′ w′ gm′ gk′)
Ψn-bbʰ m′ .(lev m′ p) (keep p refl) gm′ gk′ h = nodeAt-bbʰ m′ p G.lc bb-lc gm′ h
Ψn-bbʰ m′ j′ fold gm′ gk′ h = lR 0 h

Ψn-nnʰ : ∀ m m′ j j′ (w : Way m j) (w′ : Way m′ j′) → WayR w w′ →
  ∀ {gm : Raw j → Raw m} {gk : Raw j → Raw j} {gm′ : Raw j′ → Raw m′} {gk′ : Raw j′ → Raw j′} →
  j ≡ j′ → Simʰ j j′ G.top G.top →
  (∀ η η′ → Simʰ j j′ η η′ → Simʰ m m′ (gm η) (gm′ η′)) →
  (∀ η η′ → Simʰ j j′ η η′ → Simʰ j j′ (gk η) (gk′ η′)) →
  Simʰ m m′ (Ψn m j w gm gk) (Ψn m′ j′ w′ gm′ gk′)
Ψn-nnʰ m m′ .(lev m p) .(lev m′ p′) (keep p refl) (keep p′ refl) kk e t hm hk =
  nodeAt-bnʰ m p G.lc m′ p′ G.lc bn-lc e t hm
Ψn-nnʰ m m′ j j′ fold fold ff e t hm hk = lL (λ n → lR n (hm _ _ (chain-monoʰ j j′ t hk n)))

ΨN-bbʰ : ∀ {M} m′ k′ r′ (w′ : Way m′ (lev k′ r′)) gm′ gk′ {x : Raw M} →
  Simʰ M m′ x (gm′ (Lay.tp (Lo k′ r′))) → Simʰ M m′ x (ΨN m′ k′ r′ w′ gm′ gk′)
ΨN-bbʰ m′ (suc k) (inj₁ _) = Ψn-bbʰ m′ k
ΨN-bbʰ m′ (suc k) (inj₂ r) = ΨN-bbʰ m′ k r
ΨN-bbʰ m′ (lim f) (n , r) = ΨN-bbʰ m′ (f n) r
ΨN-bbʰ m′ (lc j g) (η , _ , r) = ΨN-bbʰ m′ (g η) r

ΨN-nnQ : ∀ m m′ j (w : Way m j) k′ r′ (w′ : Way m′ (lev k′ r′)) → WayR w w′ →
  ∀ {gm : Raw j → Raw m} {gk : Raw j → Raw j}
    {gm′ : Lay.A (Lo k′ r′) → Raw m′} {gk′ : Lay.A (Lo k′ r′) → Raw (lev k′ r′)} →
  j ≡ lev k′ r′ → SimQ j k′ r′ G.top (Lay.tp (Lo k′ r′)) →
  (∀ η η′ → SimQ j k′ r′ η η′ → Simʰ m m′ (gm η) (gm′ η′)) →
  (∀ η η′ → SimQ j k′ r′ η η′ → Simʰ j (lev k′ r′) (gk η) (gk′ η′)) →
  Simʰ m m′ (Ψn m j w gm gk) (ΨN m′ k′ r′ w′ gm′ gk′)
ΨN-nnQ m m′ j w (suc k′) (inj₁ _) w′ = Ψn-nnʰ m m′ j k′ w w′
ΨN-nnQ m m′ j w (suc k′) (inj₂ r′) w′ = ΨN-nnQ m m′ j w k′ r′ w′
ΨN-nnQ m m′ j w (lim f′) (n , r′) w′ = ΨN-nnQ m m′ j w (f′ n) r′ w′
ΨN-nnQ m m′ j w (lc j′ g′) (η , _ , r′) w′ = ΨN-nnQ m m′ j w (g′ η) r′ w′

ΨN-nnʰ : ∀ m m′ k r (w : Way m (lev k r)) k′ r′ (w′ : Way m′ (lev k′ r′)) → WayR w w′ →
  ∀ {gm : Lay.A (Lo k r) → Raw m} {gk : Lay.A (Lo k r) → Raw (lev k r)}
    {gm′ : Lay.A (Lo k′ r′) → Raw m′} {gk′ : Lay.A (Lo k′ r′) → Raw (lev k′ r′)} →
  lev k r ≡ lev k′ r′ → SimP k k′ r r′ (Lay.tp (Lo k r)) (Lay.tp (Lo k′ r′)) →
  (∀ η η′ → SimP k k′ r r′ η η′ → Simʰ m m′ (gm η) (gm′ η′)) →
  (∀ η η′ → SimP k k′ r r′ η η′ → Simʰ (lev k r) (lev k′ r′) (gk η) (gk′ η′)) →
  Simʰ m m′ (ΨN m k r w gm gk) (ΨN m′ k′ r′ w′ gm′ gk′)
ΨN-nnʰ m m′ (suc k) (inj₁ _) w = ΨN-nnQ m m′ k w
ΨN-nnʰ m m′ (suc k) (inj₂ r) w = ΨN-nnʰ m m′ k r w
ΨN-nnʰ m m′ (lim f) (n , r) w = ΨN-nnʰ m m′ (f n) r w
ΨN-nnʰ m m′ (lc j g) (η , _ , r) w = ΨN-nnʰ m m′ (g η) r w

ΩT-bbʰ : ∀ {M} m′ j′ (w′ : Way m′ j′) K o {x : Raw M} → Simʰ M m′ x (K G.top) → Simʰ M m′ x (o 0) →
  Simʰ M m′ x (ΩT m′ j′ w′ K o)
ΩT-bbʰ m′ .(lev m′ p) (keep p refl) K o h₁ h₂ = nodeAt-bbʰ m′ p G.lc bb-lc K h₁
ΩT-bbʰ m′ j′ fold K o h₁ h₂ = lR 0 h₂

ΩT-nnʰ : ∀ m m′ j j′ (w : Way m j) (w′ : Way m′ j′) → WayR w w′ →
  ∀ {K : Raw j → Raw m} {K′ : Raw j′ → Raw m′} {o : ℕ → Raw m} {o′ : ℕ → Raw m′} →
  j ≡ j′ → Simʰ j j′ G.top G.top →
  (∀ {p q p′ q′} → w ≡ keep p q → w′ ≡ keep p′ q′ → ∀ η η′ → Simʰ j j′ η η′ → Simʰ m m′ (K η) (K′ η′)) →
  Simʰ m m′ (G.lim o) (G.lim o′) → Simʰ m m′ (ΩT m j w K o) (ΩT m′ j′ w′ K′ o′)
ΩT-nnʰ m m′ .(lev m p) .(lev m′ p′) (keep p refl) (keep p′ refl) kk e t hK ho =
  nodeAt-bnʰ m p G.lc m′ p′ G.lc bn-lc e t (hK refl refl)
ΩT-nnʰ m m′ j j′ fold fold ff e t hK ho = ho
```
