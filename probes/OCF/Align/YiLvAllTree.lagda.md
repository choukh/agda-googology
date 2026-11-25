# YiLvAll 底座：树一侧的派发在变量层号上的两条方程

**验收文件，档位：编译定理 (方程)。** 目标层 `sucᵐ 0` 上层号 `sucʲ 0` 的结点：`j < m` 时折叠等于槽位 `s` (`levN m s = j`) 上的保留结点
`nodeA m s` (`TREE-KEEP`)，`m ≤ j` 时等于链行 (`TREE-FOLD`)。办法：`KO` 在派发结果是 `keep s e` 时对 `e` 用 J，
于是 `stepˢ` 的两种情况各是一条对变量层号成立的方程 (`KO-top`, `KO-below`)。入口 [YiLvAll](YiLvAll.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiLvAllTree where

open import Data.Nat.Base using (ℕ; zero; suc; _<_; _≤_)
open import Data.Nat.Properties using (<-irrefl; <⇒≤)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (tt)
open import Data.Maybe.Base using (Maybe; just; nothing; map)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans)
open import OCF.Align.RR5IrrCore
open import OCF.Align.YiIrrIf using (iterate)
open import OCF.Align.YiLvIf using (lev)
open import OCF.Align.YiLvFoldAdd using (Alg; shS; rawAlg)
open import OCF.Align.YiLvFoldBase using (Way; keep; fold; nodeAt; Dom; startᴸ; module Node)
open import OCF.Align.YiLvFoldFin
  using (fin; eqᶠ; stepˢ; wayᵇ; eqᶠ-fin; IsKeep; step-just; step-keep; ψ; ψn; out; next)
open import OCF.Align.YiLvAllRel using (levN; levN<)
```

## 1 `eqᶠ` 在不等的有限层号上

```agda
eqᶠ-ne : ∀ a b → (a ≡ b → ⊥) → eqᶠ (fin a) (fin b) ≡ nothing
eqᶠ-ne zero zero ne with ne refl
... | ()
eqᶠ-ne zero (suc b) ne = refl
eqᶠ-ne (suc a) zero ne = refl
eqᶠ-ne (suc a) (suc b) ne = cong (map (cong suc)) (eqᶠ-ne a b (λ e → ne (cong suc e)))

eqᶠ-slot : ∀ m r → eqᶠ (fin m) (fin (levN m r)) ≡ nothing
eqᶠ-slot m r = eqᶠ-ne m (levN m r) (λ e → <-irrefl (sym e) (levN< m r))
```

## 2 保留结果与槽位

`KO` 把保留的派发结果连同 `lev` 的方程读成槽位上的结点 (`nodeAt`)；`nodeA` 是同一个结点，下界直接在 `Raw (sucʲ 0)` 里。

```agda
KO : ∀ M k → Way (fin M) k → (A : Alg (fin M)) (c : Raw k) → Alg.T A →
  ((η : Raw k) → .(Gd k c η) → Alg.T A) → Alg.T A
KO M .(lev (fin M) s) (keep s refl) A c t g = nodeAt (fin M) s A c t g
KO M k fold A c t g = t

nodeA : ∀ m (s : Pre (fin m)) (A : Alg (fin m)) (c : Raw (fin (levN m s))) → Alg.T A →
  ((a : Raw (fin (levN m s))) → .(Gd (fin (levN m s)) c a) → Alg.T A) → Alg.T A
nodeA zero ()
nodeA (suc m) (inj₁ _) A c t g = Alg.nT A (inj₁ tt) c t g
nodeA (suc m) (inj₂ r) A c t g = nodeA m r (shS A) c t g

KO-top : ∀ N (z : Maybe (fin N ≡ fin N)) → z ≡ just refl → (y : Way (fin N) (fin N)) →
  ∀ (A : Alg (fin (suc N))) c t g →
  KO (suc N) (fin N) (stepˢ z y) A c t g ≡ Alg.nT A (inj₁ tt) c t g
KO-top N .(just refl) refl y A c t g = refl

KO-below : ∀ N k (z : Maybe (fin N ≡ k)) → z ≡ nothing → (y : Way (fin N) k) →
  ∀ (A : Alg (fin (suc N))) c t g →
  KO (suc N) k (stepˢ z y) A c t g ≡ KO N k y (shS A) c t g
KO-below N .(lev (fin N) s) .nothing refl (keep s refl) A c t g = refl
KO-below N k .nothing refl fold A c t g = refl

way-slot : ∀ m (s : Pre (fin m)) (A : Alg (fin m)) c t g →
  KO m (fin (levN m s)) (wayᵇ (fin m) (fin (levN m s))) A c t g ≡ nodeA m s A c t g
way-slot zero ()
way-slot (suc N) (inj₁ _) A c t g = KO-top N _ (eqᶠ-fin N) _ A c t g
way-slot (suc N) (inj₂ r) A c t g =
  trans (KO-below N (fin (levN N r)) _ (eqᶠ-slot N r) _ A c t g) (way-slot N r (shS A) c t g)

keep-slot : ∀ m s → IsKeep (wayᵇ (fin m) (fin (levN m s)))
keep-slot zero ()
keep-slot (suc N) (inj₁ _) = step-just _ _ refl (eqᶠ-fin N)
keep-slot (suc N) (inj₂ r) = step-keep _ _ (keep-slot N r)

ψn-KO : ∀ M k (y : Way (fin M) k) → IsKeep y → ∀ c .(w : Lgl k c) .(b : Nested k c) t
  (g : (η : Raw k) → .(Gd k c η) → LF) .(d : Dom (lc k c w b t g)) →
  ψn (fin M) k y c w b t g d ≡
  KO M k y (rawAlg (fin M)) c (ψ (fin M) t (Node.first k c w b t g d))
    (λ η e → ψ (fin M) (g η e) (Node.branch k c w b t g d η e))
ψn-KO M .(lev (fin M) s) (keep s refl) h c w b t g d = refl
ψn-KO M k fold () c w b t g d
```

## 3 两条方程

```agda
TREE-KEEP : ∀ m (s : Pre (fin m)) (c : Raw (fin (levN m s))) .(w : Lgl (fin (levN m s)) c)
  .(b : Nested (fin (levN m s)) c) t
  (g : (a : Raw (fin (levN m s))) → .(Gd (fin (levN m s)) c a) → LF)
  .(d : Dom (lc (fin (levN m s)) c w b t g)) →
  ψ (fin m) (lc (fin (levN m s)) c w b t g) d ≡
  nodeA m s (rawAlg (fin m)) c (ψ (fin m) t (Node.first (fin (levN m s)) c w b t g d))
    (λ a e → ψ (fin m) (g a e) (Node.branch (fin (levN m s)) c w b t g d a e))
TREE-KEEP m s c w b t g d =
  trans (ψn-KO m (fin (levN m s)) (wayᵇ (fin m) (fin (levN m s))) (keep-slot m s) c w b t g d)
    (way-slot m s (rawAlg (fin m)) c _ _)

step-fold : ∀ {M k} (z : Maybe (M ≡ k)) (y : Way M k) → z ≡ nothing → y ≡ fold →
  stepˢ z y ≡ fold
step-fold .nothing .fold refl refl = refl

way-fold : ∀ m j → m ≤ j → wayᵇ (fin m) (fin j) ≡ fold
way-fold zero j le = refl
way-fold (suc m) j le =
  step-fold _ _ (eqᶠ-ne m j (λ e → <-irrefl e le)) (way-fold m j (<⇒≤ le))

TREE-FOLD : ∀ m j → m ≤ j → ∀ (c : Raw (fin j)) .(w : Lgl (fin j) c) .(b : Nested (fin j) c) t
  (g : (a : Raw (fin j)) → .(Gd (fin j) c a) → LF) .(d : Dom (lc (fin j) c w b t g)) →
  ψ (fin m) (lc (fin j) c w b t g) d ≡
  G.lim (λ n → out (fin m) (fin j) c w b t g d
    (iterate (next (fin j) c w b t g d) (startᴸ (fin j) c w b) n))
TREE-FOLD m j le c w b t g d = cong (λ y → ψn (fin m) (fin j) y c w b t g d) (way-fold m j le)
```
