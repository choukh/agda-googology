# YiXVFiniteFamily
> 验收文件。档位：编译定理。有限层参照侧的统一比较工具；尚无所有 pre n 或 Goal。
> 证明参照 YiOverOps 与 YiXVCan2* 并按有限层统一，不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVFiniteFamily where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Data.Fin as F
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; s≼s; z≼)
import OCF.Lean.YiXVFiniteIndex as I
open I using (T)

module Layer (n : ℕ)
  (Go : (i : F.Fin (suc n)) → T (I.rank n i) → Set)
  (Lo : (i : F.Fin (suc n)) → T (I.rank n i) → T (I.rank n i) → Set) where
  Current = T (suc n)
  one : Current
  one = L.suc L.zero
  start : ∀ {i} (q : i L.<ᴵ L.natᴵ (suc n)) → L.U i (L.<→◃ q)
  start {i} q = L.into (L.<→◃ q) (L.Ω i)
  next : ∀ {i} (q : i L.<ᴵ L.natᴵ (suc n)) → L.U i (L.<→◃ q) → L.U i (L.<→◃ q)
  next q u = L.into (L.<→◃ q) (L.suc (L.out (L.<→◃ q) u))
  GU : ∀ {i} (q : i L.<ᴵ L.natᴵ (suc n)) → L.U i (L.<→◃ q) → Set
  GU q u = Go (I.FinSlot.index (I.cutF n q)) (I.Uref n q u)
  RU : ∀ {i} (q : i L.<ᴵ L.natᴵ (suc n)) → L.U i (L.<→◃ q) → L.U i (L.<→◃ q) → Set
  RU q u v = Lo (I.FinSlot.index (I.cutF n q)) (I.Uref n q u) (I.Uref n q v)
  Floor : ∀ {i} (q : i L.<ᴵ L.natᴵ (suc n)) → L.U i (L.<→◃ q) → Set
  Floor q u = Lo (I.FinSlot.index (I.cutF n q)) (L.Ω (L.natᴵ (I.rank n (I.FinSlot.index (I.cutF n q))))) (I.Uref n q u)

  mutual
    data Gd : Current → Set
    data Le : Current → Current → Set
    data Step : Current → Current → Set
    record SC {i} (q : i L.<ᴵ L.natᴵ (suc n)) (f : L.U i (L.<→◃ q) → Current) : Set where
      inductive
      constructor sc
      field
        mo : ∀ u v → GU q u → GU q v → Floor q u → RU q u v → Le (f u) (f v)
        db : ∀ u → GU q u → Floor q u → Le (L.suc (f u)) (f (next q u))
        po : Le one (f (start q))
    data Gd where
      gz : Gd L.zero
      gs : ∀ {X} → Gd X → Gd (L.suc X)
      gl : ∀ {a : ℕ → Current} → (∀ k → Gd (a k)) → Gd (L.lim a)
      gn : ∀ {i} {q : i L.<ᴵ L.natᴵ (suc n)} {f : L.U i (L.<→◃ q) → Current} →
        SC q f → (∀ u → GU q u → Floor q u → Gd (f u)) → Gd (L.limᵢ q f)
      gu : ∀ {X : T n} → Go F.zero X → Gd (L.up L.zero X)
    data Le where
      pack : ∀ {X Y} → Gd X → Gd Y → Step X Y → Le X Y
    data Step where
      rr : ∀ {X} → Step X X
      zz : ∀ {Y} → Step L.zero Y
      ss : ∀ {X Y} → Le X Y → Step (L.suc X) (L.suc Y)
      ws : ∀ {X Y} → Le X Y → Step X (L.suc Y)
      ll : ∀ {a Y} → (∀ k → Le (a k) Y) → Step (L.lim a) Y
      lr : ∀ {X a} k → Le X (a k) → Step X (L.lim a)
      nn : ∀ {i} {q : i L.<ᴵ L.natᴵ (suc n)} {f g : L.U i (L.<→◃ q) → Current} →
        (∀ u v → GU q u → GU q v → Floor q u → RU q u v → Le (f u) (g v)) → Step (L.limᵢ q f) (L.limᵢ q g)
      aa : ∀ {i X} {q : i L.<ᴵ L.natᴵ (suc n)} {g : L.U i (L.<→◃ q) → Current} → Le X (g (start q)) → Step X (L.limᵢ q g)
      uu : ∀ {X Y : T n} → Lo F.zero X Y → Step (L.up L.zero X) (L.up L.zero Y)
      uS : ∀ {X : T n} → Go F.zero X → Step (L.suc (L.up L.zero X)) (L.up L.zero (L.suc X))
      uS⁻ : ∀ {X : T n} → Go F.zero X → Step (L.up L.zero (L.suc X)) (L.suc (L.up L.zero X))
      uZ : Step (L.up L.zero (L.zero {ℓ = L.natᴵ n})) L.zero
      uZ⁻ : Step L.zero (L.up L.zero (L.zero {ℓ = L.natᴵ n}))
      uL : ∀ {a : ℕ → T n} → (∀ k → Go F.zero (a k)) → Step (L.up L.zero (L.lim a)) (L.lim (λ k → L.up L.zero (a k)))
      uL⁻ : ∀ {a : ℕ → T n} → (∀ k → Go F.zero (a k)) → Step (L.lim (λ k → L.up L.zero (a k))) (L.up L.zero (L.lim a))
      uN : ∀ {i} {q : i L.<ᴵ L.natᴵ n} {a : L.U i (L.<→◃ q) → T n} → Go F.zero (L.limᵢ q a) →
        Step (L.up L.zero (L.limᵢ q a)) (L.limᵢ (L.suc q) (λ u → L.up L.zero (a u)))
      uN⁻ : ∀ {i} {q : i L.<ᴵ L.natᴵ n} {a : L.U i (L.<→◃ q) → T n} → Go F.zero (L.limᵢ q a) →
        Step (L.limᵢ (L.suc q) (λ u → L.up L.zero (a u))) (L.up L.zero (L.limᵢ q a))
      tr : ∀ {X Y Z} → Le X Y → Le Y Z → Step X Z

  left : ∀ {X Y} → Le X Y → Gd X
  left (pack gx gy p) = gx
  right : ∀ {X Y} → Le X Y → Gd Y
  right (pack gx gy p) = gy
  refl : ∀ {X} → Gd X → Le X X
  refl gx = pack gx gx rr
  trans : ∀ {X Y Z} → Le X Y → Le Y Z → Le X Z
  trans p q = pack (left p) (right q) (tr p q)
  z≤ : ∀ {Y} → Gd Y → Le L.zero Y
  z≤ gy = pack gz gy zz
  s≤ : ∀ {X Y} → Le X Y → Le (L.suc X) (L.suc Y)
  s≤ p = pack (gs (left p)) (gs (right p)) (ss p)
  u≤ : ∀ {X Y : T n} → Go F.zero X → Go F.zero Y → Lo F.zero X Y → Le (L.up L.zero X) (L.up L.zero Y)
  u≤ gx gy p = pack (gu gx) (gu gy) (uu p)
  upS≤ : ∀ {X : T n} → Go F.zero X → Go F.zero (L.suc X) → Le (L.suc (L.up L.zero X)) (L.up L.zero (L.suc X))
  upS≤ gx gsx = pack (gs (gu gx)) (gu gsx) (uS gx)

mutual
  GoFam : ∀ n (i : F.Fin (suc n)) → T (I.rank n i) → Set
  GoFam zero F.zero X = ⊤
  GoFam zero (F.suc ()) X
  GoFam (suc n) F.zero X = Layer.Gd n (GoFam n) (LeFam n) X
  GoFam (suc n) (F.suc i) X = GoFam n i X
  LeFam : ∀ n (i : F.Fin (suc n)) → T (I.rank n i) → T (I.rank n i) → Set
  LeFam zero F.zero X Y = X ≼ Y
  LeFam zero (F.suc ()) X Y
  LeFam (suc n) F.zero X Y = Layer.Le n (GoFam n) (LeFam n) X Y
  LeFam (suc n) (F.suc i) X Y = LeFam n i X Y

Gd : ∀ n → T n → Set
Gd n = GoFam n F.zero
Le : ∀ n → T n → T n → Set
Le n = LeFam n F.zero

zero-good : ∀ n → Gd n L.zero
zero-good zero = tt
zero-good (suc n) = Layer.gz
suc-good : ∀ n {X} → Gd n X → Gd n (L.suc X)
suc-good zero gx = tt
suc-good (suc n) gx = Layer.gs gx

module D₁ = Layer 0 (GoFam 0) (LeFam 0)
one-up₁ : D₁.Le D₁.one (L.up L.zero (L.Ω L.zero))
one-up₁ = D₁.trans (D₁.s≤ (D₁.z≤ (D₁.gu tt))) (D₁.upS≤ tt tt)
actual₁ : Gd 1 (L.Ω (L.natᴵ 1))
actual₁ = D₁.gn (D₁.sc (λ u v gu gv o q → D₁.u≤ tt tt q) (λ u gu o → D₁.upS≤ tt tt) one-up₁) (λ u gu o → D₁.gu tt)
pos₁ : Le 1 (L.suc L.zero) (L.Ω (L.natᴵ 1))
pos₁ = D₁.pack (D₁.gs D₁.gz) actual₁ (D₁.aa one-up₁)

module D₂ = Layer 1 (GoFam 1) (LeFam 1)
one-up₂ : D₂.Le D₂.one (L.up L.zero (L.Ω (L.natᴵ 1)))
one-up₂ = D₂.trans (D₂.trans (D₂.s≤ (D₂.z≤ (D₂.gu D₁.gz))) (D₂.upS≤ D₁.gz (D₁.gs D₁.gz)))
  (D₂.u≤ (D₁.gs D₁.gz) actual₁ pos₁)
actual₂ : Gd 2 (L.Ω (L.natᴵ 2))
actual₂ = D₂.gn (D₂.sc (λ u v gu gv o q → D₂.u≤ gu gv q) (λ u gu o → D₂.upS≤ gu (D₁.gs gu)) one-up₂) (λ u gu o → D₂.gu gu)
pos₂ : Le 2 (L.suc L.zero) (L.Ω (L.natᴵ 2))
pos₂ = D₂.pack (D₂.gs D₂.gz) actual₂ (D₂.aa one-up₂)

module D₃ = Layer 2 (GoFam 2) (LeFam 2)
one-up₃ : D₃.Le D₃.one (L.up L.zero (L.Ω (L.natᴵ 2)))
one-up₃ = D₃.trans (D₃.trans (D₃.s≤ (D₃.z≤ (D₃.gu D₂.gz))) (D₃.upS≤ D₂.gz (D₂.gs D₂.gz)))
  (D₃.u≤ (D₂.gs D₂.gz) actual₂ pos₂)
actual₃ : Gd 3 (L.Ω (L.natᴵ 3))
actual₃ = D₃.gn (D₃.sc (λ u v gu gv o q → D₃.u≤ gu gv q) (λ u gu o → D₃.upS≤ gu (D₂.gs gu)) one-up₃) (λ u gu o → D₃.gu gu)
```
