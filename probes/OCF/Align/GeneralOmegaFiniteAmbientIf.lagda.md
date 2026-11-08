# 固定公共源界的有限typed读回关系

验收专用。右端始终是原HB(F B)，观察目标始终携Within B m。
左侧up仅更新σ而不缩小B；Ω源下标与同一有限界内的原kind显式对齐。
这不是裸下标判等律，也不把任意高层raw树视作自相关。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaFiniteAmbientIf where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaFiniteObserveIf using (F; floor; Within)
import OCF.Align.Level as L
open import OCF.Align.GeneralOmegaFiniteRank using (nat)

rank : ∀ B → K (F B) → ℕ
rank zero ()
rank (suc B) (inj₁ κ) = rank B κ
rank (suc B) (inj₂ _) = B
bound : ∀ B (κ : K (F B)) → nat (rank B κ) L.<ᴵ nat B
bound zero ()
bound (suc B) (inj₁ κ) = L.suc (bound B κ)
bound (suc B) (inj₂ _) = L.zero
canonical : ∀ B → L.Simᴵ (nat B) (nat (suc B))
canonical B q = L.suc q

data Bridge (B : ℕ)
  (Q : ∀ κ → L.Ordᶜ (nat (rank B κ)) → E (F B) κ → Set) :
  ∀ {ℓ} → L.Simᴵ ℓ (nat (suc B)) → L.Ordᶜ ℓ → HB (F B) → Set where
  rz : ∀ {ℓ} {σ : L.Simᴵ ℓ (nat (suc B))} → Bridge B Q {ℓ} σ L.zero hz
  rs : ∀ {ℓ} {σ : L.Simᴵ ℓ (nat (suc B))} {a b} → Bridge B Q {ℓ} σ a b → Bridge B Q σ (L.suc a) (hs b)
  rl : ∀ {ℓ} {σ : L.Simᴵ ℓ (nat (suc B))} {f g} → (∀ n → Bridge B Q {ℓ} σ (f n) (g n)) → Bridge B Q σ (L.lim f) (hl g)
  ro : ∀ {ℓ} {σ : L.Simᴵ ℓ (nat (suc B))} (κ : K (F B)) (q : nat (rank B κ) L.<ᴵ ℓ) {f g} →
    σ q ≡ L.suc (bound B κ) →
    L.limᵢ q f L.≅ L.limᵢ q f →
    (∀ x e → Q κ x e → Bridge B Q σ (f (L.into (L.<→◃ q) x)) (g e)) →
    Bridge B Q σ (L.limᵢ q f) (hΩ κ g)
  ru-s : ∀ {ℓ} {σ : L.Simᴵ (L.suc ℓ) (nat (suc B))} {a b} → Bridge B Q {ℓ} (λ q → σ (L.suc q)) a b →
    Bridge B Q {L.suc ℓ} σ (L.up L.zero a) b
  ru-l : ∀ {f s} {σ : L.Simᴵ (L.lim f s) (nat (suc B))} {i a b} → Bridge B Q {f i} (λ q → σ (L.lim i q)) a b →
    Bridge B Q {L.lim f s} σ (L.up (L.self i) a) b

  rc : ∀ {ℓ} {σ : L.Simᴵ ℓ (nat (suc B))} {a a′ b} →
    a L.≅ a′ → Bridge B Q σ a′ b → Bridge B Q σ a b

mutual
  Read : ∀ B {ℓ} → L.Simᴵ ℓ (nat (suc B)) → L.Ordᶜ ℓ → HB (F B) → Set
  Read B = Bridge B (Coord B)
  Coord : ∀ B κ → L.Ordᶜ (nat (rank B κ)) → E (F B) κ → Set
  Coord zero ()
  Coord (suc B) (inj₁ κ) = Coord B κ
  Coord (suc B) (inj₂ _) = Read B (canonical B)

-- 源up注入和左侧原up并非同一个动作；前者保留原左对象而扩大ambient。
up-read : ∀ {B ℓ} {σ : L.Simᴵ ℓ (nat (suc B))} {a b} → Read B {ℓ} σ a b →
  Read (suc B) (λ q → L.suc (σ q)) a (up b)
up-read rz = rz
up-read (rs p) = rs (up-read p)
up-read (rl p) = rl (λ n → up-read (p n))
up-read (ro κ q e sa p) = ro (inj₁ κ) q (cong L.suc e) sa (λ x c r → up-read (p x c r))
up-read (ru-s p) = ru-s (up-read p)
up-read (ru-l p) = ru-l (up-read p)
up-read (rc e p) = rc e (up-read p)

floor-read : ∀ B → Read B (canonical B) (L.Ω (nat B)) (floor B)
floor-read zero = rs rz
floor-read (suc B) = ro (inj₂ tt) L.zero refl (L.Ω-refl (nat (suc B))) (λ x e p → ru-s (up-read p))

self : ∀ {B ℓ} {σ : L.Simᴵ ℓ (nat (suc B))} {a b} → Read B σ a b → a L.≅ a
self rz = L.z≅
self (rs p) = L.s≅ (self p)
self (rl p) = L.l≅ (λ n → self (p n))
self (ro κ q e sa p) = sa
self (ru-s p) = L.upˡ (L.upʳ (self p))
self (ru-l p) = L.upˡ (L.upʳ (self p))
self (rc e p) = L.≅-trans e (L.≅-sym e)
```

floor-read实填全部原有限地板，包括0层的1。Coord只向严格较低有限
层递归；Bridge的分支律预先以Q为参数，不把同层关系负递归放入定义。
ro显式携原节点自相关，避免猜测任意高层坐标可反射。
尚未在本篇声称观察保持Read或完成全有限族值验收。
