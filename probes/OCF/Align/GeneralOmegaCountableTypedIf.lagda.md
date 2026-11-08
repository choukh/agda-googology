# 原可数高度的typed异层读回接口

验收专用。参照高度按原B的形状构造，合法步进来自原LgB。ambient
映射进入height B本身，故并层注入能沿相同Nat编号映真实kind前驱；
不把整个极限分量误认作其并层的严格前驱。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableTypedIf where
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaCountableObserveIf using (F)
open import OCF.Lean.GeneralOmegaCountableNextCapturePoint using (pointFloor)
open import OCF.Lean.GeneralOmegaCountableNextCapturePointIf using (point-observe)
import OCF.Align.Level as L
import OCF.Align.LambdaCountableBridge as Z
open import OCF.Align.GeneralOmegaCountableTypedHeight using (height)

rank : ∀ B → LgB B → K (F B) → L.Ordᴵ
rank hz lB ()
rank (hs B) lB (inj₁ κ) = rank B lB κ
rank (hs B) lB (inj₂ _) = height B lB
rank (hl f) lB (n , κ) = rank (f n) (proj₂ lB n) κ
rank (hΩ () f) lB κ
bound : ∀ B (lB : LgB B) κ → rank B lB κ L.<ᴵ height B lB
bound hz lB ()
bound (hs B) lB (inj₁ κ) = L.suc (bound B lB κ)
bound (hs B) lB (inj₂ _) = L.zero
bound (hl f) lB (n , κ) = L.lim n (bound (f n) (proj₂ lB n) κ)
bound (hΩ () f) lB κ
canonical : ∀ B lB → L.Simᴵ (height B lB) (height B lB)
canonical B lB q = q

data Bridge (B : Cd) (lB : LgB B)
  (Q : ∀ κ → L.Ordᶜ (rank B lB κ) → E (F B) κ → Set) :
  ∀ {ℓ} → L.Simᴵ ℓ (height B lB) → L.Ordᶜ ℓ → HB (F B) → Set where
  rz : ∀ {ℓ} {σ : L.Simᴵ ℓ (height B lB)} → Bridge B lB Q σ L.zero hz
  rs : ∀ {ℓ} {σ : L.Simᴵ ℓ (height B lB)} {a b} → Bridge B lB Q σ a b → Bridge B lB Q σ (L.suc a) (hs b)
  rl : ∀ {ℓ} {σ : L.Simᴵ ℓ (height B lB)} {f g} → (∀ n → Bridge B lB Q σ (f n) (g n)) → Bridge B lB Q σ (L.lim f) (hl g)
  ro : ∀ {ℓ} {σ : L.Simᴵ ℓ (height B lB)} (κ : K (F B)) (q : rank B lB κ L.<ᴵ ℓ) {f g} →
    σ q ≡ bound B lB κ → L.limᵢ q f L.≅ L.limᵢ q f →
    (∀ x e → Q κ x e → Bridge B lB Q σ (f (L.into (L.<→◃ q) x)) (g e)) →
    Bridge B lB Q σ (L.limᵢ q f) (hΩ κ g)
  ru-s : ∀ {ℓ} {σ : L.Simᴵ (L.suc ℓ) (height B lB)} {a b} →
    Bridge B lB Q (λ q → σ (L.suc q)) a b → Bridge B lB Q σ (L.up L.zero a) b
  ru-l : ∀ {f s} {σ : L.Simᴵ (L.lim f s) (height B lB)} {i a b} →
    Bridge B lB Q (λ q → σ (L.lim i q)) a b → Bridge B lB Q σ (L.up (L.self i) a) b
  rc : ∀ {ℓ} {σ : L.Simᴵ ℓ (height B lB)} {a a′ b} →
    a L.≅ a′ → Bridge B lB Q σ a′ b → Bridge B lB Q σ a b

Read : ∀ B lB {ℓ} → L.Simᴵ ℓ (height B lB) → L.Ordᶜ ℓ → HB (F B) → Set
Coord : ∀ B lB κ → L.Ordᶜ (rank B lB κ) → E (F B) κ → Set
Read B lB = Bridge B lB (Coord B lB)
Coord hz lB ()
Coord (hs B) lB (inj₁ κ) = Coord B lB κ
Coord (hs B) lB (inj₂ _) = Read B lB (canonical B lB)
Coord (hl f) lB (n , κ) = Coord (f n) (proj₂ lB n) κ
Coord (hΩ () f) lB κ

record PointReading : Set₁ where
  field
    floor-read : ∀ B lB → Read B lB (canonical B lB) (L.Ω (height B lB)) (pointFloor B)
    self : ∀ {B lB ℓ} {σ : L.Simᴵ ℓ (height B lB)} {a b} → Read B lB σ a b → a L.≅ a
    coord-tr⁻ : ∀ B lB κ {x c} → Coord B lB κ x c →
      Coord B lB κ (L.tr⁻ (L.≅ᴵ-refl (rank B lB κ)) x) c
record RootObservation : Set₁ where
  field
    preserve : ∀ B lB {ℓ} {σ : L.Simᴵ ℓ (height B lB)} {a b} → Read B lB σ a b →
      L.ψ⁰ a L.≅ Z.read (point-observe B lB hz (z⊲ᴮ B) b)
```

ro显式给自相关，Coord只沿严格低层递归。PointReading须以原全B
逐点地板实填；RootObservation另列尚待验证的完整观察义务，不能
由floor-read推出。输入完成后的异秩变化未被此固定原B接口消除。
