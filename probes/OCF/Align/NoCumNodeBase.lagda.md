# 第 0 层是值: 高度 0 的项与 `CumReadCF` 同值

> 不含记号. 入口 [NoCumNode](NoCumNode.lagda.md). `V-Q`: 高度 0 的项 $x$ 与 [CumReadCF](CumReadCF.lagda.md) 的项对应 (`Sq`), 则 $x$ 的值 $\cong$ `ord (ψ azero x′)`. 这里第 0 层的加法是树上的 (`rep₀`), 那边是数据上的, 差结合律 (`rep-ord`); 那边高度 0 没有闭包, 所以这两边一致, $\psi_0(\Omega_\Omega)$ 这一站不变.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NoCumNodeBase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Free.Level as FL
open FL using (_≅_; z≅; s≅; l≅; lᵢ≅; upˡ; upʳ)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; Lg; z⊲; ≪S; ≪⊲; ⊲-tr; keep; rise; rkT; Tg; tgS; lgS)
import OCF.Align.CumReadCF as C
open C using () renaming (O to Oᶜ)
open import OCF.Align.CumReadCFThm using (ord; Y)
open import OCF.Align.NoCumLit hiding (Sq)
open import Data.Product using (_,_)
open import OCF.Align.NoCumW
open import OCF.Align.NoCumForce using (outs)
open import OCF.Align.NoCumHnBridge
open import OCF.Align.NoCumNodeE hiding (zP)
open import OCF.Align.Om1HnCx using (≅₀-refl; ≅₀-sym; ≅₀-trans)

z+₀ : ∀ a → FL.zero +₀ a ≅ a
z+₀ FL.zero = z≅
z+₀ (FL.suc a) = s≅ (z+₀ a)
z+₀ (FL.lim f) = l≅ (λ n → z+₀ (f n))
z+₀ (FL.limᵢ () f)
z+₀ (FL.up () x)

+₀assoc : ∀ a b c → (a +₀ b) +₀ c ≅ a +₀ (b +₀ c)
+₀assoc a b FL.zero = ≅₀-refl (a +₀ b)
+₀assoc a b (FL.suc c) = s≅ (+₀assoc a b c)
+₀assoc a b (FL.lim f) = l≅ (λ n → +₀assoc a b (f n))
+₀assoc a b (FL.limᵢ () f)
+₀assoc a b (FL.up () x)

rep-comm : ∀ a n → rep₀ a n +₀ a ≅ a +₀ rep₀ a n
rep-comm a zero = z+₀ a
rep-comm a (suc n) = ≅₀-trans (+₀assoc a (rep₀ a n) a) (+₀≅ (≅₀-refl a) (rep-comm a n))

add-ord : ∀ (W y : Oᶜ azero) → ord (C.add W C.self y) ≅ ord W +₀ ord y
add-ord W C.o0 = ≅₀-refl (ord W)
add-ord W (C.os y) = s≅ (add-ord W y)
add-ord W (C.ol F) = l≅ (λ n → add-ord W (F n))
add-ord W (C.oi () h)
add-ord W (C.oe () x)

rep-ord : ∀ {a} (W : Oᶜ azero) → a ≅ ord W → ∀ n → rep₀ a n ≅ ord (C.rep W n)
rep-ord W e zero = z≅
rep-ord W e (suc zero) = e
rep-ord {a} W e (suc (suc n)) =
  ≅₀-trans (≅₀-sym (rep-comm a (suc n))) (≅₀-trans (+₀≅ (rep-ord W e (suc n)) e) (≅₀-sym (add-ord (C.rep W (suc n)) W)))

Q⌜⌝ : ∀ {a} (z : Oᶜ azero) → a ≅ ord z → Sq ⌜ a ⌝ z
Q⌜⌝ C.o0 z≅ = qz
Q⌜⌝ (C.os z) (s≅ e) = qs (Q⌜⌝ z e)
Q⌜⌝ (C.ol F) (l≅ h) = qL (λ n → Q⌜⌝ (F n) (h n))
Q⌜⌝ (C.oi () h) e
Q⌜⌝ (C.oe () x) e

V-Q : ∀ {a u} {x : 𝓞 zero a u} {x′ : Oᶜ a} {gu m gm um am} (T : Tg azero a) (w : Lg a) → Sq x x′ → (d : E x gu m gm um am) → val x d ≅ ord (C.ψ azero T w x′)
V-i : ∀ {a u k} {r r′ : k ≪ a} {h : ∀ {v} → u ⊲ v → Gw v → Vs zero a (≪S r) v → 𝓞 zero a v} {h′ : C.Vs a (≪S r′) → Oᶜ a} (T : Tg azero a) (w : Lg a) →
      (∀ {v} (w₁ : u ⊲ v) (g : Gw v) (z : 𝓞 zero k v) (z′ : Oᶜ k) → SS a (≪S r) (inS (≪S r) z) z′ → Sq (h w₁ g (inS (≪S r) z)) (h′ (C.inS (≪S r′) z′))) →
      ∀ {m gm um am kM} (R : Rs {zero} {a} {m} {zero} {k} gm am kM (λ z → h um gm (inS (≪S r) z)) (λ z → Ev (h um gm (inS (≪S r) z)) gm m gm C.self am) (λ z d → val (h um gm (inS (≪S r) z)) d)) →
      FL.lim (vRs R) ≅ FL.lim (λ n → ord (C.ψ azero T w (h′ (C.inS (≪S r′) (C.chainᵒ (λ z → C.ψ k (inj₁ (≪⊲ r′)) w (h′ (C.inS (≪S r′) z))) n)))))

V-Q T w qz d = s≅ z≅
V-Q T w (qs e) d = l≅ (rep-ord _ (V-Q T w e d))
V-Q T w (qL h) (Es , st) = l≅ (λ n → V-Q T w (h n) (Es n))
V-Q T w (qe es d) A₁ = V-Q _ _ d A₁
V-Q T w (qe (el n) d) A₁ = V-Q _ _ d A₁
V-Q T w (qw d) A₁ = V-Q T w d A₁
V-Q {m = m} {gm} {um} {am} T w (qi {r = r} {r′ = r′} {h = h} {h′ = h′} H) A₁ with rkT r′ T w
... | keep ()
... | rise _ = V-i {r = r} {r′} {h} {h′} T w H {m} {gm} {um} {am} A₁

V-i {k = k} {r} {r′} {h} {h′} T w H {m} {gm} {um} {am} {kM} (rg nz Es st) = l≅ (λ n → V-Q T w (H um gm _ _ (Q→S (≪S r) (chain n))) (Es n))
  where
  chain : ∀ n → Sq (chainᵒ gm (λ z₁ → ψ zero k (h um gm (inS (≪S r) z₁)) gm m gm C.self kM am) n)
                   (C.chainᵒ (λ z → C.ψ k (inj₁ (≪⊲ r′)) w (h′ (C.inS (≪S r′) z))) n)
  chain zero = Q-Ωat k gm
  chain (suc n) = Q-ψ gm m gm C.self kM am (inj₁ (≪⊲ r′)) w (H um gm _ _ (Q→S (≪S r) (chain n)))
V-i {r = r} {r′} {h} {h′} T w H {m} {gm} {um} {am} {kM} (rv is0 vz Es tS st) = l≅ (λ n → V-Q T w (H um gm _ _ (Q→S (≪S r) (Qz n))) (Es n))
  where
  zc = C.chainᵒ (λ z → C.ψ azero (inj₁ (≪⊲ r′)) w (h′ (C.inS (≪S r′) z)))
  vv : ∀ n → outs v₁ vz n ≅ ord (zc n)
  Qz : ∀ n → Sq (lfv gm (outs v₁ vz n)) (zc n)
  vv zero = s≅ z≅
  vv (suc n) = ≅₀-trans (tS n) (V-Q (inj₁ (≪⊲ r′)) w (H um gm _ _ (Q→S (≪S r) (Qz n))) (Es n))
  Qz n = qw (Q⌜⌝ (zc n) (vv n))
```
