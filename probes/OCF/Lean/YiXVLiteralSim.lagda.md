# YiXVLiteralSim
> 验收文件。档位：编译定理。字面代表性质在恒等父界换型、字面 Sim、前驱包含复合与后继中保持。
> 按 YiLSRead.St≺/st-dn/lt≺ 与 Level.sim/<ᴵ-dec 的现有计算证明；未交可数层折叠闭包或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVLiteralSim where
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
import OCF.Align.Level as L

Literal : ∀ {a b} → a L.≺ᴵ b → Set
Literal {a} (L.via {a′} e r) = a ≡ a′
LitSim : ∀ {a b} → a L.⊑ᴵ b → Set
LitSim {a} w = ∀ {i} (q : i L.<ᴵ a) → Literal (L.sim w q)
pred : L.Ordᴵ → L.Ordᴵ
pred L.zero = L.zero
pred (L.suc a) = a
pred (L.lim f s) = L.zero
at : L.Ordᴵ → ℕ → L.Ordᴵ
at L.zero n = L.zero
at (L.suc a) n = L.zero
at (L.lim f s) n = f n
moved : ∀ {i a b} (q : i L.<ᴵ a) (e : a L.≅ᴵ b) → a ≡ b → Literal (L.<-≅ q e)
moved L.zero (L.s≅ e) same = cong pred same
moved (L.suc q) (L.s≅ e) same with L.<-≅ q e | moved q e (cong pred same)
... | L.via d r | h = h
moved (L.lim n q) (L.l≅ f) same with L.<-≅ q (f n) | moved q (f n) (cong (λ a → at a n) same)
... | L.via d r | h = h
composed : ∀ {a b c} (p : a L.≺ᴵ b) (q : b L.≺ᴵ c) → Literal p → Literal q → Literal (L.≺ᴵ-trans p q)
composed (L.via e r) (L.via f s) hp hq with L.<-≅ r f | moved r f hq
... | L.via d t | ht = trans hp ht
canonical : ∀ {a b} (σ : L.Simᴵ a b) → LitSim (L.Sim→⊑ᴵ σ)
canonical {a = L.zero} σ ()
canonical {a = L.suc a} σ L.zero = refl
canonical {a = L.suc a} σ (L.suc q) = composed (L.<-≅ q (L.≅ᴵ-refl a)) (L.via (L.≅ᴵ-refl a) (σ L.zero))
  (moved q (L.≅ᴵ-refl a) refl) refl
canonical {a = L.lim f s} σ (L.lim n q) = canonical (λ r → σ (L.lim n r)) q

composition : ∀ {a b c} (p : a L.⊑ᴵ b) (q : b L.⊑ᴵ c) → LitSim p → LitSim q → LitSim (L.⊑ᴵ-trans p q)
composition L.z⊑ q hp hq ()
composition (L.s⊑ {a = a} e r) q hp hq t with L.sim q r | hq r
... | L.via f s | he = go t
  where
  eq : a ≡ _
  eq = trans (hp L.zero) he
  go : ∀ {i} (t : i L.<ᴵ L.suc a) → Literal (L.sim (L.s⊑ (L.≅ᴵ-trans e f) s) t)
  go L.zero = eq
  go (L.suc t) = composed (L.<-≅ t (L.≅ᴵ-trans e f)) (L.via (L.≅ᴵ-refl _) s)
    (moved t (L.≅ᴵ-trans e f) eq) refl
composition (L.l⊑ h) q hp hq (L.lim n t) = composition (h n) q (λ r → hp (L.lim n r)) hq t

succ : ∀ {a b} (p : a L.≺ᴵ b) → Literal p → Literal (L.≺-suc p)
succ (L.via e r) h = h
limit : ∀ {a : L.Ordᴵ} {f : ℕ → L.Ordᴵ} {s : ∀ n → f n L.⊑ᴵ f (suc n)} n (p : a L.≺ᴵ f n) → Literal p → Literal (L.≺-lim {s = s} n p)
limit n (L.via e r) h = h
successor : ∀ {a b} (p : a L.≺ᴵ b) → Literal p → LitSim (L.s⊑′ p)
successor (L.via e r) hp L.zero = hp
successor (L.via e r) hp (L.suc q) = composed (L.<-≅ q e) (L.via (L.≅ᴵ-refl _) r) (moved q e hp) refl
```
