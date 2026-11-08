# Ladder 底输出的直接融合

直接生成 Z；高目标的反馈仍逐字调用原运行器。这里只融合最后的
Run／Ordˢ zero／toZ 三层，不删除 cap 或非零回灌。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.TreeEmitBuild (𝕊 : HtB) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥-elim)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁)
open import Relation.Binary.PropositionalEquality using (subst; refl)
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; Ordˢ; Ord₊ˢ; toZ; _+ˢ_; Ωˢ)
open import OCF.Free.Floor
open import OCF.Free.OrbitRewriteIf
open import OCF.Align.LadderOrdTree 𝕊
open import OCF.Align.TreeEmitIf 𝕊

point-self : ∀ a → Pointwise a a
point-self Z.zero = pz
point-self (Z.suc a) = ps (point-self a)
point-self (Z.lim f) = pl (λ n → point-self (f n))
point-self (Z.ĉᴸ c t g o h) = pc (point-self t) (λ η e → point-self (g η e)) (point-self o) (λ η e → point-self (h η e))

compose : ∀ {a b c} → Pointwise a b → Pointwise b c → Pointwise a c
compose pz pz = pz
compose (ps p) (ps q) = ps (compose p q)
compose (pl p) (pl q) = pl (λ n → compose (p n) (q n))
compose (pc p f q g) (pc p′ f′ q′ g′) = pc (compose p p′) (λ η e → compose (f η e) (f′ η e)) (compose q q′) (λ η e → compose (g η e) (g′ η e))

add : Z → Z → Z
add a Z.zero = a
add a (Z.suc b) = Z.suc (add a b)
add a (Z.lim f) = Z.lim (λ n → add a (f n))
add a (Z.ĉᴸ c t g o h) = Z.ĉᴸ c t g (add a o) (λ η e → add a (h η e))

add-related : ∀ {a a′ b b′} → Pointwise a a′ → Pointwise b b′ → Pointwise (add a b) (add a′ b′)
add-related p pz = p
add-related p (ps q) = ps (add-related p q)
add-related p (pl q) = pl (λ n → add-related p (q n))
add-related p (pc q f r g) = pc q f (add-related p r) (λ η e → add-related p (g η e))

add-fusion : ∀ (a b : Ordˢ zero) → Pointwise (toZ (a +ˢ b)) (add (toZ a) (toZ b))
add-fusion a Ord₊ˢ.zero = point-self (toZ a)
add-fusion a (Ord₊ˢ.suc b) = ps (add-fusion a b)
add-fusion a (Ord₊ˢ.lim f) = pl (λ n → add-fusion a (f n))
add-fusion a (Ord₊ˢ.limᵢ () f)
add-fusion a (Ord₊ˢ.up () b)
add-fusion a (Ord₊ˢ.ŝ c t g) = pc (point-self (toZ t)) (λ η e → point-self (toZ (g η e))) (add-fusion a t) (λ η e → add-fusion a (g η e))
add-fusion a (Ord₊ˢ.ĉᴸ c t g o h) = pc (point-self t) (λ η e → point-self (g η e)) (add-fusion a o) (λ η e → add-fusion a (h η e))

repeat-fusion : ∀ (a : Ordˢ zero) {b} → Pointwise (toZ a) b → ∀ n → Pointwise (toZ (iter (a +ˢ_) Ord₊ˢ.zero n)) (iter (add b) Z.zero n)
repeat-fusion a p zero = pz
repeat-fusion a p (suc n) = compose (add-fusion a _) (add-related p (repeat-fusion a p n))

emit : ∀ {m c φ χ w ℓ} → Ok w → Eh h₀ m w χ → Q m c φ χ → Ev ℓ φ → zero <ᴵ ℓ → Z
emit ok e q0 ev p = Z.suc Z.zero
emit ok e (qs a) ev p = Z.lim (iter (add (emit ok e a ev p)) Z.zero)
emit ok e (ql f) ev p = Z.lim (λ n → emit ok e (f n) ev p)
emit ok e (qi ac f) ev p with <ᴵ-dec (ac ev) p
... | injᵃ (via eq ())
... | injᵇ _ = Z.lim (λ n → emit ok e (f (iter (λ x → ψ̄ᵠ ok e (f x) ev (ac ev)) (Ωˢ _) n)) ev p)
... | injᶜ _ = Z.lim (λ n → emit ok e (f (iter (λ x → ψ̄ᵠ ok e (f x) ev (ac ev)) (Ωˢ _) n)) ev p)
emit ok e (qŝ c t g) ev p = Z.ĉᴸ c (emit ok e t ev p) (λ η d → emit ok e (g η d) ev p) (emit ok e t ev p) (λ η d → emit ok e (g η d) ev p)
emit ok e (qĉ c t g o h) ev p = Z.ĉᴸ c t g (emit ok e o ev p) (λ η d → emit ok e (h η d) ev p)
emit ok e (qclo {φ = φ} t g) ev p = Z.ĉᴸ (Bd B) (emit ok e t ev p) next (emit ok e t ev p) next
  where
  B = bound (φ ⊔ fk zero) ev p
  next = λ η d → emit ok e (g η) (evη φ B η d) (lim 0 (iF B))
emit {χ = χ} {w = w} ok e (qcl {n = n} q ψ s t g) ev p = Z.ĉᴸ (Bd B) (emit ok e t ev p) next (emit ok e t ev p) next
  where
  B = bound (ψ ⊔ fk zero) (s (e n (Hi-0 n) q)) (zr ok n)
  next = λ η d → emit (upd-ok n w ok (tt , λ q′ → lim 0 (proj₂ (evF B) q′))) (λ i h r → upd-ev n i w χ (evη ψ B η d) (e i h r)) (g η) ev p
emit ok e (qwk le le′ x) ev p = emit ok (λ i h r → le′ i r (e i h r)) x (le ev) p
emit ok e (omk r z x) ev p = emit ok e x ev p
emit {φ = φ} {χ = χ} ok e (qΩ↓ {n = n} q fe ac h) ev p = Z.lim (λ i → emit ok (e⁺ n ok e) (h φ (Z* χ) (intoV q (chainᵠ fe fc* (λ z → qwk (λ v → fe v , (v , v)) (⇑ (cv* n)) (Ψ q ok (e⁺ n ok (e↓ e)) (ac (e↓ e n (inj₁ refl) q)) (h φ (Z* χ) (intoV q z)))) i))) (ev , ev) p)
emit {m} {φ = φ} {χ = χ} ok e (qΩ fe r h) ev p = Z.lim (λ i → emit ok (e⁺ m ok e) (h φ (Z* χ) (intoU (<→◃ r) (chainᵠ fe fc* (λ z → qwk (λ v → fe v , (v , v)) (⇑ (cv* m)) (ψᵠ r (h φ (Z* χ) (intoU (<→◃ r) z)))) i))) (ev , ev) p)

sound : ∀ {m c φ χ w ℓ} (ok : Ok w) (e : Eh h₀ m w χ) (x : Q m c φ χ) (ev : Ev ℓ φ) (p : zero <ᴵ ℓ) → Pointwise (toZ (ψ̄ᵠ ok e x ev p)) (emit ok e x ev p)
sound ok e q0 ev p = ps pz
sound ok e (qs a) ev p = pl (repeat-fusion (ψ̄ᵠ ok e a ev p) (sound ok e a ev p))
sound ok e (ql f) ev p = pl (λ n → sound ok e (f n) ev p)
sound ok e (qi ac f) ev p with <ᴵ-dec (ac ev) p
... | injᵃ (via eq ())
... | injᵇ _ = pl (λ n → sound ok e (f (iter (λ x → ψ̄ᵠ ok e (f x) ev (ac ev)) (Ωˢ _) n)) ev p)
... | injᶜ _ = pl (λ n → sound ok e (f (iter (λ x → ψ̄ᵠ ok e (f x) ev (ac ev)) (Ωˢ _) n)) ev p)
sound ok e (qŝ c t g) ev p = pc (sound ok e t ev p) (λ η d → sound ok e (g η d) ev p) (sound ok e t ev p) (λ η d → sound ok e (g η d) ev p)
sound ok e (qĉ c t g o h) ev p = pc (point-self t) (λ η d → point-self (g η d)) (sound ok e o ev p) (λ η d → sound ok e (h η d) ev p)
sound ok e (qclo {φ = φ} t g) ev p = pc (sound ok e t ev p) next (sound ok e t ev p) next
  where
  B = bound (φ ⊔ fk zero) ev p
  next = λ η d → sound ok e (g η) (evη φ B η d) (lim 0 (iF B))
sound {χ = χ} {w = w} ok e (qcl {n = n} q ψ s t g) ev p = pc (sound ok e t ev p) next (sound ok e t ev p) next
  where
  B = bound (ψ ⊔ fk zero) (s (e n (Hi-0 n) q)) (zr ok n)
  next = λ η d → sound (upd-ok n w ok (tt , λ q′ → lim 0 (proj₂ (evF B) q′))) (λ i h r → upd-ev n i w χ (evη ψ B η d) (e i h r)) (g η) ev p
sound ok e (qwk le le′ x) ev p = sound ok (λ i h r → le′ i r (e i h r)) x (le ev) p
sound ok e (omk r z x) ev p = sound ok e x ev p
sound {φ = φ} {χ = χ} ok e (qΩ↓ {n = n} q fe ac h) ev p = pl (λ i → sound ok (e⁺ n ok e) (h φ (Z* χ) (intoV q (chainᵠ fe fc* (λ z → qwk (λ v → fe v , (v , v)) (⇑ (cv* n)) (Ψ q ok (e⁺ n ok (e↓ e)) (ac (e↓ e n (inj₁ refl) q)) (h φ (Z* χ) (intoV q z)))) i))) (ev , ev) p)
sound {m} {φ = φ} {χ = χ} ok e (qΩ fe r h) ev p = pl (λ i → sound ok (e⁺ m ok e) (h φ (Z* χ) (intoU (<→◃ r) (chainᵠ fe fc* (λ z → qwk (λ v → fe v , (v , v)) (⇑ (cv* m)) (ψᵠ r (h φ (Z* χ) (intoU (<→◃ r) z)))) i))) (ev , ev) p)

contract : EmitContract
contract = record { emit = emit ; sound = sound }
```

sound 覆盖任意原输入及当前世界证据；高层链两边调用的是同一原程序，
所以无需假定任意回调保同形，也未偷用非零参数的 D-val。
