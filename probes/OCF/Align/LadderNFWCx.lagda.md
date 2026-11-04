> **机械克隆, 验收用.** 由 `LadderNFCx` 经脚本复制, 只改导入, 把证书搬到标签阶梯的世界. 见 [LadderNFAccept](LadderNFAccept.lagda.md).

# 阶梯去记号 (三): 上下文

> 结论写在 [LadderNF](LadderNF.lagda.md). 与 `OCF.Align.LadderNFWBase` §7 同形. `Cx m c φ χ` 多三个构造子: `pΨ` (目标在高度 $H$ 的求值, 世界在栈帧上), `pD` (`ι↓`), 和 `top` 带世界. 相似 `≈ᶜ` 仍是同层, 同样的栈形, 只有底部与世界不同. 不读记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderNFWCx where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import OCF.Align.Level
open import OCF.Align.LadderNFWPrefix using (Ordˢ; trˢ; tr⁻ˢ; addˢ; toZ)
open import OCF.Align.LadderNFWEq using (_≅ˢ_; addˢ-≅; trˢ-≅; tr⁻ˢ-≅; ≅-trˢ; ≅-tr⁻ˢ; ≅ˢ-reflˡ; ≅ˢ-reflʳ)
open import OCF.Align.LadderNFWFloor using (Flr; fz; fk; _⊔_; Ev; flo; cvFlo; ∼ᶠ-refl; _∼ᶠ_)
open import OCF.Align.LadderNFWFT using (Fl)
open import OCF.Align.LadderNFWTree
open import OCF.Align.LadderNFWRel

data Obs : Ordᴵ → Set
data Cx : ℕ → Ordᴵ → Flr → Fv → Set

data Obs where
  idO  : Obs zero
  tlo  : ∀ {k χ} → Cx 0 zero (flo k) χ → Obs k
  addo : ∀ {k ℓ} → Obs ℓ → Ordˢ ℓ → Simᴵ k ℓ → Obs k
  tro  : ∀ {a b} → Obs b → a ≅ᴵ b → Obs a
  tr⁻o : ∀ {a b} → Obs a → a ≅ᴵ b → Obs b

data Cx where
  top : ∀ {m c φ χ i ℓ w} → Obs i → Ev ℓ φ → i <ᴵ ℓ → Ok w → Eh zero m w χ → Cx m c φ χ
  pa  : ∀ {m c a b φ χ} → Q m c a b → Cx m c (a ⊔ φ) (b ∪ χ) → Cx m c φ χ
  pψ  : ∀ {m c t φ χ} → t <ᴵ c → Cx m t (Fl ⊔ φ) (Z* χ) → Cx m c φ χ
  pΨ  : ∀ {H m c t φ χ w} → H <ᴸ m → Ok w → Eh H m w χ → t <ᴵ w H → Cx H t (Fl ⊔ φ) (Z* χ) → Cx m c φ χ
  pι  : ∀ {m c d φ χ} → c ◃ d → Cx m d φ χ → Cx m c φ χ
  pD  : ∀ {n k φ χ} → Cx (suc n) zero φ (upd χ n (flo k)) → Cx n k φ χ
  ptr  : ∀ {m a b φ χ} → a ≅ᴵ b → Cx m b φ χ → Cx m a φ χ
  ptr⁻ : ∀ {m a b φ χ} → a ≅ᴵ b → Cx m a φ χ → Cx m b φ χ

run  : ∀ {k} → Obs k → Ordˢ k → Ordˢ zero
runᶜ : ∀ {m c φ χ} → Cx m c φ χ → Q m c φ χ → Ordˢ zero
run idO          x = x
run (tlo {k = k} C) x = runᶜ C (tl (flo k) (cvFlo k) x)
run (addo O a σ) x = run O (addˢ a σ x)
run (tro O e)    x = run O (trˢ e x)
run (tr⁻o O e)   x = run O (tr⁻ˢ e x)
runᶜ (top O ev p ok e) x = run O (ψ̄ᵠ ok e x ev p)
runᶜ (pa W C)     x = runᶜ C (W ⊞ x)
runᶜ (pψ q C)     x = runᶜ C (ψᵠ q x)
runᶜ (pΨ qH ok e p C) x = runᶜ C (Ψ qH ok e p x)
runᶜ (pι q C)     x = runᶜ C (ι q x)
runᶜ (pD C)       x = runᶜ C (ι↓ x)
runᶜ (ptr e C)    x = runᶜ C (trQ e x)
runᶜ (ptr⁻ e C)   x = runᶜ C (tr⁻Q e x)

wkC : ∀ {m c φ χ ψ ρ} → (∀ {L} → Ev L ψ → Ev L φ) → Sub m ρ χ → Cx m c ψ ρ → Cx m c φ χ
wkC le lc (top O ev p ok e) = top O (le ev) p ok (λ i h r → lc i r (e i h r))
wkC le lc (pa W C)     = pa W (wkC (λ e → proj₁ e , le (proj₂ e)) (λ i q e → proj₁ e , lc i q (proj₂ e)) C)
wkC le lc (pψ q C)     = pψ q (wkC (λ e → proj₁ e , le (proj₂ e)) (λ i r e → proj₁ e , lc i r (proj₂ e)) C)
wkC le lc (pΨ qH ok e p C) = pΨ qH ok (λ i h r → lc i r (e i h r)) p (wkC (λ u → proj₁ u , le (proj₂ u)) (λ i r u → proj₁ u , lc i (tr< r qH) (proj₂ u)) C)
wkC le lc (pι q C)     = pι q (wkC le lc C)
wkC {m = n} le lc (pD C) = pD (wkC le (upd-sub n lc (λ e → e)) C)
wkC le lc (ptr e C)    = ptr e (wkC le lc C)
wkC le lc (ptr⁻ e C)   = ptr⁻ e (wkC le lc C)

run-wkC : ∀ {m c φ χ ψ ρ} (le : ∀ {L} → Ev L ψ → Ev L φ) (lc : Sub m ρ χ) (C : Cx m c ψ ρ) (x : Q m c φ χ) → runᶜ (wkC le lc C) x ≡ runᶜ C (qwk le lc x)
run-wkC le lc (top O ev p ok e) x = refl
run-wkC le lc (pa W C)     x = run-wkC (λ e → proj₁ e , le (proj₂ e)) (λ i q e → proj₁ e , lc i q (proj₂ e)) C (W ⊞ x)
run-wkC le lc (pψ q C)     x = run-wkC (λ e → proj₁ e , le (proj₂ e)) (λ i r e → proj₁ e , lc i r (proj₂ e)) C (ψᵠ q x)
run-wkC le lc (pΨ qH ok e p C) x = run-wkC (λ u → proj₁ u , le (proj₂ u)) (λ i r u → proj₁ u , lc i (tr< r qH) (proj₂ u)) C (Ψ qH ok (λ i h r → lc i r (e i h r)) p x)
run-wkC le lc (pι q C)     x = run-wkC le lc C (ι q x)
run-wkC {m = n} le lc (pD C) x = run-wkC le (upd-sub n lc (λ e → e)) C (ι↓ x)
run-wkC le lc (ptr e C)    x = run-wkC le lc C (trQ e x)
run-wkC le lc (ptr⁻ e C)   x = run-wkC le lc C (tr⁻Q e x)

infix 4 _≈ᵒ_ _≈ᶜ_
data _≈ᵒ_ : ∀ {k k′} → Obs k → Obs k′ → Set
data _≈ᶜ_ : ∀ {m c φ χ ψ ρ} → Cx m c φ χ → Cx m c ψ ρ → Set

data _≈ᵒ_ where
  idO  : idO ≈ᵒ idO
  tlo  : ∀ {k k′ χ ρ} {C : Cx 0 zero (flo k) χ} {C′ : Cx 0 zero (flo k′) ρ} → C ≈ᶜ C′ → tlo C ≈ᵒ tlo C′
  addo : ∀ {k k′ ℓ ℓ′} {O : Obs ℓ} {O′ : Obs ℓ′} {a : Ordˢ ℓ} {a′ : Ordˢ ℓ′} {σ : Simᴵ k ℓ} {σ′ : Simᴵ k′ ℓ′} →
         O ≈ᵒ O′ → ℓ ≅ᴵ ℓ′ → a ≅ˢ a′ → addo O a σ ≈ᵒ addo O′ a′ σ′
  tro  : ∀ {a a′ b b′} {O : Obs b} {O′ : Obs b′} {e : a ≅ᴵ b} {e′ : a′ ≅ᴵ b′} → O ≈ᵒ O′ → tro O e ≈ᵒ tro O′ e′
  tr⁻o : ∀ {a a′ b b′} {O : Obs a} {O′ : Obs a′} {e : a ≅ᴵ b} {e′ : a′ ≅ᴵ b′} → O ≈ᵒ O′ → tr⁻o O e ≈ᵒ tr⁻o O′ e′

data _≈ᶜ_ where
  top : ∀ {m c φ χ ψ ρ i ℓ ℓ′ w w′} {O O′ : Obs i} {ev : Ev ℓ φ} {ev′ : Ev ℓ′ ψ} {p : i <ᴵ ℓ} {p′ : i <ᴵ ℓ′} {ok : Ok w} {ok′ : Ok w′} {e : Eh zero m w χ} {e′ : Eh zero m w′ ρ} → O ≈ᵒ O′ → _≈ᶜ_ {m} {c} (top O ev p ok e) (top O′ ev′ p′ ok′ e′)
  pa  : ∀ {m c a b φ χ ψ ρ} {W : Q m c a b} {C : Cx m c (a ⊔ φ) (b ∪ χ)} {C′ : Cx m c (a ⊔ ψ) (b ∪ ρ)} → Rq m c c W W → C ≈ᶜ C′ → pa W C ≈ᶜ pa W C′
  pψ  : ∀ {m c t φ χ ψ ρ} {q : t <ᴵ c} {C : Cx m t (Fl ⊔ φ) (Z* χ)} {C′ : Cx m t (Fl ⊔ ψ) (Z* ρ)} → C ≈ᶜ C′ → pψ q C ≈ᶜ pψ q C′
  pΨ  : ∀ {H m c t φ χ ψ ρ w w′} {qH : H <ᴸ m} {ok : Ok w} {ok′ : Ok w′} {e : Eh H m w χ} {e′ : Eh H m w′ ρ} {p : t <ᴵ w H} {p′ : t <ᴵ w′ H} {C : Cx H t (Fl ⊔ φ) (Z* χ)} {C′ : Cx H t (Fl ⊔ ψ) (Z* ρ)} →
        C ≈ᶜ C′ → _≈ᶜ_ {m} {c} (pΨ qH ok e p C) (pΨ qH ok′ e′ p′ C′)
  pι  : ∀ {m c d φ χ ψ ρ} {q : c ◃ d} {C : Cx m d φ χ} {C′ : Cx m d ψ ρ} → C ≈ᶜ C′ → pι q C ≈ᶜ pι q C′
  pD  : ∀ {n k φ χ ψ ρ} {C : Cx (suc n) zero φ (upd χ n (flo k))} {C′ : Cx (suc n) zero ψ (upd ρ n (flo k))} → C ≈ᶜ C′ → pD C ≈ᶜ pD C′
  ptr  : ∀ {m a b φ χ ψ ρ} {e e′ : a ≅ᴵ b} {C : Cx m b φ χ} {C′ : Cx m b ψ ρ} → C ≈ᶜ C′ → ptr e C ≈ᶜ ptr e′ C′
  ptr⁻ : ∀ {m a b φ χ ψ ρ} {e e′ : a ≅ᴵ b} {C : Cx m a φ χ} {C′ : Cx m a ψ ρ} → C ≈ᶜ C′ → ptr⁻ e C ≈ᶜ ptr⁻ e′ C′

run-≅  : ∀ {k k′} {O : Obs k} {O′ : Obs k′} {x : Ordˢ k} {x′ : Ordˢ k′} → O ≈ᵒ O′ → x ≅ˢ x′ → run O x ≅ˢ run O′ x′
runᶜ-≅ : ∀ {m c φ χ ψ ρ} {C : Cx m c φ χ} {C′ : Cx m c ψ ρ} {x : Q m c φ χ} {x′ : Q m c ψ ρ} → C ≈ᶜ C′ → Rq m c c x x′ → runᶜ C x ≅ˢ runᶜ C′ x′
run-≅ idO          d = d
run-≅ (tlo o)      d = runᶜ-≅ o (R-tl d)
run-≅ (addo o k a) d = run-≅ o (addˢ-≅ k a d)
run-≅ (tro {e = e} {e′ = e′} o)  d = run-≅ o (trˢ-≅ e (≅-trˢ e′ d))
run-≅ (tr⁻o {e = e} {e′ = e′} o) d = run-≅ o (tr⁻ˢ-≅ e (≅-tr⁻ˢ e′ d))
runᶜ-≅ (top {i = i} {ok = ok} {ok′ = ok′} {e = e} {e′ = e′} o) r = run-≅ o (R→≈ᵠ r ok e ok′ e′ _ _ _ _ (≅ᴵ-refl i))
runᶜ-≅ (pa {a = a} {b = b} rW o) r = runᶜ-≅ o (R-⊞ (∼ᶠ-refl a) (λ i q → ∼ᶠ-refl (b i)) rW r)
runᶜ-≅ (pψ {q = q} o) r = runᶜ-≅ o (R-ψᵠ q q (≅ᴵ-refl _) r)
runᶜ-≅ (pΨ {t = t} {qH = qH} {ok = ok} {ok′ = ok′} {e = e} {e′ = e′} {p = p} {p′ = p′} o) r = runᶜ-≅ o (R-Ψ qH ok e p ok′ e′ p′ (≅ᴵ-refl t) r)
runᶜ-≅ (pι {q = q} o) r = runᶜ-≅ o (R-ι q q r)
runᶜ-≅ (pD {k = k} o) r = runᶜ-≅ o (R-ι↓ (≅ᴵ-refl k) r)
runᶜ-≅ (ptr {e = e} {e′ = e′} o) r = runᶜ-≅ o (R-trˡ e (R-trʳ e′ r))
runᶜ-≅ (ptr⁻ {e = e} {e′ = e′} o) r = runᶜ-≅ o (R-tr⁻ˡ e (R-tr⁻ʳ e′ r))
```
