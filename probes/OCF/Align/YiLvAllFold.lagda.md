# YiLvAll 主引理：一切输入层与目标层的折叠保持关系

**验收文件，档位：编译定理。** `FOLD M m`：`Rel M x η` 推出 `Rel m (ψ p σ x) (ψ_{sucᵐ 0} (up η))`，对一切 `M`, `m`, `p`, `σ`。
结点处参照一侧按 `<ᴵ-dec` 分情况，读成 `ℕ` 的三歧 (`below-nat`, `nat-inj`)；树一侧用 `TREE-KEEP`, `TREE-FOLD`。
保留时分支的输入过一次 `tr⁻`，由 `TRC-all` 吸收；折叠时两条链同步 (`ChainJ`)。入口 [YiLvAll](YiLvAll.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiLvAllFold where

open import Data.Nat.Base using (ℕ; zero; suc; _<_; _≤_)
open import Data.Nat.Properties using (<⇒≤; ≤-reflexive; ≮⇒≥; _<?_)
open import Relation.Nullary using (yes; no)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
import OCF.Align.RR5IrrCore as B
open B using (module G; LF; Raw; Pre; Low; GdL; Gd; Lgl; Nested; LglLow; NestedLow; lc)
open import OCF.Align.RR5IrrCheck using (cO; cO-Lgl; cO-Nested; up; upN; upT)
open import OCF.Align.YiIrrIf using (R; iterate)
open import OCF.Align.YiIrrFbIf using (Pt; pt; at)
open import OCF.Align.YiLvFoldBase using (Dom; dom-at; startᴸ; module Node)
open import OCF.Align.YiLvFoldFin using (fin; ψ; next; out)
open import OCF.Align.YiIrrFoldValue using (read)
open import OCF.Align.YiLvValBase using (⟨_⟩)
open import OCF.Align.YiLvAllRel
open import OCF.Align.YiLvAllTree using (TREE-KEEP; TREE-FOLD)
open import OCF.Align.YiLvAllAdd
import OCF.Align.Level as L
import OCF.Align.Value as V
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open L using (_≅ᴵ_; _<ᴵ_)
open V using (_≼_; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼)
```

## 1 结点：分支的归纳假设，链，保留，折叠

`Branches j q f c g`：参照结点 `limᵢ q f` 的每个分支对树结点的每个分支，在一切目标层上保持关系 (由 `FOLD` 对子推导的递归给出)。

```agda
Branches : ∀ j {j′ K} (q : j′ <ᴵ K) (f : L.U j′ (L.<→◃ q) → L.Ordᶜ K) (c : Raw (fin j))
  (g : (a : Raw (fin j)) → .(Gd (fin j) c a) → LF) → Set
Branches j {K = K} q f c g = ∀ m′ {ℓ′} (p′ : ⟨ m′ ⟩ <ᴵ ℓ′) (σ′ : L.Simᴵ K ℓ′) y a
  .(e : Gd (fin j) c a) .(d′ : Dom (g a e)) → Rel j y a →
  Rel m′ (L.ψ p′ σ′ (f (L.into (L.<→◃ q) y))) (ψ (fin m′) (g a e) d′)

module ChainJ (j : ℕ) {K} (q : ⟨ j ⟩ <ᴵ K) (f : L.U ⟨ j ⟩ (L.<→◃ q) → L.Ordᶜ K)
  (c : Raw (fin j)) .(w : Lgl (fin j) c) .(b : Nested (fin j) c) (t : LF)
  (g : (a : Raw (fin j)) → .(Gd (fin j) c a) → LF) .(d : Dom (lc (fin j) c w b t g))
  (base : Rel j (L.Ω ⟨ j ⟩) c) (IH : Branches j q f c g) where

  pts : ℕ → Pt (fin j) c
  pts = iterate (next (fin j) c w b t g d) (startᴸ (fin j) c w b)

  δ : ℕ → L.Ordᶜ ⟨ j ⟩
  δ = iter (λ x → L.ψ q (λ r → r) (f (L.into (L.<→◃ q) x))) (L.Ω ⟨ j ⟩)

  stepAt : ∀ (P : Pt (fin j) c) {x} → Rel j x (at P) →
    Rel j (L.ψ q (λ r → r) (f (L.into (L.<→◃ q) x))) (at (next (fin j) c w b t g d P))
  stepAt (pt a e) r =
    ABSORB j a (IH j q (λ r → r) _ a e (Node.branch (fin j) c w b t g d a e) r)

  chain : ∀ n → Rel j (δ n) (at (pts n))
  chain zero = base
  chain (suc n) = stepAt (pts n) (chain n)

  obsAt : ∀ m {ℓ} (p : ⟨ m ⟩ <ᴵ ℓ) (σ : L.Simᴵ K ℓ) (P : Pt (fin j) c) {x} → Rel j x (at P) →
    Rel m (L.ψ p σ (f (L.into (L.<→◃ q) x))) (out (fin m) (fin j) c w b t g d P)
  obsAt m p σ (pt a e) r = IH m p σ _ a e (Node.branch (fin j) c w b t g d a e) r

  obs : ∀ m {ℓ} (p : ⟨ m ⟩ <ᴵ ℓ) (σ : L.Simᴵ K ℓ) n →
    Rel m (L.ψ p σ (f (L.into (L.<→◃ q) (δ n)))) (out (fin m) (fin j) c w b t g d (pts n))
  obs m p σ n = obsAt m p σ (pts n) (chain n)

FOLDC : ∀ m j → m ≤ j → ∀ {K} (q : ⟨ j ⟩ <ᴵ K) (f : L.U ⟨ j ⟩ (L.<→◃ q) → L.Ordᶜ K)
  {ℓ} (p : ⟨ m ⟩ <ᴵ ℓ) (σ : L.Simᴵ K ℓ)
  (c : Raw (fin j)) .(w : Lgl (fin j) c) .(b : Nested (fin j) c) (t : LF)
  (g : (a : Raw (fin j)) → .(Gd (fin j) c a) → LF) .(d : Dom (lc (fin j) c w b t g)) →
  Rel j (L.Ω ⟨ j ⟩) c → Branches j q f c g →
  Rel m (L.lim (λ n → L.ψ p σ (f (L.into (L.<→◃ q)
      (iter (λ x → L.ψ q (λ r → r) (f (L.into (L.<→◃ q) x))) (L.Ω ⟨ j ⟩) n)))))
    (ψ (fin m) (lc (fin j) c w b t g) d)
FOLDC m j le q f p σ c w b t g d base IH =
  subst (Rel m _) (sym (TREE-FOLD m j le c w b t g d))
    (out-ll m (λ n → out-l m n (ChainJ.obs j q f c w b t g d base IH m p σ n)))

KEEPs : ∀ m (s : Pre (fin m)) j → levN m s ≡ j →
  ∀ {K} (q : ⟨ j ⟩ <ᴵ K) (f : L.U ⟨ j ⟩ (L.<→◃ q) → L.Ordᶜ K)
  {ℓ} (p : ⟨ m ⟩ <ᴵ ℓ) (σ : L.Simᴵ K ℓ) {a′} (e : ⟨ j ⟩ ≅ᴵ a′) (r : a′ <ᴵ ⟨ m ⟩)
  (c : Raw (fin j)) .(w : Lgl (fin j) c) .(b : Nested (fin j) c) (t : LF)
  (g : (a : Raw (fin j)) → .(Gd (fin j) c a) → LF) .(d : Dom (lc (fin j) c w b t g)) →
  Rel j (L.Ω ⟨ j ⟩) c → Branches j q f c g →
  Rel m (L.limᵢ r (λ y → L.ψ p σ (f (L.into (L.<→◃ q) (L.tr⁻ e (L.out (L.<→◃ r) y))))))
    (ψ (fin m) (lc (fin j) c w b t g) d)
KEEPs zero ()
KEEPs (suc N) s .(levN (suc N) s) refl q f p σ e r c w b t g d base IH =
  subst (Rel (suc N) _) (sym (TREE-KEEP (suc N) s c w b t g d))
    (ndA (suc N) s (rawRA N) c
      (ψ (fin (suc N)) t (Node.first (fin (levN (suc N) s)) c w b t g d))
      (λ a e′ → ψ (fin (suc N)) (g a e′) (Node.branch (fin (levN (suc N) s)) c w b t g d a e′))
      (L.≅ᴵ-sym e) base (λ y a e′ rl →
        subst (λ z → Rel (suc N) (L.ψ p σ (f (L.into (L.<→◃ q) (L.tr⁻ e z))))
            (ψ (fin (suc N)) (g a e′) (Node.branch (fin (levN (suc N) s)) c w b t g d a e′)))
          (sym (L.out-into (L.<→◃ r) y))
          (IH (suc N) p σ (L.tr⁻ e y) a e′ (Node.branch (fin (levN (suc N) s)) c w b t g d a e′)
            (TRC.tr⁻ᴿ (TRC-all (levN (suc N) s)) e rl))))

NODEl : ∀ m j {K} (q : ⟨ j ⟩ <ᴵ K) (f : L.U ⟨ j ⟩ (L.<→◃ q) → L.Ordᶜ K)
  {ℓ} (p : ⟨ m ⟩ <ᴵ ℓ) (σ : L.Simᴵ K ℓ)
  (c : Raw (fin j)) .(w : Lgl (fin j) c) .(b : Nested (fin j) c) (t : LF)
  (g : (a : Raw (fin j)) → .(Gd (fin j) c a) → LF) .(d : Dom (lc (fin j) c w b t g)) →
  Rel j (L.Ω ⟨ j ⟩) c → Branches j q f c g →
  Rel m (L.ψ p σ (L.limᵢ q f)) (ψ (fin m) (lc (fin j) c w b t g) d)
NODEl m j q f p σ c w b t g d base IH with L.<ᴵ-dec (σ q) p
... | injᵃ (L.via e r) =
  KEEPs m (proj₁ (slotOf m j (below-nat j m e r))) j (proj₂ (slotOf m j (below-nat j m e r)))
    q f p σ e r c w b t g d base IH
... | injᵇ (L.via e r) = FOLDC m j (<⇒≤ (below-nat m j e r)) q f p σ c w b t g d base IH
... | injᶜ e = FOLDC m j (≤-reflexive (sym (nat-inj j m e))) q f p σ c w b t g d base IH

NODE≡ : ∀ m j {j′ K} → j′ ≡ ⟨ j ⟩ → ∀ (q : j′ <ᴵ K) (f : L.U j′ (L.<→◃ q) → L.Ordᶜ K)
  {ℓ} (p : ⟨ m ⟩ <ᴵ ℓ) (σ : L.Simᴵ K ℓ)
  (c : Raw (fin j)) .(w : Lgl (fin j) c) .(b : Nested (fin j) c) (t : LF)
  (g : (a : Raw (fin j)) → .(Gd (fin j) c a) → LF) .(d : Dom (lc (fin j) c w b t g)) →
  Rel j (L.Ω ⟨ j ⟩) c → Branches j q f c g →
  Rel m (L.ψ p σ (L.limᵢ q f)) (ψ (fin m) (lc (fin j) c w b t g) d)
NODE≡ m j refl = NODEl m j

NODE : ∀ m j {j′ K} → j′ ≅ᴵ ⟨ j ⟩ → ∀ (q : j′ <ᴵ K) (f : L.U j′ (L.<→◃ q) → L.Ordᶜ K)
  {ℓ} (p : ⟨ m ⟩ <ᴵ ℓ) (σ : L.Simᴵ K ℓ)
  (c : Raw (fin j)) .(w : Lgl (fin j) c) .(b : Nested (fin j) c) (t : LF)
  (g : (a : Raw (fin j)) → .(Gd (fin j) c a) → LF) .(d : Dom (lc (fin j) c w b t g)) →
  Rel j (L.Ω ⟨ j ⟩) c → Branches j q f c g →
  Rel m (L.ψ p σ (L.limᵢ q f)) (ψ (fin m) (lc (fin j) c w b t g) d)
NODE m j lv = NODE≡ m j (nat-eq j lv)
```

## 2 只看第一支：树结点在目标层 `m` 上

```agda
FIRSTk : ∀ m (s : Pre (fin m)) j → levN m s ≡ j →
  (c : Raw (fin j)) .(w : Lgl (fin j) c) .(b : Nested (fin j) c) (t : LF)
  (g : (a : Raw (fin j)) → .(Gd (fin j) c a) → LF) .(d : Dom (lc (fin j) c w b t g))
  {x : L.Ordᶜ ⟨ m ⟩} → (∀ .(e : Gd (fin j) c c) .(d′ : Dom (g c e)) → Rel m x (ψ (fin m) (g c e) d′)) →
  Rel m x (ψ (fin m) (lc (fin j) c w b t g) d)
FIRSTk zero ()
FIRSTk (suc N) s .(levN (suc N) s) refl c w b t g d H =
  subst (Rel (suc N) _) (sym (TREE-KEEP (suc N) s c w b t g d))
    (bA (suc N) s (rawRA N) c
      (ψ (fin (suc N)) t (Node.first (fin (levN (suc N) s)) c w b t g d))
      (λ a e′ → ψ (fin (suc N)) (g a e′) (Node.branch (fin (levN (suc N) s)) c w b t g d a e′))
      (λ e → H e (Node.branch (fin (levN (suc N) s)) c w b t g d c e)))

FIRST : ∀ m j (c : Raw (fin j)) .(w : Lgl (fin j) c) .(b : Nested (fin j) c) (t : LF)
  (g : (a : Raw (fin j)) → .(Gd (fin j) c a) → LF) .(d : Dom (lc (fin j) c w b t g))
  {x : L.Ordᶜ ⟨ m ⟩} → (∀ .(e : Gd (fin j) c c) .(d′ : Dom (g c e)) → Rel m x (ψ (fin m) (g c e) d′)) →
  Rel m x (ψ (fin m) (lc (fin j) c w b t g) d)
FIRST m j c w b t g d H with j <? m
... | yes lt = FIRSTk m (proj₁ (slotOf m j lt)) j (proj₂ (slotOf m j lt)) c w b t g d H
... | no nlt = subst (Rel m _) (sym (TREE-FOLD m j (≮⇒≥ nlt) c w b t g d))
  (out-l m 0 (H (inj₁ refl , w , b) (Node.branch (fin j) c w b t g d c (inj₁ refl , w , b))))
```

## 3 沿槽位走到结点

`upN (sucᴺ 0) s` 对 `(N, s)` 递归，到 `inj₁` 时是层号 `sucᴺ′ 0` 的结点，下界在 `Raw` 里；槽位关系同步递归到 `Rel N′`。

```agda
WALKN : ∀ N (s : Pre (fin N)) m {j′ K} → j′ ≅ᴵ ⟨ levN N s ⟩ →
  ∀ (q : j′ <ᴵ K) (f : L.U j′ (L.<→◃ q) → L.Ordᶜ K) {ℓ} (p : ⟨ m ⟩ <ᴵ ℓ) (σ : L.Simᴵ K ℓ)
  (c : Low (fin N) s) .(w : LglLow (fin N) s c) .(b : NestedLow (fin N) s c) (t : LF)
  (g : (a : Low (fin N) s) → .(GdL (fin N) s c a) → LF) .(d : Dom (upN (fin N) s c w b t g)) →
  RelL N s (L.Ω ⟨ levN N s ⟩) c →
  (∀ m′ {ℓ′} (p′ : ⟨ m′ ⟩ <ᴵ ℓ′) (σ′ : L.Simᴵ K ℓ′) y a .(e : GdL (fin N) s c a)
    .(d′ : Dom (g a e)) → RelL N s y a →
    Rel m′ (L.ψ p′ σ′ (f (L.into (L.<→◃ q) y))) (ψ (fin m′) (g a e) d′)) →
  Rel m (L.ψ p σ (L.limᵢ q f)) (ψ (fin m) (upN (fin N) s c w b t g) d)
WALKN zero ()
WALKN (suc N) (inj₁ _) m lv q f p σ c w b t g d base IH = NODE m N lv q f p σ c w b t g d base IH
WALKN (suc N) (inj₂ r) m lv q f p σ c w b t g d base IH = WALKN N r m lv q f p σ c w b t g d base IH

WALKF : ∀ N (s : Pre (fin N)) m
  (c : Low (fin N) s) .(w : LglLow (fin N) s c) .(b : NestedLow (fin N) s c) (t : LF)
  (g : (a : Low (fin N) s) → .(GdL (fin N) s c a) → LF) .(d : Dom (upN (fin N) s c w b t g))
  {x : L.Ordᶜ ⟨ m ⟩} → (∀ .(e : GdL (fin N) s c c) .(d′ : Dom (g c e)) → Rel m x (ψ (fin m) (g c e) d′)) →
  Rel m x (ψ (fin m) (upN (fin N) s c w b t g) d)
WALKF zero ()
WALKF (suc N) (inj₁ _) m c w b t g d H = FIRST m N c w b t g d H
WALKF (suc N) (inj₂ r) m c w b t g d H = WALKF N r m c w b t g d H
```

## 4 起点与主引理

```agda
OMEGA : ∀ M m (η : Raw (fin M)) .(nb : Nested (fin M) η) .(d : Dom (up (fin M) η nb)) →
  Rel m (L.Ω ⟨ m ⟩) (ψ (fin m) (up (fin M) η nb) d)
OMEGA M m G.zero nb d = START m
OMEGA M m (G.suc η) nb d = out-l m 0 (OMEGA M m η nb d)
OMEGA M m (G.lim F) nb d =
  out-l m 0 (OMEGA M m (F 0) (nb 0) (dom-at (λ n → up (fin M) (F n) (nb n)) d 0))
OMEGA M m (G.lc s c t g) nb d =
  WALKF M s m c (proj₁ nb) (proj₁ (proj₂ nb)) (up (fin M) t (proj₁ (proj₂ (proj₂ nb))))
    (λ a e → up (fin M) (g a e) (proj₂ (proj₂ (proj₂ nb)) a e)) d
    (λ e d′ → OMEGA M m (g c e) (proj₂ (proj₂ (proj₂ nb)) c e) d′)
OMEGA zero m (G.em () a) nb d
OMEGA zero m G.top nb d = out-l m 0 (START m)
OMEGA (suc N) m (G.em _ a) nb d = OMEGA N m a nb d
OMEGA (suc N) m G.top nb d =
  FIRST m N (cO (fin N)) (cO-Lgl (fin N)) (cO-Nested (fin N)) (upT (fin N))
    (λ a e → up (fin N) a (proj₂ (proj₂ e))) d
    (λ e d′ → OMEGA N m (cO (fin N)) (proj₂ (proj₂ e)) d′)

FOLD0 : ∀ m {y b : L.Ordᶜ L.zero} → y ≼ b → ∀ a → b ≡ read a →
  ∀ {ℓ} (p : ⟨ m ⟩ <ᴵ ℓ) (σ : L.Simᴵ L.zero ℓ) .(nb : Nested B.zero a) .(d : Dom (up B.zero a nb)) →
  Rel m (L.ψ p σ y) (ψ (fin m) (up B.zero a nb) d)
FOLD0 m z≼ a q p σ nb d = OMEGA 0 m a nb d
FOLD0 m (s≼s r) (G.suc a) refl p σ nb d = SUCC m (FOLD0 m r a refl p σ nb d)
FOLD0 m (s≼s r) G.top refl p σ nb d = SUCC m (FOLD0 m r G.zero refl p σ tt (tt , tt , tt))
FOLD0 m (≼l n r) (G.lim f) refl p σ nb d =
  out-l m n (FOLD0 m r (f n) refl p σ (nb n) (dom-at (λ n → up B.zero (f n) (nb n)) d n))
FOLD0 m (l≼ h) a q p σ nb d = out-ll m (λ n → FOLD0 m (h n) a q p σ nb d)
FOLD0 m (≼i {p = ()} x ex r) a q p σ nb d
FOLD0 m (i≼ {p = ()} h) a q p σ nb d
FOLD0 m (≼u {r = ()} r) a q p σ nb d
FOLD0 m (u≼ {r = ()} r) a q p σ nb d

FOLD : ∀ M m {k} {x : L.Ordᶜ k} {η : Raw (fin M)} → Rel M x η →
  ∀ {ℓ} (p : ⟨ m ⟩ <ᴵ ℓ) (σ : L.Simᴵ k ℓ) .(nb : Nested (fin M) η) .(d : Dom (up (fin M) η nb)) →
  Rel m (L.ψ p σ x) (ψ (fin m) (up (fin M) η nb) d)
FOLD zero m {η = a} (r0 q) p σ nb d = FOLD0 m q a refl p σ nb d
FOLD (suc N) m {η = η} zr p σ nb d = OMEGA (suc N) m η nb d
FOLD (suc N) m (ssr r) p σ nb d = SUCC m (FOLD (suc N) m r p σ nb d)
FOLD (suc N) m (sr r) p σ nb d = out-l m 0 (FOLD (suc N) m r p σ nb d)
FOLD (suc N) m {η = G.lim F} (lr n r) p σ nb d =
  out-l m n (FOLD (suc N) m r p σ (nb n) (dom-at (λ n → up (fin (suc N)) (F n) (nb n)) d n))
FOLD (suc N) m (llr h) p σ nb d = out-ll m (λ n → FOLD (suc N) m (h n) p σ nb d)
FOLD (suc N) m (br {s = s} {c = c} {t = t} {g = g} h) p σ nb d =
  WALKF (suc N) s m c (proj₁ nb) (proj₁ (proj₂ nb)) (up (fin (suc N)) t (proj₁ (proj₂ (proj₂ nb))))
    (λ a e → up (fin (suc N)) (g a e) (proj₂ (proj₂ (proj₂ nb)) a e)) d
    (λ e d′ → FOLD (suc N) m (h e) p σ (proj₂ (proj₂ (proj₂ nb)) c e) d′)
FOLD (suc N) m (ndr {s = s} {c = c} {t = t} {g = g} {q = q} {f = f} lv base h) p σ nb d =
  WALKN (suc N) s m lv q f p σ c (proj₁ nb) (proj₁ (proj₂ nb))
    (up (fin (suc N)) t (proj₁ (proj₂ (proj₂ nb))))
    (λ a e → up (fin (suc N)) (g a e) (proj₂ (proj₂ (proj₂ nb)) a e)) d base
    (λ m′ p′ σ′ y a e d′ r → FOLD (suc N) m′ (h y a e r) p′ σ′ (proj₂ (proj₂ (proj₂ nb)) a e) d′)
FOLD (suc N) m (ntr {q = q} {f = f} lv h) p σ nb d =
  NODE m N lv q f p σ (cO (fin N)) (cO-Lgl (fin N)) (cO-Nested (fin N)) (upT (fin N))
    (λ a e → up (fin N) a (proj₂ (proj₂ e))) d (START N)
    (λ m′ p′ σ′ y a e d′ r → FOLD (suc N) m′ (h y a r) p′ σ′ (proj₂ (proj₂ e)) d′)
FOLD (suc N) m (emr r) p σ nb d = FOLD N m r p σ nb d
FOLD (suc N) m (ur r) p σ nb d = FOLD (suc N) m r p (λ q → σ (L.suc q)) nb d
```
