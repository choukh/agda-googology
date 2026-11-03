# 分层的 $\approx$: 低层含 `limᴼ`, 目标 $\Omega+1$, $\Omega\cdot2$ (闭实例)

> 不含记号. 结论写在 [LvStrat](LvStrat.lagda.md). 闭实例: 自然数的塔, 第 1 层的世界取 $\psi_1(1)+1$ (里面字面地有 $\Omega_1+m$), 并到 $\omega$; 再加 $\Omega_1=$ `limᴼ 0 toLv` 与全部 $\Omega_1+n$. `Cert-Ω₊`: 目标 $\Omega_1+1$. `Cert-Ω·2`: 目标 $\Omega_1\cdot2=\lim_n(\Omega_1+n)$. **都对任何 `S`, 没有 `HE`**: 输入是目标的后继, 模式是字面的, 判决不问 `S`. 第 0 层的世界是 $\omega$; 第 0 层的世界更大时低层要先含它的全部前驱, 那个塔这里没有造 (判断见 [LvStrat](LvStrat.lagda.md)).

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.LvStratOmega where

open import Data.Nat using (ℕ; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; <⇒≤)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Align.InaccTreeBase using
  (Lv; zero; suc; lim; limᴼ; Ordᴸ; Pre; at; Tree; limᵢ; up; Ω; toLv; Sim; σ-id; add; _+_; iter)
open import OCF.Align.InaccFloorTree using (Sib; natL; Mode; lt; fin; verdict; module PF)
open import OCF.Align.LvStratBase using (Fl; module Leaf; Stage; Ext; module Move)
open import OCF.Align.LvStratFin using (IsK; module Fin; at-nat)
open import OCF.Align.LvStratLvP using (module LvPs)
open import OCF.Align.LvStratUnion using (module UnionG)
open import OCF.Align.LvStratTower
```

## §1 通用: 低层上的 $\Omega$ 的层号好

```agda
module GenΩ (St : Stage) where
  open Stage St
  open Leaf fl

  cxΩs : ∀ j → Lw j → Cx (limᴼ j toLv)
  cxΩs j l =
    (dir , (Ω j , ΩA j l , pΩ j l , ≺→⊑ (pΩ j l)) , (λ x a → proj₁ (cxA j x a))) ,
    ((λ x b → proj₁ (proj₂ (cxA j x (b l)))) , (λ z z′ d d′ e → e)) ,
    ((λ x a → proj₂ (proj₂ (cxA j x a))) , (λ z z′ a a′ σ → σ))
    where
    dir : ∀ x y → A j x → A j y → Σ (Ordᴸ j) λ z → A j z × toLv x ⊑ᴬ toLv z × toLv y ⊑ᴬ toLv z
    dir x y ax ay with cmpA j x y ax ay
    ... | injᵃ p = y , ay , ≺→⊑ p , ⊑ᴬ-refl
    ... | injᵇ p = x , ax , ⊑ᴬ-refl , ≺→⊑ p
    ... | injᶜ e = y , ay , ≈⊑ e , ⊑ᴬ-refl

  loA : ∀ {j x} → A j x → Lo (toLv x)
  loA {j} {x} a = lo-toLv (lw→bl (A→Lw j x a)) x (twA j x a)

  loΩs : ∀ j → Lw j → Lo (limᴼ j toLv)
  loΩs j l = l , (λ x a → loA a)

  nat≈′ : ∀ n {a} → a ≈ᴮ natL n → a ≡ natL n
  nat≈′ ℕ.zero z≈ = refl
  nat≈′ (ℕ.suc n) (s≈ e) = cong Lv.suc (nat≈′ n e)
```

## §2 $\Omega_1+n$

```agda
Ω₁L : Lv
Ω₁L = limᴼ zero toLv

sucs : ℕ → Lv
sucs ℕ.zero    = Ω₁L
sucs (ℕ.suc n) = suc (sucs n)

Ω₁·2 : Lv
Ω₁·2 = lim sucs

add-nt : ∀ {l} (a : Ordᴸ l) (σ : Sim zero l) m → toLv (add a σ (nt m)) ≡ iter suc (toLv a) m
add-nt a σ ℕ.zero    = refl
add-nt a σ (ℕ.suc m) = cong suc (add-nt a σ m)

sucs≡ : ∀ m → iter suc Ω₁L m ≡ sucs m
sucs≡ ℕ.zero    = refl
sucs≡ (ℕ.suc m) = cong suc (sucs≡ m)

-- 这些只看 `≈` 的头, 对任何地板成立
module Sep (F : Fl) where
  open Leaf F

  s≉nat : ∀ i m → sucs i ≈ᴮ natL m → ⊥
  s≉nat ℕ.zero ℕ.zero ()
  s≉nat ℕ.zero (ℕ.suc m) ()
  s≉nat (ℕ.suc i) ℕ.zero ()
  s≉nat (ℕ.suc i) (ℕ.suc m) (s≈ e) = s≉nat i m e

  s≉s : ∀ {i j} → i < j → sucs j ≈ᴮ sucs i → ⊥
  s≉s {ℕ.zero} {ℕ.suc j} (s≤s _) ()
  s≉s {ℕ.suc i} {ℕ.suc j} (s≤s p) (s≈ e) = s≉s p e

  s≉lim : ∀ i → sucs i ≈ᴮ Ω₁·2 → ⊥
  s≉lim ℕ.zero ()
  s≉lim (ℕ.suc i) ()

  nat≉lim : ∀ m {f} → natL m ≈ᴮ lim f → ⊥
  nat≉lim ℕ.zero ()
  nat≉lim (ℕ.suc m) ()
```

## §3 自然数的塔并到 $\omega$

第 1 层的世界取 $\psi_1(\Omega_0)+1$. 它字面地含 $\Omega_1+m$ (`s≺w₀`): 这是 $\Omega_1+m\prec\Omega_2$ 的来源. 最小世界 $\Omega_1+1$ 不够.

```agda
module Closed (S : Sib) where
  ch : Choice
  ch ℕ.zero    t = Worlds.WF.W-F S 0 (proj₁ t) (proj₁ (proj₂ t)) (proj₂ (proj₂ (proj₂ t))) zero (tt , tt , tt)
  ch (ℕ.suc k) t = Worlds.W-Ω S (ℕ.suc k) (proj₁ t) (proj₁ (proj₂ t))

  Tn : ∀ K → Twr K
  Tn = tower W-ω ch

  Sn : ℕ → Stage
  Sn K = proj₁ (Tn K)

  isKn : ∀ K → IsK K (Sn K)
  isKn K = proj₁ (proj₂ (Tn K))

  ext-n : ∀ K → Ext (Stage.fl (Sn K)) (Stage.fl (Sn (ℕ.suc K)))
  ext-n ℕ.zero = Step.ext 0 St₀ isK₀ (λ _ ()) (λ _ ()) W-ω
  ext-n (ℕ.suc k) =
    let t = Tn (ℕ.suc k)
    in Step.ext (ℕ.suc k) (proj₁ t) (proj₁ (proj₂ t)) (proj₁ (proj₂ (proj₂ t))) (proj₂ (proj₂ (proj₂ t))) (ch k t)

  module U = UnionG Sn ext-n
  module Mω = U.M∞

  Stω : Stage
  Stω = U.St∞

  flω : Fl
  flω = U.fl∞

  open Stage Stω hiding (fl) public
  open Leaf flω public
  open GenΩ Stω using (cxΩs; loΩs; loA) public

  -- 第 0 层的地板元的层号字面是自然数
  a0 : ∀ K x → Fl.A (Stage.fl (Sn K)) zero x → Σ ℕ λ n → toLv x ≡ natL n
  a0 ℕ.zero x ()
  a0 (ℕ.suc ℕ.zero) x (inj₂ (_ , _ , (n , r) , _ , e)) with at-nat n r
  ... | m , _ , q = m , GenΩ.nat≈′ St₀ m (subst (λ u → Leaf._≈ᴮ_ fl₀ (toLv x) u) q e)
  a0 (ℕ.suc (ℕ.suc k)) x (inj₁ a) = a0 (ℕ.suc k) x a
  a0 (ℕ.suc (ℕ.suc k)) x (inj₂ (() , _))

  A0 : ∀ {x} → A zero x → Σ ℕ λ n → toLv x ≡ natL n
  A0 {x} (K , a) = a0 K x a

  lw-nat : ∀ b → Lw b → Σ ℕ λ m → b ≡ natL m
  lw-nat b (K , l) with IsK.lw⇒ (isKn K) b l
  ... | m , _ , e = m , e

  low-n : ∀ m → Lw (natL m)
  low-n m = ℕ.suc m , IsK.⇐lw (isKn (ℕ.suc m)) m ≤-refl

  tw-nt : ∀ n → Fl.Tw fl₀ zero (nt n)
  tw-nt ℕ.zero    = tt
  tw-nt (ℕ.suc n) = tw-nt n

  A0-nt : ∀ n → A zero (nt n)
  A0-nt n = 1 , inj₂ (Leaf.z≈ , tw-nt n , (ℕ.suc n , inj₁ tt) , tt , Leaf.≡→≈′ fl₀ (nt≡ n))

  at-lit : ∀ {a b} (e : a ≡ b) (r : Pre a) → at a r ≡ at b (subst Pre e r)
  at-lit refl r = refl

  bl-Ω₁ : BL Ω₁L
  bl-Ω₁ (inj₁ (inj₁ _)) _ = low-n 0
  bl-Ω₁ (inj₂ (x , r)) (ax , d) with A0 {x} ax
  ... | n , e with at-nat n (subst Pre e r)
  ...   | m , _ , q = subst Lw (sym (trans (at-lit e r) q)) (low-n m)

  -- 第 1 层的地板含 $\psi_1(\Omega_0)$, 它含 $\Omega_1+m$
  w₀ : Ordᴸ (natL 1)
  w₀ = PF.ψⁿ S 1 (Ω zero)

  private
    module T₁ = Fin S (Sn 1)
    module K₁ = T₁.K-stage 1 (isKn 1)

  w₀∈ : A (natL 1) w₀
  w₀∈ = 2 , inj₂ (Leaf.≈ᴮ-refl (Stage.fl (Sn 1)) (natL 1) , T₁.eq→tw K₁.bl-K w₀ (K₁.Eq-ψᴷ {x = Ω zero} (T₁.Ω-self zero tt tt)) , inj₁ tt , tt , Leaf.≈ᴮ-refl (Stage.fl (Sn 1)) (toLv w₀))

  ≡≈ : ∀ {a b} → a ≡ b → a ≈ᴮ b
  ≡≈ = ≡→≈′

  s≺w₀ : ∀ m → sucs m ≺ᴬ toLv w₀
  s≺w₀ m = viaᴬ (2 , inj₂ (nt (ℕ.suc m) , inj₁ tt)) (A0-nt (ℕ.suc m) , tt)
             (≡≈ (sym (trans (add-nt (Ω (natL 1)) _ m) (sucs≡ m))))

  s≺Ω₂ : ∀ m → sucs m ≺ᴬ toLv (Ω (natL 2))
  s≺Ω₂ m with s≺w₀ m
  ... | viaᴬ q d e = viaᴬ (inj₂ (w₀ , q)) (w₀∈ , d) e

  s≺ΩΩ : ∀ m → sucs m ≺ᴬ toLv (Ω Ω₁L)
  s≺ΩΩ m with s≺Ω₂ m
  ... | viaᴬ q d e = viaᴬ (inj₂ (nt 2 , q)) (A0-nt 2 , d) e
```

`w₀-free`: 第 1 层的世界不读 `S`: 它的节点全在第 0 层以下, 目标是字面的 1. 其余世界 $\Omega_{\ldots}+1$ 的层号由 `Ω` 算, 也不读 `S`. 所以这里的地板本身与 `S` 无关.

```agda
w₀-free : ∀ S S′ → PF.ψⁿ S 1 (Ω zero) ≡ PF.ψⁿ S′ 1 (Ω zero)
w₀-free S S′ = refl
```

## §4 加 $\Omega_1$ 与 $\Omega_1+n$

`Inv k St`: 阶段 `St` 的低层是自然数, 或 $\approx$ 某个 $\Omega_1+i$ ($i\le k$), 第 $k$ 个是低层, 而且 $\Omega_{\Omega_1+k}$ 含全部 $\Omega_1+m$ (`big`). `next-s`: 加下一层. 新层不 $\approx$ 任何旧的低层 (`nw-≉`) 由 `Sep` 给, 只看 $\approx$ 的头.

```agda
record Inv (S : Sib) (k : ℕ) (St : Stage) : Set where
  open Stage St
  open Leaf fl
  field
    cl    : ∀ b → Lw b → (Σ ℕ λ m → b ≡ natL m) ⊎ (Σ ℕ λ i → i ≤ k × b ≈ᴮ sucs i)
    low-s : Lw (sucs k)
    big   : ∀ m → sucs m ≺ᴬ toLv (Ω (sucs k))

module Base (S : Sib) where
  open Closed S public
  open LvPs S Stω using (lvp-cx; lvg-low; Good-Ω; Ω-self; cx-tree; eq→tw; LvP; LvG)
  private module N₀ = NewLevel

  N₀′ : NewLevel Stω Ω₁L
  N₀′ = record
    { nw-lo = loΩs zero (low-n 0)
    ; nw-cx = cxΩs zero (low-n 0)
    ; nw-at = bl-Ω₁
    ; nw-≉ = λ {b} l e → let m , q = lw-nat b l in Sep.s≉nat flω 0 m (subst (λ u → Ω₁L ≈ᴮ u) q e)
    ; nw-pΩ = s≺ΩΩ 0
    }

  -- $\Omega_1$ 在 `Stω` 上是好层号: 分支的层号都是自然数
  lvg-Ω₁ : LvG Ω₁L
  lvg-Ω₁ = inj₁ (low-n 0) , tt , (λ x b → let n , e = A0 {x} (b (low-n 0)) in subst LvG (sym e) (lvg-low (natL n) (low-n n)))

  lvp-Ω₁ : LvP Ω₁L
  lvp-Ω₁ = lvp-cx Ω₁L (loΩs zero (low-n 0)) (cxΩs zero (low-n 0)) lvg-Ω₁

  ΩΩ₁-self = Ω-self Ω₁L (proj₁ lvp-Ω₁) (proj₁ (proj₂ lvp-Ω₁))

  W₀′ : World Stω Ω₁L
  W₀′ = record
    { L = suc (toLv (Ω Ω₁L))
    ; loL = lo-toLv bl-Ω₁ (Ω Ω₁L) (eq→tw bl-Ω₁ (Ω Ω₁L) ΩΩ₁-self)
    ; cxL = cx-tree bl-Ω₁ (Good-Ω Ω₁L lvp-Ω₁) ΩΩ₁-self
    ; hΩ = viaᴬ (inj₁ tt) tt (≈ᴮ-refl _)
    }

  module X₀ = Next Stω Ω₁L N₀′ W₀′

  T₀ : Stage
  T₀ = X₀.St′

  inv₀ : Inv S 0 T₀
  inv₀ = record
    { cl = λ { b (inj₁ l) → inj₁ (lw-nat b l)
             ; b (inj₂ e) → inj₂ (0 , z≤n , X₀.≈↑ e) }
    ; low-s = inj₂ (≈ᴮ-refl _)
    ; big = λ m → X₀.≺↑ (s≺ΩΩ m)
    }

module NextS (S : Sib) (k : ℕ) (St : Stage) (iv : Inv S k St) where
  open Stage St
  open Leaf fl
  open Inv iv
  open LvPs S St using (lvp-cx; Good-Ω; Ω-self; cx-tree; eq→tw; LvP; LvG; low→lvt; t→g; lvp-low)

  new : Lv
  new = suc (sucs k)

  bl-new : BL new
  bl-new (inj₁ _) _ = low-s
  bl-new (inj₂ r) d = low-at (sucs k) low-s r d

  lo-s = low-lo (sucs k) low-s
  cx-s = low-cx (sucs k) low-s

  ≉new : ∀ {b} → Lw b → new ≈ᴮ b → ⊥
  ≉new {b} l e with cl b l
  ... | inj₁ (m , q) = Sep.s≉nat fl (ℕ.suc k) m (subst (λ u → new ≈ᴮ u) q e)
  ... | inj₂ (i , p , q) = Sep.s≉s fl (s≤s p) (≈ᴮ-trans e q)

  bigΩ : ∀ m → sucs m ≺ᴬ toLv (Ω new)
  bigΩ m with big m
  ... | viaᴬ q d e = viaᴬ (inj₂ (Ω (sucs k) , q)) (ΩA (sucs k) low-s , d) e

  N : NewLevel St new
  N = record { nw-lo = lo-s ; nw-cx = cx-s ; nw-at = bl-new ; nw-≉ = ≉new ; nw-pΩ = bigΩ (ℕ.suc k) }

  lvp-new : LvP new
  lvp-new = lvp-cx new lo-s cx-s (inj₁ low-s , low→lvt (sucs k) low-s)

  Ωn-self = Ω-self new (proj₁ lvp-new) (proj₁ (proj₂ lvp-new))

  W : World St new
  W = record
    { L = suc (toLv (Ω new))
    ; loL = lo-toLv bl-new (Ω new) (eq→tw bl-new (Ω new) Ωn-self)
    ; cxL = cx-tree bl-new (Good-Ω new lvp-new) Ωn-self
    ; hΩ = viaᴬ (inj₁ tt) tt (≈ᴮ-refl _)
    }

  module X = Next St new N W

  inv′ : Inv S (ℕ.suc k) X.St′
  inv′ = record
    { cl = λ { b (inj₁ l) → cl′ b (cl b l)
             ; b (inj₂ e) → inj₂ (ℕ.suc k , ≤-refl , X.≈↑ e) }
    ; low-s = inj₂ (≈ᴮ-refl _)
    ; big = λ m → X.≺↑ (bigΩ m)
    }
    where
    cl′ : ∀ b → ((Σ ℕ λ m → b ≡ natL m) ⊎ (Σ ℕ λ i → i ≤ k × b ≈ᴮ sucs i)) →
          (Σ ℕ λ m → b ≡ natL m) ⊎ (Σ ℕ λ i → i ≤ ℕ.suc k × Leaf._≈ᴮ_ X.fl′ b (sucs i))
    cl′ b (inj₁ x) = inj₁ x
    cl′ b (inj₂ (i , p , q)) = inj₂ (i , ≤-trans p (<⇒≤ ≤-refl) , X.≈↑ q)
```

## §5 目标 $\Omega_1+1$

输入 $\Omega_{\Omega_1+2}$, 目标 $\Omega_1+1$, 节点 $\Omega_1+1$ 上升, 链的目标是目标自己. `S` 没有被问到. 这是 `¬lowΩ₁` 说做不到的那个层号: 它的前驱 $\Omega_1$ 在这里是低层.

```agda
module TopΩ (S : Sib) where
  open Base S using (T₀; inv₀; low-n; A0-nt; A0; lw-nat; Stω; flω)
  open Inv inv₀
  open LvPs S T₀

  L₁ : Lv
  L₁ = sucs 1

  bl-L₁ : BL L₁
  bl-L₁ (inj₁ _) _ = low-s
  bl-L₁ (inj₂ r) d = low-at Ω₁L low-s r d

  lo-L₁ = low-lo Ω₁L low-s
  cx-L₁ = low-cx Ω₁L low-s

  lw₀ : ∀ m → Lw (natL m)
  lw₀ m = inj₁ (low-n m)

  zt-L₁ : Zt L₁
  zt-L₁ j l with cl j l
  ... | inj₁ (m , refl) =
        inj₂ (inj₂ (nt (ℕ.suc m) , inj₁ tt)) , (inj₁ (A0-nt (ℕ.suc m)) , tt) , ≡→≈′ (nt≡ m)
  ... | inj₂ (ℕ.zero , _ , e) = inj₁ tt , tt , ≈ᴮ-sym e

  ti-L₁ : Ti L₁
  ti-L₁ = bl→lvt L₁ bl-L₁ , zt-L₁ , lvr-rp L₁ lo-L₁ (proj₁ (proj₂ cx-L₁))

  lvp-L₁ : LvP L₁
  lvp-L₁ = lvp-cx L₁ lo-L₁ cx-L₁ (inj₁ low-s , low→lvt Ω₁L low-s)

  m₁ : Mode (suc L₁) L₁
  m₁ = lt (inj₁ tt) refl

  low≉L₁ : ∀ b → Lw b → b ≈ᴮ L₁ → ⊥
  low≉L₁ b l e with cl b l
  ... | inj₁ (m , refl) = Sep.s≉nat fl 1 m (≈ᴮ-sym e)
  ... | inj₂ (ℕ.zero , _ , q) = Sep.s≉s fl (s≤s z≤n) (≈ᴮ-trans (≈ᴮ-sym e) q)

  ok₁ : OK (suc L₁) m₁
  ok₁ = cvs , okB L₁ (σ-id L₁) (λ r d → d)
    where
    cvs : ∀ r → AdmB (suc L₁) r → CV (verdict S m₁ r)
    cvs (inj₁ _) _ = cvr λ r d e → low≉L₁ _ (blL {L₁} bl-L₁ r d) e
    cvs (inj₂ r) d = cvp r refl d

  lvp-θ₁ : LvP (suc L₁)
  lvp-θ₁ = lvp-cx (suc L₁) lo-L₁ cx-L₁ (inj₂ (ok₁ , zt-L₁) , proj₁ ti-L₁)

  Cert-Ω₊ : WFᴬ (toLv (ψᵖ m₁ (Ω (suc L₁))))
  Cert-Ω₊ = Cert-top m₁ bl-L₁ ti-L₁ lvp-L₁ ok₁ lvp-θ₁
```

## §6 目标 $\Omega_1\cdot2$

对 $k$ 递归地造 $\Omega_1+k$ 的塔 (`Tk`), 取并 (`St₂`). 目标 $\Omega_1\cdot2=\lim_n(\Omega_1+n)$ 不是低层, 它的可容许前驱都是. **这是 `reach-W` 要的第一个层号**: 含 `limᴼ` 的层号的 $\mathbb N$-极限作字面目标. `S` 没有被问到.

```agda
module TopΩ2 (S : Sib) where
  open Base S using (T₀; inv₀; low-n; A0-nt; flω)

  Tk : ∀ k → Σ Stage (Inv S k)
  Tk ℕ.zero    = T₀ , inv₀
  Tk (ℕ.suc k) = NextS.X.St′ S k (proj₁ (Tk k)) (proj₂ (Tk k)) , NextS.inv′ S k (proj₁ (Tk k)) (proj₂ (Tk k))

  Sk : ℕ → Stage
  Sk k = proj₁ (Tk k)

  ext-k : ∀ k → Ext (Stage.fl (Sk k)) (Stage.fl (Sk (ℕ.suc k)))
  ext-k k = NextS.X.ext S k (proj₁ (Tk k)) (proj₂ (Tk k))

  module U₂ = UnionG Sk ext-k
  module M₂ = U₂.M∞

  St₂ : Stage
  St₂ = U₂.St∞

  open LvPs S St₂

  low-sk : ∀ n → Lw (sucs n)
  low-sk n = n , Inv.low-s (proj₂ (Tk n))

  low-k0 : ∀ m → Lw (natL m)
  low-k0 m = 0 , inj₁ (low-n m)

  A0₂ : ∀ n → A zero (nt n)
  A0₂ n = 0 , inj₁ (A0-nt n)

  bl-L₂ : BL Ω₁·2
  bl-L₂ (n , r) d = low-at (sucs n) (low-sk n) r d

  lo-L₂ : Lo Ω₁·2
  lo-L₂ n = low-lo (sucs n) (low-sk n)

  cx-L₂ : Cx Ω₁·2
  cx-L₂ = ((λ n r d → viaᴬ (inj₂ r) d (≈ᴮ-refl _)) , (λ n → proj₁ (low-cx (sucs n) (low-sk n)))) ,
          (λ n → proj₁ (proj₂ (low-cx (sucs n) (low-sk n)))) ,
          (λ n → proj₂ (proj₂ (low-cx (sucs n) (low-sk n))))

  cl₂ : ∀ b → Lw b → (Σ ℕ λ m → b ≡ natL m) ⊎ (Σ ℕ λ i → b ≈ᴮ sucs i)
  cl₂ b (n , l) with Inv.cl (proj₂ (Tk n)) b l
  ... | inj₁ x = inj₁ x
  ... | inj₂ (i , _ , e) = inj₂ (i , M₂.≈↑ n e)

  zt-L₂ : Zt Ω₁·2
  zt-L₂ j l with cl₂ j l
  ... | inj₁ (m , refl) =
        (0 , inj₂ (nt (ℕ.suc m) , inj₁ tt)) , (A0₂ (ℕ.suc m) , tt) , ≡→≈′ (nt≡ m)
  ... | inj₂ (i , e) = (ℕ.suc i , inj₁ tt) , tt , ≈ᴮ-sym e

  ti-L₂ : Ti Ω₁·2
  ti-L₂ = bl→lvt Ω₁·2 bl-L₂ , zt-L₂ , lvr-rp Ω₁·2 lo-L₂ (proj₁ (proj₂ cx-L₂))

  lvp-L₂ : LvP Ω₁·2
  lvp-L₂ = lvp-cx Ω₁·2 lo-L₂ cx-L₂ (λ n → lvg-low (sucs n) (low-sk n))

  m₂ : Mode (suc Ω₁·2) Ω₁·2
  m₂ = lt (inj₁ tt) refl

  low≉L₂ : ∀ b → Lw b → b ≈ᴮ Ω₁·2 → ⊥
  low≉L₂ b l e with cl₂ b l
  ... | inj₁ (m , refl) = Sep.nat≉lim fl m e
  ... | inj₂ (i , q) = Sep.s≉lim fl i (≈ᴮ-trans (≈ᴮ-sym q) e)

  ok₂ : OK (suc Ω₁·2) m₂
  ok₂ = cvs , okB Ω₁·2 (σ-id Ω₁·2) (λ r d → d)
    where
    cvs : ∀ r → AdmB (suc Ω₁·2) r → CV (verdict S m₂ r)
    cvs (inj₁ _) _ = cvr λ r d e → low≉L₂ _ (blL {Ω₁·2} bl-L₂ r d) e
    cvs (inj₂ r) d = cvp r refl d

  lvp-θ₂ : LvP (suc Ω₁·2)
  lvp-θ₂ = lvp-cx (suc Ω₁·2) lo-L₂ cx-L₂ (inj₂ (ok₂ , zt-L₂) , proj₁ ti-L₂)

  Cert-Ω·2 : WFᴬ (toLv (ψᵖ m₂ (Ω (suc Ω₁·2))))
  Cert-Ω·2 = Cert-top m₂ bl-L₂ ti-L₂ lvp-L₂ ok₂ lvp-θ₂
```
