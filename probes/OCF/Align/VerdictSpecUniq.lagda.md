# 判决的规格: 唯一性 (底座)

> 底座, 不含记号. 结论写在 [VerdictSpec](VerdictSpec.lagda.md). 两个 `CVx` 正确的判决种类相同 (`cv-kind`, `cv-kind≈`); 路径可以不同 (`two-paths`, `paths≢`), 所以关系是 `Eq`, 不是 $\equiv$. 目标 $\ge1$ 的结论是 `ψ≃`. 目标 0 没有 `Zt`, 这里补上 (`ψ≃₀`), 代价是每个第 0 层节点的链点要在 `B₀` 里 (`CZ`). 第 0 层的 `Eq` 给出 `FGH` 逐点相等 (`FGH≃`), 所以**大数由判决的正确性决定**.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.VerdictSpecUniq where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; cong)
open import OCF.Align.InaccTreeBase using
  (Lv; zero; suc; lim; limᴼ; Ordᴸ; Pre; Low; Dn; DnT; at; down; outL; intoL; outD; intoD; Tree; limᵢ; up; Ω; toLv;
   Sim; σ-id; ι; _∘σ_; add; _+_; iter; Verdict; pen; rise; FGH)
open import OCF.Align.InaccFloorTree using (Sib; Mode; fin; upM; verdict; chM; natL; isN; finD; asN; module PF)
open import OCF.Align.InaccThetaRel using (module Leaf)
open import OCF.Align.InaccThetaEq using (module Eqv)
open import OCF.Align.VerdictSpecBase using (module Eqx)
open import OCF.Align.VerdictSpecTwo using (module Two)
```

## §1 种类由正确性决定

`CVx` 不依赖 `S`, 只是写在 `Eqx S B₀` 里, 所以左右各一份. `cv-kind≈` 对 $\approx$-相关的两对都成立, `cv-kind` 是它的实例.

```agda
data Kd : Set where
  kp kr : Kd

kd : ∀ {j i} → Verdict j i → Kd
kd (pen _ _) = kp
kd rise      = kr

module Kinds (S S′ : Sib) (B₀ : Ordᴸ zero → Set) where
  module L = Eqx S B₀
  module R = Eqx S′ B₀
  open Leaf B₀

  cv-kind≈ : ∀ {j j′ i i′} {v : Verdict j i} {w : Verdict j′ i′} → j ≈ᴮ j′ → i ≈ᴮ i′ → L.CVx v → R.CVx w → kd v ≡ kd w
  cv-kind≈ jj ii (L.cvp _ _ _ _ _) (R.cvp _ _ _ _ _) = refl
  cv-kind≈ jj ii (L.cvr _)         (R.cvr _)         = refl
  cv-kind≈ jj ii (L.cvp r _ a e _) (R.cvr k)         = ⊥-elim (L.clash ii jj r e a k)
  cv-kind≈ jj ii (L.cvr k)         (R.cvp r _ a e _) = ⊥-elim (L.clash (≈ᴮ-sym ii) (≈ᴮ-sym jj) r e a k)

  cv-kind : ∀ {j i} {v w : Verdict j i} → L.CVx v → R.CVx w → kd v ≡ kd w
  cv-kind {j} {i} = cv-kind≈ (≈ᴮ-refl j) (≈ᴮ-refl i)
```

## §2 路径不唯一, 所以不是 $\equiv$

$\omega$ 里到第 1 层的路径有无穷多条. 两个判决都 `CV` 正确, 路径不同. 所以两个正确的 `S` 给的树一般不字面相等 (`paths≢`), 只能 `Eq`.

```agda
ω₀ : Lv
ω₀ = lim natL

module Paths (B₀ : Ordᴸ zero → Set) where
  open Eqx (λ _ _ → rise) B₀ using (CVx; cvp; bl; ≈ᴮ-refl)

  v₂ v₃ : Verdict (natL 1) ω₀
  v₂ = pen (2 , inj₁ tt) (λ y → y)
  v₃ = pen (3 , inj₂ (inj₁ tt)) (λ y → y)

  two-paths : CVx v₂ × CVx v₃
  two-paths = cvp (2 , inj₁ tt) _ tt (≈ᴮ-refl _) (bl refl) , cvp (3 , inj₂ (inj₁ tt)) _ tt (≈ᴮ-refl _) (bl refl)

  paths≢ : v₂ ≢ v₃
  paths≢ ()
```

## §3 第 0 层: `FGH`

第 0 层的 `Eq` 只有 `z≃`, `s≃`, `l≃`: `Pre zero` 与 `Dn zero` 是空的.

```agda
iter-cong : ∀ {A : Set} {g g′ : A → A} → (∀ x → g x ≡ g′ x) → ∀ (a : A) n → iter g a n ≡ iter g′ a n
iter-cong h a zero    = refl
iter-cong {g = g} {g′} h a (suc n) rewrite iter-cong {g = g} {g′} h a n = h _

module Uniq (S S′ : Sib) (B₀ : Ordᴸ zero → Set) where
  open Two S S′ B₀ public
  private
    module T₀ = Two

  FGH≃ : ∀ {x y : Ordᴸ zero} → Eq zero x {zero} y → ∀ n → FGH x n ≡ FGH y n
  FGH≃ z≃ n = refl
  FGH≃ (s≃ {a = a} {b = b} e) n = iter-cong (FGH≃ e) n n
  FGH≃ (l≃ h) n = FGH≃ (h n) n
  FGH≃ (i≃ {r = ()} _ _ _ _ _) n
  FGH≃ (uˡ {d = ()} _ _) n
  FGH≃ (uʳ {d = ()} _ _) n

  Z-refl : ∀ (z : Ordᴸ zero) → Eq zero z {zero} z
  Z-refl Tree.zero    = z≃
  Z-refl (Tree.suc z) = s≃ (Z-refl z)
  Z-refl (Tree.lim f) = l≃ (λ n → Z-refl (f n))
```

## §4 目标 0

目标 0 没有路径, 判决永远是 `rise`, 自动正确. 但第 0 层的节点上升时, 链点是第 0 层的树, 没有 `Bs-nz`, 要它们在 `B₀` 里. `CZ m x` 把这件事沿 `x` 的结构写出来; 这是对原始树的结构递归, 与 `ψᵖ` 同形. 取 `B₀ = ⊤` 时它是定理 (`cz-triv`).

```agda
module CZS (S : Sib) (B₀ : Ordᴸ zero → Set) where
  open Eqx S B₀

  CZ : ∀ {k i} → Mode k i → Ordᴸ k → Set
  CZ m Tree.zero    = ⊤
  CZ m (Tree.suc a) = CZ m a
  CZ m (Tree.lim f) = ∀ n → CZ m (f n)
  CZ {k} m (limᵢ r f) = ∀ n →
    Bs (at k r) (iter (λ x → ψᵖ (chM k r) (f (intoL k r x))) (Ω (at k r)) n) ×
    CZ m (f (intoL k r (iter (λ x → ψᵖ (chM k r) (f (intoL k r x))) (Ω (at k r)) n))) ×
    (at k r ≡ zero → CZ (chM k r) (f (intoL k r (iter (λ x → ψᵖ (chM k r) (f (intoL k r x))) (Ω (at k r)) n))))
  CZ {suc k}    m (up d x) = CZ (upM (suc k) d m) x
  CZ {lim f}    m (up d x) = CZ (upM (lim f) d m) x
  CZ {limᴼ k g} m (up d x) = CZ (upM (limᴼ k g) d m) x

  cz-triv : (∀ k x → Bs k x) → ∀ {k i} (m : Mode k i) (x : Ordᴸ k) → CZ m x
  cz-triv all m Tree.zero    = tt
  cz-triv all m (Tree.suc a) = cz-triv all m a
  cz-triv all m (Tree.lim f) = λ n → cz-triv all m (f n)
  cz-triv all {k} m (limᵢ r f) = λ n → all _ _ , cz-triv all m _ , (λ _ → cz-triv all (chM k r) _)
  cz-triv all {suc k}    m (up d x) = cz-triv all (upM (suc k) d m) x
  cz-triv all {lim f}    m (up d x) = cz-triv all (upM (lim f) d m) x
  cz-triv all {limᴼ k g} m (up d x) = cz-triv all (upM (limᴼ k g) d m) x

-- 有限目标的判决字面正确, 对任何 `S`
module FinLit (S : Sib) (B₀ : Ordᴸ zero → Set) where
  open Eqv S B₀

  isN-nn : ∀ n {j} → natL n ≈ᴮ j → isN j n ≡ nothing → ⊥
  isN-nn zero z≈ ()
  isN-nn (suc n) (s≈ {b = j} e) eq with isN j n | isN-nn n e
  isN-nn (suc n) (s≈ {b = _} e) () | just refl | _
  ... | nothing | k = k refl

  fin-cv : ∀ j n → CV (finD j n)
  fin-cv j zero = cvr (λ ())
  fin-cv j (suc n) with isN j n in eq
  ... | just refl = cvp (inj₁ tt) refl tt
  ... | nothing with finD j n | fin-cv j n
  ...   | _ | cvp r e a = cvp {i = natL (suc n)} (inj₂ r) e a
  ...   | _ | cvr k = cvr {i = natL (suc n)} (λ where
        (inj₁ _) _ q → isN-nn n q eq
        (inj₂ r) d q → k r d q)

  okF : ∀ k {i} n (e : i ≡ natL n) → OK k (fin n e)
  okF zero       n refl = tt
  okF (suc k)    n refl = (λ r d → fin-cv _ n) , okF k n refl
  okF (lim f)    n refl = (λ r d → fin-cv _ n) , (λ m → okF (f m) n refl)
  okF (limᴼ k g) n refl = (λ r d → fin-cv _ n) , (λ x _ → okF (g x) n refl)

module Target₀ (S S′ : Sib) (B₀ : Ordᴸ zero → Set) where
  open Uniq S S′ B₀ public
  module CL = CZS S B₀
  module CR = CZS S′ B₀

  z? : (j : Lv) → (j ≡ zero) ⊎ (j ≡ zero → ⊥)
  z? zero       = inj₁ refl
  z? (suc _)    = inj₂ λ ()
  z? (lim _)    = inj₂ λ ()
  z? (limᴼ _ _) = inj₂ λ ()

  ≈z : ∀ {a b} → a ≈ᴮ b → a ≡ zero → b ≡ zero
  ≈z z≈ _ = refl

  z≈′ : ∀ {a b} → a ≈ᴮ b → b ≡ zero → a ≡ zero
  z≈′ z≈ _ = refl

  ψ≃₀ : ∀ {k k′ i i′} → i ≡ zero → i′ ≡ zero → (m : Mode k i) (m′ : Mode k′ i′) {x : Ordᴸ k} {y : Ordᴸ k′} →
        CL.CZ m x → CR.CZ m′ y → Eq k x y → Eq i (L.ψᵖ m x) (R.ψᵖ m′ y)
  chain₀≃ : ∀ {k k′} {r : Pre k} {r′ : Pre k′} {f : Low k r → Ordᴸ k} {f′ : Low k′ r′ → Ordᴸ k′} →
           L.ND k r → R.ND k′ r′ → at k r ≈ᴮ at k′ r′ → LRo k r →
           (∀ z z′ → Bs _ z → Bs _ z′ → RLo k r z z′ → Eq k (f (intoL k r z)) (f′ (intoL k′ r′ z′))) →
           ∀ {m : Mode k zero} {m′ : Mode k′ zero} → CL.CZ m (limᵢ r f) → CR.CZ m′ (limᵢ r′ f′) →
           ∀ n → Eq (at k r) (chainL k r f n) (chainR k′ r′ f′ n)

  ψ≃₀ refl refl m m′ cl cr z≃ = s≃ z≃
  ψ≃₀ refl refl m m′ cl cr (s≃ e) = l≃ (iter≃ tt tt tt (ψ≃₀ refl refl m m′ cl cr e))
  ψ≃₀ refl refl m m′ cl cr (l≃ h) = l≃ (λ n → ψ≃₀ refl refl m m′ (cl n) (cr n) (h n))
  ψ≃₀ {k} {k′} refl refl m m′ cl cr (i≃ {r = r} {r′ = r′} {f = f} {f′ = f′} nd nd′ e lr h)
    with verdict S m r | verdict S′ m′ r′
  ... | pen () _ | _
  ... | rise | pen () _
  ... | rise | rise = l≃ (λ n → ψ≃₀ refl refl m m′ (proj₁ (proj₂ (cl n))) (proj₁ (proj₂ (cr n)))
          (h _ _ (proj₁ (cl n)) (proj₁ (cr n)) (Eq→R k r (chain₀≃ {f = f} {f′ = f′} nd nd′ e lr h {m} {m′} cl cr n))))
  ψ≃₀ {suc k} refl refl m m′ cl cr (uˡ {d = d} db e) = ψ≃₀ refl refl (upM (suc k) d m) m′ cl cr e
  ψ≃₀ {lim f} refl refl m m′ cl cr (uˡ {d = d} db e) = ψ≃₀ refl refl (upM (lim f) d m) m′ cl cr e
  ψ≃₀ {limᴼ k g} refl refl m m′ cl cr (uˡ {d = d} db e) = ψ≃₀ refl refl (upM (limᴼ k g) d m) m′ cl cr e
  ψ≃₀ {k′ = suc k} refl refl m m′ cl cr (uʳ {d = d} db e) = ψ≃₀ refl refl m (upM (suc k) d m′) cl cr e
  ψ≃₀ {k′ = lim f} refl refl m m′ cl cr (uʳ {d = d} db e) = ψ≃₀ refl refl m (upM (lim f) d m′) cl cr e
  ψ≃₀ {k′ = limᴼ k g} refl refl m m′ cl cr (uʳ {d = d} db e) = ψ≃₀ refl refl m (upM (limᴼ k g) d m′) cl cr e

  chain₀≃ {k} {k′} {r} {r′} nd nd′ e lr h cl cr zero =
    Ω≃ e (L.t→g _ (proj₂ (proj₂ nd))) (R.t→g _ (proj₂ (proj₂ nd′))) (L→R k r (proj₁ nd) lr)
  chain₀≃ {k} {k′} {r} {r′} {f} {f′} nd nd′ e lr h {m} {m′} cl cr (suc n) with z? (at k r)
  ... | inj₂ n₀ = chain≃ {f = f} {f′ = f′} nd nd′ e lr n₀ (λ q → n₀ (z≈′ e q)) h (suc n)
  ... | inj₁ e₀ = ψ≃₀ e₀ (≈z e e₀) (chM k r) (chM k′ r′)
        (proj₂ (proj₂ (cl n)) e₀) (proj₂ (proj₂ (cr n)) (≈z e e₀))
        (h _ _ (proj₁ (cl n)) (proj₁ (cr n)) (Eq→R k r (chain₀≃ {f = f} {f′ = f′} nd nd′ e lr h {m} {m′} cl cr n)))

  -- 目标 0 的结论: 大数相等
  FGH-ψ₀ : ∀ {k k′} (m : Mode k zero) (m′ : Mode k′ zero) {x : Ordᴸ k} {y : Ordᴸ k′} →
           CL.CZ m x → CR.CZ m′ y → Eq k x y → ∀ n → FGH (L.ψᵖ m x) n ≡ FGH (R.ψᵖ m′ y) n
  FGH-ψ₀ m m′ cl cr e = FGH≃ (ψ≃₀ refl refl m m′ cl cr e)

  -- ψ₀(Ω_L)
  T≃ : ∀ {a b} → a ≈ᴮ b → L.LvG a → R.LvG b → LvR a →
       CL.CZ (fin 0 refl) (Ω a) → CR.CZ (fin 0 refl) (Ω b) →
       ∀ n → FGH (L.T a) n ≡ FGH (R.T b) n
  T≃ e ga gb ra cl cr = FGH-ψ₀ (fin 0 refl) (fin 0 refl) cl cr (Ω≃ e ga gb ra)
```

## §5 第 1 层与第 5 站

模式 `fin` 对任何 `S` 都 `OK`, 所以 $\psi_1$ 不问 `S`, 但它的输入 (链的目标) 可能问. `toLv≃`: 第 $\le1$ 层的 `Eq` 给出层号的 $\approx^\mathsf{B}$, 这是嵌套下标的传递; 第 $\ge2$ 层的节点层只有 $\approx^\mathsf{B}$-相关, 而 `o≈` 要参数层字面相同, 所以这个传递**只到第 1 层**.

```agda
  private
    module FL = FinLit S B₀
    module FR = FinLit S′ B₀

  okF-L : ∀ k {i} n (e : i ≡ natL n) → L.OK k (fin n e)
  okF-L k n e = L.OK→OKx k _ (FL.okF k n e)

  okF-R : ∀ k {i} n (e : i ≡ natL n) → R.OK k (fin n e)
  okF-R k n e = R.OK→OKx k _ (FR.okF k n e)

  T₁ : Tg (natL 1) (natL 1)
  T₁ = tg (s≈ z≈)
          ((λ { (inj₁ _) _ → inj₁ refl }) , tt)
          ((λ { (inj₁ _) _ → inj₁ refl }) , tt)
          (inj₁ tt , tt , refl)
          (inj₁ tt , tt , refl)
          tt

  F≃ : ∀ {a b} → a ≈ᴮ b → L.LvG a → R.LvG b → LvR a → Eq (natL 1) (L.F a) (R.F b)
  F≃ {a} {b} e ga gb ra = ψ≃ (fin 1 refl) (fin 1 refl) (okF-L a 1 refl) (okF-R b 1 refl) T₁ (Ω≃ e ga gb ra)

  data Lo : Lv → Set where
    l0 : Lo zero
    l1 : Lo (natL 1)

  toLv≃ : ∀ {k k′} → Lo k → Lo k′ → {x : Ordᴸ k} {y : Ordᴸ k′} → Eq k x y → toLv x ≈ᴮ toLv y
  toLv≃ lk lk′ z≃ = z≈
  toLv≃ lk lk′ (s≃ e) = s≈ (toLv≃ lk lk′ e)
  toLv≃ lk lk′ (l≃ h) = l≈ (λ n → toLv≃ lk lk′ (h n))
  toLv≃ l1 l1 (i≃ {r = inj₁ _} {r′ = inj₁ _} nd nd′ e lr h) =
    o≈ (λ x bx → toLv≃ l1 l1 (h x x bx bx (Z-refl x)))
  toLv≃ l1 lk′ (uˡ {d = d} db e) = toLv≃ l0 lk′ e
  toLv≃ lk l1 (uʳ {d = d} db e) = toLv≃ lk l0 e

  -- 第 5 站: ψ₀(Ω_{ψ₁(Ω_Ω)}): 两个正确的判决给同一个大数
  LΩ : Lv
  LΩ = toLv (Ω (natL 1))

  L₅ R₅ : Lv
  L₅ = toLv (L.F LΩ)
  R₅ = toLv (R.F LΩ)

  Station5≃ : L.LvG LΩ → R.LvG LΩ → LvR LΩ → L.LvG L₅ → R.LvG R₅ → LvR L₅ →
              CL.CZ (fin 0 refl) (Ω L₅) → CR.CZ (fin 0 refl) (Ω R₅) →
              ∀ n → FGH (L.T₅) n ≡ FGH (R.T₅) n
  Station5≃ g g′ r g₅ g₅′ r₅ cl cr =
    T≃ (toLv≃ l1 l1 (F≃ (≈ᴮ-refl LΩ) g g′ r)) g₅ g₅′ r₅ cl cr
```

## §6 非空: 有限层号上是定理

取 `B₀ = ⊤`. 这时任何 `S`, `S′` 都满足前提, 所以这里 `S` 没有被问到; 这只说明定理的前提不是空的.

```agda
asN-nat : ∀ n → asN (natL n) ≡ just (n , refl)
asN-nat zero    = refl
asN-nat (suc n) rewrite asN-nat n = refl

asN-no : ∀ j n → j ≡ natL n → asN j ≡ nothing → ⊥
asN-no _ n refl eq with () ← trans (sym (asN-nat n)) eq

at-n : ∀ n (r : Pre (natL n)) → Σ ℕ λ m → at (natL n) r ≡ natL m
at-n (suc n) (inj₁ _) = n , refl
at-n (suc n) (inj₂ r) = at-n n r

module Sanity (S S′ : Sib) where
  open Target₀ S S′ (λ _ → ⊤)

  all⊤ : ∀ k x → Bs k x
  all⊤ zero       x = tt
  all⊤ (suc _)    x = tt
  all⊤ (lim _)    x = tt
  all⊤ (limᴼ _ _) x = tt

  lvr-nat : ∀ n → LvR (natL n)
  lvr-nat zero    = tt
  lvr-nat (suc n) = lvr-nat n

  go : ∀ n → Σ (Pre (natL (suc n))) λ r → AdmB (natL (suc n)) r × at (natL (suc n)) r ≡ zero
  go zero    = inj₁ tt , tt , refl
  go (suc n) with go n
  ... | r , d , e = inj₂ r , d , e

  okcL : ∀ k (r : Pre k) m → at k r ≡ natL m → L.OK k (chM k r)
  okcL k r m e with asN (at k r) in eq
  ... | just (m′ , e′) = okF-L k m′ e′
  ... | nothing = ⊥-elim (asN-no _ m e eq)

  okcR : ∀ k (r : Pre k) m → at k r ≡ natL m → R.OK k (chM k r)
  okcR k r m e with asN (at k r) in eq
  ... | just (m′ , e′) = okF-R k m′ e′
  ... | nothing = ⊥-elim (asN-no _ m e eq)

  lvtL : ∀ n → L.LvT (natL n)
  lvtL zero    = tt
  lvtL (suc n) = (λ r d → ch r) , lvtL n where
    ch : (r : Pre (natL (suc n))) → L.ChOK (natL (suc n)) r
    ch r with at-n (suc n) r
    ... | zero , e = inj₁ e
    ... | suc m , e = inj₂ (okcL (natL (suc n)) r (suc m) e , subst L.Zt (sym e) (go m))

  lvtR : ∀ n → R.LvT (natL n)
  lvtR zero    = tt
  lvtR (suc n) = (λ r d → ch r) , lvtR n where
    ch : (r : Pre (natL (suc n))) → R.ChOK (natL (suc n)) r
    ch r with at-n (suc n) r
    ... | zero , e = inj₁ e
    ... | suc m , e = inj₂ (okcR (natL (suc n)) r (suc m) e , subst R.Zt (sym e) (go m))

  T-nat : ∀ m n → FGH (L.T (natL m)) n ≡ FGH (R.T (natL m)) n
  T-nat m = T≃ (≈ᴮ-refl (natL m)) (L.t→g _ (lvtL m)) (R.t→g _ (lvtR m)) (lvr-nat m)
            (CL.cz-triv all⊤ (fin 0 refl) _) (CR.cz-triv all⊤ (fin 0 refl) _)
```
