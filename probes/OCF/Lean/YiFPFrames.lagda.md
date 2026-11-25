# NoΩ 域上的沿帧执行与换目标
验收机制文件；编译定理：任意 NoΩ 源层的 St/nxt/thru、执行等式、Gd 与上下文复用。
来源：YiLSFold 的 St 至 good-stOf；配置改为 Ok/Rb/Base，ℕ 极限前向走 thru，后向复合路径。
这些定理不读参照记号；没有给出一般主引理的源关系与读回对应，不声称 Need 或值界。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFPFrames where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base)
open import OCF.Lean.YiNRHit using (NoΩ; chN)
import OCF.Lean.YiTBRow as TB

Cfg : L → Set
Cfg a = Ok a × TB.Rb a × Base a

data St (j a : L) : Set where
  fo : Cfg a → j ≤ a → Tr⁺ j → St j a
  uf : Dn j a → Tr⁺ j → St j a
run⁺ : ∀ {j a} → St j a → Tr a → Tr⁺ j
run⁺ {j} {a} (fo (o , r , B) w β) y = TB.ψ a o r B j w β y
run⁺ {j} {a} (uf d b) y = Up a d b y
run : ∀ {j a} → St j a → Tr a → Tr j
run s y = proj₁ (run⁺ s y)
child : ∀ {s h} → Cfg (nd s h) → Tr (nd s h) → (c : Ch s) → Cfg (h c)
child {s} {h} (o , r , B) x c = proj₂ o c , proj₂ r c , λ i u → TB.ψ (nd s h) o r B i (inc c u) (B i (inc c u)) x

kid : (a : L) → CH a → L
kid (nd s h) c = h c
asChild : ∀ a c → ChT a c → Tr (kid a c)
asChild (nd s h) c y = y

mutual
  nxt : ∀ {a} → NoΩ a → ∀ {j} → St j a → Tr a → (c : CH a) → St j (kid a c)
  nxt {a = zero} n s x ()
  nxt {nd s h} n st@(fo C self β) x c = uf (down stop c) (run⁺ st x)
  nxt {nd s h} n st@(fo C (inu ws) β) x c = fo (child C x c) (ws c) (run⁺ st x)
  nxt {nd sS h} n st@(fo C (inc tt v) β) x tt = fo (child C x tt) v (run⁺ st x)
  nxt {nd sL g} n st@(fo C (inc k v) β) x m = nxtW n C x m k (way g (proj₁ (proj₁ C)) m k) v (run⁺ st x)
  nxt {nd (sΩ k) h} () (fo C (inc c v) β) x c′
  nxt {nd (sΩ k) h} () (fo C (ink v) β) x c
  nxt {nd s h} n st@(uf d b) x c = uf (down d c) (run⁺ st x)

  nxtW : ∀ {g} → (∀ k → NoΩ (g k)) → Cfg (nd sL g) → Tr (nd sL g) → (m k : ℕ)
    → (g m ≤ g k) ⊎ (g k ≤ g m) → ∀ {j} → j ≤ g k → Tr⁺ j → St j (g m)
  nxtW {g} ns C x m k (inj₁ v) w β = thru (ns k) v (fo (child C x k) w β)
  nxtW {g} ns C x m k (inj₂ v) w β = fo (child C x m) (w ∙ v) β

  thru : ∀ {a} → NoΩ a → ∀ {k} → k ≤ a → ∀ {j} → St j a → St j k
  thru ns self st = st
  thru {nd s h} ns (inc c v) st = thru (chN s h ns c) v (nxt ns st zero c)
  thru {nd s h} ns (inu vs) st = thru (chN s h ns (c₀ s)) (vs (c₀ s)) (nxt ns st zero (c₀ s))
  thru {nd (sΩ k) h} () (ink v) st

mutual
  run-up : ∀ {a} (ns : NoΩ a) {j} (st : St j a) (x : Tr a) (c : CH a)
    (y : ChT a c) (e : RCh a c (chZ a c) y)
    → run st (up x c y e) ≡ run (nxt ns st x c) (asChild _ c y)
  run-up {a = zero} ns st x () y e
  run-up {nd s h} ns (fo C self β) x c y e = refl
  run-up {nd s h} ns (fo C (inu ws) β) x c y e = refl
  run-up {nd sS h} ns (fo C (inc tt v) β) x tt y e = refl
  run-up {nd sL g} ns st@(fo C (inc k v) β) x m y e = run-upW ns C x m k (way g (proj₁ (proj₁ C)) m k) v (run⁺ st x) (y , e)
  run-up {nd (sΩ k) h} () (fo C (inc c v) β) x c′ y e
  run-up {nd (sΩ k) h} () (fo C (ink v) β) x c y e
  run-up {nd s h} ns (uf d b) x c y e = refl

  run-upW : ∀ {g} (ns : ∀ k → NoΩ (g k)) (C : Cfg (nd sL g)) (x : Tr (nd sL g)) (m k : ℕ)
    (W : (g m ≤ g k) ⊎ (g k ≤ g m)) {j} (w : j ≤ g k) (β : Tr⁺ j) (y : Tr⁺ (g m))
    → proj₁ (cW W
        (λ v → TB.ψ (g k) (proj₂ (proj₁ C) k) (proj₂ (proj₁ (proj₂ C)) k) (proj₂ (proj₂ (child C x k))) j w β
          (proj₁ (emb (g k) (proj₂ (proj₁ C) k) v y)))
        (λ v → TB.ψ (g m) (proj₂ (proj₁ C) m) (proj₂ (proj₁ (proj₂ C)) m) (proj₂ (proj₂ (child C x m))) j (w ∙ v) β (proj₁ y)))
      ≡ run (nxtW ns C x m k W w β) (proj₁ y)
  run-upW ns C x m k (inj₁ v) w β y = run-thru (ns k) (child C x k) v (fo (child C x k) w β) y
  run-upW ns C x m k (inj₂ v) w β y = refl

  run-thru : ∀ {a} (ns : NoΩ a) (C : Cfg a) {k} (v : k ≤ a) {j} (st : St j a) (y : Tr⁺ k)
    → run st (proj₁ (emb a (proj₁ C) v y)) ≡ run (thru ns v st) (proj₁ y)
  run-thru ns C self st y = refl
  run-thru {nd s h} ns C (inc c v) st y =
    trans (run-up ns st zero c (proj₁ (emb (h c) (proj₂ (proj₁ C) c) v y)) (proj₂ (emb (h c) (proj₂ (proj₁ C) c) v y)))
      (run-thru (chN s h ns c) (child C zero c) v (nxt ns st zero c) y)
  run-thru {nd s h} ns C (inu vs) st y =
    trans (run-up ns st zero (c₀ s) (proj₁ (emb (h (c₀ s)) (proj₂ (proj₁ C) (c₀ s)) (vs (c₀ s)) y))
      (proj₂ (emb (h (c₀ s)) (proj₂ (proj₁ C) (c₀ s)) (vs (c₀ s)) y)))
      (run-thru (chN s h ns (c₀ s)) (child C zero (c₀ s)) (vs (c₀ s)) (nxt ns st zero (c₀ s)) y)
  run-thru {nd (sΩ k) h} () C (ink v) st y

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ)
open import Relation.Binary.PropositionalEquality using (sym; cong)
open import OCF.Lean.YiRWCheck using (way-refl)
cfgOf : ∀ {j a} → St j a → Maybe (Cfg a)
cfgOf (fo C w β) = just C
cfgOf (uf d b) = nothing
can : ∀ {j a} → Cfg a → j ≤ a → St j a
can {j} (o , r , B) w = fo (o , r , B) w (B j w)
no-nj : ∀ {A Z : Set} {x : A} → nothing ≡ just x → Z
no-nj ()
record Gd {a k : L} (Φ : ∀ {j} → St j a → St j k) : Set where
  field
    g-uf : ∀ {j} (st : St j a) → cfgOf st ≡ nothing → cfgOf (Φ st) ≡ nothing
    g-fo : ∀ {j} (C : Cfg a) (w : j ≤ a) (β : Tr⁺ j) {C′ : Cfg k}
      → cfgOf (Φ (fo C w β)) ≡ just C′
      → ∀ {j′} (w′ : j′ ≤ k) → Σ (j′ ≤ a) (λ v → Φ (can C v) ≡ can C′ w′)
open Gd public
good-id : ∀ {a} → Gd {a} {a} (λ st → st)
good-id = record { g-uf = λ st e → e ; g-fo = λ { C w β refl w′ → w′ , refl } }
good-∘ : ∀ {a k k′} {Φ : ∀ {j} → St j a → St j k} {Ψ : ∀ {j} → St j k → St j k′}
  → Gd Φ → Gd Ψ → Gd (λ st → Ψ (Φ st))
good-∘ {a} {k} {k′} {Φ} {Ψ} GΦ GΨ = record { g-uf = λ st e → g-uf GΨ (Φ st) (g-uf GΦ st e) ; g-fo = gf }
  where
  aux : ∀ {j} (C : Cfg a) (w : j ≤ a) (β : Tr⁺ j) {C″ : Cfg k′}
    (st′ : St j k) → Φ (fo C w β) ≡ st′ → cfgOf (Ψ st′) ≡ just C″
    → ∀ {j′} (w′ : j′ ≤ k′) → Σ (j′ ≤ a) (λ v → Ψ (Φ (can C v)) ≡ can C″ w′)
  aux C w β (uf d b) e eq w′ = no-nj (trans (sym (g-uf GΨ (uf d b) refl)) eq)
  aux C w β (fo C′ v β′) e eq w′ =
    proj₁ (g-fo GΦ C w β (cong cfgOf e) (proj₁ (g-fo GΨ C′ v β′ eq w′)))
    , trans (cong (λ st → Ψ st) (proj₂ (g-fo GΦ C w β (cong cfgOf e) (proj₁ (g-fo GΨ C′ v β′ eq w′)))))
      (proj₂ (g-fo GΨ C′ v β′ eq w′))
  gf : ∀ {j} (C : Cfg a) (w : j ≤ a) (β : Tr⁺ j) {C″ : Cfg k′}
    → cfgOf (Ψ (Φ (fo C w β))) ≡ just C″
    → ∀ {j′} (w′ : j′ ≤ k′) → Σ (j′ ≤ a) (λ v → Ψ (Φ (can C v)) ≡ can C″ w′)
  gf C w β eq w′ = aux C w β (Φ (fo C w β)) refl eq w′

nxt-same : ∀ {g} (ns : ∀ n → NoΩ (g n)) (C : Cfg (nd sL g)) (x : Tr (nd sL g)) (m : ℕ)
  {j} (w : j ≤ g m) (β : Tr⁺ j)
  → nxtW ns C x m m (way g (proj₁ (proj₁ C)) m m) w β ≡ fo (child C x m) w β
nxt-same {g} ns C x m w β = cong (λ W → nxtW ns C x m m W w β) (way-refl g (proj₁ (proj₁ C)) m)

mutual
  good-nxt : ∀ {a} (ns : NoΩ a) (x : Tr a) (c : CH a) → Gd (λ st → nxt ns st x c)
  good-nxt {a = zero} ns x ()
  good-nxt {nd sS h} ns x tt = record { g-uf = gu ; g-fo = gf }
    where
    gu : ∀ {j} (st : St j (nd sS h)) → cfgOf st ≡ nothing → cfgOf (nxt ns st x tt) ≡ nothing
    gu (uf d b) e = refl
    gf : ∀ {j} (C : Cfg (nd sS h)) (w : j ≤ nd sS h) (β : Tr⁺ j) {C′ : Cfg (h tt)}
      → cfgOf (nxt ns (fo C w β) x tt) ≡ just C′
      → ∀ {j′} (w′ : j′ ≤ h tt) → Σ (j′ ≤ nd sS h) (λ v → nxt ns (can C v) x tt ≡ can C′ w′)
    gf C (inc tt v) β refl w′ = inc tt w′ , refl
    gf C (inu vs) β refl w′ = inc tt w′ , refl
  good-nxt {nd sL g} ns x m = record { g-uf = gu ; g-fo = gf }
    where
    gu : ∀ {j} (st : St j (nd sL g)) → cfgOf st ≡ nothing → cfgOf (nxt ns st x m) ≡ nothing
    gu (uf d b) e = refl
    gf : ∀ {j} (C : Cfg (nd sL g)) (w : j ≤ nd sL g) (β : Tr⁺ j) {C′ : Cfg (g m)}
      → cfgOf (nxt ns (fo C w β) x m) ≡ just C′
      → ∀ {j′} (w′ : j′ ≤ g m) → Σ (j′ ≤ nd sL g) (λ v → nxt ns (can C v) x m ≡ can C′ w′)
    gf C (inu vs) β refl w′ = inc m w′ , nxt-same ns C x m w′ _
    gf C (inc k v) β eq w′ = goodW ns C x m k (way g (proj₁ (proj₁ C)) m k) refl v _ eq w′
  good-nxt {nd (sΩ k) h} () x c

  goodW : ∀ {g} (ns : ∀ n → NoΩ (g n)) (C : Cfg (nd sL g)) (x : Tr (nd sL g))
    (m k : ℕ) (W : (g m ≤ g k) ⊎ (g k ≤ g m)) → way g (proj₁ (proj₁ C)) m k ≡ W
    → ∀ {j} (w : j ≤ g k) (β : Tr⁺ j) {C′ : Cfg (g m)}
    → cfgOf (nxtW ns C x m k W w β) ≡ just C′
    → ∀ {j′} (w′ : j′ ≤ g m) → Σ (j′ ≤ nd sL g) (λ v → nxt ns (can C v) x m ≡ can C′ w′)
  goodW {g} ns C x m k (inj₁ v) eW w β eq {j′} w′ = inc k (proj₁ R₂)
    , trans (cong (λ W → nxtW ns C x m k W (proj₁ R₂) (proj₂ (proj₂ (child C x k)) j′ (proj₁ R₂))) eW) (proj₂ R₂)
    where
    R₂ = g-fo (good-thru (ns k) v) (child C x k) w β eq w′
  goodW ns C x m k (inj₂ v) eW w β refl w′ = inc m w′ , nxt-same ns C x m w′ _

  good-thru : ∀ {a} (ns : NoΩ a) {k} (v : k ≤ a) → Gd (λ st → thru ns v st)
  good-thru ns self = good-id
  good-thru {nd s h} ns (inc c v) = good-∘ (good-nxt ns zero c) (good-thru (chN s h ns c) v)
  good-thru {nd s h} ns (inu vs) = good-∘ (good-nxt ns zero (c₀ s)) (good-thru (chN s h ns (c₀ s)) (vs (c₀ s)))
  good-thru {nd (sΩ k) h} () (ink v)

kidN : ∀ {a} → NoΩ a → (c : CH a) → NoΩ (kid a c)
kidN {nd s h} ns c = chN s h ns c

data Dc (a : L) : L → Set where
  [] : Dc a a
  _∷_ : (c : CH a) → ∀ {b} → Dc (kid a c) b → Dc a b
snocD : ∀ {a b} → Dc a b → (c : CH b) → Dc a (kid b c)
snocD [] c = c ∷ []
snocD (c′ ∷ d) c = c′ ∷ snocD d c

data Ctx (a : L) : ∀ {b} → Dc a b → Set where
  [] : Ctx a []
  fr : ∀ {b} (x : Tr a) (c : CH a) {d : Dc (kid a c) b} → Ctx (kid a c) d → Ctx a (c ∷ d)
snocC : ∀ {a b} {d : Dc a b} → Ctx a d → Tr b → (c : CH b) → Ctx a (snocD d c)
snocC [] x c = fr x c []
snocC (fr x′ c′ Γ) x c = fr x′ c′ (snocC Γ x c)
stOf : ∀ {a j} → NoΩ a → St j a → ∀ {b} {d : Dc a b} → Ctx a d → St j b
stOf ns st [] = st
stOf ns st (fr x c Γ) = stOf (kidN ns c) (nxt ns st x c) Γ
noΩD : ∀ {a} → NoΩ a → ∀ {b} {d : Dc a b} → Ctx a d → NoΩ b
noΩD ns [] = ns
noΩD ns (fr x c Γ) = noΩD (kidN ns c) Γ
stOf-snoc : ∀ {a j b} (ns : NoΩ a) (st : St j a) {d : Dc a b} (Γ : Ctx a d) (x : Tr b) (c : CH b)
  → stOf ns st (snocC Γ x c) ≡ nxt (noΩD ns Γ) (stOf ns st Γ) x c
stOf-snoc ns st [] x c = refl
stOf-snoc ns st (fr x′ c′ Γ) x c = stOf-snoc (kidN ns c′) (nxt ns st x′ c′) Γ x c
good-stOf : ∀ {a} (ns : NoΩ a) {b} {d : Dc a b} (Γ : Ctx a d) → Gd (λ st → stOf ns st Γ)
good-stOf ns [] = good-id
good-stOf ns (fr x c Γ) = good-∘ (good-nxt ns x c) (good-stOf (kidN ns c) Γ)
```
