# 降维打击的检验: `Commute` 的前提可满足 (有限下标片段, 验收)

> **验收节.** `Commute` 不是空真. 取下标类 `N` = 自然数项, 判决 `ver`: §1 证明 `GV` 对 `N` 成立, §2–§3 证明封闭性, §4 得到 `nat-label`: 下标全是自然数的任意可数项都带标签, 不要求标准形, 只以 `Funext` 为参数. 这是 Ω_n 段, 不触及任何非有限比较.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.InaccStrikeNat where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import OCF.Align.InaccTreeBase hiding (eq)
open import OCF.Align.InaccTree using (IsNat; nz; ns; natL; natIs; atNat; same-≅)
open import OCF.Align.InaccStrikeBase
open import OCF.Align.InaccStrikeCommute
open import OCF.Align.InaccTreeAccept using (LabN)
import OCF.Align.EBO as E
open E using (T; PT; cmpᵀ; Cmp; lt; eq; gt; 𝟏) renaming (natT to natᵗ)
```

## §1 `ver` 在自然数上满足 `GV`

```agda
upT : ∀ {k} → (x : Ordᴸ k) → Ordᴸ (suc k)
upT x = up tt x

module Cast (fe : Funext) where
  cast-id : ∀ {a} → IsNat a → (y : Ordᴸ a) → cast a a y ≡ y
  castP-id : ∀ {a} → IsNat a → (r : Pre a) →
             Σ (Ordᴸ (at a r) → Ordᴸ (at a r)) λ bk → (castP a a r ≡ just (r , bk)) × (∀ y → bk y ≡ y)

  castP-id (ns i) (inj₁ _) = cast _ _ , refl , cast-id i
  castP-id {suc a} (ns i) (inj₂ r) with castP a a r | castP-id i r
  ... | just _ | bk , refl , h = bk , refl , h

  cast-id i zero    = refl
  cast-id i (suc y) = cong (Tree.suc) (cast-id i y)
  cast-id i (lim f) = cong (Tree.lim) (fe (λ n → cast-id i (f n)))
  cast-id {a} i (limᵢ r f) with castP a a r | castP-id i r
  ... | just _ | bk , refl , h = cong (Tree.limᵢ r) (fe λ y →
        trans (cast-id i (f (intoL a r (bk (outL a r y)))))
              (cong f (trans (cong (intoL a r) (h (outL a r y))) (into-out a r y))))
  cast-id {suc a} (ns i) (up _ x) = cong (up tt) (cast-id i x)
```

```agda
natS : ℕ → St
natS zero    = zero
natS (suc n) = suc (natS n)

add1 : ∀ n → addS (suc zero) (natS n) ≡ natS (suc n)
add1 zero    = refl
add1 (suc n) = cong sucS (add1 n)

S-nat : ∀ D n → Tr.S D (natᵗ n) ≡ natS n
S-nat D zero    = refl
S-nat D (suc n) = trans (cong (addS (suc zero)) (S-nat D n)) (add1 n)

toLv-natS : ∀ n → toLvS (natS n) ≡ natL n
toLv-natS zero    = refl
toLv-natS (suc n) = cong sucL (toLv-natS n)

L-nat : ∀ D n → Tr.L D (natᵗ n) ≡ natL n
L-nat D n = trans (cong toLvS (S-nat D n)) (toLv-natS n)

cmpN : ℕ → ℕ → Cmp
cmpN zero    zero    = eq
cmpN zero    (suc _) = lt
cmpN (suc _) zero    = gt
cmpN (suc a) (suc b) = cmpN a b

cmp-nat : ∀ a b → cmpᵀ (natᵗ a) (natᵗ b) ≡ cmpN a b
cmp-nat zero    zero    = refl
cmp-nat zero    (suc b) = refl
cmp-nat (suc a) zero    = refl
cmp-nat (suc a) (suc b) = cmp-nat a b

same-≡ : ∀ a b → same (natL a) (natL b) ≡ true → a ≡ b
same-≡ zero    zero    e = refl
same-≡ zero    (suc b) ()
same-≡ (suc a) zero    ()
same-≡ (suc a) (suc b) e = cong suc (same-≡ a b e)

same-refl : ∀ a → same (natL a) (natL a) ≡ true
same-refl zero    = refl
same-refl (suc a) = same-refl a

lt-suc : ∀ a b → cmpN a b ≡ lt → cmpN a (suc b) ≡ lt
lt-suc zero    zero    ()
lt-suc zero    (suc b) e = refl
lt-suc (suc a) zero    ()
lt-suc (suc a) (suc b) e = lt-suc a b e

eq-≡ : ∀ a b → cmpN a b ≡ eq → a ≡ b
eq-≡ zero    zero    e = refl
eq-≡ (suc a) (suc b) e = cong suc (eq-≡ a b e)

gt-suc : ∀ a b → cmpN a b ≡ gt → GV {zero} {zero} (cmpN a (suc b)) rise
gt-suc (suc zero)    zero    e = tt
gt-suc (suc (suc a)) zero    e = tt
gt-suc (suc a)       (suc b) e = gt-suc a b e

lt-self : ∀ a → cmpN a (suc a) ≡ lt
lt-self zero    = refl
lt-self (suc a) = lt-self a

module VerNat (fe : Funext) where
  open Cast fe

  verNat : ∀ a b → GV (cmpN a b) (ver (natL a) (natL b))
  verNat zero    zero    = tt
  verNat (suc a) zero    = tt
  verNat a (suc b) with same (natL a) (natL b) in se
  ... | true with same-≡ a b se
  ...   | refl = subst (λ v → GV v (pen {natL a} {suc (natL a)} (inj₁ tt) (cast (natL a) (natL a)))) (sym (lt-self a))
                       (refl , λ y → cong strip (cast-id (natIs a) y))
  verNat a (suc b) | false with cmpN a b in ce | ver (natL a) (natL b) | verNat a b
  ... | lt | pen r bk | l , s′ = subst (λ v → GV v (pen {natL a} {suc (natL b)} (inj₂ r) bk)) (sym (lt-suc a b ce)) (l , s′)
  ... | lt | rise | ()
  ... | eq | pen r bk | ()
  ... | gt | pen r bk | ()
  ... | eq | rise | g with eq-≡ a b ce
  ...   | refl with () ← trans (sym se) (same-refl a)
  verNat a (suc b) | false | gt | rise | g = gv (cmpN a (suc b)) (gt-suc a b ce) where
    gv : ∀ v → GV {zero} {zero} v rise → GV {natL a} {suc (natL b)} v rise
    gv eq t = t
    gv gt t = t

N : T → Set
N t = Σ ℕ λ n → t ≡ natᵗ n

agrN : (fe : Funext) → ∀ u v → N u → N v → GV (cmpᵀ u v) (ver (Tr.L ver u) (Tr.L ver v))
agrN fe _ _ (a , refl) (b , refl) rewrite L-nat ver a | L-nat ver b | cmp-nat a b = VerNat.verNat fe a b
```

## §2 下标全是自然数的项: 语法封闭性

```agda
data Q : T → Set where
  q[] : Q []
  q∷  : ∀ {u w xs} → N u → Q w → Q xs → Q (E.ψ u w ∷ xs)

Q-nat : ∀ n → Q (natᵗ n)
Q-nat zero    = q[]
Q-nat (suc n) = q∷ (0 , refl) q[] (Q-nat n)

cof-nat : ∀ n → E.cof (natᵗ (suc n)) ≡ E.c1
cof-nat zero    = refl
cof-nat (suc n) = cof-nat n

pred-nat : ∀ n → E.pred (natᵗ (suc n)) ≡ natᵗ n
pred-nat zero    = refl
pred-nat (suc n) = cong (𝟏 ∷_) (pred-nat n)

N-ne : ∀ {w ws} → N (w ∷ ws) → Σ ℕ λ n → (w ∷ ws) ≡ natᵗ (suc n)
N-ne (suc n , e) = n , e

c1-of : ∀ {w ws c} → N (w ∷ ws) → E.cof (w ∷ ws) ≡ c → c ≡ E.c1
c1-of n refl with N-ne n
... | m , e = trans (cong E.cof e) (cof-nat m)

nu : ∀ {w ν} → Q w → E.cof w ≡ E.cΩ ν → N ν
nu (q∷ {xs = _ ∷ _} _ _ qx) e = nu qx e
nu (q∷ {u = u} {w = y ∷ ys} {xs = []} _ qw _) e = go (E.cof (y ∷ ys)) refl e where
  go : ∀ c → E.cof (y ∷ ys) ≡ c → ∀ {ν} → E.cofA u c ≡ E.cΩ ν → N ν
  go (E.cΩ μ) be e′ = go′ (cmpᵀ (E.sucT μ) u) e′ where
    go′ : ∀ m {ν} → E.cofψ₊ u μ m ≡ E.cΩ ν → N ν
    go′ lt refl = nu qw be
    go′ eq refl = nu qw be
    go′ gt ()
  go E.c0 _ ()
  go E.c1 _ ()
  go E.cω _ ()
nu (q∷ {u = []} {w = []} {xs = []} _ _ _) ()
nu (q∷ {u = w ∷ ws} {w = []} {xs = []} nu′ _ _) e = go (E.cof (w ∷ ws)) refl e where
  go : ∀ c → E.cof (w ∷ ws) ≡ c → ∀ {ν} → E.cofψ0 (w ∷ ws) c ≡ E.cΩ ν → N ν
  go E.c0 be ()
  go E.c1 be refl with N-ne nu′
  ... | m , ee = m , trans (cong E.pred ee) (pred-nat m)
  go E.cω be ()
  go (E.cΩ μ) be refl with () ← trans (sym be) (c1-of nu′ refl)

clQ : ClQ Q N
clQ = record
  { cl-tl  = λ { (q∷ _ _ qx) → qx }
  ; cl-sub = λ { (q∷ (n , refl) _ _) → Q-nat n }
  ; cl-arg = λ { (q∷ _ qw _) → qw }
  ; cl-idx = λ { (q∷ nu′ _ _) → nu′ }
  ; cl-nu  = nu
  }
```

## §3 基本列的封闭性 (纯语法, 不要求标准形)

```agda
Q-pred : ∀ {t} → Q t → Q (E.pred t)
Q-pred q[] = q[]
Q-pred (q∷ {xs = _ ∷ _} n w x) = q∷ n w (Q-pred x)
Q-pred (q∷ {u = []} {w = []} {xs = []} n w x) = q[]
Q-pred (q∷ {u = []} {w = _ ∷ _} {xs = []} n w x) = q∷ n w x
Q-pred (q∷ {u = _ ∷ _} {xs = []} n w x) = q∷ n w x

Q-fsT : ∀ b → Q b → ∀ η → Q η → Q (E.fsT b η)
Q-fsT [] _ η qη = q[]
Q-fsT (x ∷ y ∷ ys) (q∷ n w r) η qη = q∷ n w (Q-fsT (y ∷ ys) r η qη)
Q-fsT (E.ψ [] [] ∷ []) _ η qη = q[]
Q-fsT (E.ψ (w ∷ ws) [] ∷ []) (q∷ n a r) η qη = go (E.cof (w ∷ ws)) refl where
  go : ∀ c → E.cof (w ∷ ws) ≡ c → Q (E.fsT0 (w ∷ ws) c η)
  go E.c0 be = q∷ n a r
  go E.c1 be = qη
  go E.cω be = q∷ n a r
  go (E.cΩ ν) be with () ← trans (sym be) (c1-of n refl)
Q-fsT (E.ψ u (y ∷ ys) ∷ []) (q∷ n a r) η qη = go (E.cof (y ∷ ys)) where
  go : ∀ c → Q (E.fsT₊ u (y ∷ ys) c η)
  go E.c0 = q∷ n a r
  go E.c1 = q∷ n a r
  go E.cω = q∷ n a r
  go (E.cΩ ν) = go′ (cmpᵀ (E.sucT ν) u) where
    go′ : ∀ m → Q (E.fsTc u (y ∷ ys) ν m η)
    go′ lt = q∷ n (Q-fsT (y ∷ ys) a η qη) q[]
    go′ eq = q∷ n (Q-fsT (y ∷ ys) a η qη) q[]
    go′ gt = q∷ n a r

Q-γ : ∀ b ν → Q b → N ν → ∀ k → Q (E.γT b ν k)
Q-γ b ν qb nν zero    = q∷ nν q[] q[]
Q-γ b ν qb nν (suc k) = q∷ nν (Q-fsT b qb _ (Q-γ b ν qb nν k)) q[]

Q-rep : ∀ u {p a} (a′< : p E.<ᵀ a) → N u → Q p → ∀ n → Q (E.trm (E.rep↓ u a′< n))
Q-rep u a′< nu′ qp zero    = q[]
Q-rep u a′< nu′ qp (suc n) = q∷ nu′ qp (Q-rep u a′< nu′ qp n)

Q-fsn↓ : ∀ x xs → Q (x ∷ xs) → ∀ n → Q (E.trm (E.fsn↓ x xs n))
Q-fsn↓ x (y ∷ ys) (q∷ a b r) n = q∷ a b (Q-fsn↓ y ys r n)
Q-fsn↓ (E.ψ [] []) [] q n = q[]
Q-fsn↓ (E.ψ (w ∷ ws) []) [] (q∷ a b r) n = go (E.cof (w ∷ ws)) refl where
  go : ∀ c (be : E.cof (w ∷ ws) ≡ c) → Q (E.trm (E.fsn↓0 w ws c be n))
  go E.c0 be = q[]
  go E.c1 be = Q-nat n
  go E.cω be with () ← trans (sym be) (c1-of a refl)
  go (E.cΩ ν) be with () ← trans (sym be) (c1-of a refl)
Q-fsn↓ (E.ψ u (y ∷ ys)) [] (q∷ a qb r) n = go (E.cof (y ∷ ys)) refl where
  go : ∀ c (be : E.cof (y ∷ ys) ≡ c) → Q (E.trm (E.fsn↓₊ u y ys c be n))
  go E.c0 be = q[]
  go E.c1 be = Q-rep u (E.pred-< (y ∷ ys) be) a (Q-pred qb) n
  go E.cω be = q∷ a (Q-fsn↓ y ys qb n) q[]
  go (E.cΩ ν) be = go′ (cmpᵀ (E.sucT ν) u) where
    fT : ∀ {η} (η< : η E.<ᵀ E.Ωs ν) → Q η → Q (E.trm (E.fsT↓ (y ∷ ys) be η<))
    fT {η} η< qη = subst Q (sym (E.fsT↓-trm (y ∷ ys) be η<)) (Q-fsT (y ∷ ys) qb η qη)
    go′ : ∀ m → Q (E.trm (E.fsn↓c u y ys ν be m n))
    go′ gt = q∷ a (fT (E.dec (E.γ↓ (y ∷ ys) ν be n))
                 (subst Q (sym (E.γ↓-trm (y ∷ ys) ν be n)) (Q-γ (y ∷ ys) ν qb (nu qb be) n))) q[]
    go′ lt = q∷ a (fT (E.natT<Ωs n ν) (Q-nat n)) q[]
    go′ eq = q∷ a (fT (E.natT<Ωs n ν) (Q-nat n)) q[]

data Ctb : T → Set where
  c[] : Ctb []
  c∷  : ∀ {w xs} → Ctb xs → Ctb (E.ψ [] w ∷ xs)

Ctb-pred : ∀ {t} → Ctb t → Ctb (E.pred t)
Ctb-pred c[] = c[]
Ctb-pred (c∷ {xs = _ ∷ _} r) = c∷ (Ctb-pred r)
Ctb-pred (c∷ {w = []} {xs = []} r) = c[]
Ctb-pred (c∷ {w = _ ∷ _} {xs = []} r) = c∷ r

Ctb-rep : ∀ {p a} (a′< : p E.<ᵀ a) n → Ctb (E.trm (E.rep↓ [] a′< n))
Ctb-rep a′< zero    = c[]
Ctb-rep a′< (suc n) = c∷ (Ctb-rep a′< n)

Ctb-fsn↓ : ∀ x xs → Ctb (x ∷ xs) → ∀ n → Ctb (E.trm (E.fsn↓ x xs n))
Ctb-fsn↓ x (y ∷ ys) (c∷ r) n = c∷ (Ctb-fsn↓ y ys r n)
Ctb-fsn↓ (E.ψ [] []) [] _ n = c[]
Ctb-fsn↓ (E.ψ [] (y ∷ ys)) [] _ n = go (E.cof (y ∷ ys)) refl where
  go : ∀ c (be : E.cof (y ∷ ys) ≡ c) → Ctb (E.trm (E.fsn↓₊ [] y ys c be n))
  go E.c0 be = c[]
  go E.c1 be = Ctb-rep (E.pred-< (y ∷ ys) be) n
  go E.cω be = c∷ c[]
  go (E.cΩ ν) be = go′ (cmpᵀ (E.sucT ν) []) where
    go′ : ∀ m → Ctb (E.trm (E.fsn↓c [] y ys ν be m n))
    go′ lt = c∷ c[]
    go′ eq = c∷ c[]
    go′ gt = c∷ c[]

sucT-gt : ∀ μ → cmpᵀ (E.sucT μ) [] ≡ gt
sucT-gt []      = refl
sucT-gt (_ ∷ _) = refl

Ctb-nc : ∀ {t ν} → Ctb t → E.cof t ≡ E.cΩ ν → ⊥
Ctb-nc (c∷ {xs = y ∷ ys} r) e = Ctb-nc r e
Ctb-nc (c∷ {w = []} {xs = []} r) ()
Ctb-nc (c∷ {w = y ∷ ys} {xs = []} r) e = go (E.cof (y ∷ ys)) e where
  go : ∀ c {ν} → E.cofA [] c ≡ E.cΩ ν → ⊥
  go E.c0 ()
  go E.c1 ()
  go E.cω ()
  go (E.cΩ μ) e′ rewrite sucT-gt μ with () ← e′
```

## §4 定理: 有限下标片段上的标签 (模外延性, 无其它前提)

`LabN` 对下标全是自然数的**任意**可数项成立, 不要求标准形. 判决是具体的 `ver`.

```agda
P : T → Set
P t = Q t × Ctb t

P-fs : ∀ {t} → P t → E.cof t ≡ E.cω → ∀ n → P (E.fsn t n)
P-fs {t = []} _ ()
P-fs {t = x ∷ xs} (q , c) _ n = Q-fsn↓ x xs q n , Ctb-fsn↓ x xs c n

module NatLabel (fe : Funext) where
  open Main fe ver Q N clQ (agrN fe)
  open Lab P proj₁ P-fs
    (λ { (q , c) _ → Q-pred q , Ctb-pred c })
    (λ { (_ , c) e → Ctb-nc c e })

  nat-label : ∀ t → P t → LabN (dz (Tr.S ver t)) t
  nat-label = Commute
```
