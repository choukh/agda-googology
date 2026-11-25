# 换基证据与码域的两条编译否定
编译否定，不读记号：(1) 合法性推不出换基证据：合法的 Ω 形状层号 `Z` 上没有 `Schema`（`noS`），所以没有从合法性给出满证据的统一构造（对一切合法层号 `no-uniform`；对变量 a 的同步对象 `nd (sΩ zero) a`，缺在孩子上，`no-sync`）；反例不在读回域内，读作量化域太宽。
(2) `YiBSRead` 的码域在嵌入下不封闭：码读出的树顶不是嵌入（`read-not-up`），沿非平凡路径嵌入的树顶是嵌入（`emb-up`），所以不在任何 `Domain` 里（`emb∉read`、`∉dom`）。
不否定什么：不否定值，不否定加了嵌入码的码域；读回域上的覆盖见 `YiBCCover`，嵌入块到达换基行见 `YiBCReach`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBCNeg where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiBSBase
open import OCF.Lean.YiBSRead using (Read; omega; next; plus; limit; read; source; Domain)
open import OCF.Lean.YiBCCover using (Full)
```

## (1) 合法而无证据的层号

`Z = nd (sΩ one) hZ`：孩子 0 是 ω，其余孩子是 ω′（从 1 起的 ω）；下标层 `one` 在两者之内，但没有公共地板 F 满足 `one ≤ F` 且两孩子都是 `F ⊕ _`。

```agda
natL : ℕ → L
natL zero    = zero
natL (suc n) = nd sS (λ _ → natL n)

one ω ω′ : L
one = natL 1
ω   = nd sL natL
ω′  = nd sL (λ n → natL (suc n))

ok-nat : ∀ n → Ok (natL n)
ok-nat zero    = tt
ok-nat (suc n) = tt , λ _ → ok-nat n

hZ : Tr one → L
hZ zero         = ω
hZ (suc _)      = ω′
hZ (lim _ _)    = ω′
hZ (Ω _ _)      = ω′
hZ (up _ _ _ _) = ω′

Z : L
Z = nd (sΩ one) hZ

kZ : (c : Tr one) → one ≤ hZ c
kZ zero         = inc 1 self
kZ (suc _)      = inc 0 self
kZ (lim _ _)    = inc 0 self
kZ (Ω _ _)      = inc 0 self
kZ (up _ _ _ _) = inc 0 self

oZ : (c : Tr one) → Ok (hZ c)
oZ zero         = (λ n → inc tt self) , ok-nat
oZ (suc _)      = (λ n → inc tt self) , λ n → ok-nat (suc n)
oZ (lim _ _)    = (λ n → inc tt self) , λ n → ok-nat (suc n)
oZ (Ω _ _)      = (λ n → inc tt self) , λ n → ok-nat (suc n)
oZ (up _ _ _ _) = (λ n → inc tt self) , λ n → ok-nat (suc n)

ok-Z : Ok Z
ok-Z = (ok-nat 1 , kZ) , oZ
```

```agda
subL : L → ℕ → L
subL (nd sL g) n = g n
subL _         n = zero

subS : L → L
subS (nd sS h) = h tt
subS _         = zero

zero-⊕ : (F b : L) → zero ≡ F ⊕ b → F ≡ zero
zero-⊕ F zero     e = sym e
zero-⊕ F (nd s h) ()

nat≢ω⊕ : (b : L) (m : ℕ) → natL m ≡ ω ⊕ b → ⊥
nat≢ω⊕ zero          zero    ()
nat≢ω⊕ (nd s h)      zero    ()
nat≢ω⊕ zero          (suc m) ()
nat≢ω⊕ (nd sS h)     (suc m) e = nat≢ω⊕ (h tt) m (cong subS e)
nat≢ω⊕ (nd sL h)     (suc m) ()
nat≢ω⊕ (nd (sΩ k) h) (suc m) ()

ω′≢ω⊕ : (b : L) → ω′ ≡ ω ⊕ b → ⊥
ω′≢ω⊕ zero          e  with cong (λ x → subL x 0) e
... | ()
ω′≢ω⊕ (nd sL g)     e  = nat≢ω⊕ (g 0) 1 (cong (λ x → subL x 0) e)
ω′≢ω⊕ (nd sS h)     ()
ω′≢ω⊕ (nd (sΩ k) h) ()

no1≤0 : one ≤ zero → ⊥
no1≤0 ()

noS : Schema one hZ → ⊥
noS S = go (floor S) (offsets S zero) (offsets S (suc zero)) (index-floor S) (shape S zero) (shape S (suc zero))
  where
  go : (F b₀ b₁ : L) → one ≤ F → ω ≡ F ⊕ b₀ → ω′ ≡ F ⊕ b₁ → ⊥
  go F zero          b₁ v e₀ e₁ = ω′≢ω⊕ b₁ (trans e₁ (cong (_⊕ b₁) (sym e₀)))
  go F (nd sL g)     b₁ v e₀ e₁ = no1≤0 (subst (one ≤_) (zero-⊕ F (g 0) (cong (λ x → subL x 0) e₀)) v)
  go F (nd sS h)     b₁ v () e₁
  go F (nd (sΩ k) h) b₁ v () e₁

no-full-Z : (r : Rb Z) → Full Z r → ⊥
no-full-Z (just S , _) _        = noS S
no-full-Z (nothing , _) (() , _)

no-uniform : ((ℓ : L) → Ok ℓ → Σ (Rb ℓ) (Full ℓ)) → ⊥
no-uniform F = no-full-Z (proj₁ (F Z ok-Z)) (proj₂ (F Z ok-Z))
```

变量 a 的同步对象（`YiSYReduce.Sync` 的量化域）：取 `a = λ _ → Z`；缺的是孩子上的证据（顶上那一份在折叠里用不到，`YiBCCover.top-idle`）。

```agda
aZ : Tr zero → L
aZ _ = Z

ok-aZ : Ok (nd (sΩ zero) aZ)
ok-aZ = (tt , λ c → z≤ Z) , λ c → ok-Z

no-sync : ((a : Tr zero → L) → Ok (nd (sΩ zero) a) → Σ (Rb (nd (sΩ zero) a)) (Full (nd (sΩ zero) a))) → ⊥
no-sync F = no-full-Z (proj₂ (proj₁ (F aZ ok-aZ)) zero) (proj₂ (proj₂ (F aZ ok-aZ)) zero)
```

## (2) 码域在嵌入下不封闭

```agda
IsUp : ∀ {S} → T S → Set
IsUp (up _ _ _ _) = ⊤
IsUp zero         = ⊥
IsUp (suc _)      = ⊥
IsUp (lim _ _)    = ⊥
IsUp (Ω _ _)      = ⊥

Ωt-not-up : (ℓ : L) → IsUp (proj₁ (Ωt ℓ)) → ⊥
Ωt-not-up zero          ()
Ωt-not-up (nd sS h)     ()
Ωt-not-up (nd sL g)     ()
Ωt-not-up (nd (sΩ k) h) ()

plus-not-up : ∀ {S} (x y : T S) → (IsUp x → ⊥) → (IsUp y → ⊥) → IsUp (x + y) → ⊥
plus-not-up x zero         nx ny u = nx u
plus-not-up x (suc y)      nx ny ()
plus-not-up x (lim f a)    nx ny ()
plus-not-up x (Ω p g)      nx ny ()
plus-not-up x (up y c w e) nx ny u = ny tt

read-not-up : (ℓ : L) (d : Read) → IsUp (proj₁ (read ℓ d)) → ⊥
read-not-up ℓ omega      = Ωt-not-up ℓ
read-not-up ℓ (next d)   ()
read-not-up ℓ (plus d e) =
  plus-not-up (proj₁ (read ℓ d)) (proj₁ (read ℓ e)) (read-not-up ℓ d) (read-not-up ℓ e)
read-not-up ℓ (limit f)  ()

Step : ∀ {b j ℓ} → Pth b j ℓ → Set
Step self      = ⊥
Step (inc _ _) = ⊤
Step (inu _)   = ⊤
Step (ink _)   = ⊤

emb-up : (ℓ : L) (o : Ok ℓ) {k : L} (w : k ≤ ℓ) (y : Tr⁺ k) → Step w → IsUp (proj₁ (emb ℓ o w y))
emb-up ℓ             o self      y ()
emb-up (nd s h)      o (inc c v) y st = tt
emb-up (nd s h)      o (inu vs)  y st = tt
emb-up (nd (sΩ k) h) o (ink v)   y st = tt

emb∉read : (ℓ : L) (o : Ok ℓ) {k : L} (w : k ≤ ℓ) (y : Tr⁺ k) → Step w
  → (d : Read) → proj₁ (read ℓ d) ≡ proj₁ (emb ℓ o w y) → ⊥
emb∉read ℓ o w y st d e = read-not-up ℓ d (subst IsUp (sym e) (emb-up ℓ o w y st))

up-subst : ∀ {a b} (e : a ≡ b) (t : Tr⁺ a) → IsUp (proj₁ (subst Tr⁺ e t)) → IsUp (proj₁ t)
up-subst refl t u = u

∉dom : ∀ {k h} (S : Schema k h) c (y : Tr (h c)) → IsUp y → Domain S c y → ⊥
∉dom S c y u (d , e) = read-not-up (floor S ⊕ offsets S c) d
  (up-subst (sym (shape S c)) (read (floor S ⊕ offsets S c) d) (subst IsUp e u))
```
