# 加了嵌入码之后码域仍不含的三类块
编译否定，不读记号：(1) 上折的输出不是任何码的读出（`no-up-code⁺`，任意 `a ⊕ b ≡ two` 的分解；`up∉`：不在任何以 `two` 为孩子层的 `Domain⁺` 里）；(2) 偏移为零处只有旧码，沿非平凡路径嵌入进地板的树不是码（`floor-emb∉`）；(3) Ω 结点第一分支的块不是 Ω 树那一个的树不是码（`odd∉`，带任意分支函数的块的最小例）。
另有两条行的形状（`refl`）：后继形状层的 Ω 树槽位只在自身目标下保留（`sS-keep`、`sS-keepᵘ`），自身目标的嵌入行是上折、不进 `seen`（`self-row`）。
不否定什么：不否定值，不说这三类块在折叠里到达 `seen`（到达与否是判断，见 `YiEMChain` 文首）。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiEMNeg where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; nothing)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; kp)
open import OCF.Lean.YiBSBase
import OCF.Lean.YiBSFold as BS
open import OCF.Lean.YiBSRead using (Read; omega; next; plus; limit; read)
open import OCF.Lean.YiBSUpNeg using (two; mark; mark-read; lifted; lifted-mark)
open import OCF.Lean.YiBCNeg using (IsUp; read-not-up; emb-up; Step)
open import OCF.Lean.YiEMRead
```

## (1) 上折的输出

`YiBSUpNeg` 的标记对旧码为假；嵌入码读出的树顶是嵌入，标记也为假。

```agda
m-old : ∀ {ℓ} (e : ℓ ≡ two) (d : Read) → mark (proj₁ (subst Tr⁺ e (read ℓ d))) ≡ false
m-old refl d = mark-read d

m-up : ∀ {ℓ} (e : ℓ ≡ two) (t : Tr⁺ ℓ) → IsUp (proj₁ t) → mark (proj₁ (subst Tr⁺ e t)) ≡ false
m-up refl (up _ _ _ _ , _) _ = refl
m-up refl (zero    , _) ()
m-up refl (suc _   , _) ()
m-up refl (lim _ _ , _) ()
m-up refl (Ω _ _   , _) ()

mark-code : (a b : L) (e : a ⊕ b ≡ two) (d : Read⁺ b) → mark (proj₁ (subst Tr⁺ e (read⁺ a d))) ≡ false
mark-code a b e (old d)  = m-old e d
mark-code a _ e (em c d) = m-up e (upz c (read⁺ a d)) tt

no-up-code⁺ : (a b : L) (e : a ⊕ b ≡ two) (d : Read⁺ b) → proj₁ (subst Tr⁺ e (read⁺ a d)) ≡ proj₁ lifted → ⊥
no-up-code⁺ a b e d eq with trans (sym (mark-code a b e d)) (trans (cong mark eq) lifted-mark)
... | ()

sub-tr : ∀ {x y z : L} (e₁ : x ≡ y) (e₂ : y ≡ z) (t : Tr⁺ x) → subst Tr e₂ (proj₁ (subst Tr⁺ e₁ t)) ≡ proj₁ (subst Tr⁺ (trans e₁ e₂) t)
sub-tr refl refl t = refl

up∉ : ∀ {k} {h : Tr k → L} (S : Schema k h) (c : Tr k) (e : h c ≡ two) (y : Tr (h c))
  → subst Tr e y ≡ proj₁ lifted → Domain⁺ S c y → ⊥
up∉ S c e y q (d , r) = no-up-code⁺ (floor S) (offsets S c) (trans (sym (shape S c)) e) d
  (trans (sym (sub-tr (sym (shape S c)) e (read⁺ (floor S) d))) (trans (cong (subst Tr e) (sym r)) q))
```

## (2) 嵌入进地板

```agda
old-only : (d : Read⁺ zero) → Σ Read λ d′ → d ≡ old d′
old-only (old d) = d , refl

zero-not-up : (a : L) (d : Read⁺ zero) → IsUp (proj₁ (read⁺ a d)) → ⊥
zero-not-up a (old d) = read-not-up a d

floor-emb∉ : (a : L) (o : Ok a) {k : L} (w : k ≤ a) (y : Tr⁺ k) → Step w
  → (d : Read⁺ zero) → proj₁ (read⁺ a d) ≡ proj₁ (emb a o w y) → ⊥
floor-emb∉ a o w y st d eq = zero-not-up a d (subst IsUp (sym eq) (emb-up a o w y st))
```

## (3) 第一分支的块不是 Ω 树那一个

第 1 层（后继形状，唯一槽位是第 0 层）上，码读出的 Ω 结点第 0 支都是 `up _ tt (suc zero) _`（`Good`）；加法保持（`good-plus`，要右项非零 `lt-nz`）。`odd` 的第 0 支块是 `suc (suc zero)`。

```agda
one : L
one = nd sS (λ _ → zero)

data S1 : Tr one → Set where
  s1 : ∀ x e → S1 (up x tt (suc zero) e)

Good : Tr one → Set
Good (Ω (inj₂ (tt , inj₁ _)) g) = S1 (g zero)
Good (Ω (inj₂ (tt , inj₂ ())) g)
Good (Ω (inj₁ ()) g)
Good zero         = ⊤
Good (suc _)      = ⊤
Good (lim _ _)    = ⊤
Good (up _ _ _ _) = ⊤

NZ : ∀ {S} → T S → Set
NZ zero         = ⊥
NZ (suc _)      = ⊤
NZ (lim _ _)    = ⊤
NZ (Ω _ _)      = ⊤
NZ (up _ _ _ _) = ⊤

lt-nz : ∀ {S x y} → Lt S x y → NZ y
lt-nz ◃s            = tt
lt-nz (◃l n)        = tt
lt-nz ◃w            = tt
lt-nz (◃u x c y e)  = tt
lt-nz (◃c x c d)    = tt
lt-nz (◃t d e)      = lt-nz e

s1-plus : (x : Tr one) {t : Tr one} → S1 t → S1 (x + t)
s1-plus x (s1 y e) = s1 (x + y) e

good-plus : (x y : Tr one) → Good y → NZ y → Good (x + y)
good-plus x zero          gy ()
good-plus x (suc y)       gy nz = tt
good-plus x (lim f a)     gy nz = tt
good-plus x (Ω (inj₂ (tt , inj₁ _)) g) gy nz = s1-plus x gy
good-plus x (Ω (inj₂ (tt , inj₂ ())) g) gy nz
good-plus x (Ω (inj₁ ()) g) gy nz
good-plus x (up y c w e)  gy nz = tt

read-good : (d : Read) → Good (proj₁ (read one d))
read-good omega      = s1 zero (z◃ zero ◃s)
read-good (next d)   = tt
read-good (plus d e) = good-plus (proj₁ (read one d)) (proj₁ (read one e)) (read-good e) (lt-nz (proj₂ (read one e)))
read-good (limit f)  = tt

g-old : ∀ {ℓ} (e : ℓ ≡ one) (d : Read) → Good (proj₁ (subst Tr⁺ e (read ℓ d)))
g-old refl d = read-good d

g-up : ∀ {ℓ} (e : ℓ ≡ one) (t : Tr⁺ ℓ) → IsUp (proj₁ t) → Good (proj₁ (subst Tr⁺ e t))
g-up refl (up _ _ _ _ , _) _ = tt
g-up refl (zero    , _) ()
g-up refl (suc _   , _) ()
g-up refl (lim _ _ , _) ()
g-up refl (Ω _ _   , _) ()

code-good : (a b : L) (e : a ⊕ b ≡ one) (d : Read⁺ b) → Good (proj₁ (subst Tr⁺ e (read⁺ a d)))
code-good a b e (old d)  = g-old e d
code-good a _ e (em c d) = g-up e (upz c (read⁺ a d)) tt

odd : Tr one
odd = Ω (inj₂ (tt , inj₁ tt)) (λ c → up zero tt (suc (suc c)) (z◃ (suc c) ◃s))

odd-bad : Good odd → ⊥
odd-bad ()

odd∉ : (a b : L) (e : a ⊕ b ≡ one) (d : Read⁺ b) → proj₁ (subst Tr⁺ e (read⁺ a d)) ≡ odd → ⊥
odd∉ a b e d eq = odd-bad (subst Good eq (code-good a b e d))
```

## 行的形状：保留分支的变量块只在自身目标下折

后继形状层的 Ω 树（`Ωt (nd sS h)`）的槽位就是孩子层自身，目标经孩子或经 `inu` 时不保留；保留只在目标是自身时，那里的嵌入行是上折。

```agda
sS-keep : (h : ⊤ → L) (o : Ok (nd sS h)) {j : L} (v : j ≤ h tt)
  → kp (nd sS h) o (inj₂ (tt , inj₁ tt)) (inc tt v) ≡ nothing
sS-keep h o v = refl

sS-keepᵘ : (h : ⊤ → L) (o : Ok (nd sS h)) {j : L} (vs : (c : ⊤) → j ≤ h c)
  → kp (nd sS h) o (inj₂ (tt , inj₁ tt)) (inu vs) ≡ nothing
sS-keepᵘ h o vs = refl

self-row : (s : Sh) (h : Ch s → L) (o : Ok (nd s h)) (r : Rb (nd s h)) (B : Base (nd s h)) (β : Tr⁺ (nd s h))
  (x : Tr (nd s h)) (c : Ch s) (y : Tr (h c)) (e : h c ⊢ zero ◃ y)
  → BS.ψ (nd s h) o r B (nd s h) self β (up x c y e) ≡ Up (h c) (down stop c) (BS.ψ (nd s h) o r B (nd s h) self β x) y
self-row s h o r B β x c y e = refl
```

前提可满足：`two`、`one` 都有分解（`two₀`、`one₀`），沿非平凡路径的嵌入有实例（`step₁`）。

```agda
two₀ : zero ⊕ two ≡ two
two₀ = refl

one₀ : zero ⊕ one ≡ one
one₀ = refl

step₁ : Step {b = true} {j = zero} {ℓ = one} (inc tt self)
step₁ = tt
```
