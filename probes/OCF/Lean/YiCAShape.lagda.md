# 第 2 个链点的孩子层号：形状与字面路径的否定
不读记号；编译定理与编译否定：源第 2 链点是源前缀的 ℕ 极限（`two-lim`），其孩子层号含后继结点 `S1 (G ω)`（`sl-two`），槽位层号还嵌套（`S1 (G (ω+ω))` 也在其中，`G (ω+ω)` 又含 `S1 (G ω)`：`sl-nest`、`sl-inner`）；`G ω` 不是目标颈结点任一子层号的子层号（`no-neck`、`no-under`）。
取 g n = G (p n)、h n = shift (p n) 时 `YiPTChain.Chain` 的前提 `tg`、`eh`、`Hg` 不成立（`no-tow`、`no-eh`、`no-adj`），第 1 链点所用的首支事实也不成立（`no-first`）；对照：有限塔 `G (nat k)` 落在目标孩子层号里（`tower-in`，第 1 链点孩子层号的各支是这种，`YiPTAll.tg`）。
不否定 `ChainAdvance 2`、`Cover` 或别的证法（如跨孩子层的值关系，台账 V120）；只否定在公共层号上比较（`YiPTLadder.E`、`climb` 的做法）所需的字面路径。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCAShape where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps using (c₀; _+_)
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiTBRow using (nat)
import OCF.Lean.YiTZSmall as Small
import OCF.Lean.YiTZLocal as T
import OCF.Lean.YiTQChain as Q
import OCF.Lean.YiTNLocal as NL
import OCF.Lean.YiTNRow as R
import OCF.Lean.YiOGState as St
open import OCF.Lean.YiPTLadder using (S1; S2)
open import OCF.Lean.YiPTTow using (Tow; Adj)
open import OCF.Lean.YiPTAll using (shift-nat)
```

## 形状判别

```agda
G : Tr zero → L
G = T.source-child

data K : Set where kz kS kL kΩ : K
kind : L → K
kind zero = kz
kind (nd sS _) = kS
kind (nd sL _) = kL
kind (nd (sΩ _) _) = kΩ

br0 : L → L
br0 (nd sL g) = g 0
br0 (nd sS h) = h tt
br0 _ = zero

data TK : Set where tz ts tl : TK
tkind : Tr zero → TK
tkind zero = tz
tkind (suc _) = ts
tkind (lim _ _) = tl

brZ : Tr zero → Tr zero
brZ (lim f _) = f 0
brZ (suc x) = x
brZ zero = zero
```

## 第 2 个链点与它的孩子层号

`p n` 是源前缀 n 的折叠输出；`sl-in` 的路径沿 `p 0` 的第 1、0、0、0 支到 `suc ω`，`sl-nest` 沿第 1、0、1、1、0 支到 `suc (ω + ω)`。

```agda
p : ℕ → Tr zero
p n = proj₁ (St.G.piece n)

two-lim : T.Source.chain 2 ≡ lim p St.G.adj
two-lim = trans NL.source-two (trans (sym St.A.source-wire) St.G.row)

child-two : G (T.Source.chain 2) ≡ nd sL (λ n → G (p n))
child-two = cong G two-lim

og₂ : Ok (nd sL (λ n → G (p n)))
og₂ = proj₂ (Ok-tw 1) (lim p St.G.adj)

opaque
  unfolding St.G.piece St.G.fold St.G.prefix St.G.part
  sl-in : S1 (G Q.omega) ⊑ G (p 0)
  sl-in = inc 1 (inc 0 (inc 0 (inc 0 self)))
  sl-nest : S1 (G (Q.omega + Q.omega)) ⊑ G (p 0)
  sl-nest = inc 1 (inc 0 (inc 1 (inc 1 (inc 0 self))))
  piece0-lim : tkind (p 0) ≡ tl
  piece0-lim = refl
  no-tow : ¬ Tow (G (p 0))
  no-tow ()
  no-eh : ¬ (R.shift (p 0) ≡ S2 (G (p 0)))
  no-eh e with cong kind e
  ... | ()
  no-adj : ¬ Adj (λ n → G (p n)) (proj₁ og₂)
  no-adj H with cong (λ q → kind (proj₁ q)) (H 0)
  ... | ()

sl-two : S1 (G Q.omega) ⊑ G (T.Source.chain 2)
sl-two = subst (λ X → S1 (G Q.omega) ⊑ X) (sym child-two) (inc 0 sl-in)

sl-inner : S1 (G Q.omega) ⊑ G (Q.omega + Q.omega)
sl-inner = inc 0 self
```

## 形如 two ⊕ Y 的层号不含 G ω

`sub⊕`：two ⊕ Y 的子层号或在 two 之内，或仍形如 two ⊕ Y′。

```agda
sub⊕ : (Y : L) {X : L} → X ⊑ (T.two ⊕ Y) → (X ⊑ T.two) ⊎ Σ L (λ Y′ → X ≡ T.two ⊕ Y′)
sub⊕ zero q = inj₁ q
sub⊕ (nd s h) self = inj₂ (nd s h , refl)
sub⊕ (nd s h) (inc c q) = sub⊕ (h c) q
sub⊕ (nd s h) (inu qs) = sub⊕ (h (c₀ s)) (qs (c₀ s))

no-zero : ∀ {g} → ¬ (nd sL g ⊑ zero)
no-zero ()
no-one : ∀ {g} → ¬ (nd sL g ⊑ Small.one)
no-one (inc _ q) = no-zero q
no-one (inu qs) = no-zero (qs tt)
no-two : ∀ {g} → ¬ (nd sL g ⊑ T.two)
no-two (inc _ q) = no-one q
no-two (inu qs) = no-one (qs tt)

nz⊕ : (Y : L) → ¬ (zero ≡ T.two ⊕ Y)
nz⊕ zero e with cong kind e
... | ()
nz⊕ (nd sS h) e with cong kind e
... | ()
nz⊕ (nd sL h) e with cong kind e
... | ()
nz⊕ (nd (sΩ k) h) e with cong kind e
... | ()

no1⊕ : (Y : L) → ¬ (Small.one ≡ T.two ⊕ Y)
no1⊕ zero e with cong kind (cong br0 e)
... | ()
no1⊕ (nd sS h) e = nz⊕ (h tt) (cong br0 e)
no1⊕ (nd sL h) e with cong kind e
... | ()
no1⊕ (nd (sΩ k) h) e with cong kind e
... | ()

no-form : (Y : L) → ¬ (G Q.omega ≡ T.two ⊕ Y)
no-form zero e with cong kind e
... | ()
no-form (nd sS h) e with cong kind e
... | ()
no-form (nd sL h) e = no1⊕ (h 0) (cong br0 e)
no-form (nd (sΩ k) h) e with cong kind e
... | ()

no-lit : (Y : L) → ¬ (G Q.omega ⊑ T.two ⊕ Y)
no-lit Y q with sub⊕ Y q
... | inj₁ r = no-two r
... | inj₂ (Y′ , e) = no-form Y′ e

no-child : (d : Tr zero) → ¬ (G Q.omega ⊑ T.child d)
no-child d = no-lit (zero ⊕ (zero ⊕ ↑ zero (suc d)))

no-shift : (d : Tr zero) → ¬ (G Q.omega ⊑ R.shift d)
no-shift d = no-lit (zero ⊕ (zero ⊕ ↑ zero d))

no-neck : ¬ (G Q.omega ⊑ T.neck)
no-neck (inc d q) = no-child d q
no-neck (inu qs) = no-child zero (qs zero)

no-under : {Z : L} → Z ⊑ T.neck → ¬ (G Q.omega ⊑ Z)
no-under q r = no-neck (r ∙ q)

tower-in : (k : ℕ) → G (nat k) ⊑ T.child (nat k)
tower-in k = inc tt (subst (λ X → G (nat k) ⊑ X) (sym (shift-nat k)) (inc tt (inc tt self)))
```

## 第 1 链点的首支事实不移到第 2 链点

第 1 链点上 `YiTNShift` 用的是 "目标第 1 链点的首支即源第 1 链点"（`YiTNShape.first`）。

```agda
opaque
  unfolding T.Canonical.Target.feed T.Canonical.Target.g
  t2-first : brZ (T.Canonical.Target.chain 2) ≡ Q.omega
  t2-first = refl

no-first : ¬ (T.Source.chain 2 ≡ brZ (T.Canonical.Target.chain 2))
no-first e with trans (sym piece0-lim)
  (cong (λ x → tkind (brZ x)) (trans (sym two-lim) (trans e t2-first)))
... | ()
```
