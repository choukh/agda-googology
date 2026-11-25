# 两层塌缩内的强临界序数

第四层。给定一份阶段参数，以它以下的原名作为常量，构造 Freund 定理 3.5 的带有限支撑塌缩。[实际返回与序型下界](W4PTOGamma.lagda.md)使用该定理的最小性。
两层都用同一本地标准形，所造的可数名有共同上界 $D_0D_2^20$。[列更新](EboPTOPadding.lagda.md) · [Freund，定义 1.3 与定理 3.5](https://arxiv.org/pdf/1906.07448)

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.EboPTOGamma where

open import Data.List.Base using ([]; _∷_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.EboLeanDef
open import OCF.Align.EboLeanBase
open import Survey.EboPTOPadding
open import Survey.EboPTOFinite using (nf-num; num-support)

Ω₁ = Ωt one
marker = D₁ Ω₁
one<two : one <ᵀ two
one<two = tl< []<

count< : ∀ {a u b ts} → Ctbl a → [] <ᵀ u → a <ᵀ (ψ u b ∷ ts)
count< c[] _ = []<
count< (c∷ _) l = hd< (lv< l)

history : ∀ {x q} → NF x → Ctbl x → x <ᵀ out q → GB [] x (high q)
history (n∷ (nψ _ _ g) h nt) (c∷ cs) (hd< (ar< l)) (gp (gh _)) = l
history (n∷ (nψ _ _ g) h nt) (c∷ cs) (hd< (ar< l)) (gp (gc _ z)) = <ᵀ-trans (g z) l
history (n∷ _ h nt) (c∷ cs) ord (gtl z) = history nt cs (<ᵀ-trans (tail< _ _ h nt) ord) z

Ω₁-support : ∀ {z} → InG [] z Ω₁ → z ≡ []
Ω₁-support (gp (gh _)) = refl
Ω₁-support (gp (gw _ g)) = num-support 1 g
Ω₁-support (gp (gc _ ()))
Ω₁-support (gtl ())

mark-support : ∀ {z u} → InGP u z marker → z ≤ᵀ Ω₁
mark-support (gh _) = inj₂ refl
mark-support {u = u} (gw _ g) rewrite num-support 1 (G-mono (Survey.EboPTOFinite.bottom u) g) = inj₁ []<
mark-support {u = u} (gc _ g) rewrite Ω₁-support (G-mono (Survey.EboPTOFinite.bottom u) g) = inj₁ []<

nf-marker : NFP marker
nf-marker = nψ (nf-num 1) (nf-Ω (nf-num 1)) λ g →
  let eq = Ω₁-support (G-mono (inj₁ []<) g) in elim eq
  where elim : ∀ {z} → z ≡ [] → z <ᵀ Ω₁
        elim refl = []<

record Atom (s : Stage) : Set where
  constructor atom
  field
    term : T
    nf : NF term
    cnt : Ctbl term
    fits : ∀ {q} → p s <ᵀ q → term <ᵀ out q
open Atom

record Code (s : Stage) : Set where
  constructor code
  field
    key : T
    normal-key : NF key
    small-key : key <ᵀ Ωt two
    head≤ : HdLe marker key
    at-one : GB one key key
    at-zero : ∀ {q} → p s <ᵀ q → GB [] key (high q)
open Code

code-atom : ∀ {s} → Atom s → Code s
code-atom x = code (term x) (nf x) (count< (cnt x) []<) (head (cnt x))
  (λ g → ⊥-elim (dark (nf x) (count< (cnt x) []<) g))
  (λ h → history (nf x) (cnt x) (fits x h))
  where
  head : ∀ {a} → Ctbl a → HdLe marker a
  head c[] = tt
  head (c∷ _) = inj₁ (lv< []<)

pair-code : ∀ {s} → Atom s → Atom s → Code s
pair-code x y = code raw sorted′ (hd< (lv< one<two)) (inj₁ (ar< (count< (cnt x) []<))) guard₁ guard₀
  where
  raw = D₁ (term x) ∷ term y
  tail-ok : ∀ {a} → Ctbl a → HdLe (D₁ (term x)) a
  tail-ok c[] = tt
  tail-ok (c∷ _) = inj₁ (lv< []<)
  sorted′ = n∷ (nψ (nf-num 1) (nf x) (λ g → ⊥-elim (dark (nf x) (count< (cnt x) []<) g)))
    (tail-ok (cnt y)) (nf y)
  guard₁ : GB one raw raw
  guard₁ (gp (gh _)) = count< (cnt x) []<
  guard₁ (gp (gw _ g)) = ⊥-elim (dark (nf-num 1) (hd< (lv< []<)) g)
  guard₁ (gp (gc _ g)) = ⊥-elim (dark (nf x) (count< (cnt x) []<) g)
  guard₁ (gtl g) = ⊥-elim (dark (nf y) (count< (cnt y) []<) g)
  guard₀ : ∀ {q} → _ <ᵀ q → GB [] raw (high q)
  guard₀ h (gp (gh _)) = count< (cnt x) []<
  guard₀ h (gp (gw _ g)) rewrite num-support 1 g = []<
  guard₀ h (gp (gc _ g)) = history (nf x) (cnt x) (fits x h) g
  guard₀ h (gtl g) = history (nf y) (cnt y) (fits y h) g

mark : ∀ {s} → Code s → Code s
mark c = code (marker ∷ key c) (n∷ nf-marker (head≤ c) (normal-key c))
  (hd< (lv< one<two)) (inj₂ refl) guard₁ guard₀
  where
  guard₁ : GB one (marker ∷ key c) (marker ∷ key c)
  guard₁ (gp g) = ≤-< (mark-support g) (hd< (ar< []<))
  guard₁ (gtl g) = <ᵀ-trans (at-one c g) (tail< _ _ (head≤ c) (normal-key c))
  guard₀ : ∀ {q} → _ <ᵀ q → GB [] (marker ∷ key c) (high q)
  guard₀ h (gp g) = ≤-< (mark-support g) (hd< (lv< one<two))
  guard₀ h (gtl g) = at-zero c h g

build : ∀ {s} (c : Code s) → Σ Stage λ t → Push (D₁ (key c)) (p s) (p t)
build {s} c = extend s (key c) (nψ (nf-num 1) (normal-key c) (at-one c)) guarded
  where
  guarded : ∀ {q} → p s <ᵀ q → ∀ {z} → InGP [] z (D₁ (key c)) → z <ᵀ high q
  guarded h (gh _) = low-high (small-key c)
  guarded h (gw _ g) rewrite num-support 1 g = []<
  guarded h (gc _ g) = at-zero c h g
```

两个二元行按行号、第一坐标、第二坐标依次比较。常量放在两行之后。构造中的最大值只在有限个本地参数上取。

```agda
record Join (a b : Stage) : Set where
  constructor join
  field
    biggest : Stage
    left≤ : p a ≤ᵀ p biggest
    right≤ : p b ≤ᵀ p biggest
    under : ∀ {q} → p a <ᵀ q → p b <ᵀ q → p biggest <ᵀ q
open Join

maximum : (a b : Stage) → Join a b
maximum a b with dec≤ (p a) (p b)
... | inj₁ h = join b h (inj₂ refl) (λ _ r → r)
... | inj₂ h = join a (inj₂ refl) (inj₁ h) (λ l _ → l)

data Row : Set where lower upper : Row
data Input (s : Stage) : Set where
  unitQ : Input s
  binQ : Row → Stage → Stage → Input s
  constQ : (x : T) → NF x → Ctbl x → x <ᵀ out (p s) → Input s

members : ∀ {s} → Input s → (T → Set) → Set
members (binQ i a b) f = f (p a) × f (p b)
members unitQ f = ⊤
members (constQ _ _ _ _) f = ⊤

record Pad {s : Stage} (v : Input s) : Set where
  constructor pad
  field
    base-stage : Stage
    seed≤ : p s ≤ᵀ p base-stage
    parts≤ : members v (_≤ᵀ p base-stage)
    bound : ∀ {q} → p s <ᵀ q → members v (_<ᵀ q) → p base-stage <ᵀ q
open Pad

prepare : ∀ {s} (v : Input s) → Pad v
prepare {s} unitQ = pad s (inj₂ refl) tt (λ h _ → h)
prepare {s} (constQ _ _ _ _) = pad s (inj₂ refl) tt (λ h _ → h)
prepare {s} (binQ i a b) = pad (biggest m) (left≤ m)
  (≤-trans′ (left≤ n) (right≤ m) , ≤-trans′ (right≤ n) (right≤ m))
  (λ h vv → under m h (under n (proj₁ vv) (proj₂ vv)))
  where
  n = maximum a b
  m = maximum s (biggest n)

as-atom : ∀ {r} (a : Stage) → p a ≤ᵀ p r → Atom r
as-atom a h = atom (out (p a)) (out-normal a) (c∷ c[]) (λ z → out< (≤-< h z))

row-key : Row → T → T
row-key lower w = w
row-key upper w = marker ∷ w

encode : ∀ {s} → Input s → T
encode unitQ = []
encode (binQ i a b) = row-key i (D₁ (out (p a)) ∷ out (p b))
encode (constQ x _ _ _) = marker ∷ marker ∷ x

zeroCode : ∀ {s} → Code s
zeroCode = code-atom (atom [] n[] c[] (λ _ → []<))

shell : ∀ {s r} (v : Input s) → p s ≤ᵀ p r → members v (_≤ᵀ p r) → Code r
shell unitQ _ _ = zeroCode
shell (binQ lower a b) _ (h , j) = pair-code (as-atom a h) (as-atom b j)
shell (binQ upper a b) _ (h , j) = mark (pair-code (as-atom a h) (as-atom b j))
shell (constQ x nx cx l) h _ = mark (mark (code-atom
  (atom x nx cx (λ z → <ᵀ-trans l (out< (≤-< h z))))))

shell-key : ∀ {s r} (v : Input s) (h : p s ≤ᵀ p r) (j : members v (_≤ᵀ p r)) →
  key (shell {r = r} v h j) ≡ encode v
shell-key unitQ _ _ = refl
shell-key (binQ lower _ _) _ (_ , _) = refl
shell-key (binQ upper _ _) _ (_ , _) = refl
shell-key (constQ _ _ _ _) _ _ = refl

result : ∀ {s} (v : Input s) → Σ Stage λ t →
  Push (D₁ (encode v)) (p (base-stage (prepare v))) (p t)
result v with prepare v
... | pad r h j b rewrite Relation.Binary.PropositionalEquality.sym (shell-key {r = r} v h j) =
  build {s = r} (shell v h j)

θ : ∀ {s} → Input s → Stage
θ v = proj₁ (result v)

seed-up : ∀ {s} (v : Input s) → p s <ᵀ p (θ v)
seed-up v = ≤-< (seed≤ (prepare v)) (rises (proj₂ (result v)))

support-up : ∀ {s} (v : Input s) → members v (_<ᵀ p (θ v))
support-up unitQ = tt
support-up (constQ _ _ _ _) = tt
support-up v@(binQ _ _ _) = ≤-< (proj₁ (parts≤ (prepare v))) h , ≤-< (proj₂ (parts≤ (prepare v))) h
  where h = rises (proj₂ (result v))

conditional-order : ∀ {s} (v w : Input s) → encode v <ᵀ encode w →
  members v (_<ᵀ p (θ w)) → p (θ v) <ᵀ p (θ w)
conditional-order v w h j = below (proj₂ (result v)) (floor (proj₂ (result w)))
  (ar< h) (bound (prepare v) (seed-up w) j)

capKey = marker ∷ marker ∷ marker ∷ []
capStage : Stage
capStage = proj₁ (build {s = emptyStage} (mark (mark (mark zeroCode))))

key-small : ∀ {s} (v : Input s) → encode v <ᵀ capKey
key-small unitQ = []<
key-small (binQ lower a b) = hd< (ar< (count< (c∷ c[]) []<))
key-small (binQ upper a b) = tl< (hd< (ar< (count< (c∷ c[]) []<)))
key-small (constQ _ _ cx _) = tl< (tl< (count< cx []<))

bounded : ∀ {s} (v : Input s) → p s <ᵀ p capStage →
  members v (_<ᵀ p capStage) → p (θ v) <ᵀ p capStage
bounded v h j = below (proj₂ (result v)) (more (inj₂ refl) nil) (ar< (key-small v)) (bound (prepare v) h j)

positive-seed : Stage
positive-seed = θ {s = emptyStage} unitQ

base<seed : out (p emptyStage) <ᵀ out (p positive-seed)
base<seed = out< (seed-up {s = emptyStage} unitQ)

seed<cap : p positive-seed <ᵀ p capStage
seed<cap = bounded {s = emptyStage} unitQ []< tt
```

```agda
row-strict : ∀ i {v w} → v <ᵀ w → row-key i v <ᵀ row-key i w
row-strict lower h = h
row-strict upper h = tl< h

pair-first : ∀ {s} i (a b a′ b′ : Stage) → p a <ᵀ p a′ →
  encode {s} (binQ i a b) <ᵀ encode (binQ {s} i a′ b′)
pair-first i a b a′ b′ h = row-strict i (hd< (ar< (out< h)))

pair-second : ∀ {s} i (a a′ b b′ : Stage) → p a ≡ p a′ → p b <ᵀ p b′ →
  encode {s} (binQ i a b) <ᵀ encode (binQ {s} i a′ b′)
pair-second i a a′ b b′ e h rewrite e = row-strict i (tl< (out< h))

record Constant (s : Stage) : Set where
  constructor constant
  field
    x : T
    n : NF x
    c : Ctbl x
    inside : x <ᵀ out (p s)
open Constant

old : ∀ {s} → Constant s → Input s
old w = constQ (x w) (n w) (c w) (inside w)

unit-bin : ∀ {s} i a b → encode (unitQ {s}) <ᵀ encode (binQ {s} i a b)
unit-bin lower _ _ = []<
unit-bin upper _ _ = []<

unit-const : ∀ {s} (w : Constant s) → encode (unitQ {s}) <ᵀ encode (old w)
unit-const _ = []<

lower-upper : ∀ {s} a b a′ b′ → encode (binQ {s} lower a b) <ᵀ encode (binQ {s} upper a′ b′)
lower-upper _ _ _ _ = hd< (ar< (count< (c∷ c[]) []<))

bin-const : ∀ {s} i a b (w : Constant s) → encode (binQ {s} i a b) <ᵀ encode (old w)
bin-const lower _ _ _ = hd< (ar< (count< (c∷ c[]) []<))
bin-const upper _ _ _ = tl< (hd< (ar< (count< (c∷ c[]) []<)))

const-order : ∀ {s} (w v : Constant s) → x w <ᵀ x v → encode (old w) <ᵀ encode (old v)
const-order _ _ h = tl< (tl< h)
```
