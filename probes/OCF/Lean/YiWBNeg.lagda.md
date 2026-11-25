# 左边放宽不能给出前缀 2 的底前提
不读记号；编译否定：第 2 层上任何 `WS` 关系 (`Le` 的规则加左规则 `YiWBRel.Ω≼`, 分支关系任取, 只要在 `p₁` 上让两个零相关、在 `p₀` 上自反) 都不能把源前缀 2 的底分量 `YiOGSelf.source-next` 放在满足 `Dry` 的树之下 (`Neg.no-next`)；所以 `W`、`Wᴸ`、`Le` 形式的底前提对拉回分量满足 `Dry` 的一切目标底不成立 (`no-wbase-dry`, `no-lbase-dry`, `no-base-le`)，`W` 对齐到目标前缀 0、1 时无条件 (`no-wbase-two-at0/1`)，对齐到 2 时以 `Dry target-next` 为条件 (`no-wbase-two`)。
机制：第 2 层的树读到第 1 层的值 `ρ` (第 0 层槽位的结点取全部分支, 其余结点只取第一分支), 它沿这些关系单调 (`Mono.ρ-mono`)；源的分量读出无界的第 0 层槽位结点 (`left-ρ`)，满足 `Dry` 的树读出无 Ω 的值 (`dry→free`, `unbounded`)。配对：值序 `val left ≼ val right` 成立 (`val-left-right`)，用到右边第 1 层槽位结点的非首分支。
不否定值比较、ActualMissing、Offset、Cover，也不否定右边放宽的关系。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiWBNeg where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; subst₂; sym)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath using (self; inc; _≤_; _⊑_)
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiVRRel as R
import OCF.Lean.YiVRFold as RF
import OCF.Lean.YiVWVal as V
import OCF.Lean.YiOFLocal as C
import OCF.Lean.YiOFPath as OP
import OCF.Lean.YiOGState as St
import OCF.Lean.YiOGSelf as Self
import OCF.Lean.YiOGFold as Fold
open import OCF.Lean.YiWBRel
```

## 第 2 层读到第 1 层的值

第 2 层有两个槽位: `p₁` 在第 1 层 (分支是第 1 层的树), `p₀` 在第 0 层 (分支是第 0 层的树)。实际链的孩子 `C.g 1` 逐字是 `L2`。

```agda
L2 : L
L2 = nd sS (λ _ → L1)

two-is : C.g 1 ≡ L2
two-is = refl

p₁ p₀ : Pos L2
p₁ = inj₂ (tt , inj₁ tt)
p₀ = inj₂ (tt , inj₂ (inj₂ (tt , inj₁ tt)))

ρ : Tr L2 → V.V L1
ρ zero = V.zero
ρ (suc x) = V.suc (ρ x)
ρ (lim f a) = V.lim (λ n → ρ (f n))
ρ (Ω (inj₂ (tt , inj₁ tt)) g) = ρ (g zero)
ρ (Ω (inj₂ (tt , inj₂ (inj₂ (tt , inj₁ tt)))) g) = V.Ω s₀ (λ z → ρ (g z))
ρ (up x c y e) = V.suc (ρ x)
```

单调只要分支关系在 `p₁` 上让两个零相关、在 `p₀` 上自反; 孩子关系不用。隐式参数显式写出, 免得 `--lossy-unification` 把 `ρ` 当单射。

```agda
module Mono {RB : (p : Pos L2) → Br L2 p → Br L2 p → Set} {RD : (c : CH L2) → ChT L2 c → ChT L2 c → Set}
  (rz : RB p₁ zero zero) (rr : (z : Tr zero) → RB p₀ z z) where
  ρ-mono : ∀ {x y} → WS (Sig L2) RB RD x y → ρ x V.≼ ρ y
  ρ-mono z≼ = V.z≼
  ρ-mono (s≼s d) = V.s≼s (ρ-mono d)
  ρ-mono (≼s d) = V.≼-suc (ρ-mono d)
  ρ-mono (≼l n d) = V.≼l n (ρ-mono d)
  ρ-mono (l≼ h) = V.l≼ (λ n → ρ-mono (h n))
  ρ-mono (≼w {p = inj₂ (tt , inj₁ tt)} {g = g} d) = ρ-mono {y = g zero} d
  ρ-mono (≼w {p = inj₂ (tt , inj₂ (inj₂ (tt , inj₁ tt)))} d) = V.≼Ω zero (ρ-mono d)
  ρ-mono (w≼w {p = inj₂ (tt , inj₁ tt)} {g = g} {g′ = g′} h) = ρ-mono {x = g zero} {y = g′ zero} (h zero zero rz)
  ρ-mono (w≼w {p = inj₂ (tt , inj₂ (inj₂ (tt , inj₁ tt)))} h) = V.Ω≼ (λ z → V.≼Ω z (ρ-mono (h z z (rr z))))
  ρ-mono (Ω≼ {p = inj₂ (tt , inj₁ tt)} {g = g} h) = ρ-mono {x = g zero} (h zero)
  ρ-mono (Ω≼ {p = inj₂ (tt , inj₂ (inj₂ (tt , inj₁ tt)))} h) = V.Ω≼ (λ z → ρ-mono (h z))
  ρ-mono (≼u d) = V.≼-suc (ρ-mono d)
  ρ-mono (u≼u dx dy) = V.s≼s (ρ-mono dx)
```

## 满足 Dry 的树读出无 Ω 的值, 无 Ω 的值被第 0 层的一棵树盖住

`≼⊹ʳ` 照 `YiLPNoBM.≼⊹ʳ` (旧块的值) 逐行搬来。

```agda
Free : V.V L1 → Set
Free V.zero = ⊤
Free (V.suc a) = Free a
Free (V.lim f) = (n : ℕ) → Free (f n)
Free (V.Ω p g) = ⊥

dry→free : (x : Tr L2) → Self.Dry L2 x → Free (ρ x)
dry→free zero d = tt
dry→free (suc x) d = dry→free x d
dry→free (lim f a) d = λ n → dry→free (f n) (d n)
dry→free (Ω (inj₂ (tt , inj₁ tt)) g) d = dry→free (g zero) (proj₂ d)
dry→free (Ω (inj₂ (tt , inj₂ (inj₂ (tt , inj₁ tt)))) g) (() , _)
dry→free (up x c y e) d = dry→free x (proj₁ d)

≼⊹ʳ : ∀ {ℓ} (a b : V.V ℓ) → b V.≼ a V.⊹ b
≼⊹ʳ a V.zero = V.z≼
≼⊹ʳ a (V.suc b) = V.s≼s (≼⊹ʳ a b)
≼⊹ʳ a (V.lim f) = V.l≼ (λ n → V.≼l n (≼⊹ʳ a (f n)))
≼⊹ʳ a (V.Ω p g) = V.Ω≼ (λ z → V.≼Ω z (≼⊹ʳ a (g z)))

cum-ge : (F : ℕ → Tr zero) (n : ℕ) → V.val zero (F n) V.≼ V.val zero (cum F n)
cum-ge F zero = V.≼-refl _
cum-ge F (suc n) = V.≼-trans (≼⊹ʳ (V.val zero (cum F n)) (V.val zero (F (suc n))))
  (proj₂ (V.val-+ (cum F n) (F (suc n))))

toZ : (b : V.V L1) → Free b → Tr zero
toZ V.zero _ = zero
toZ (V.suc b) fb = suc (toZ b fb)
toZ (V.lim f) fb = lim (cum (λ n → suc (toZ (f n) (fb n))))
  (λ n → +-mono (cum (λ n → suc (toZ (f n) (fb n))) n) (z◃ (toZ (f (suc n)) (fb (suc n))) ◃s))

b≼toZ : (b : V.V L1) (fb : Free b) → b V.≼ V.val zero (toZ b fb)
b≼toZ V.zero _ = V.z≼
b≼toZ (V.suc b) fb = V.s≼s (b≼toZ b fb)
b≼toZ (V.lim f) fb = V.l≼ (λ n → V.≼l n (V.≼-trans (V.≼-suc (b≼toZ (f n) (fb n)))
  (cum-ge (λ n → suc (toZ (f n) (fb n))) n)))

irr : (x : Tr zero) → V.suc (V.val zero x) V.≼ V.val zero x → ⊥
irr zero ()
irr (suc x) (V.s≼s d) = irr x d
irr (lim f a) (V.≼l n d) = irr (f n) (V.≼-trans (V.s≼s (V.≼l n (V.≼-refl _))) d)

unbounded : (b : V.V L1) → Free b → ((z : Tr zero) → V.val zero z V.≼ b) → ⊥
unbounded b fb h = irr (toZ b fb) (V.≼-trans (h (suc (toZ b fb))) (b≼toZ b fb))
```

## 源前缀 1 的输出读出无界的结点

`leftT` 逐字是 `YiOGSelf.left` (`left-form`): 第 0 层的 Ω 树经上折进第 2 层, 第 z 个分支读出不低于 z (`grow`)。

```agda
ρ-+ : (x y : Tr L2) → ρ x V.⊹ ρ y V.≼ ρ (x + y)
ρ-+ x zero = V.≼-refl _
ρ-+ x (suc y) = V.s≼s (ρ-+ x y)
ρ-+ x (lim f a) = V.l≼ (λ n → V.≼l n (ρ-+ x (f n)))
ρ-+ x (Ω (inj₂ (tt , inj₁ tt)) g) = ρ-+ x (g zero)
ρ-+ x (Ω (inj₂ (tt , inj₂ (inj₂ (tt , inj₁ tt)))) g) = V.Ω≼ (λ z → V.≼Ω z (ρ-+ x (g z)))
ρ-+ x (up y c w e) = V.s≼s (ρ-+ x y)

U : Tr zero → Tr⁺ L2
U z = Up zero (down (down stop tt) tt) (Ωt L2) z

v1 : V.V L1
v1 = V.suc V.zero

one≼ : (z : Tr zero) → v1 V.≼ ρ (proj₁ (U z))
one≼ zero = V.s≼s V.z≼
one≼ (suc z) = V.≼l 0 (one≼ z)
one≼ (lim f a) = V.≼l 0 (one≼ (f 0))

grow : (z : Tr zero) → V.val zero z V.≼ ρ (proj₁ (U z))
grow zero = V.z≼
grow (suc z) = V.≼l 1 (V.≼-trans (V.s≼s (grow z))
  (V.≼-trans (V.⊹-mono (ρ (proj₁ (U z))) (one≼ z)) (ρ-+ (proj₁ (U z)) (proj₁ (U z)))))
grow (lim f a) = V.l≼ (λ n → V.≼l n (grow (f n)))

leftT : Tr⁺ L2
leftT = Up L1 (down stop tt) (Ωt L2) (proj₁ (Ωt L1))

left-ρ : (b : V.V L1) → Free b → ρ (proj₁ leftT) V.≼ b → ⊥
left-ρ b fb d = unbounded b fb (λ z → V.≼-trans (grow z) (V.≼-trans (V.≼l 0 (V.≼-refl _)) (V.Ω⁻ z d)))

ρ-sn : ρ (proj₁ Self.source-carry) V.≼ ρ (proj₁ Self.source-next)
ρ-sn = V.≼l 0 (V.≼-refl _)
```

## 否定

对一切满足 `rz`、`rr` 的分支关系: 源前缀 2 的底分量 (及其中的 `left`) 不在任何满足 `Dry` 的树之下; 底的一般形式里关系族 `Rel` 任取, 只要它在第 2 层落进 `WS`。

```agda
module Neg {RB : (p : Pos L2) → Br L2 p → Br L2 p → Set} {RD : (c : CH L2) → ChT L2 c → ChT L2 c → Set}
  (rz : RB p₁ zero zero) (rr : (z : Tr zero) → RB p₀ z z) where
  open Mono {RB} {RD} rz rr

  no-left : (Y : Tr L2) → WS (Sig L2) RB RD (proj₁ Self.left) Y → Self.Dry L2 Y → ⊥
  no-left Y d dy = left-ρ (ρ Y) (dry→free Y dy)
    (subst (λ t → ρ (proj₁ t) V.≼ ρ Y) Self.left-form (ρ-mono d))

  no-next : (Y : Tr L2) → WS (Sig L2) RB RD (proj₁ Self.source-next) Y → Self.Dry L2 Y → ⊥
  no-next Y d dy = left-ρ (ρ Y) (dry→free Y dy)
    (subst (λ t → ρ (proj₁ t) V.≼ ρ Y) Self.left-form
      (subst (λ t → ρ (proj₁ t) V.≼ ρ Y) Self.source-carry-two (V.≼-trans ρ-sn (ρ-mono d))))

  no-base : (Rel : (j : L) → Tr j → Tr j → Set) → (∀ {x y} → Rel L2 x y → WS (Sig L2) RB RD x y)
    → ∀ {ℓ′} (v : C.g 2 ⊑ ℓ′) (B′ : F.Base ℓ′)
    → Self.Dry (C.g 1) (proj₁ (OP.pull-base v B′ (C.g 1) (inc tt self)))
    → ((j : L) (w : j ≤ C.g 2) → RF.Pr w → Rel j (proj₁ (St.G.base-at 2 j w)) (proj₁ (OP.pull-base v B′ j w)))
    → ⊥
  no-base Rel cv v B′ d hB = no-next _
    (cv (subst (λ x → Rel L2 (proj₁ x) (proj₁ (OP.pull-base v B′ (C.g 1) (inc tt self))))
      Self.source-query-two (hB (C.g 1) (inc tt self) tt))) d

module NW = Neg {RB = WB L2} {RD = WC L2} z≼ wrefl₀
module NL = Neg {RB = R.LB L2} {RD = WCᴸ L2} R.z≼ R.refl₀
```

`W` 形式的底前提 (`_⊴ᵂ_`, `RF._⊴_` 换成 `W`) 在三种对齐上的否定; `Wᴸ` 与 `Le` 同样由 `NL.no-base` 给出 (`no-lbase-dry`, `no-base-le`)。

```agda
infix 4 _⊴ᵂ_
_⊴ᵂ_ : ∀ {ℓ} → F.Base ℓ → F.Base ℓ → Set
_⊴ᵂ_ {ℓ} B B′ = (j : L) (w : j ≤ ℓ) → RF.Pr w → W j (proj₁ (B j w)) (proj₁ (B′ j w))

no-wbase-dry : ∀ {ℓ′} (v : C.g 2 ⊑ ℓ′) (B′ : F.Base ℓ′)
  → Self.Dry (C.g 1) (proj₁ (OP.pull-base v B′ (C.g 1) (inc tt self)))
  → St.G.base-at 2 ⊴ᵂ OP.pull-base v B′ → ⊥
no-wbase-dry = NW.no-base W (λ d → d)

no-lbase-dry : ∀ {ℓ′} (v : C.g 2 ⊑ ℓ′) (B′ : F.Base ℓ′)
  → Self.Dry (C.g 1) (proj₁ (OP.pull-base v B′ (C.g 1) (inc tt self)))
  → ((j : L) (w : j ≤ C.g 2) → RF.Pr w → Wᴸ j (proj₁ (St.G.base-at 2 j w)) (proj₁ (OP.pull-base v B′ j w))) → ⊥
no-lbase-dry = NL.no-base Wᴸ (λ d → d)

no-base-le : ∀ {ℓ′} (v : C.g 2 ⊑ ℓ′) (B′ : F.Base ℓ′)
  → Self.Dry (C.g 1) (proj₁ (OP.pull-base v B′ (C.g 1) (inc tt self)))
  → St.G.base-at 2 RF.⊴ OP.pull-base v B′ → ⊥
no-base-le = NL.no-base R.Le (le→wᴸ L2)

no-wbase-two-at0 : St.G.base-at 2 ⊴ᵂ OP.pull-base {b = C.h 0} self (St.T.base-at 0) → ⊥
no-wbase-two-at0 = no-wbase-dry self (St.T.base-at 0)
  (subst (λ x → Self.Dry (C.g 1) (proj₁ x)) (sym (St.target-base-first (C.g 1) (inc tt self))) Self.omega-two)

no-wbase-two-at1 : St.G.base-at 2 ⊴ᵂ OP.pull-base {b = C.h 1} (inc tt self) (St.T.base-at 1) → ⊥
no-wbase-two-at1 = no-wbase-dry (inc tt self) (St.T.base-at 1) Self.right-dry

v2 : C.g 2 ⊑ C.h 2
v2 = inc tt (inc tt self)

no-wbase-two : Self.Dry (C.g 1) (proj₁ Self.target-next) → St.G.base-at 2 ⊴ᵂ OP.pull-base v2 (St.T.base-at 2) → ⊥
no-wbase-two dt = no-wbase-dry v2 (St.T.base-at 2)
  (subst (λ x → Self.Dry (C.g 1) (proj₁ x)) (sym Self.target-query-two) dt)

no-carry-w : W L2 (proj₁ Self.source-carry) (proj₁ Self.target-carry) → ⊥
no-carry-w d = NW.no-left _ (subst (λ x → W L2 (proj₁ x) (proj₁ Self.target-carry)) Self.source-carry-two d)
  (subst (λ x → Self.Dry L2 (proj₁ x)) (sym Self.target-carry-two) Self.right-dry)
```

## 配对: 值序成立

`right` 的第 1 个累计支里, `ψ_self(Ωt₂, Ωt₂)` 是第 1 层槽位的结点, 它在分支 `Ωt L1` (非首分支) 处逐字含 `left`。`tick` 在 `YiOGSelf.High` 里不透明, 这里只展开它在零处的一步。

```agda
opaque
  unfolding Self.Hi.tick
  tick-zero : Self.Hi.tick zero ≡ proj₁ (next⁺ (Ωt L2))
  tick-zero = refl

Pc : Tr L2 → Tr⁺ L2
Pc c = next⁺ (Fold.ψ L2 Self.Hi.oa (F.B₀ L2) L2 self (Ωt L2) c)

val-left-P : V.val L2 (proj₁ leftT) V.≼ V.val L2 (proj₁ (Pc (proj₁ (next⁺ (Ωt L2)))))
val-left-P = V.≼l 0 (V.≼l 0 (V.≼Ω (proj₁ (Ωt L1)) (V.≼l 0 (V.≼-refl _))))

val-left-right : V.val L2 (proj₁ Self.left) V.≼ V.val L2 (proj₁ Self.right)
val-left-right = subst₂ (λ x y → V.val L2 (proj₁ x) V.≼ V.val L2 (proj₁ y)) (sym Self.left-form) (sym Self.right-form)
  (subst (λ t → V.val L2 (proj₁ leftT) V.≼ V.val L2 t) (sym Self.Hi.value-row)
    (V.≼l 1 (V.≼-trans (subst (λ t → V.val L2 (proj₁ leftT) V.≼ V.val L2 (proj₁ (Pc t))) (sym tick-zero) val-left-P)
      (V.≼-trans (≼⊹ʳ (V.val L2 (proj₁ (Self.Hi.piece 0))) (V.val L2 (proj₁ (Self.Hi.piece 1))))
        (proj₂ (V.val-+ (proj₁ (Self.Hi.piece 0)) (proj₁ (Self.Hi.piece 1))))))))
```
