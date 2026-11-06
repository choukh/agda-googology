# NegFab6 (二): 层的代数里 `ext` 给的是倍数的上确界

> 不含记号. 入口 [NegFab6](NegFab6.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延. 只依赖 stdlib, `Fab6*`, `NegFab6Sim`.
>
> **这一篇证什么.** `Fab6Lay.ext L` 的新结点的分支是 `Ψ L` 作用在 `brL L c` 上, 而 `brL L c` 是同底折叠的输出. 同底折叠把外部结点当原子 (`NegFab6Sim.sim`), `Ψ L` 对外部结点是加上一个固定的树 (`ad`), 所以分支不超过这个树的 $P(c)$ 倍 (`Mult`), $P(c)$ 是普通塔的折叠. 这是 $\Omega_1$-树之间的关系 (`≼`), 不是序数读法; 读法的下调是判断 (入口 §5).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegFab6Lay where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.Fab6Base
open import OCF.Lean.Fab6Fold
open import OCF.Lean.Fab6 using (leg; Lg-leg)
open import OCF.Lean.Fab6Lay
open import OCF.Lean.NegFab6Sim
```

## §1 好的层

`Gd L`: 这一层的地板 `fl L` 与普通树 `b₀` 对齐 (只含允许的外部结点), 这一层的折叠 `Ψ L` 在第 0 层上逐构造子走, 允许的外部结点加上不超过 `A` 的树. `G`, `b₀`, `A` 都是数据.

```agda
record Gd (L : FL) : Set₁ where
  field
    G  : (x : KX (X L)) → ((y : EX (X L) x) → Br (X L) x y) → Set
    b₀ : Cd
    A  : HB X⊥ S₁
    sd : Ali.Sim {X L} G (Ali.rT {X L} G {S₁} hz) (fl L) b₀
    ψz : Ψ L hz hz ≼ hz
    ψs : ∀ h → Ψ L hz (hs h) ≼ hs (Ψ L hz h)
    ψl : ∀ f → Ψ L hz (hl f) ≼ hl (λ n → Ψ L hz (f n))
    ad : ∀ x p g → G x g → Ψ L hz (hE x p g) ≼ Ψ L hz p ⊞ A
open Gd
```

`Mult A v`: $A$ 的 $v$ 倍 (后继加一个 $A$, 外加 $1$ 盖住普通的后继). `brL L c`: `ext L` 的新结点坐标 $c$ 处交给 `Ψ L` 的树. `PL D c`: 普通塔上同样的折叠, 种子 `b₀`.

```agda
Mult : HB X⊥ S₁ → Cd → HB X⊥ S₁
Mult A hz = hz
Mult A (hs v) = hs (Mult A v) ⊞ A
Mult A (hl f) = hl (λ n → Mult A (f n))
Mult A (hΩ () _)
Mult A (hE () _ _)

Mult-⊲ : ∀ A {a b} → a ⊲ b → Mult A a ≼ Mult A b
Mult-⊲ A {a} hself = ≼-refl (Mult A a)
Mult-⊲ A {a} {hs b} (hsuc p) = ≼-tr (Mult-⊲ A p) (≼-tr (≼s (≼-refl (Mult A b))) (≼⊞l (hs (Mult A b)) A))
Mult-⊲ A (hlim n p) = ≼l n (Mult-⊲ A p)
Mult-⊲ A (hLim {κ = ()} _ _)
Mult-⊲ A (hEx {x = ()} _)

brL : (L : FL) → Cd → HB (X L) S₁
brL L c = Φ (leg c) (wf (leg c)) (Lg-leg c) hz (z⊲ᴮ (leg c)) (fl L) (topT (X L) S₁ (fl L) (leg c))

PL : Cd → Cd → Cd
PL b c = Φ {X⊥} {S⊥} (leg c) (wf (leg c)) (Lg-leg c) hz (z⊲ᴮ (leg c)) b (topT X⊥ S⊥ b (leg c))
```

## §2 分支不超过 `A` 的倍数

```agda
module _ {L : FL} (D : Gd L) where
  open Ali₂ {X L} (G D) using (Sim; zz; ss; ll; oo; es; el; rT; Sim-top)
  private module T = Thm {X L} (G D)

  Ψ≼ : ∀ {u v} → Sim (rT {S₁} hz) u v → Ψ L hz u ≼ Mult (A D) v
  Ψ≼ zz = ψz D
  Ψ≼ {hs u} {hs v} (ss p) = ≼-tr (ψs D u) (≼-tr (s≼s (Ψ≼ p)) (≼⊞l (hs (Mult (A D) v)) (A D)))
  Ψ≼ {hl f} (ll k) = ≼-tr (ψl D f) (l≼ (λ n → ≼l n (Ψ≼ (k n))))
  Ψ≼ (oo () _)
  Ψ≼ {hE x p g} {hs v} (es e q) =
    ≼-tr (ad D x p g e) (⊞-mono (≼s (Ψ≼ q)) (≼-refl (A D)))
  Ψ≼ {hE x p g} {hl w} (el e q gp) =
    ≼l 1 (≼-tr (ad D x p g e) (≼-tr (⊞-mono (≼s (Ψ≼ q)) (≼-refl (A D))) (Mult-⊲ (A D) (gp {tt}))))

  brL~ : ∀ c → Sim (rT {S₁} hz) (brL L c) (PL (b₀ D) c)
  brL~ c = T.sim (leg c) (wf (leg c)) (Lg-leg c) hz (z⊲ᴮ (leg c)) (sd D) (Sim-top (sd D) (leg c))

  br≼ : ∀ c → Ψ L hz (brL L c) ≼ Mult (A D) (PL (b₀ D) c)
  br≼ c = Ψ≼ (brL~ c)

  fl≼ : Ψ L hz (fl L) ≼ Mult (A D) (b₀ D)
  fl≼ = Ψ≼ (sd D)
```

## §3 算子保持好性质

**`ext`**, 两种写法: 不知道 `L` 的好性质时 (比如 `L₀`, 它的地板是真的 $\Omega_1$-结点), `A` 取新结点本身; 知道时, `A` 取 "$\sup_c$ 旧 `A` 的 $P(c)$ 倍" (`Gd-ext`). 允许的外部结点只有新种类, 分支是塔的地板.

```agda
Gx : (L : FL) → (x : KX (extX L)) → ((y : EX (extX L) x) → Br (extX L) x y) → Set
Gx L (inj₁ x) g = ⊥
Gx L (inj₂ _) g = g ≡ topT (X L) S₁ (fl L)

node : (L : FL) → HB X⊥ S₁
node L = hΩ Ω₁ (λ c → Ψ L hz (brL L c))

Gd-ext′ : (L : FL) → Gd (ext L)
Gd-ext′ L = record
  { G = Gx L ; b₀ = hs hz ; A = node L
  ; sd = Ali.es refl Ali.zz
  ; ψz = z≼ ; ψs = λ h → ≼-refl _ ; ψl = λ f → ≼-refl _
  ; ad = ad′ }
  where
  ad′ : ∀ x p g → Gx L x g → Ψ (ext L) hz (hE x p g) ≼ Ψ (ext L) hz p ⊞ node L
  ad′ (inj₂ _) p g refl = ≼-refl _

sup× : (A : HB X⊥ S₁) → Cd → HB X⊥ S₁
sup× A b = hΩ Ω₁ (λ c → Mult A (PL b c))

Gd-ext : {L : FL} → (D : Gd L) → Gd (ext L)
Gd-ext {L} D = record
  { G = Gx L ; b₀ = hs hz ; A = sup× (A D) (b₀ D)
  ; sd = Ali.es refl Ali.zz
  ; ψz = z≼ ; ψs = λ h → ≼-refl _ ; ψl = λ f → ≼-refl _
  ; ad = ad′ }
  where
  ad′ : ∀ x p g → Gx L x g → Ψ (ext L) hz (hE x p g) ≼ Ψ (ext L) hz p ⊞ sup× (A D) (b₀ D)
  ad′ (inj₂ _) p g refl = ⊞-mono (≼-refl (Ψ (ext L) hz p)) (Ω≼Ω (br≼ D))
```

**定理 (`ext-mul`).** 对一切好的层 $L$: `ext L` 的地板经 `Ψ` 不超过 "$\sup_c$ `A` 的 $P(c)$ 倍" 加 $0$ 前缀.

```agda
ext-mul : {L : FL} (D : Gd L) → Ψ (ext L) hz (fl (ext L)) ≼ hz ⊞ sup× (A D) (b₀ D)
ext-mul {L} D = ad (Gd-ext D) (inj₂ tt) hz (topT (X L) S₁ (fl L)) refl
```

**`diag`**: 一个外部种类, 分支固定. 给各层地板的上界 `B`, `A` 取 `hΩ Ω₁ B`.

```agda
fls : (F : Cd → FL) → (y : Cd) → HB (X (F y)) S₁
fls F c = fl (F c)

Gd-diag : (F : Cd → FL) (B : Cd → HB X⊥ S₁) → (∀ c → Ψ (F c) hz (fl (F c)) ≼ B c) → Gd (diag F)
Gd-diag F B q = record
  { G = λ _ g → g ≡ fls F ; b₀ = hs hz ; A = hΩ Ω₁ B
  ; sd = Ali.es refl Ali.zz
  ; ψz = z≼ ; ψs = λ h → ≼-refl _ ; ψl = λ f → ≼-refl _
  ; ad = ad′ }
  where
  ad′ : ∀ x p g → g ≡ fls F → Ψ (diag F) hz (hE x p g) ≼ Ψ (diag F) hz p ⊞ hΩ Ω₁ B
  ad′ x p g refl = ⊞-mono (≼-refl (Ψ (diag F) hz p)) (Ω≼Ω q)
```

**`supL`**: 外部种类取和, `b₀` 与 `A` 都取部分和.

```agda
z⊞≼ : ∀ (x : HB X⊥ S₁) → hz ⊞ x ≼ x
z⊞≼ hz = z≼
z⊞≼ (hs x) = s≼s (z⊞≼ x)
z⊞≼ (hl f) = l≼ (λ n → ≼l n (z⊞≼ (f n)))
z⊞≼ (hΩ κ g) = Ω≼Ω (λ c → z⊞≼ (g c))
z⊞≼ (hE () _ _)

Σ≼ : (a : ℕ → HB X⊥ S₁) → ∀ n → a n ≼ Σ⁺ a n
Σ≼ a zero = ≼-refl (a 0)
Σ≼ a (suc n) = ≼⊞r (Σ⁺ a n) (a (suc n))

module _ (F : ℕ → FL) (D : ∀ n → Gd (F n)) where
  Gs : (x : KX (supX F)) → ((y : EX (supX F) x) → Br (supX F) x y) → Set
  Gs (n , x) g = G (D n) x g

  ιX~ : ∀ n {u v} → Ali.Sim {X (F n)} (G (D n)) (Ali.rT {X (F n)} (G (D n)) {S₁} hz) u v →
        Ali.Sim {supX F} Gs (Ali.rT {supX F} Gs {S₁} hz) (ιX F n u) v
  ιX~ n Ali.zz = Ali.zz
  ιX~ n (Ali.ss p) = Ali.ss (ιX~ n p)
  ιX~ n (Ali.ll k) = Ali.ll (λ m → ιX~ n (k m))
  ιX~ n (Ali.oo () _)
  ιX~ n (Ali.es g p) = Ali.es g (ιX~ n p)
  ιX~ n (Ali.el g p gp) = Ali.el g (ιX~ n p) gp

  Gd-sup : Gd (supL F)
  Gd-sup = record
    { G = Gs ; b₀ = hl (Σ⁺ (λ n → b₀ (D n))) ; A = hl As
    ; sd = Ali.ll (Ali.Sim-Σ {supX F} Gs (λ n → ιX~ n (sd (D n))))
    ; ψz = z≼ ; ψs = λ h → ≼-refl _ ; ψl = λ f → ≼-refl _
    ; ad = ad′ }
    where
    As : ℕ → HB X⊥ S₁
    As = Σ⁺ (λ n → A (D n))
    ad′ : ∀ x p g → Gs x g → Ψ (supL F) hz (hE x p g) ≼ Ψ (supL F) hz p ⊞ hl As
    ad′ (n , x) p g e = ⊞-mono (≼-refl (Ψ (supL F) hz p))
      (≼-tr (≼-tr (ad (D n) x hz g e) (≼-tr (⊞-mono (ψz (D n)) (≼-refl (A (D n)))) (z⊞≼ (A (D n)))))
            (≼l n (Σ≼ (λ m → A (D m)) n)))
```

## §4 闭项的层: 上界对一切站一条

`TΩΩ₂` 的层是 `pow L₀ 2 = ext (ext L₀)`; 一般的: `Pc c L one` 对一切层 `L`, 一切 $c$ 都好 (`ext`, `diag`, `supL` 各走一次). `Gd-pow`: $\mathrm{pow}\,L_0\,(c+1)$ 都好.

```agda
Gd-pow : ∀ c → Gd (pow L₀ (hs c))
Gd-pow hz = Gd-ext′ L₀
Gd-pow (hs c) = Gd-ext (Gd-pow c)
Gd-pow (hl f) = Gd-ext′ (pow L₀ (hl f))
Gd-pow (hΩ () _)
Gd-pow (hE () _ _)

Gd-Pc : ∀ c (L : FL) → Gd (Pc c L one)
Gd-Pc hz L = Gd-ext′ L
Gd-Pc (hs c) L = Gd-diag (Pc c L) (λ y → Ψ (Pc c L y) hz (fl (Pc c L y))) (λ y → ≼-refl _)
Gd-Pc (hl f) L = Gd-sup (λ n → Pc (f n) L one) (λ n → Gd-Pc (f n) L)
Gd-Pc (hΩ () _) L
Gd-Pc (hE () _ _) L
```

闭项的两个实例: `TΩΩ₂` 的层是 `ext (ext L₀)`, 地板经 `Ψ` 不超过 "$\sup_c$ `node L₀` 的 $P(c)$ 倍" (`TΩΩ₂-mul`). `TΩ^Ω` 的层是 `diag` 作用在 `Pc c L₀ one` 上, 地板经 `Ψ` 不超过 $\sup_c$ 各分量的 `A` 的 `b₀` 倍 (`TΩ^Ω-bd`). 右边都是 `HB X⊥ S₁` 上的树, 没有外部结点.

```agda
TΩΩ₂-mul : Ψ (pow L₀ (hs one)) hz (fl (pow L₀ (hs one))) ≼ hz ⊞ sup× (node L₀) (hs hz)
TΩΩ₂-mul = ext-mul (Gd-ext′ L₀)

FΩ^Ω : Cd → FL
FΩ^Ω c = Pc c L₀ one

BΩ^Ω : Cd → HB X⊥ S₁
BΩ^Ω c = Mult (A (Gd-Pc c L₀)) (b₀ (Gd-Pc c L₀))

TΩ^Ω-bd : Ψ (diag FΩ^Ω) hz (fl (diag FΩ^Ω)) ≼ hz ⊞ hΩ Ω₁ BΩ^Ω
TΩ^Ω-bd = ad (Gd-diag FΩ^Ω BΩ^Ω (λ c → fl≼ (Gd-Pc c L₀))) tt hz (fls FΩ^Ω) refl
```

这一篇到 $\Omega_1$-树为止: 最后一步 `Φ (hs hz) → hz` 对 `≼` 不单调 (`NegFab6.anti-out` 是同一现象), 所以没有推到 `Cd` 上的界.
