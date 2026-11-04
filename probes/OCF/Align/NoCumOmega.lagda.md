# $\psi_0(\Omega_\Omega)$, 不累加

> 不含记号. 验收在 [NoCumAcceptOmega](NoCumAcceptOmega.lagda.md). 没有 `⊞`, 没有 `asuc` 补偿, 没有 `cumA`: 链点 $\eta_n\approx$ `rd` $y_n$ (`tie`), 字面合法. 折叠就是 [CumReadCF](CumReadCF.lagda.md) 的 `Y`, 它本来就不累加.
>
> **定义依赖证书**: `cell` 读 `Y-lit` 与 `Y-⊴`. 这两条都是对一切合法下标的定理 (与 `Uniform` 同类), 不与链互递归.
>
> 全文 `--safe --without-K --lossy-unification`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NoCumOmega where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁)
import OCF.Free.Level as FL
open FL using (HS; hl; s≅; z≅)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; Lg; O; o0; os; ol; oi; oe; Ω̇; ⊲-tr; z⊲; Strict)
import OCF.Align.CumReadCF as C
open import OCF.Align.CumReadCFEq using (Ω≈)
open import OCF.Align.CumReadCFThm using (_⊴_; rf; s; l; nd; eR; eL; Ω⊴; ψL; WF; ψW; ΩW; ord; ≈→≅; Y)
open import OCF.Align.NoCumLit

one : A
one = asuc azero

⊴→⊴₀ : {x y : O azero} → x ⊴ y → ord x ⊴₀ ord y
⊴→⊴₀ {x} {y} (rf e) = r0 (≈→≅ x y e)
⊴→⊴₀ (s d) = s0 (⊴→⊴₀ d)
⊴→⊴₀ (l n d) = l0 n (⊴→⊴₀ d)
⊴→⊴₀ (nd {r = ()} d)
⊴→⊴₀ (eR {R = ()} d)
⊴→⊴₀ (eL {R = ()} d)

Lit-ord : (x : O azero) → WF x → Lit₀ (ord x)
Lit-ord o0 u = tt
Lit-ord (os x) u = Lit-ord x u
Lit-ord (ol F) (st , u) = (λ n → ⊴→⊴₀ (st n)) , (λ n → Lit-ord (F n) (u n))
Lit-ord (oi () h) u
Lit-ord (oe () x) u

Y-lit : ∀ η (w : Lg η) → Lit₀ (Y η w)
Y-lit η w = Lit-ord _ (ψW (Ω̇ η) _ w tt (Ω≈ η) (ΩW η w))

Y-⊴ : ∀ {a b} (wa : Lg a) (wb : Lg b) → a ⊲ b → Y a wa ⊴₀ Y b wb
Y-⊴ wa wb p = ⊴→⊴₀ (ψL _ wa _ wb (Ω⊴ p))
```

## §1 链

`Cell`: 输出 $y$, 它的字面读出 $\eta$, 以及 $y\trianglelefteq Y_\eta$. 下一格: 输出 $Y_\eta$, 下标 $\eta'$ 是 $Y_\eta$ 的字面读出, 嫁接上 $\eta$ 作第一位置 (要 $y\trianglelefteq Y_\eta$).

```agda
record Cell : Set where
  field
    y    : Ord₀
    η    : A
    tie  : η ≈ᴬ rd y
    wη   : Lg η
    up   : one ⊲ η
    mono : y ⊴₀ Y η wη
open Cell public

one⊴ : FL.suc FL.zero ⊴₀ Y one tt
one⊴ = l0 0 (l0 1 (r0 (s≅ z≅)))

y₀ : Ord₀
y₀ = Y one tt

g₀ : Gr (rd y₀) one
g₀ = graft₀ one⊴ (lit y₀ (Y-lit one tt)) (el one (s≈ z≈) tt)

cell : ℕ → Cell
cell zero = record
  { y = y₀ ; η = g (gE g₀) ; tie = eq (gE g₀) ; wη = lg (gE g₀) ; up = at g₀
  ; mono = Y-⊴ tt (lg (gE g₀)) (at g₀) }
cell (suc n) = record
  { y = Y η₀ w₀ ; η = g (gE r) ; tie = eq (gE r) ; wη = lg (gE r) ; up = ⊲-tr (up c) (at r)
  ; mono = Y-⊴ w₀ (lg (gE r)) (at r) }
  where
  c = cell n
  η₀ = η c
  w₀ = wη c
  r : Gr (rd (Y η₀ w₀)) η₀
  r = graft₀ (mono c) (lit (Y η₀ w₀) (Y-lit η₀ w₀)) (el η₀ (tie c) w₀)

ys⁰ : ℕ → Ord₀
ys⁰ n = y (cell n)

T⁰ : Ord₀
T⁰ = FL.lim ys⁰

Lit-ys : ∀ n → Lit₀ (ys⁰ n)
Lit-ys zero = Y-lit one tt
Lit-ys (suc n) = Y-lit (η (cell n)) (wη (cell n))

Lit-T⁰ : Lit₀ T⁰
Lit-T⁰ = (λ n → mono (cell n)) , Lit-ys

HS-T⁰ : HS T⁰
HS-T⁰ = HS₀ T⁰ Lit-T⁰
```
