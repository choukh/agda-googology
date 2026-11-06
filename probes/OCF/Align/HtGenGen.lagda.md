# 高度由回灌生成 (一): 一个下标就是一层

> 不含记号. 入口 [HtGen](HtGen.lagda.md). 差树的形态, 用 [SumOne](SumOne.lagda.md) 的折叠, **没有新构造子, 没有新的层种类**. 层就是字面合法的下标 $x:A$ (`SumOneTree` 的 `cnt x`). 下标只由两种方式产生:
>
> - **折叠的输出经 `sum` 回灌**: `Ψ x` 是层 $x$ 的 $\Omega_x$ 折叠到第 0 层的输出; `nx x = sum (x+1) Δ_{x+1}` 是把层 $x+1$ 的输出接在 $x+1$ 后面. 合法性是 `Lg-sum` 的一次调用, 第一位置是 `sum-fst`.
> - **ℕ-极限**: `Lim f x = lim_n f^n(x)`, 只要 $f$ 保合法且 $y\lhd f(y)$. 合法性由形状给出.
>
> 生成原则是一条: `Up 0 = nx`, `Up (k+1) y = Lim (Up k) (Up k y)`. 不按维数分情况, 不加字典序; 比较只用 `⊲` (字面第一位置), 在 `Run` 内部才用 `cmpF` (字面世界之下).
>
> 定义里没有 `HS`, `Goodᴺ`, `WF`, `ψW`, 没有证书参数.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtGenGen where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; Ωd; sum; sum-fst; Lg-sum; cnt)
open import OCF.Align.SumOneClosed using (Run; Step; St; st; zeroD; yc; accCn; Ig; T₀; Lg-T₀)
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; ⊲→≤)
```

## §1 一层的折叠

`ΔΩ x`: 层 $x$ 自己的 $\Omega_x$ (`Ωd`), 世界取 $x$, 折叠到第 0 层的差. 与 `SumOneClosed.ΨΩ`, `SumHtClosed.TΩ` 同一个写法, 只是层是任意的下标.

```agda
Act : ∀ {x} → Ig (cnt x) x
Act p lW′ _ Y = Step Y

ΔΩ : ∀ x → Lg x → D azero x
ΔΩ x lx = yc (Run (accCn x) (Ωd x C.self lx) C.self lx C.self Act n0 (st zeroD n0)) (inj₁ (z⊲ x)) tt

-- ψ₀(Ω_x), 读法是判断
Ψ : ∀ x → Lg x → A
Ψ x lx = sum azero (n1 ⨾ ΔΩ x lx)

Lg-Ψ : ∀ x (lx : Lg x) → Lg (Ψ x lx)
Lg-Ψ x lx = Lg-sum azero (n1 ⨾ ΔΩ x lx) tt
```

## §2 回灌一步

`nx x`: 层 $x+1$ 的输出接在 $x+1$ 后面. 与 `SumOne` 的部分和 $v_{n+1}=v_n+\Delta_n$ 同形 (那里 `step≈` 说部分和的值就是折叠, 第 4 层定理; 这里没有对应的定理).

```agda
nx : ∀ x → Lg x → A
nx x lx = sum (asuc x) (ΔΩ (asuc x) lx)

Lg-nx : ∀ x (lx : Lg x) → Lg (nx x lx)
Lg-nx x lx = Lg-sum (asuc x) (ΔΩ (asuc x) lx) lx

nx-fst : ∀ x (lx : Lg x) → asuc x ⊲ nx x lx
nx-fst x lx = sum-fst (asuc x) (ΔΩ (asuc x) lx)
```

## §3 生成原则

`Op`: 保合法, 往上走. `Lim`: 它的 ℕ-极限闭包. `Up k`: 第 $k$ 次闭包. 一条定义对一切 $k$.

```agda
record Op : Set where
  field
    f   : ∀ x → Lg x → A
    lf  : ∀ x (lx : Lg x) → Lg (f x lx)
    fst : ∀ x (lx : Lg x) → asuc x ⊲ f x lx
open Op public

it : Op → ∀ x → Lg x → ℕ → Σ A Lg
it F x lx zero = x , lx
it F x lx (suc n) = f F (proj₁ (it F x lx n)) (proj₂ (it F x lx n)) , lf F _ (proj₂ (it F x lx n))

it-st : ∀ F x lx n → proj₁ (it F x lx n) ⊲ proj₁ (it F x lx (suc n))
it-st F x lx n = ⊲-tr (C.suc C.self) (fst F _ (proj₂ (it F x lx n)))

Lim : Op → ∀ x → Lg x → A
Lim F x lx = alim (λ n → proj₁ (it F x lx n))

Lg-Lim : ∀ F x (lx : Lg x) → Lg (Lim F x lx)
Lg-Lim F x lx = it-st F x lx , (λ n → proj₂ (it F x lx n))

-- 下一级: 从 F y 起闭包
up : Op → Op
up F = record
  { f = λ y ly → Lim F (f F y ly) (lf F y ly)
  ; lf = λ y ly → Lg-Lim F (f F y ly) (lf F y ly)
  ; fst = λ y ly → C.lim 0 (fst F y ly) }

NX : Op
NX = record { f = nx ; lf = Lg-nx ; fst = nx-fst }

Up : ℕ → Op
Up zero = NX
Up (suc k) = up (Up k)

-- Up 的对角: 第 k 级取 k 次
dg : ∀ x → Lg x → ℕ → Σ A Lg
dg x lx zero = x , lx
dg x lx (suc k) = f (Up k) (proj₁ (dg x lx k)) (proj₂ (dg x lx k)) , lf (Up k) _ (proj₂ (dg x lx k))

Upω : ∀ x → Lg x → A
Upω x lx = alim (λ k → proj₁ (dg x lx k))

Lg-Upω : ∀ x (lx : Lg x) → Lg (Upω x lx)
Lg-Upω x lx = (λ k → ⊲-tr (C.suc C.self) (fst (Up k) _ (proj₂ (dg x lx k)))) , (λ k → proj₂ (dg x lx k))
```

## §4 严格

`asuc a ≤ b` 在布劳威尔树上是严格的 (`lt-irr`). 每一级都字面地往上走.

```agda
≤-suc⁻ : ∀ {a b} → asuc a ≤ b → a ≤ b
≤-suc⁻ (s≤ p) = ≤-trans p (⊲→≤ (C.suc C.self))
≤-suc⁻ (≤l n p) = ≤l n (≤-suc⁻ p)

lt-irr : ∀ a → ¬ (asuc a ≤ a)
lt-irr azero ()
lt-irr (asuc a) (s≤ p) = lt-irr a p
lt-irr (alim f) (≤l n p) = lt-irr (f n) (≤-trans (s≤ (≤l n (≤-refl (f n)))) p)

op-up : ∀ F x (lx : Lg x) → asuc x ≤ f F x lx
op-up F x lx = ⊲→≤ (fst F x lx)

op-strict : ∀ F x (lx : Lg x) → ¬ (f F x lx ≤ x)
op-strict F x lx p = lt-irr x (≤-trans (op-up F x lx) p)
```

## §5 闭项

都是闭项, 没有参数. 读法都是判断, 见 [HtGen](HtGen.lagda.md) 的判断一节: **按 EBO 的值, $\psi_0(\Omega_x)\le\psi_0(\Omega_\Omega)$ 对一切可数 $x$ 成立 (单调, $\Omega_x<\Omega_\Omega$)**, 所以 $\psi_0(\Omega_{\psi_0(\Omega_\Omega)})$ 这类读法不是 EBO 意义下更高的站.

```agda
-- ψ₀(Ω_Ω): SumOne 的顶层闭包
s₀ : A
s₀ = T₀

-- "ψ₀(Ω_{ψ₀(Ω_Ω)})": 回灌得到的下标作层
s₁ : A
s₁ = Ψ T₀ Lg-T₀

-- 回灌一步
s₂ : A
s₂ = nx T₀ Lg-T₀

-- 回灌的 ℕ-闭包, 第 1, 2 级, 对角
s₃ s₄ s₅ sω : A
s₃ = f (Up 1) T₀ Lg-T₀
s₄ = f (Up 2) T₀ Lg-T₀
s₅ = f (Up 3) T₀ Lg-T₀
sω = Upω T₀ Lg-T₀

-- 新层: 闭包的输出再作层
s₆ : A
s₆ = Ψ sω (Lg-Upω T₀ Lg-T₀)
```

## §6 每站严格增长

```agda
s₀<s₂ : asuc s₀ ≤ s₂
s₀<s₂ = op-up NX T₀ Lg-T₀

-- 第 k+1 级的第 0 项就是第 k 级
lvl : ∀ k x (lx : Lg x) → asuc (f (Up k) x lx) ≤ f (Up (suc k)) x lx
lvl k x lx = ≤l 1 (op-up (Up k) (f (Up k) x lx) (lf (Up k) x lx))

s₂<s₃ : asuc s₂ ≤ s₃
s₂<s₃ = lvl 0 T₀ Lg-T₀

s₃<s₄ : asuc s₃ ≤ s₄
s₃<s₄ = lvl 1 T₀ Lg-T₀

s₄<s₅ : asuc s₄ ≤ s₅
s₄<s₅ = lvl 2 T₀ Lg-T₀

-- 对角: 第 k+1 项是第 k 项上的第 k 级
dg-up : ∀ k → asuc (proj₁ (dg T₀ Lg-T₀ k)) ≤ sω
dg-up k = ≤l (suc k) (op-up (Up k) _ (proj₂ (dg T₀ Lg-T₀ k)))


```

## §7 下标类型没有顶

一条很浅的定理, 但它划出边界: 层若只是 $A$ 的元素, 读法 "层 $x$ 在层 $y$ 之下当且仅当 $x\le y$", 就没有一层在一切层之上. 所以 $\Omega_\Omega$ (`SumOne` 的 `top`) 不能是一个 $A$-层, 必须是另一种层; $\Omega_{\Omega+1}$ 起的下标同样. 这只否定 "用一个 $A$ 当 $\Omega_\Omega$ 的下标"; 不否定别的下标类型.

```agda
no-top : ∀ x → Lg x → Σ A λ y → Lg y × ¬ (y ≤ x)
no-top x lx = nx x lx , Lg-nx x lx , op-strict NX x lx
```
