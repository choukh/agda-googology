# K2：第 0 层算子与由加法产生的坐标链

本篇只用原 `LevelFixCore`／`LevelFixVal`，不复制或修改块。
`R = Raw zero` 是第 0 层输出；`up zero` 将输出读回原 `LF`。
全 `Legal` 域的 gt 行能否启动，另在 [Stop](YiK2Stop.lagda.md) 检验。

## 四行的选择与义务

零行取字面 1；后继行取从零开始的 n 份复制的极限；ℕ 极限逐项折叠。
这三种写法沿用 `JiaExactFold` 模板，只参考其规则，不导入该模块。
`Raw zero` 另有形式的 `top`，其读回为 1，故按输入 1 的后继行计算。

拟用的 gt 行仍取 `lim (λ n → ψ (g γₙ))`；链改为
`γₙ₊₁ = γₙ + ψ (g γₙ)`。这里加法在右参数递归。
增长理由是每份 ψ 输出都带一条从 0 到它的严格第一位置路径；
固定左参数的加法把此路径变成从 γₙ 到下一点的路径。
不比较点、不识别相等或停顿。初项必须另有原 `Gd` 守卫；
这不是由增长定理自动提供的。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiK2Base where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.LevelFixCore as F
import OCF.Align.LevelFixVal as V
open F using (module G)

R : Set
R = F.Raw F.zero

one : R
one = G.suc G.zero

infixl 6 _+ʳ_
_+ʳ_ : R → R → R
x +ʳ G.zero = x
x +ʳ G.suc y = G.suc (x +ʳ y)
x +ʳ G.lim f = G.lim (λ n → x +ʳ f n)
x +ʳ G.lc () c t g
x +ʳ G.em () t
x +ʳ G.top = G.suc x

add-cp : ∀ x {a b} → F.Cp F.zero a b →
  F.Cp F.zero (x +ʳ a) (x +ʳ b)
add-dn : ∀ x {a} b → F.Dn F.zero a b →
  F.Dn F.zero (x +ʳ a) (x +ʳ b)
add-cp x (inj₁ refl) = inj₁ refl
add-cp x {b = b} (inj₂ p) = inj₂ (add-dn x b p)
add-dn x (G.suc b) p = add-cp x p
add-dn x (G.lim f) (n , p) = n , add-cp x p
add-dn x (G.lc () c t g) p
add-dn x (G.em () t) p
add-dn x G.top ()

add-legal : ∀ x y → F.Lgl F.zero x → F.Lgl F.zero y →
  F.Lgl F.zero (x +ʳ y)
add-legal x G.zero lx ly = lx
add-legal x (G.suc y) lx ly = add-legal x y lx ly
add-legal x (G.lim f) lx (st , lf) =
  (λ n → add-cp x (st n)) , (λ n → add-legal x (f n) lx (lf n))
add-legal x (G.lc () c t g) lx ly
add-legal x (G.em () t) lx ly
add-legal x G.top lx ly = lx

copies : R → ℕ → R
copies x zero = G.zero
copies x (suc n) = x +ʳ copies x n

successor : R → R
successor x = G.lim (copies x)

ψᶜ : R → R
ψᶜ G.zero = one
ψᶜ (G.suc x) = successor (ψᶜ x)
ψᶜ (G.lim f) = G.lim (λ n → ψᶜ (f n))
ψᶜ (G.lc () c t g)
ψᶜ (G.em () t)
ψᶜ G.top = successor one

positive : ∀ x → F.Dn F.zero G.zero (ψᶜ x)
positive G.zero = inj₁ refl
positive (G.suc x) = zero , inj₁ refl
positive (G.lim f) = zero , inj₂ (positive (f zero))
positive (G.lc () c t g)
positive (G.em () t)
positive G.top = zero , inj₁ refl

copies-step : ∀ x → F.Cp F.zero G.zero x → ∀ n →
  F.Cp F.zero (copies x n) (copies x (suc n))
copies-step x p zero = p
copies-step x p (suc n) = add-cp x (copies-step x p n)

copies-legal : ∀ x → F.Lgl F.zero x → ∀ n →
  F.Lgl F.zero (copies x n)
copies-legal x lx zero = tt
copies-legal x lx (suc n) = add-legal x (copies x n) lx (copies-legal x lx n)

ψᶜ-cp : ∀ {a b} → F.Cp F.zero a b → F.Cp F.zero (ψᶜ a) (ψᶜ b)
ψᶜ-dn : ∀ {a} b → F.Dn F.zero a b → F.Dn F.zero (ψᶜ a) (ψᶜ b)
ψᶜ-cp (inj₁ refl) = inj₁ refl
ψᶜ-cp {b = b} (inj₂ p) = inj₂ (ψᶜ-dn b p)
ψᶜ-dn (G.suc b) p = 1 , ψᶜ-cp p
ψᶜ-dn (G.lim f) (n , p) = n , ψᶜ-cp p
ψᶜ-dn (G.lc () c t g) p
ψᶜ-dn (G.em () t) p
ψᶜ-dn G.top ()

ψᶜ-legal : ∀ x → F.Lgl F.zero x → F.Lgl F.zero (ψᶜ x)
ψᶜ-legal G.zero lx = tt
ψᶜ-legal (G.suc x) lx =
  copies-step (ψᶜ x) (inj₂ (positive x)) , copies-legal (ψᶜ x) (ψᶜ-legal x lx)
ψᶜ-legal (G.lim f) (st , lf) =
  (λ n → ψᶜ-cp (st n)) , (λ n → ψᶜ-legal (f n) (lf n))
ψᶜ-legal (G.lc () c t g) lx
ψᶜ-legal (G.em () t) lx
ψᶜ-legal G.top lx = copies-step one (inj₂ (inj₁ refl)) , copies-legal one tt

ψᶜ-read-legal : ∀ x → F.Lgl F.zero x → V.Legal (V.up F.zero (ψᶜ x))
ψᶜ-read-legal x lx = V.lgl→Legal F.zero tt _ (ψᶜ-legal x lx)
```

## 给定可入初项后，链点由规则产生

`body` 的值在第 0 层；这覆盖根为 gt、分支带 Raw 0 证据的子问题。
下列合法性与单调性是显式的 Raw 0 充分前提，并非链增长的假设。
它们可经原 cp→CP／lgl→Legal 送到 LF；没有从任意 LF 源的 Legal 恢复它们的定理，
不能把读回后的 CP 与 Raw 的 Cp 混同。规范实例由原守卫直接填上这两条。
`next` 真正生成下一点及其守卫，`chain-grow` 的结论没有 `Grow` 前提。

```agda
Point : R → Set
Point c = Σ R (F.Gd F.zero c)

module Chain (c : R) (body : (η : R) → F.Gd F.zero c η → R)
  (lawful : ∀ η e → F.Lgl F.zero (body η e))
  (monotone : ∀ η e η′ e′ → F.Gd F.zero η η′ →
    F.Cp F.zero (body η e) (body η′ e′)) where

  out : Point c → R
  out (η , e) = ψᶜ (body η e)

  next : Point c → Point c
  next p@(η , e) =
    (η +ʳ out p) ,
    (F.Cp-tr F.zero (proj₁ e) (add-cp η (inj₂ (positive (body η e)))) ,
     add-legal η (out p) (proj₂ e) (ψᶜ-legal (body η e) (lawful η e)))

  grow : ∀ p → F.Dn F.zero (proj₁ p) (proj₁ (next p))
  grow p@(η , e) = add-dn η (out p) (positive (body η e))

  chain : Point c → ℕ → Point c
  chain start zero = start
  chain start (suc n) = next (chain start n)

  chain-grow : ∀ start n →
    F.Dn F.zero (proj₁ (chain start n)) (proj₁ (chain start (suc n)))
  chain-grow start n = grow (chain start n)

  collapse : Point c → R
  collapse start = G.lim (λ n → out (chain start n))

  collapse-legal : ∀ start → F.Lgl F.zero (collapse start)
  collapse-legal start =
    (λ n → ψᶜ-cp (monotone _ _ _ _
      (inj₂ (chain-grow start n) , proj₂ (proj₂ (chain start (suc n)))))) ,
    (λ n → ψᶜ-legal _ (lawful _ _))

  collapse-read-legal : ∀ start → V.Legal (V.up F.zero (collapse start))
  collapse-read-legal start = V.lgl→Legal F.zero tt _ (collapse-legal start)

id-body : (η : R) → F.Gd F.zero one η → R
id-body η e = η

canonical-source : F.LF
canonical-source = F.lc F.zero one (F.suc F.zero) (λ η e → V.up F.zero η)

canonical-is-Ω₁ : canonical-source ≡ V.Ω₁
canonical-is-Ω₁ = refl

canonical-source-legal : V.Legal canonical-source
canonical-source-legal = V.Legal-Ω̂ (F.suc F.zero) tt

module Canonical = Chain one id-body (λ η e → proj₂ e) (λ η e η′ e′ d → proj₁ d)

start : Point one
start = one , (inj₁ refl , tt)

closed : R
closed = Canonical.collapse start

closed-legal : F.Lgl F.zero closed
closed-legal = Canonical.collapse-legal start

closed-read-legal : V.Legal (V.up F.zero closed)
closed-read-legal = Canonical.collapse-read-legal start
```

`closed` 是规范 Ω₁ 的根折叠闭项，分支 `up zero η` 的子折叠为 `ψᶜ η`。
这没有实现任意嵌套 gt 的完整折叠；不能将局部 `Chain` 冒称完整 ψ。
全域初项义务的否定见 Stop；本闭项的值另在第 4 层验收。
