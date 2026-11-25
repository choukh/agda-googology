# YiIrrFold 底座：第 0 层算术、定义域与加法链

构造路的第一件。块是 [RR5IrrCore](RR5IrrCore.lagda.md)，接口是 [YiIrrIf](YiIrrIf.lagda.md)
的记录 `FoldRows`；折叠本身在 [YiIrrFold](YiIrrFold.lagda.md)。本篇没有折叠，只有三样：

1. 第 0 层的第一位置传递与加法引理。证明来源是 `LevelFixCore` §3 与 [YiK2Base](YiK2Base.lagda.md)，
   只取目标层 0 用到的那几条，逐行照搬，换了块。
2. 定义域 `Dom`。它比 `Only0 × Legal` 多一项 `Seed`，原因见 §2。
3. 加法链 `Chain`：链点带无关的守卫，下一点的守卫在无关位置里由加法引理造出。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiIrrFoldBase where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck using (raw0-Nested; tw)
open import OCF.Align.YiIrrIf
```

## 1 第 0 层的第一位置与加法

`Cp-tr₀`, `Dn-cp₀`, `lgl-cp₀`, `lgl-dn₀` 是 `LevelFixCore` §3 的 `Cp-tr`, `Dn-cp`, `lgl-cp`, `lgl-dn`
在层号 0 的那几行：第 0 层的值没有 Ω 结点与 `em`，`top` 之下没有第一位置。
`add-cp`, `add-dn`, `add-legal`, `copies-step`, `copies-legal` 照 `YiK2Base`，只换了块。
`LevelFixCore` §3 的一般层版本 (含 `cmpC`) 本轮没有搬：目标层 0 用不到。

```agda
Cp-tr₀ : ∀ {a b d} → Cp zero a b → Cp zero b d → Cp zero a d
Dn-cp₀ : ∀ {a b} d → Cp zero a b → Dn zero b d → Dn zero a d
Cp-tr₀ (inj₁ refl) q = q
Cp-tr₀ (inj₂ p) (inj₁ refl) = inj₂ p
Cp-tr₀ {d = d} (inj₂ p) (inj₂ q) = inj₂ (Dn-cp₀ d (inj₂ p) q)
Dn-cp₀ (G.suc d) p q = Cp-tr₀ p q
Dn-cp₀ (G.lim f) p (n , q) = n , Cp-tr₀ p q
Dn-cp₀ (G.lc () c t g) p q
Dn-cp₀ (G.em () T) p q
Dn-cp₀ G.top p ()

lgl-cp₀ : ∀ {a b} → Cp zero a b → Lgl zero b → Lgl zero a
lgl-dn₀ : ∀ {a} b → Dn zero a b → Lgl zero b → Lgl zero a
lgl-cp₀ (inj₁ refl) l = l
lgl-cp₀ {b = b} (inj₂ p) l = lgl-dn₀ b p l
lgl-dn₀ (G.suc b) p l = lgl-cp₀ p l
lgl-dn₀ (G.lim f) (n , p) (st , lf) = lgl-cp₀ p (lf n)
lgl-dn₀ (G.lc () c t g) p l
lgl-dn₀ (G.em () T) p l
lgl-dn₀ G.top () l

add-cp : ∀ x {a b} → Cp zero a b → Cp zero (x +ʳ a) (x +ʳ b)
add-dn : ∀ x {a} b → Dn zero a b → Dn zero (x +ʳ a) (x +ʳ b)
add-cp x (inj₁ refl) = inj₁ refl
add-cp x {b = b} (inj₂ p) = inj₂ (add-dn x b p)
add-dn x (G.suc b) p = add-cp x p
add-dn x (G.lim f) (n , p) = n , add-cp x p
add-dn x (G.lc () c t g) p
add-dn x (G.em () T) p
add-dn x G.top ()

add-legal : ∀ x y → Lgl zero x → Lgl zero y → Lgl zero (x +ʳ y)
add-legal x G.zero lx ly = lx
add-legal x (G.suc y) lx ly = add-legal x y lx ly
add-legal x (G.lim f) lx (st , lf) =
  (λ n → add-cp x (st n)) , (λ n → add-legal x (f n) lx (lf n))
add-legal x (G.lc () c t g) lx ly
add-legal x (G.em () T) lx ly
add-legal x G.top lx ly = lx

copies-step : ∀ x → Cp zero G.zero x → ∀ n →
  Cp zero (copies x n) (copies x (suc n))
copies-step x p zero = p
copies-step x p (suc n) = add-cp x (copies-step x p n)

copies-legal : ∀ x → Lgl zero x → ∀ n → Lgl zero (copies x n)
copies-legal x lx zero = tt
copies-legal x lx (suc n) = add-legal x (copies x n) lx (copies-legal x lx n)
```

## 2 定义域：`Only0 × Legal` 之外还要一份相关的起点证据

**先试的定义域是 `Only0 x × Legal x`，没有走通（判断，机制如下）。**
`Legal (lc k c w b t g)` 的三条关于分支的字段 (`tg`, `dir`, 分支合法) 都以一份*相关的*守卫
`e : Gd k c η` 为自变量：`CP t (g η e)` 这条路径是从 `e` 里的路径算出来的 (规范 Ω₁ 上是
`read0-cp η (proj₁ e)`)，所以这里的守卫不能改成无关参数。结点里存的 `w : Lgl k c` 是无关的，
证明 "输出合法" 与 "位置保持" 这两条*相关的*结论时不能拿它去造相关的守卫。检查器的原话
(最小实验：对树做模式匹配，把起点守卫写成 `inj₁ refl , w , b` 交给 `Legal` 的 `tg` 字段；
临时文件 `<实验目录>/exp/SeedExp.agda` 不进仓库)：

```text
SeedExp.agda:32.21-22: error: [VariableIsIrrelevant]
Variable w is declared irrelevant, so it cannot be used here
when checking that the expression w has type Lgl k c
```

下面两条说明缺的恰是下界合法性这一件：有任何一份相关的守卫，就有相关的 `Lgl 0 c`；反过来它给出起点守卫。
所以没有它时 `Legal` 的分支字段一条也用不上。另外两种写法 (无关定义；无关位置里用消去子) 同样被拒绝，
"`Only0 × Legal` 的树都有起点证据" 与一条把无关证明变回相关证明的原则等价；
两件事都在 [YiIrrFoldSeed](YiIrrFoldSeed.lagda.md)。

```agda
guard→low : ∀ {c η} → Gd zero c η → Lgl zero c
guard→low (p , l , _) = lgl-cp₀ p l

low→guard : ∀ {c} → Lgl zero c → Gd zero c c
low→guard {c} l = inj₁ refl , l , raw0-Nested c
```

于是把它加进证书。`Seed x`：沿后继、极限、分支走到的每个 Ω 结点，下界合法有一份相关的证明。
它不沿第一支 `t` 走：折叠不递归第一支。它在树外，是证书的一部分；折叠只在无关位置读证书。
旧块上的对应物是 `YiCarry.Carry` 里 `Lgl k c` 那一项；那里另带 `Reg` 与第一支的 `Carry`，这里都不带。

```agda
Seed : LF → Set
Seed zero = ⊤
Seed (suc x) = Seed x
Seed (lim f) = ∀ n → Seed (f n)
Seed (lc k c w b t g) =
  (Lgl k c × Nested k c) × (∀ η (e : Gd k c η) → Seed (g η e))

Dom : LF → Set
Dom x = Only0 x × Legal x × Seed x

dom-pred : ∀ x → Dom (suc x) → Dom x
dom-pred x d = d

dom-at : ∀ f → Dom (lim f) → ∀ n → Dom (f n)
dom-at f (o , (st , l) , s) n = o n , l n , s n

dom-branch : ∀ c .(w : Lgl zero c) .(b : Nested zero c) t
  (g : (η : R) → .(Gd zero c η) → LF) →
  Dom (lc zero c w b t g) → ∀ η (e : Gd zero c η) → Dom (g η e)
dom-branch c w b t g ((ot , og) , (lk , tg , dir , irr , lt , lg) , (s , sg)) η e =
  og η e , lg η e , sg η e

dom-seed : ∀ c .(w : Lgl zero c) .(b : Nested zero c) t
  (g : (η : R) → .(Gd zero c η) → LF) →
  Dom (lc zero c w b t g) → Gd zero c c
dom-seed c w b t g (o , l , (s , sg)) = inj₁ refl , s

dom-first : ∀ c .(w : Lgl zero c) .(b : Nested zero c) t
  (g : (η : R) → .(Gd zero c η) → LF) →
  Dom (lc zero c w b t g) → ∀ η (e : Gd zero c η) → CP t (g η e)
dom-first c w b t g (o , (lk , tg , dir , irr , lt , lg) , s) = tg

dom-directed : ∀ c .(w : Lgl zero c) .(b : Nested zero c) t
  (g : (η : R) → .(Gd zero c η) → LF) →
  Dom (lc zero c w b t g) →
  ∀ η (e : Gd zero c η) η′ (e′ : Gd zero c η′) → Gd zero η η′ →
  CP (g η e) (g η′ e′)
dom-directed c w b t g (o , (lk , tg , dir , irr , lt , lg) , s) = dir
```

规范的 Ω₁ 在定义域里。读回 `read0 η` 里没有 Ω 结点，`Seed` 对它是平凡的。

```agda
read0-seed : ∀ a → Seed (read0 a)
read0-seed G.zero = tt
read0-seed (G.suc a) = read0-seed a
read0-seed (G.lim f) = λ n → read0-seed (f n)
read0-seed (G.lc () c t g)
read0-seed (G.em () a)
read0-seed G.top = tt

read0-dom : ∀ a → Lgl zero a → Dom (read0 a)
read0-dom a l = read0-only a , read0-legal a l , read0-seed a

Ω₁-seed : Seed (tw 2)
Ω₁-seed = (tt , tt) , (λ η e → read0-seed η)

dom-Ω₁ : Dom (tw 2)
dom-Ω₁ = Ω₁-only , Ω₁-legal , Ω₁-seed
```

## 3 加法链

`body` 是链点处的子折叠。`lawful` 只在下一点的守卫里用，所以是无关的模块参数；
`positive` 给增长，要相关地用，但它的守卫参数是无关的 (折叠输出为正只看树的形状，不看证书)。
下一点是 `η +ʳ body η`，它的守卫在无关位置里造：下界到它的路径由正性经加法给出，合法性由加法保持。

```agda
module Chain (c : R) (body : (η : R) → .(Gd zero c η) → R)
  .(lawful : ∀ η (e : Gd zero c η) → Lgl zero (body η e))
  (positive : ∀ η .(e : Gd zero c η) → Dn zero G.zero (body η e)) where

  out : Point c → R
  out (point η e) = body η e

  next : Point c → Point c
  next (point η e) = point (η +ʳ body η e)
    (Cp-tr₀ (proj₁ e) (add-cp η (inj₂ (positive η e))) ,
     add-legal η (body η e) (proj₁ (proj₂ e)) (lawful η e) ,
     raw0-Nested (η +ʳ body η e))

  grow : ∀ p → Dn zero (coordinate p) (coordinate (next p))
  grow (point η e) = add-dn η (body η e) (positive η e)

  collapse : Point c → R
  collapse p = G.lim (λ n → out (iterate next p n))
```

链点的守卫是无关的，而 `Legal` 的字段要相关的守卫。证明里另造一列相关的守卫，
坐标就是定义里那条链的坐标 (不另起一条链)：起点用证书里的 `Lgl 0 c`，下一点照 `next` 的无关分量重写一遍。
`monotone` 是分支输出沿守卫的位置保持，由 `Legal.dir` 加折叠的位置保持给出。

```agda
module ChainLegal (c : R) (body : (η : R) → .(Gd zero c η) → R)
  (lawful : ∀ η (e : Gd zero c η) → Lgl zero (body η e))
  (positive : ∀ η .(e : Gd zero c η) → Dn zero G.zero (body η e))
  (monotone : ∀ η (e : Gd zero c η) η′ (e′ : Gd zero c η′) →
    Gd zero η η′ → Cp zero (body η e) (body η′ e′))
  (p₀ : Point c) (e₀ : Gd zero c (coordinate p₀)) where

  open Chain c body lawful positive

  points : ℕ → Point c
  points = iterate next p₀

  guards : ∀ n → Gd zero c (coordinate (points n))
  guards zero = e₀
  guards (suc n) =
    Cp-tr₀ (proj₁ (guards n)) (inj₂ (grow (points n))) ,
    add-legal (coordinate (points n)) (out (points n))
      (proj₁ (proj₂ (guards n))) (lawful (coordinate (points n)) (guards n)) ,
    raw0-Nested (coordinate (points (suc n)))

  step : ∀ n → Cp zero (out (points n)) (out (points (suc n)))
  step n = monotone (coordinate (points n)) (guards n)
    (coordinate (points (suc n))) (guards (suc n))
    (inj₂ (grow (points n)) , proj₂ (guards (suc n)))

  collapse-legal : Lgl zero (collapse p₀)
  collapse-legal = step , (λ n → lawful (coordinate (points n)) (guards n))
```
