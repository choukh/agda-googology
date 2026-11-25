# YiIrrFold 的定义域：起点证据 `Seed` 从哪里来，能不能省

构造路的第四件。[YiIrrFoldBase](YiIrrFoldBase.lagda.md) 的定义域是 `Only0 × Legal × Seed`，
比先试的 `Only0 × Legal` 多一项。本篇只关于定义域，没有新的折叠，回答四个问题：

0. **在 `Only0 × Legal` 上试过哪些写法。** 五个，检查器都因无关性拒绝 (§0，实测，不是定理)。
1. **省掉 `Seed` 等价于什么。** "一切 `Only0 × Legal` 的树都有 `Seed`" 与 `Unsquash`
   (第 0 层的合法性可以从无关的证明变回相关的证明) 互相推出 (`seed-all→unsquash`, `unsquash→seed-all`)。
2. **有 `Unsquash` 时。** 接口在 `Only0 × Legal` 上实填，折叠是同一个 `ψ` (`Wide.wide-rows`，条件定理)。
3. **`Seed` 在规范塔上是不是空的要求。** 不是：把它写成对层号、第一支、分支都遗传的 `Seedᶠ`，
   它对 Ω 与读回封闭，一切层号，一步 (`seed-Ω̂`, `seed-up`)；塔 `tw n` 与 Λ 都满足 (`seed-tw`, `seed-Λ`)。

**关于 `Unsquash` 这个前提 (判断)。** 它在 Agda 里没有实例，也没有反驳。把无关标注全部擦掉的解释下它是恒等函数，
所以它与本仓库的选项相容；但第 0 层的 `Cp` 是和类型，极限处还要选下标，无关的证明里拿不出这份数据。
所以第 2 条只说明 "`Only0 × Legal` 上缺的只有这一件"，不是一个无条件的构造。
在 `Only0 × Legal` 上实填接口这件事，本轮未走通，没有否定定理。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiIrrFoldSeed where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck
open import OCF.Align.YiIrrIf
open import OCF.Align.YiIrrFoldBase
open import OCF.Align.YiIrrFold
```

## 0 在 `Only0 × Legal` 上试过的写法 (检查器实测)

要的东西是同一件：在 Ω 结点 `lc zero c w b t g` 处拿到起点守卫 `Gd 0 c c`，其中要一份 `Lgl 0 c`。
结点里有 `w : Lgl 0 c`，但它是无关的。试了三种直接的写法与一种绕道，临时文件在 `<实验目录>/exp/`，不进仓库。

1. *相关的引理里直接用 `w`* (`SeedExp.agda`)：对树做模式匹配，把 `inj₁ refl , w , b` 交给 `Legal` 的 `tg` 字段。
2. *无关定义* (`IrrDef.agda`)：名字前加点的定义 `.tree-seed : ∀ x → Seed x`，在定义体里读 `w`，
   打算只在 `ψ` 的无关位置调用它。检查器不在无关模式下检查无关定义的定义体。
3. *无关位置里现场用消去子* (`IrrElim.agda`)：写一个 `LF` 的消去子，Ω 结点那一支以无关的方式收到 `w`；
   在 `ψ` 的证书位置 (无关位置) 里用它，由 λ 绑定的 `w` 造 `Seed`。无关位置只放开已在上下文里的无关变量，
   位置里面新绑定的无关变量仍不能相关地用。

三次的报错原文相同，位置不同：

```text
SeedExp.agda:32.21-22: error: [VariableIsIrrelevant]
IrrDef.agda:19.31-32: error: [VariableIsIrrelevant]
IrrElim.agda:32.33-34: error: [VariableIsIrrelevant]
Variable w is declared irrelevant, so it cannot be used here
when checking that the expression w has type Lgl k c
```

4. *绕道：把结论压扁* (`Squash1.agda`, `Squash3.agda`)。若 "输出合法" 只以无关的方式被消费，可以把它的类型换成
   带无关字段的记录 `Squash (Lgl 0 …)`，定义体就整个落在无关位置里。但 gt 行与极限行要把可数个压扁的证明
   并成一个 (`(∀ n → Squash (P n)) → Squash (∀ n → P n)`)。用字段投影写，或在无关位置里做模式匹配写，都被拒绝：

```text
Squash1.agda:12.27-39: error: [ProjectionIsIrrelevant]
Projection  Squash.proof  is irrelevant.
Turn on option --irrelevant-projections to use it (unsafe)
when checking that the expression Squash.proof (f n) has type P n

Squash3.agda:16.60-61: error: [VariableIsIrrelevant]
Variable p is declared irrelevant, so it cannot be used here
when checking that the expression p has type P n
```

这些是五个具体写法的检查器事实，不是 "一切写法都不行" 的定理。读法 (判断)：
**结点里存的无关证明，只能原样转交给另一个无关位置 (分支的守卫，新结点的字段)；
要对一棵未知的树递归地把它们收集起来，在不开 `--irrelevant-projections` 的检查器里没有找到写法。**
`ψ` 的四行只做前一种事；证明 "输出合法" 与 "位置保持" 要后一种，于是证书里要一份树外的拷贝，就是 `Seed`。

## 1 省掉 `Seed` 等价于把无关的合法性变回相关的

探针 `probe c w`：下界是任意的 `c`，它的合法性 `w` 只以无关的方式给出；第一支与分支都是零。
它是退化结点 (常值分支)，只用来读出 "`Seed` 的根分量就是相关的 `Lgl 0 c`"；
它的 `Only0` 与 `Legal` 不需要相关的 `w`。所以这条等价说的是谓词 `Only0 × Legal` 的宽度，不是数学障碍。

```agda
Unsquash : Set
Unsquash = ∀ (c : R) → .(Lgl zero c) → Lgl zero c

SeedAll : Set
SeedAll = ∀ x → Only0 x → Legal x → Seed x

probe : (c : R) → .(Lgl zero c) → LF
probe c w = lc zero c w (raw0-Nested c) zero (λ η e → zero)

probe-only : ∀ c .(w : Lgl zero c) → Only0 (probe c w)
probe-only c w = tt , (λ η e → tt)

probe-legal : ∀ c .(w : Lgl zero c) → Legal (probe c w)
probe-legal c w =
  tt , (λ η e → self) , (λ η e η′ e′ q → self) , (λ η e e′ → refl) ,
  tt , (λ η e → tt)

seed-all→unsquash : SeedAll → Unsquash
seed-all→unsquash h c w =
  proj₁ (proj₁ (h (probe c w) (probe-only c w) (probe-legal c w)))

unsquash→seed : Unsquash → ∀ x → Only0 x → Seed x
unsquash→seed u zero o = tt
unsquash→seed u (suc x) o = unsquash→seed u x o
unsquash→seed u (lim f) o = λ n → unsquash→seed u (f n) (o n)
unsquash→seed u (lc zero c w b t g) (ot , og) =
  (u c w , raw0-Nested c) , (λ η e → unsquash→seed u (g η e) (og η e))
unsquash→seed u (lc (suc k) c w b t g) ()
unsquash→seed u (lc (lim f) c w b t g) ()
unsquash→seed u (lc (lc k c₀ w₀ b₀ t₀ g₀) c w b t g) ()

unsquash→seed-all : Unsquash → SeedAll
unsquash→seed-all u x o l = unsquash→seed u x o
```

## 2 条件定理：有 `Unsquash` 时，接口在 `Only0 × Legal` 上实填

折叠就是 [YiIrrFold](YiIrrFold.lagda.md) 的 `ψ`；证书在无关位置，行仍是 `refl`。

```agda
module Wide (unsquash : Unsquash) where

  Domʷ : LF → Set
  Domʷ x = Only0 x × Legal x

  widen : ∀ x → Domʷ x → Dom x
  widen x (o , l) = o , l , unsquash→seed unsquash x o

  wide-rows : FoldRows
  wide-rows = record
    { Dom = Domʷ
    ; dom-pred = λ x d → d
    ; dom-at = λ f d n → proj₁ d n , proj₂ (proj₂ d) n
    ; dom-branch = λ c w b t g d η e →
        proj₂ (proj₁ d) η e , proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ d))))) η e
    ; dom-only = λ x d → proj₁ d
    ; dom-legal = λ x d → proj₂ d
    ; dom-Ω₁ = Ω₁-only , Ω₁-legal
    ; ψ = λ x d → ψ x (widen x d)
    ; next = λ c w b t g d → next c w b t g (widen (lc zero c w b t g) d)
    ; zero-row = λ d → refl
    ; suc-row = λ x d → refl
    ; lim-row = λ f d → refl
    ; next-additive = λ c w b t g d p → refl
    ; next-grow = λ c w b t g d p →
        next-grow c w b t g (widen (lc zero c w b t g) d) p
    ; gt-row = λ c w b t g d → refl
    ; fold-legal = λ x d → ψ-legal x (widen x d)
    ; fold-positive = λ x d → ψ-positive x (widen x d)
    ; position = λ x y dx dy → ψ-position x y (widen x dx) (widen y dy)
    }
```

## 3 `Seed` 在规范塔上：对 Ω 与读回封闭，一切层号

`Seedᶠ` 与 `Legal` 同形地遗传 (层号 `k`，第一支 `t`，分支)。读回一个 Ω 结点时，
新结点的下界合法性来自坐标的嵌套证据 `Nested`；这里把它当相关的证明拿来，放进树外的 `Seedᶠ`，
树里存的仍是无关的那一份。证明照 `LevelFixVal` 的 `legalN`, `Legal-Ω̂`, `lgl→Legal` 的递归。

```agda
Seedᶠ : LF → Set
Seedᶠ zero = ⊤
Seedᶠ (suc x) = Seedᶠ x
Seedᶠ (lim f) = ∀ n → Seedᶠ (f n)
Seedᶠ (lc k c w b t g) =
  Seedᶠ k × (Lgl k c × Nested k c) × Seedᶠ t ×
  (∀ η (e : Gd k c η) → Seedᶠ (g η e))

full→seed : ∀ x → Seedᶠ x → Seed x
full→seed zero s = tt
full→seed (suc x) s = full→seed x s
full→seed (lim f) s = λ n → full→seed (f n) (s n)
full→seed (lc k c w b t g) (sk , s , st , sg) =
  s , (λ η e → full→seed (g η e) (sg η e))

seedN : ∀ y r c (l : LglLow y r c) (nb : NestedLow y r c) t
  (g : (η : Low y r) → .(GdL y r c η) → LF) →
  Seedᶠ y → Seedᶠ t → (∀ η (e : GdL y r c η) → Seedᶠ (g η e)) →
  Seedᶠ (upN y r c l nb t g)
seedN zero ()
seedN (suc k) (inj₁ _) c l nb t g sy st sg = sy , (l , nb) , st , sg
seedN (suc k) (inj₂ r) c l nb t g sy st sg = seedN k r c l nb t g sy st sg
seedN (lim f) (n , r) c l nb t g sy st sg =
  seedN (f n) r c l nb t g (sy n) st sg
seedN (lc k c₀ w₀ b₀ t₀ g₀) (inj₁ (inj₁ _)) c l nb t g (sk , _ , _ , _) st sg =
  sk , (l , nb) , st , sg
seedN (lc k c₀ w₀ b₀ t₀ g₀) (inj₁ (inj₂ r)) c l nb t g (sk , _ , _ , _) st sg =
  seedN k r c l nb t g sk st sg
seedN (lc k c₀ w₀ b₀ t₀ g₀) (inj₂ (inj₁ r)) c l nb t g (_ , _ , st₀ , _) st sg =
  seedN t₀ r c l nb t g st₀ st sg
seedN (lc k c₀ w₀ b₀ t₀ g₀) (inj₂ (inj₂ (η , e , r))) c l nb t g
  (_ , _ , _ , sg₀) st sg = seedN (g₀ η e) r c l nb t g (sg₀ η e) st sg

seed-Ω̂ : ∀ x → Seedᶠ x → Seedᶠ (Ω̂ x)
seed-up : ∀ y → Seedᶠ y → ∀ a (nb : Nested y a) → Seedᶠ (up y a nb)
seed-upK : ∀ y → Seedᶠ y → ∀ i T (nb : NestedKid y i T) →
  Seedᶠ (upK y i T nb)

seed-Ω̂ zero s = tt
seed-Ω̂ (suc k) s =
  s , (cO-Lgl k , cO-Nested k) , seed-Ω̂ k s ,
  (λ η e → seed-up k s η (proj₂ (proj₂ e)))
seed-Ω̂ (lim f) s = λ n → seed-Ω̂ (f n) (s n)
seed-Ω̂ (lc k c w b t g) (sk , s , st , sg) =
  sk , s , seed-Ω̂ t st , (λ η e → seed-Ω̂ (g η e) (sg η e))

seed-up y s G.zero nb = tt
seed-up y s (G.suc a) nb = seed-up y s a nb
seed-up y s (G.lim f) nb = λ n → seed-up y s (f n) (nb n)
seed-up y s (G.lc r c t g) (l , nl , nt , ng) =
  seedN y r c l nl (up y t nt) (λ η e → up y (g η e) (ng η e)) s
    (seed-up y s t nt) (λ η e → seed-up y s (g η e) (ng η e))
seed-up y s (G.em i T) nb = seed-upK y s i T nb
seed-up y s G.top nb = seed-Ω̂ y s

seed-upK (suc k) s _ T nb = seed-up k s T nb
seed-upK (lim f) s n T nb = seed-up (f n) (s n) T nb
seed-upK (lc k c w b t g) (sk , _ , _ , _) (inj₁ _) T nb = seed-up k sk T nb
seed-upK (lc k c w b t g) (_ , _ , st , _) (inj₂ (inj₁ _)) T nb =
  seed-up t st T nb
seed-upK (lc k c w b t g) (_ , _ , _ , sg) (inj₂ (inj₂ (η , e))) T nb =
  seed-up (g η e) (sg η e) T nb

seed-tw : ∀ n → Seedᶠ (tw n)
seed-tw zero = tt
seed-tw (suc n) = seed-Ω̂ (tw n) (seed-tw n)

seed-Λ : Seedᶠ Λ
seed-Λ = seed-tw

-- 折叠的定义域用的那一项, 在塔与 Λ 上由上面的推出.
tower-seed : ∀ n → Seed (tw n)
tower-seed n = full→seed (tw n) (seed-tw n)

Λ-seed : Seed Λ
Λ-seed = full→seed Λ seed-Λ
```

`seed-tw` 与 `seed-Λ` 只说起点证据在塔与 Λ 上有；它们不是折叠，也不说 `tw 3` 以上在 `Dom` 里
(那些树有层号不为 0 的 Ω 结点，`Only0` 不成立)。目标层不为 0 的折叠本篇没有碰。

## 4 观察：在 `Dom` 上，起点守卫取结点里的那份还是证书里的那份，是同一个链点

折叠的定义里，结点自己存的 `w`, `b` 只用在两处：gt 行的起点 `start c w b`，与 `ψ-positive` 看的起点那一支。
证书里现在也有一份 `Lgl 0 c`。守卫是无关的，所以两种取法给出同一个链点：

```agda
start-from-certificate : ∀ c (w : Lgl zero c) (b : Nested zero c) t
  (g : (η : R) → .(Gd zero c η) → LF) (d : Dom (lc zero c w b t g)) →
  start c w b ≡ point c (dom-seed c w b t g d)
start-from-certificate c w b t g d = refl
```

读法 (判断)：在 `Dom` 上，这个折叠用到新块的两件事是 "分支的守卫参数无关" 与 "证书参数无关"；
"证据存在结点里" 这一件，折叠可以不用。结点里的证据另有它的用处 (只读树的算子能调用起点，
没有守卫域为空的结点，见 [RR5IrrCheck](RR5IrrCheck.lagda.md))，本篇不评价。
