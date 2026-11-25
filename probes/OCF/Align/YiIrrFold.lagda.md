# YiIrrFold：无关证据块上，目标层 0 的完整递归折叠

**判决：接口 [YiIrrIf](YiIrrIf.lagda.md) 的记录 `FoldRows` 已实填 (`fold-rows`)，定义域是
`Dom x = Only0 x × Legal x × Seed x`。先试的 `Only0 x × Legal x` 未走通，没有否定定理。**

**对纲领与目标意味着什么。** 分三件说。

- *证书。* 折叠 `ψ : (x : LF) → .(Dom x) → R` 的证书参数是无关的：换证书输出定义性相等
  (`certificate-free`，`refl`)。证书是树外的三项谓词，不引用记号。K2′ 三轮卡住的 "证明被当成数据"
  ([RR5-SoftStops](../../Survey/RR5-SoftStops.md) §1.3) 在这种写法下没有出现：
  `ψ` 把证书里的证明交给分支与链点的守卫，这些位置都是无关的。
- *构造。* `ψ` 对树结构递归，四行都是 `refl`：零给 1；后继给 `successor`；ℕ 极限逐项；
  层号 0 的 Ω 结点走加法链 ηₙ₊₁ = ηₙ + ψ(g ηₙ)，从下界自身起步。它是片段上的一个全定义的折叠，
  不是为某个族单写的。闭项 (规范 Ω₁，Ω₁·(n+1)，它们的极限，Ω₁²) 在 [YiIrrFoldInst](YiIrrFoldInst.lagda.md)。
- *值。* 本篇没有值。第 4 层在 [YiIrrFoldValue](YiIrrFoldValue.lagda.md)：Ω₁，Ω₁·(n+1) 与极限上，
  输出与 `Level.ψ⁰` 的参照互相 `≼`。强度没有变化，这些值都在 ψ₀(Ω₁·ω) 以内，
  记号无关树侧的值前沿仍是 ψ₀(Ω_{Ω·ω²})。

**一处与预想不同。** 输出合法 (`ψ-legal`) 与位置保持 (`ψ-position`) 是对未知的树递归的相关引理，
证明它们要调用 `Legal` 的分支字段，这些字段的守卫参数是相关的；结点里存的下界合法性是无关的，
在引理的定义体里不能拿来用。而 gt 行里下一个链点的守卫正要 "子树的输出合法" 这条引理。
所以证书里多一项 `Seed` (每个走到的 Ω 结点，下界合法有一份相关的证明)。它只进引理的证明，
不进 `ψ` 的输出。试过的写法、它等价于什么、在规范塔上是否成立，见 [YiIrrFoldSeed](YiIrrFoldSeed.lagda.md)。

文件：[YiIrrFoldBase](YiIrrFoldBase.lagda.md) (第 0 层算术，`Dom`，加法链)，本篇 (折叠与接口实填)，
[YiIrrFoldInst](YiIrrFoldInst.lagda.md) (规范实例)，[YiIrrFoldSeed](YiIrrFoldSeed.lagda.md) (定义域的分析)，
[YiIrrFoldValue](YiIrrFoldValue.lagda.md) (验收，第 4 层)。前四件的导入闭包里只有 `RR5IrrCore`,
`RR5IrrCheck`, `YiIrrIf` 与标准库。全部 `--safe --without-K --lossy-unification`，无公设，无洞，
无停机或正性编译指示，无 Funext。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiIrrFold where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥-elim)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.RR5IrrCore
open import OCF.Align.YiIrrIf
open import OCF.Align.YiIrrFoldBase
```

## 1 折叠与它的三条引理：一个互递归块

四个函数一起定义，都对树结构递归。

- `ψ`：证书无关。层号不为 0 的 Ω 结点不在 `Dom` 里，那里随便给一个值 (取 1)。
- `ψ-positive`：输出为正。证书无关：它只看树的形状，Ω 结点处看下界自身那一支。
  链的增长 (`Chain.grow`) 要相关地用它，而链点的守卫是无关的，所以这一条必须不读证书。
- `ψ-legal`：输出合法。读证书。它在 `ψ` 里只出现在 `Chain` 的无关参数 `lawful` 的位置，
  用来造下一个链点的守卫。
- `ψ-position`：位置保持。读证书。对被比较的大树 `y` 递归，不对路径递归：
  落在 Ω 结点上时，路径到第一支 `t`，再由 `Legal` 的 `tg` 字段接到下界自身那一支，
  也就是链的第 0 项，然后对那一支递归。自反情形两边是同一棵树、两份证书，`inj₁ refl`。

停机：`ψ`, `ψ-positive`, `ψ-legal` 的递归调用都落在子树上 (`x`, `f n`, `g η e`)；
`ψ-position x y` 只调用自己，`y` 换成子树。检查器直接接受，没有度量，没有编译指示。

```agda
ψ : (x : LF) → .(Dom x) → R
ψ-positive : ∀ x .(d : Dom x) → Dn zero G.zero (ψ x d)
ψ-legal : ∀ x (d : Dom x) → Lgl zero (ψ x d)
ψ-position : ∀ x y (dx : Dom x) (dy : Dom y) → CP x y →
  Cp zero (ψ x dx) (ψ y dy)

ψ zero d = one
ψ (suc x) d = successor (ψ x (dom-pred x d))
ψ (lim f) d = G.lim (λ n → ψ (f n) (dom-at f d n))
ψ (lc zero c w b t g) d =
  Chain.collapse c
    (λ η e → ψ (g η e) (dom-branch c w b t g d η e))
    (λ η e → ψ-legal (g η e) (dom-branch c w b t g d η e))
    (λ η e → ψ-positive (g η e) (dom-branch c w b t g d η e))
    (start c w b)
ψ (lc (suc k) c w b t g) d = one
ψ (lc (lim f) c w b t g) d = one
ψ (lc (lc k c₀ w₀ b₀ t₀ g₀) c w b t g) d = one

ψ-positive zero d = inj₁ refl
ψ-positive (suc x) d = zero , inj₁ refl
ψ-positive (lim f) d = zero , inj₂ (ψ-positive (f zero) (dom-at f d zero))
ψ-positive (lc zero c w b t g) d = zero , inj₂
  (ψ-positive (g c (inj₁ refl , w , b))
    (dom-branch c w b t g d c (inj₁ refl , w , b)))
ψ-positive (lc (suc k) c w b t g) d = inj₁ refl
ψ-positive (lc (lim f) c w b t g) d = inj₁ refl
ψ-positive (lc (lc k c₀ w₀ b₀ t₀ g₀) c w b t g) d = inj₁ refl

ψ-legal zero d = tt
ψ-legal (suc x) d =
  copies-step (ψ x d) (inj₂ (ψ-positive x d)) ,
  copies-legal (ψ x d) (ψ-legal x d)
ψ-legal (lim f) d =
  (λ n → ψ-position (f n) (f (suc n)) (dom-at f d n) (dom-at f d (suc n))
    (proj₁ (proj₁ (proj₂ d)) n)) ,
  (λ n → ψ-legal (f n) (dom-at f d n))
ψ-legal (lc zero c w b t g) d =
  ChainLegal.collapse-legal c
    (λ η e → ψ (g η e) (dom-branch c w b t g d η e))
    (λ η e → ψ-legal (g η e) (dom-branch c w b t g d η e))
    (λ η e → ψ-positive (g η e) (dom-branch c w b t g d η e))
    (λ η e η′ e′ q → ψ-position (g η e) (g η′ e′)
      (dom-branch c w b t g d η e) (dom-branch c w b t g d η′ e′)
      (dom-directed c w b t g d η e η′ e′ q))
    (start c w b) (dom-seed c w b t g d)
ψ-legal (lc (suc k) c w b t g) d = tt
ψ-legal (lc (lim f) c w b t g) d = tt
ψ-legal (lc (lc k c₀ w₀ b₀ t₀ g₀) c w b t g) d = tt

ψ-position .zero zero dx dy self = inj₁ refl
ψ-position .(suc y) (suc y) dx dy self = inj₁ refl
ψ-position x (suc y) dx dy (suc p) =
  inj₂ (1 , ψ-position x y dx (dom-pred y dy) p)
ψ-position .(lim f) (lim f) dx dy self = inj₁ refl
ψ-position x (lim f) dx dy (lim n p) =
  inj₂ (n , ψ-position x (f n) dx (dom-at f dy n) p)
ψ-position .(lc k c w b t g) (lc k c w b t g) dx dy self = inj₁ refl
ψ-position x (lc zero c w b t g) dx dy (fst p) =
  inj₂ (zero , ψ-position x (g c (dom-seed c w b t g dy)) dx
    (dom-branch c w b t g dy c (dom-seed c w b t g dy))
    (CP-tr p (dom-first c w b t g dy c (dom-seed c w b t g dy))))
ψ-position x (lc (suc k) c w b t g) dx dy (fst p) = ⊥-elim (proj₁ dy)
ψ-position x (lc (lim f) c w b t g) dx dy (fst p) = ⊥-elim (proj₁ dy)
ψ-position x (lc (lc k c₀ w₀ b₀ t₀ g₀) c w b t g) dx dy (fst p) =
  ⊥-elim (proj₁ dy)
```

各行里用到的字段：

| 行 | 相关地用到证书的哪一项 | 无关位置里用到什么 |
|---|---|---|
| `ψ` 的四行 | 无 | `dom-pred`, `dom-at`, `dom-branch`；结点里的 `w`, `b` (起点守卫)；`ψ-legal` (下一点的守卫) |
| `ψ-positive` | 无 | 同上 |
| `ψ-legal`，极限行 | `Legal` 的步进 | |
| `ψ-legal`，gt 行 | `Legal.dir`，分支的 `Dom`，`Seed` 的根分量 (起点守卫) | |
| `ψ-position`，Ω 结点 | `Legal.tg`，`Seed` 的根分量，下界自身那一支的 `Dom` | |

换证书不换输出，是定义性相等：

```agda
certificate-free : ∀ x (d d′ : Dom x) → ψ x d ≡ ψ x d′
certificate-free x d d′ = refl
```

## 2 接口实填

`next` 与 `next-grow` 是 `Chain` 在结点处的实例。`next-grow` 对任意链点成立，链点的守卫是无关的，
所以它用的是证书无关的 `ψ-positive`。记录里的行都是 `refl`。

```agda
next : ∀ c .(w : Lgl zero c) .(b : Nested zero c) t
  (g : (η : R) → .(Gd zero c η) → LF) →
  .(Dom (lc zero c w b t g)) → Point c → Point c
next c w b t g d =
  Chain.next c
    (λ η e → ψ (g η e) (dom-branch c w b t g d η e))
    (λ η e → ψ-legal (g η e) (dom-branch c w b t g d η e))
    (λ η e → ψ-positive (g η e) (dom-branch c w b t g d η e))

next-grow : ∀ c .(w : Lgl zero c) .(b : Nested zero c) t
  (g : (η : R) → .(Gd zero c η) → LF)
  .(d : Dom (lc zero c w b t g)) (p : Point c) →
  Dn zero (coordinate p) (coordinate (next c w b t g d p))
next-grow c w b t g d =
  Chain.grow c
    (λ η e → ψ (g η e) (dom-branch c w b t g d η e))
    (λ η e → ψ-legal (g η e) (dom-branch c w b t g d η e))
    (λ η e → ψ-positive (g η e) (dom-branch c w b t g d η e))

fold-rows : FoldRows
fold-rows = record
  { Dom = Dom
  ; dom-pred = dom-pred
  ; dom-at = dom-at
  ; dom-branch = λ c w b t g → dom-branch c w b t g
  ; dom-only = λ x d → proj₁ d
  ; dom-legal = λ x d → proj₁ (proj₂ d)
  ; dom-Ω₁ = dom-Ω₁
  ; ψ = ψ
  ; next = λ c w b t g d → next c w b t g d
  ; zero-row = λ d → refl
  ; suc-row = λ x d → refl
  ; lim-row = λ f d → refl
  ; next-additive = λ c w b t g d p → refl
  ; next-grow = λ c w b t g d p → next-grow c w b t g d p
  ; gt-row = λ c w b t g d → refl
  ; fold-legal = ψ-legal
  ; fold-positive = λ x d → ψ-positive x d
  ; position = ψ-position
  }

-- gt 行的第 0 项是下界自身那一支的折叠.
gt-first : ∀ c (w : Lgl zero c) (b : Nested zero c) t
  (g : (η : R) → .(Gd zero c η) → LF) (d : Dom (lc zero c w b t g)) →
  FoldRows.out fold-rows c w b t g d (start c w b) ≡
  ψ (g c (inj₁ refl , w , b)) (dom-branch c w b t g d c (inj₁ refl , w , b))
gt-first c w b t g d = refl
```

## 3 结论与范围

| 档 | 结果 |
|---|---|
| 编译构造 | `fold-rows : FoldRows`，`Dom x = Only0 x × Legal x × Seed x`，含 `tw 2`，对后继、极限、分支遗传 |
| 编译定理 | `certificate-free`：换证书输出定义性相等 |
| 编译定理 | 四行 (`zero-row`, `suc-row`, `lim-row`, `gt-row`) 与 `next-additive` 都是 `refl` |
| 编译定理 | `ψ-legal`：输出合法；`ψ-positive`：输出为正，不读证书；`ψ-position`：字面第一位置被保持，对 `Dom` 里任意两棵树 |
| 未走通 | 定义域取 `Only0 × Legal`。缺相关的下界合法性；五个写法的报错与它同 `Unsquash` 的关系见 [YiIrrFoldSeed](YiIrrFoldSeed.lagda.md)。没有否定定理 |
| 判断 | 目标层不为 0 时的派发要拿位置证据分情况，本篇没有碰；那里的证书除起点一项外还要什么，未验证 |

**主审的分析哪些被检验了。**

- "`ψ` 写成 `ψ : (x : LF) → .(Dom x) → R`，对树结构递归，与引理互递归"：证实。
- "引理只在 `ψ` 的无关位置被调用"：对 `ψ-legal` 证实。`ψ-positive` 是例外：链的增长要相关地用它，
  所以它自己写成不读证书的。
- "位置保持的自反情形是 `inj₁ refl`；严格情形对大树递归，在 Ω 结点上用 `tg` 接到链的第 0 项"：证实。
- "先试 `Dom x = Only0 x × Legal x`"：未走通，要加 `Seed`。卡在 gt 行：下一个链点的守卫要子树的输出合法，
  这条引理要相关的起点守卫。`ψ` 的行本身只把证明转交给无关位置。
- "无关变量只能出现在无关位置；在无关参数的位置里可以对它们调用普通函数"：证实，并且有一条补充
  (实测)：无关位置只放开已在上下文里的无关变量，位置里面新绑定的无关变量 (λ 或模式匹配绑定) 仍不能相关地用，
  名字前加点的无关定义的定义体也一样。

**翻译账。** 四行的形状 (零给 1，后继给 ω 倍，极限逐项，Ω 结点取一条链的极限) 来自接口，
接口承自旧的 `FoldRows0`，再往上是记号的折叠规则；本篇没有新增这一类。由树的要求逼出的：
加法链 (守卫要字面路径，增长由构造给)，链点的无关守卫，证书里的 `Seed` (`Legal` 的字段要相关的守卫)，
位置保持经 `tg` 接到链的第 0 项。新增脚手架是 `Seed` 与 `Chain`/`ChainLegal`，都不读记号。
验收用序数值，没有用标签。第 4 层逼出：无。
