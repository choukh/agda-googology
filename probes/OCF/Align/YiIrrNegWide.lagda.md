# YiIrrNeg 第 3 项：定义域取整个 `Only0 × Legal` 片段时，接口推出 "无关证据的搜索"

否定路对 "大定义域" 的检查，接口是 [YiIrrIf](YiIrrIf.lagda.md) 的 `FoldRows`。

**对纲领与目标意味着什么。** 新块把下界合法的证明 `w` 存在结点里，但它是无关参数；
树外的 `Legal`（`YiIrrIf` §1）没有 "下界合法" 这一字段。所以 `Only0 x × Legal x`
并不交出一份可以当数据用的 `Lgl zero c`。而 `position`（以及 `fold-legal` 加极限行）
在 Ω 结点处要交出的是数据：输出极限里的一个下标和一条路径。本篇把这一处写成编译定理：
定义域含整个 `Only0 × Legal` 片段的 `FoldRows` 实例，给出
`IrrSearch : ∀ α → .(Σ n. α n ≡ true) → Σ n. α n ≡ true`，即凭一份只能无关使用的存在性证明，
算出见证。

**读法（判断，不是定理）。** `IrrSearch` 在通常的语义里是真的，本篇没有、也不可能由它推出 ⊥
或 WLPO；它只是在不开无关投影的 Agda 里没有已知的证明（文末有四个被检查器拒绝的写法，属有限测试）。
所以这条结果**不是乙线的数学障碍，也不否定 "整个合法片段" 这一目标**；它说的是
`Only0 × Legal` 这个谓词缺一个相关的字段。反例对象 `node α s` 不在规范塔的读回域内
（它的下界是为编码搜索而造的坐标）；规范 Ω₁ 的下界是字面的 1，合法性是 `tt`，不受影响。
给定义域补上相关的下界证据（§5 的 `Low0`）之后，这条攻击只能取回定义域成员自己带来的见证
（`low0-node→found`）。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiIrrNegWide where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Bool.Base using (Bool; true; false; _∨_)
open import Data.Empty using (⊥; ⊥-elim-irr)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck
open import OCF.Align.YiIrrIf
```

## 1 被推出的原则，与一个单调化的布尔列

`seen α m` 是 `α 0 ∨ … ∨ α m`。它单调，并且与 `α` 有同样的见证。

```agda
Found : (ℕ → Bool) → Set
Found α = Σ ℕ λ n → α n ≡ true

IrrSearch : Set
IrrSearch = ∀ (α : ℕ → Bool) → .(Found α) → Found α

seen : (ℕ → Bool) → ℕ → Bool
seen α zero = α zero
seen α (suc n) = seen α n ∨ α (suc n)

∨-right : ∀ x → x ∨ true ≡ true
∨-right false = refl
∨-right true = refl

∨-split : ∀ x y → x ∨ y ≡ true → (x ≡ true) ⊎ (y ≡ true)
∨-split true y p = inj₁ refl
∨-split false y p = inj₂ p

seen-mono : ∀ α n → seen α n ≡ true → seen α (suc n) ≡ true
seen-mono α n p = cong (_∨ α (suc n)) p

seen-hit : ∀ α n → α n ≡ true → seen α n ≡ true
seen-hit α zero p = p
seen-hit α (suc n) p = trans (cong (seen α n ∨_) p) (∨-right (seen α n))

seen-found : ∀ α m → seen α m ≡ true → Found α
seen-found α zero p = zero , p
seen-found α (suc m) p with ∨-split (seen α m) (α (suc m)) p
... | inj₁ q = seen-found α m q
... | inj₂ q = suc m , q
```

## 2 下界：它合法，当且仅当 `α` 有见证

`bound α = lim (1, d, d, …)`，其中 `d = lim (flag (seen α m))`。`d` 总合法；
第 0 步 `1 ⊲ d` 要在 `d` 里选一个取值为 1 的下标，这就是见证。

```agda
flag : Bool → R
flag false = G.zero
flag true = one

flag-step : ∀ x y → (x ≡ true → y ≡ true) → Cp zero (flag x) (flag y)
flag-step false false h = inj₁ refl
flag-step false true h = inj₂ (inj₁ refl)
flag-step true false h with h refl
... | ()
flag-step true true h = inj₁ refl

flag-legal : ∀ x → Lgl zero (flag x)
flag-legal false = tt
flag-legal true = tt

flag-hit : ∀ x → Cp zero one (flag x) → x ≡ true
flag-hit true p = refl
flag-hit false (inj₁ ())
flag-hit false (inj₂ ())

dense : (ℕ → Bool) → R
dense α = G.lim (λ m → flag (seen α m))

dense-legal : ∀ α → Lgl zero (dense α)
dense-legal α =
  (λ m → flag-step (seen α m) (seen α (suc m)) (seen-mono α m)) ,
  (λ m → flag-legal (seen α m))

column : (ℕ → Bool) → ℕ → R
column α zero = one
column α (suc n) = dense α

bound : (ℕ → Bool) → R
bound α = G.lim (column α)

found→legal : ∀ α → Found α → Lgl zero (bound α)
found→legal α (n , p) = step , lawful
  where
  step : ∀ k → Cp zero (column α k) (column α (suc k))
  step zero = inj₂ (n , subst (λ z → Cp zero one (flag z))
    (sym (seen-hit α n p)) (inj₁ refl))
  step (suc k) = inj₁ refl
  lawful : ∀ k → Lgl zero (column α k)
  lawful zero = tt
  lawful (suc k) = dense-legal α

legal→seen : ∀ α → Lgl zero (bound α) → Σ ℕ λ m → seen α m ≡ true
legal→seen α (st , lf) with st zero
... | inj₁ ()
... | inj₂ (m , p) = m , flag-hit (seen α m) p

-- 第 0 层的合法性沿第一位置向下封闭 (旧块 lgl-cp 的第 0 层情形).
lgl-cp : ∀ {a} b → Cp zero a b → Lgl zero b → Lgl zero a
lgl-dn : ∀ {a} b → Dn zero a b → Lgl zero b → Lgl zero a
lgl-cp b (inj₁ refl) l = l
lgl-cp b (inj₂ p) l = lgl-dn b p l
lgl-dn G.zero () l
lgl-dn (G.suc b) p l = lgl-cp b p l
lgl-dn (G.lim f) (n , p) (st , lf) = lgl-cp (f n) p (lf n)
lgl-dn (G.lc () c t g) p l
lgl-dn (G.em () a) p l
lgl-dn G.top () l
```

## 3 结点：只凭无关的见证就能造出来，并且 `Only0`、`Legal` 都有相关的证明

第一支是 1，分支恒为 `high α = lim (mark (seen α m))`。`Legal` 的第一位置字段
`CP 1 (high α)` 要一个见证；它的前提里有相关的守卫 `e`，从 `e` 能取回下界的合法性，
于是取回见证。所以 `node-legal` 不用 `s` 的内容。

```agda
unit : LF
unit = suc zero

mark : Bool → LF
mark false = zero
mark true = unit

mark-step : ∀ x y → (x ≡ true → y ≡ true) → CP (mark x) (mark y)
mark-step false false h = self
mark-step false true h = suc self
mark-step true false h with h refl
... | ()
mark-step true true h = self

mark-legal : ∀ x → Legal (mark x)
mark-legal false = tt
mark-legal true = tt

mark-only : ∀ x → Only0 (mark x)
mark-only false = tt
mark-only true = tt

high : (ℕ → Bool) → LF
high α = lim (λ m → mark (seen α m))

high-legal : ∀ α → Legal (high α)
high-legal α =
  (λ m → mark-step (seen α m) (seen α (suc m)) (seen-mono α m)) ,
  (λ m → mark-legal (seen α m))

high-only : ∀ α → Only0 (high α)
high-only α m = mark-only (seen α m)

node : ∀ α → .(Found α) → LF
node α s = lc zero (bound α) (found→legal α s) (raw0-Nested (bound α))
  unit (λ η e → high α)

node-only : ∀ α .(s : Found α) → Only0 (node α s)
node-only α s = tt , (λ η e → high-only α)

unit-below-high : ∀ α η → Gd zero (bound α) η → CP unit (high α)
unit-below-high α η e with legal→seen α (lgl-cp η (proj₁ e) (proj₁ (proj₂ e)))
... | m , q = lim m (subst (λ z → CP unit (mark z)) (sym q) self)

node-legal : ∀ α .(s : Found α) → Legal (node α s)
node-legal α s =
  tt ,
  (λ η e → unit-below-high α η e) ,
  (λ η e η′ e′ d → self) ,
  (λ η e e′ → refl) ,
  tt ,
  (λ η e → high-legal α)
```

前提可满足：`α = λ _ → true` 有见证 `(0 , refl)`，这时 `node α s` 是一棵闭的合法树。

```agda
always : ℕ → Bool
always n = true

always-found : Found always
always-found = zero , refl

closed-node : LF
closed-node = node always always-found

closed-node-legal : Legal closed-node
closed-node-legal = node-legal always always-found
```

## 4 从接口取出见证

相关的数据只有一处：`Cp zero (ψ 1) (ψ (node α s))` 的证明。它在输出极限里选了下标。
关于 `ψ (node α s)` 长什么样的等式（gt 行）要相关的 `w`，这里只有无关的；
但这些等式只用来排除不可能的情形，排除只需要无关的 ⊥。最后一步对 `seen α m` 分情况，
它是可判定的。

```agda
body : R → ℕ → R
body (G.lim f) = f
body _ = λ n → G.zero

suc≢lim : ∀ {v : R} {f : ℕ → R} → G.suc v ≡ G.lim f → ⊥
suc≢lim ()

-- ω 不在 1 的下面.
ω-not-below-one : Cp zero (successor one) one → ⊥
ω-not-below-one (inj₁ ())
ω-not-below-one (inj₂ (inj₁ ()))
ω-not-below-one (inj₂ (inj₂ ()))

value : Bool → R
value false = one
value true = successor one

finish : ∀ α m (x : Bool) → seen α m ≡ x → .((x ≡ false) → ⊥) →
  Σ ℕ λ k → seen α k ≡ true
finish α m true eq no = m , eq
finish α m false eq no = ⊥-elim-irr (no refl)

module Extract (F : FoldRows)
  (wide : ∀ x → Only0 x → Legal x → FoldRows.Dom F x) where
  open FoldRows F

  dom-zero : Dom zero
  dom-zero = wide zero tt tt

  dom-unit : Dom unit
  dom-unit = wide unit tt tt

  dom-mark : ∀ x → Dom (mark x)
  dom-mark x = wide (mark x) (mark-only x) (mark-legal x)

  dom-high : ∀ α → Dom (high α)
  dom-high α = wide (high α) (high-only α) (high-legal α)

  dom-node : ∀ α .(s : Found α) → Dom (node α s)
  dom-node α s = wide (node α s) (node-only α s) (node-legal α s)

  ψ-unit : ψ unit dom-unit ≡ successor one
  ψ-unit = trans (suc-row zero dom-unit) (cong successor (zero-row dom-zero))

  ψ-mark : ∀ x → ψ (mark x) (dom-mark x) ≡ value x
  ψ-mark false = zero-row dom-zero
  ψ-mark true = ψ-unit

  ψ-high : ∀ α → ψ (high α) (dom-high α) ≡
    G.lim (λ m → ψ (mark (seen α m)) (dom-mark (seen α m)))
  ψ-high α = lim-row (λ m → mark (seen α m)) (dom-high α)

  -- gt 行: 分支恒为 high α, 所以极限体是常函数. 这里的 s 是相关参数;
  -- 下面只在无关位置调用它.
  ψ-node : ∀ α (s : Found α) → ψ (node α s) (dom-node α s) ≡
    G.lim (λ n → ψ (high α) (dom-high α))
  ψ-node α s = gt-row (bound α) (found→legal α s) (raw0-Nested (bound α))
    unit (λ η e → high α) (dom-node α s)

  zero-not-output : ∀ x (d : Dom x) → G.zero ≡ ψ x d → ⊥
  zero-not-output x d eq = subst (Dn zero G.zero) (sym eq) (fold-positive x d)

  no-eq₁ : ∀ α → successor one ≡ G.lim (λ n → ψ (high α) (dom-high α)) → ⊥
  no-eq₁ α eq = zero-not-output (high α) (dom-high α)
    (cong (λ z → body z zero) eq)

  no-eq₂ : ∀ α → successor one ≡
    G.lim (λ m → ψ (mark (seen α m)) (dom-mark (seen α m))) → ⊥
  no-eq₂ α eq = zero-not-output (mark (seen α zero)) (dom-mark (seen α zero))
    (cong (λ z → body z zero) eq)

  no-low : ∀ α m (w : R) → seen α m ≡ false →
    Cp zero (successor one) w →
    w ≡ ψ (mark (seen α m)) (dom-mark (seen α m)) → ⊥
  no-low α m w isf q eq = ω-not-below-one
    (subst (Cp zero (successor one))
      (trans eq (trans (ψ-mark (seen α m)) (cong value isf))) q)

  -- 第二层: w 无关地等于 ψ (high α), 相关地有 ω ⊲ w.
  stage₂ : ∀ α (w : R) → Cp zero (successor one) w →
    .(w ≡ G.lim (λ m → ψ (mark (seen α m)) (dom-mark (seen α m)))) →
    Σ ℕ λ k → seen α k ≡ true
  stage₂ α w (inj₁ e) E = ⊥-elim-irr (no-eq₂ α (trans e E))
  stage₂ α G.zero (inj₂ ()) E
  stage₂ α (G.suc v) (inj₂ p) E = ⊥-elim-irr (suc≢lim E)
  stage₂ α (G.lim r) (inj₂ (m , q)) E =
    finish α m (seen α m) refl
      (λ isf → no-low α m (r m) isf q (cong (λ z → body z m) E))
  stage₂ α (G.lc () c t g) (inj₂ p) E
  stage₂ α (G.em () a) (inj₂ p) E
  stage₂ α G.top (inj₂ ()) E

  -- 第一层: v 无关地等于 ψ (node α s), 相关地有 ω ⊲ v.
  stage₁ : ∀ α (v : R) → Cp zero (successor one) v →
    .(v ≡ G.lim (λ n → ψ (high α) (dom-high α))) →
    Σ ℕ λ k → seen α k ≡ true
  stage₁ α v (inj₁ e) E = ⊥-elim-irr (no-eq₁ α (trans e E))
  stage₁ α G.zero (inj₂ ()) E
  stage₁ α (G.suc v) (inj₂ p) E = ⊥-elim-irr (suc≢lim E)
  stage₁ α (G.lim r) (inj₂ (n , q)) E =
    stage₂ α (r n) q (trans (cong (λ z → body z n) E) (ψ-high α))
  stage₁ α (G.lc () c t g) (inj₂ p) E
  stage₁ α (G.em () a) (inj₂ p) E
  stage₁ α G.top (inj₂ ()) E

  search-from : ∀ α .(s : Found α) →
    Cp zero (ψ unit dom-unit) (ψ (node α s) (dom-node α s)) → Found α
  search-from α s p with stage₁ α (ψ (node α s) (dom-node α s))
    (subst (λ z → Cp zero z (ψ (node α s) (dom-node α s))) ψ-unit p)
    (ψ-node α s)
  ... | m , q = seen-found α m q

  -- 经 position: 1 是结点的第一支, 所以 ψ 1 ⊲ ψ (node).
  by-position : IrrSearch
  by-position α s = search-from α s
    (position unit (node α s) dom-unit (dom-node α s) (fst self))

  -- 不经 position: 把 1 与结点排成一个合法的极限, 用 fold-legal 与极限行.
  wrap : ∀ α → .(Found α) → ℕ → LF
  wrap α s zero = unit
  wrap α s (suc n) = node α s

  wrap-step : ∀ α .(s : Found α) n → CP (wrap α s n) (wrap α s (suc n))
  wrap-step α s zero = fst self
  wrap-step α s (suc n) = self

  wrap-legal : ∀ α .(s : Found α) n → Legal (wrap α s n)
  wrap-legal α s zero = tt
  wrap-legal α s (suc n) = node-legal α s

  wrap-only : ∀ α .(s : Found α) n → Only0 (wrap α s n)
  wrap-only α s zero = tt
  wrap-only α s (suc n) = node-only α s

  dom-wrap : ∀ α .(s : Found α) → Dom (lim (wrap α s))
  dom-wrap α s = wide (lim (wrap α s)) (wrap-only α s)
    (wrap-step α s , wrap-legal α s)

  by-fold-legal : IrrSearch
  by-fold-legal α s = search-from α s
    (proj₁ (subst (Lgl zero) (lim-row (wrap α s) (dom-wrap α s))
      (fold-legal (lim (wrap α s)) (dom-wrap α s))) zero)

wide→irr-search : (F : FoldRows) →
  (∀ x → Only0 x → Legal x → FoldRows.Dom F x) → IrrSearch
wide→irr-search F wide = Extract.by-position F wide

wide→irr-search′ : (F : FoldRows) →
  (∀ x → Only0 x → Legal x → FoldRows.Dom F x) → IrrSearch
wide→irr-search′ F wide = Extract.by-fold-legal F wide
```

`by-position` 用到的字段：`position`、`gt-row`、`lim-row`、`suc-row`、`zero-row`、`fold-positive`。
`by-fold-legal` 把 `position` 换成 `fold-legal`。两条用的是同一个对象 `node α s`，算一条反例。

## 5 缺的是哪个字段

`Low0`：每个 Ω 结点的下界有相关的合法与嵌套证据，对第一支与带守卫的分支遗传。
规范 Ω₁ 满足它（下界是字面的 1）。`node α s` 一旦带上 `Low0`，见证就在成员资格里，
不需要搜索：上一节的攻击对 `Only0 × Legal × Low0` 这样的定义域不给出新东西。

```agda
Low0 : LF → Set
Low0 zero = ⊤
Low0 (suc x) = Low0 x
Low0 (lim f) = ∀ n → Low0 (f n)
Low0 (lc k c w b t g) =
  Lgl k c × Nested k c × Low0 t × (∀ η (e : Gd k c η) → Low0 (g η e))

read0-low : ∀ a → Low0 (read0 a)
read0-low G.zero = tt
read0-low (G.suc a) = read0-low a
read0-low (G.lim f) = λ n → read0-low (f n)
read0-low (G.lc () c t g)
read0-low (G.em () a)
read0-low G.top = tt

Ω₁-low : Low0 (tw 2)
Ω₁-low = tt , tt , tt , (λ η e → read0-low η)

low0-node→found : ∀ α .(s : Found α) → Low0 (node α s) → Found α
low0-node→found α s (l , _) with legal→seen α l
... | m , q = seen-found α m q
```

## 结论与范围

| 档 | 结果 |
|---|---|
| 编译定理 | `wide→irr-search`：`FoldRows` 的实例若定义域含整个 `Only0 × Legal` 片段，则 `IrrSearch`。用 `position` |
| 编译定理 | `wide→irr-search′`：同一结论，不用 `position`，用 `fold-legal` 与极限行 |
| 编译定理 | `node-legal`、`node-only`：反例结点只凭无关的见证就在 `Only0 × Legal` 里；`closed-node-legal` 是闭实例 |
| 编译定理 | `Ω₁-low`、`low0-node→found`：补上相关的下界证据后，规范 Ω₁ 仍在定义域里，而本篇的结点自带见证 |
| 有限测试 | 四种直接证明 `IrrSearch` 的写法（对无关的可达性证明递归、对无关的 `Σ` 取分量、对无关的相等证明匹配、以无关的燃料递归）在仓库外的实验文件里都被检查器以 `SplitOnIrrelevant` 拒绝。这是四次尝试，不是不可证性的证明 |
| 判断 | `IrrSearch` 在 `--safe` 且不开无关投影的 Agda 里没有证明。纸面理由：闭项 `(ℕ → Bool) → .(…) → ℕ` 不能读无关参数，对一切 `α` 停机并且连续；在全假的列上它读有限多项后给出 `n`，把列在更远处改成真，输出不变而 `α n` 仍假 |
| 判断 | 所以 `Dom x = Only0 x × Legal x` 这一取法写不出实例。这是 "谓词缺字段"，不是数学障碍：`IrrSearch` 在集合语义与可实现性语义里都成立，本篇没有由它推出 ⊥、WLPO 或 LPO |

**反例对象是否在读回域内。** 不在。`node α s` 的下界 `bound α` 是为编码搜索造的；
它是 `Raw (tw 1)` 里一个合法坐标的读回，但不是规范塔的任何一项或其分支。
按 AGENTS "量化域先取带证据的读回域"，这条读作 "这个定义域的谓词太宽（证据太少）"，
不读作乙线的障碍。同形的反例只此一条，没有再找第二条。

**对构造路的含义。** 想把定义域放宽到整个合法片段，定义域里要另带相关的下界证据
（例如上面的 `Low0`）；树里的 `w`、`b` 仍是无关的，`ψ` 的输出仍不依赖任何证明。
带 `Low0` 的定义域上接口可满足，实例在 [YiIrrNegModel](YiIrrNegModel.lagda.md)。

没有 Funext，没有公设，没有洞。没有序数值，强度没有变化。
翻译账：只新增闭反例与提取证明；`Low0` 是树侧的合法性字段，不来自记号。
