# YiIrrFb：层号字面为 0 或 1 的片段上，互递归的 ψ₀, ψ₁ 与第一次回灌

**判决：接口 [YiIrrFbIf](YiIrrFbIf.lagda.md) 的记录 `FbRows` 已实填 (`fb-rows`，编译构造)，定义域
`Only01 × Legal × Seedᶠ`，含规范的 Ω₂。** 回灌行是定义的一个子句：层号 1 的结点上 `ψ₀` 的链点由 `ψ₁` 的输出推进，
行都是 `refl`。本篇没有值；层号任意时的派发没有碰，不否定任何路线。底座 [YiIrrFbBase](YiIrrFbBase.lagda.md)
([YiIrrFbRaw](YiIrrFbRaw.lagda.md))，闭项 [YiIrrFbInst](YiIrrFbInst.lagda.md)，与旧 `ψ` 的一致 [YiIrrFbAgree](YiIrrFbAgree.lagda.md)
(条件)，值的下界 [YiIrrFbValue](YiIrrFbValue.lagda.md) (验收)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiIrrFb where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥-elim)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck using (up)
open import OCF.Align.YiIrrIf
open import OCF.Align.YiIrrFoldBase
  using (copies-step; copies-legal; module Chain; module ChainLegal)
open import OCF.Align.YiIrrFbIf
open import OCF.Align.YiIrrFbBase
```

## 1 一个互递归块

九个函数，都对树结构递归；检查器直接接受。派发按层号的字面形状：0 与 1 各有子句，其余形状不在 `Only01` 里，
给一个固定的值。

- `ψ₀`, `ψ₁`：证书无关。`ψ₁` 的保留行只把证书的分量交到输出结点分支的无关守卫之下；
  回灌行 (`ψ₀` 在层号 1 的结点) 把 `ψ₁-legal`, `ψ₁-nested` 交到链点的无关守卫里。
- `ψ₀-positive`, `ψ₁-positive`：不读证书。`ψ₁-positive` 不递归，只看每行输出的头。
- `ψ₀-legal`, `ψ₁-legal`, `ψ₁-nested`：读证书。保留行的嵌套证据要相关的 `Lgl 0 c`，取自 `Seedᶠ`。
- `ψ₀-position`, `ψ₁-position`：对大树递归。保留结点处路径直接进第一支；折叠结点处经 `Legal` 的 `tg`
  接到下界自身那一支，即链的第 0 项。

```agda
ψ₀ : (x : LF) → .(Dom x) → R
ψ₁ : (x : LF) → .(Dom x) → R₁
ψ₀-positive : ∀ x .(d : Dom x) → Dn zero G.zero (ψ₀ x d)
ψ₁-positive : ∀ x .(d : Dom x) → Pos₁ (ψ₁ x d)
ψ₀-legal : ∀ x (d : Dom x) → Lgl zero (ψ₀ x d)
ψ₁-legal : ∀ x (d : Dom x) → Lgl L1 (ψ₁ x d)
ψ₁-nested : ∀ x (d : Dom x) → Nested L1 (ψ₁ x d)
ψ₀-position : ∀ x y (dx : Dom x) (dy : Dom y) → CP x y →
  Cp zero (ψ₀ x dx) (ψ₀ y dy)
ψ₁-position : ∀ x y (dx : Dom x) (dy : Dom y) → CP x y →
  Cp L1 (ψ₁ x dx) (ψ₁ y dy)

ψ₀ zero d = one
ψ₀ (suc x) d = successor (ψ₀ x (dom-pred x d))
ψ₀ (lim f) d = G.lim (λ n → ψ₀ (f n) (dom-at f d n))
ψ₀ (lc zero c w b t g) d =
  Chain.collapse c
    (λ η e → ψ₀ (g η e) (Node₀.branch c w b t g d η e))
    (λ η e → ψ₀-legal (g η e) (Node₀.branch c w b t g d η e))
    (λ η e → ψ₀-positive (g η e) (Node₀.branch c w b t g d η e))
    (start c w b)
ψ₀ (lc (suc zero) c w b t g) d =
  Chain₁.collapse c
    (λ η e → ψ₁ (g η e) (Node₁.branch c w b t g d η e))
    (λ η e → ψ₁-legal (g η e) (Node₁.branch c w b t g d η e))
    (λ η e → ψ₁-nested (g η e) (Node₁.branch c w b t g d η e))
    (λ η e → ψ₁-positive (g η e) (Node₁.branch c w b t g d η e))
    zero
    (λ η e → ψ₀ (g η e) (Node₁.branch c w b t g d η e))
    (startᴸ L1 c w b)
ψ₀ (lc (suc (suc k)) c w b t g) d = one
ψ₀ (lc (suc (lim f)) c w b t g) d = one
ψ₀ (lc (suc (lc k c₀ w₀ b₀ t₀ g₀)) c w b t g) d = one
ψ₀ (lc (lim f) c w b t g) d = one
ψ₀ (lc (lc k c₀ w₀ b₀ t₀ g₀) c w b t g) d = one

ψ₁ zero d = G.top
ψ₁ (suc x) d = successor₁ (ψ₁ x (dom-pred x d))
ψ₁ (lim f) d = G.lim (λ n → ψ₁ (f n) (dom-at f d n))
ψ₁ (lc zero c w b t g) d =
  G.lc (inj₁ tt) c (ψ₁ t (Node₀.first c w b t g d))
    (λ η e → ψ₁ (g η e) (Node₀.branch c w b t g d η e))
ψ₁ (lc (suc zero) c w b t g) d =
  Chain₁.collapse c
    (λ η e → ψ₁ (g η e) (Node₁.branch c w b t g d η e))
    (λ η e → ψ₁-legal (g η e) (Node₁.branch c w b t g d η e))
    (λ η e → ψ₁-nested (g η e) (Node₁.branch c w b t g d η e))
    (λ η e → ψ₁-positive (g η e) (Node₁.branch c w b t g d η e))
    L1
    (λ η e → ψ₁ (g η e) (Node₁.branch c w b t g d η e))
    (startᴸ L1 c w b)
ψ₁ (lc (suc (suc k)) c w b t g) d = G.top
ψ₁ (lc (suc (lim f)) c w b t g) d = G.top
ψ₁ (lc (suc (lc k c₀ w₀ b₀ t₀ g₀)) c w b t g) d = G.top
ψ₁ (lc (lim f) c w b t g) d = G.top
ψ₁ (lc (lc k c₀ w₀ b₀ t₀ g₀) c w b t g) d = G.top

ψ₀-positive zero d = inj₁ refl
ψ₀-positive (suc x) d = zero , inj₁ refl
ψ₀-positive (lim f) d = zero , inj₂ (ψ₀-positive (f zero) (dom-at f d zero))
ψ₀-positive (lc zero c w b t g) d = zero , inj₂
  (ψ₀-positive (g c (inj₁ refl , w , b))
    (Node₀.branch c w b t g d c (inj₁ refl , w , b)))
ψ₀-positive (lc (suc zero) c w b t g) d = zero , inj₂
  (ψ₀-positive (g c (inj₁ refl , w , b))
    (Node₁.branch c w b t g d c (inj₁ refl , w , b)))
ψ₀-positive (lc (suc (suc k)) c w b t g) d = inj₁ refl
ψ₀-positive (lc (suc (lim f)) c w b t g) d = inj₁ refl
ψ₀-positive (lc (suc (lc k c₀ w₀ b₀ t₀ g₀)) c w b t g) d = inj₁ refl
ψ₀-positive (lc (lim f) c w b t g) d = inj₁ refl
ψ₀-positive (lc (lc k c₀ w₀ b₀ t₀ g₀) c w b t g) d = inj₁ refl

ψ₁-positive zero d = tt
ψ₁-positive (suc x) d = tt
ψ₁-positive (lim f) d = tt
ψ₁-positive (lc zero c w b t g) d = tt
ψ₁-positive (lc (suc zero) c w b t g) d = tt
ψ₁-positive (lc (suc (suc k)) c w b t g) d = tt
ψ₁-positive (lc (suc (lim f)) c w b t g) d = tt
ψ₁-positive (lc (suc (lc k c₀ w₀ b₀ t₀ g₀)) c w b t g) d = tt
ψ₁-positive (lc (lim f) c w b t g) d = tt
ψ₁-positive (lc (lc k c₀ w₀ b₀ t₀ g₀) c w b t g) d = tt

ψ₀-legal zero d = tt
ψ₀-legal (suc x) d =
  copies-step (ψ₀ x d) (inj₂ (ψ₀-positive x d)) ,
  copies-legal (ψ₀ x d) (ψ₀-legal x d)
ψ₀-legal (lim f) d =
  (λ n → ψ₀-position (f n) (f (suc n)) (dom-at f d n) (dom-at f d (suc n))
    (proj₁ (proj₁ (proj₂ d)) n)) ,
  (λ n → ψ₀-legal (f n) (dom-at f d n))
ψ₀-legal (lc zero c w b t g) d =
  ChainLegal.collapse-legal c
    (λ η e → ψ₀ (g η e) (Node₀.branch c w b t g d η e))
    (λ η e → ψ₀-legal (g η e) (Node₀.branch c w b t g d η e))
    (λ η e → ψ₀-positive (g η e) (Node₀.branch c w b t g d η e))
    (λ η e η′ e′ q → ψ₀-position (g η e) (g η′ e′)
      (Node₀.branch c w b t g d η e) (Node₀.branch c w b t g d η′ e′)
      (Node₀.directed c w b t g d η e η′ e′ q))
    (start c w b) (Node₀.seed c w b t g d)
ψ₀-legal (lc (suc zero) c w b t g) d =
  ChainLegal₁.collapse-legal c
    (λ η e → ψ₁ (g η e) (Node₁.branch c w b t g d η e))
    (λ η e → ψ₁-legal (g η e) (Node₁.branch c w b t g d η e))
    (λ η e → ψ₁-nested (g η e) (Node₁.branch c w b t g d η e))
    (λ η e → ψ₁-positive (g η e) (Node₁.branch c w b t g d η e))
    (startᴸ L1 c w b) (Node₁.seed c w b t g d)
    zero
    (λ η e → ψ₀ (g η e) (Node₁.branch c w b t g d η e))
    (λ η e → ψ₀-legal (g η e) (Node₁.branch c w b t g d η e))
    (λ η e η′ e′ q → ψ₀-position (g η e) (g η′ e′)
      (Node₁.branch c w b t g d η e) (Node₁.branch c w b t g d η′ e′)
      (Node₁.directed c w b t g d η e η′ e′ q))
ψ₀-legal (lc (suc (suc k)) c w b t g) d = tt
ψ₀-legal (lc (suc (lim f)) c w b t g) d = tt
ψ₀-legal (lc (suc (lc k c₀ w₀ b₀ t₀ g₀)) c w b t g) d = tt
ψ₀-legal (lc (lim f) c w b t g) d = tt
ψ₀-legal (lc (lc k c₀ w₀ b₀ t₀ g₀) c w b t g) d = tt

ψ₁-legal zero d = tt
ψ₁-legal (suc x) d =
  copies₁-step (ψ₁ x d) , copies₁-legal (ψ₁ x d) (ψ₁-legal x d)
ψ₁-legal (lim f) d =
  (λ n → ψ₁-position (f n) (f (suc n)) (dom-at f d n) (dom-at f d (suc n))
    (proj₁ (proj₁ (proj₂ d)) n)) ,
  (λ n → ψ₁-legal (f n) (dom-at f d n))
ψ₁-legal (lc zero c w b t g) d =
  (λ η e → ψ₁-position t (g η e)
    (Node₀.first c w b t g d) (Node₀.branch c w b t g d η e)
    (Node₀.to-branch c w b t g d η e)) ,
  (λ η e η′ e′ q → ψ₁-position (g η e) (g η′ e′)
    (Node₀.branch c w b t g d η e) (Node₀.branch c w b t g d η′ e′)
    (Node₀.directed c w b t g d η e η′ e′ q)) ,
  (λ η e e′ → refl) ,
  ψ₁-legal t (Node₀.first c w b t g d) ,
  (λ η e → ψ₁-legal (g η e) (Node₀.branch c w b t g d η e))
ψ₁-legal (lc (suc zero) c w b t g) d =
  ChainLegal₁.collapse-legal c
    (λ η e → ψ₁ (g η e) (Node₁.branch c w b t g d η e))
    (λ η e → ψ₁-legal (g η e) (Node₁.branch c w b t g d η e))
    (λ η e → ψ₁-nested (g η e) (Node₁.branch c w b t g d η e))
    (λ η e → ψ₁-positive (g η e) (Node₁.branch c w b t g d η e))
    (startᴸ L1 c w b) (Node₁.seed c w b t g d)
    L1
    (λ η e → ψ₁ (g η e) (Node₁.branch c w b t g d η e))
    (λ η e → ψ₁-legal (g η e) (Node₁.branch c w b t g d η e))
    (λ η e η′ e′ q → ψ₁-position (g η e) (g η′ e′)
      (Node₁.branch c w b t g d η e) (Node₁.branch c w b t g d η′ e′)
      (Node₁.directed c w b t g d η e η′ e′ q))
ψ₁-legal (lc (suc (suc k)) c w b t g) d = tt
ψ₁-legal (lc (suc (lim f)) c w b t g) d = tt
ψ₁-legal (lc (suc (lc k c₀ w₀ b₀ t₀ g₀)) c w b t g) d = tt
ψ₁-legal (lc (lim f) c w b t g) d = tt
ψ₁-legal (lc (lc k c₀ w₀ b₀ t₀ g₀) c w b t g) d = tt

ψ₁-nested zero d = tt
ψ₁-nested (suc x) d = copies₁-nested (ψ₁ x d) (ψ₁-nested x d)
ψ₁-nested (lim f) d = λ n → ψ₁-nested (f n) (dom-at f d n)
ψ₁-nested (lc zero c w b t g) d =
  proj₁ (Node₀.low c w b t g d) ,
  proj₂ (Node₀.low c w b t g d) ,
  ψ₁-nested t (Node₀.first c w b t g d) ,
  (λ η e → ψ₁-nested (g η e) (Node₀.branch c w b t g d η e))
ψ₁-nested (lc (suc zero) c w b t g) d =
  ChainLegal₁.collapse-nested c
    (λ η e → ψ₁ (g η e) (Node₁.branch c w b t g d η e))
    (λ η e → ψ₁-legal (g η e) (Node₁.branch c w b t g d η e))
    (λ η e → ψ₁-nested (g η e) (Node₁.branch c w b t g d η e))
    (λ η e → ψ₁-positive (g η e) (Node₁.branch c w b t g d η e))
    (startᴸ L1 c w b) (Node₁.seed c w b t g d)
    L1
    (λ η e → ψ₁ (g η e) (Node₁.branch c w b t g d η e))
    (λ η e → ψ₁-nested (g η e) (Node₁.branch c w b t g d η e))
ψ₁-nested (lc (suc (suc k)) c w b t g) d = tt
ψ₁-nested (lc (suc (lim f)) c w b t g) d = tt
ψ₁-nested (lc (suc (lc k c₀ w₀ b₀ t₀ g₀)) c w b t g) d = tt
ψ₁-nested (lc (lim f) c w b t g) d = tt
ψ₁-nested (lc (lc k c₀ w₀ b₀ t₀ g₀) c w b t g) d = tt

ψ₀-position .zero zero dx dy self = inj₁ refl
ψ₀-position .(suc y) (suc y) dx dy self = inj₁ refl
ψ₀-position x (suc y) dx dy (suc p) =
  inj₂ (1 , ψ₀-position x y dx (dom-pred y dy) p)
ψ₀-position .(lim f) (lim f) dx dy self = inj₁ refl
ψ₀-position x (lim f) dx dy (lim n p) =
  inj₂ (n , ψ₀-position x (f n) dx (dom-at f dy n) p)
ψ₀-position .(lc k c w b t g) (lc k c w b t g) dx dy self = inj₁ refl
ψ₀-position x (lc zero c w b t g) dx dy (fst p) =
  inj₂ (zero , ψ₀-position x (g c (Node₀.seed c w b t g dy)) dx
    (Node₀.branch c w b t g dy c (Node₀.seed c w b t g dy))
    (CP-tr p (Node₀.to-branch c w b t g dy c (Node₀.seed c w b t g dy))))
ψ₀-position x (lc (suc zero) c w b t g) dx dy (fst p) =
  inj₂ (zero , ψ₀-position x (g c (Node₁.seed c w b t g dy)) dx
    (Node₁.branch c w b t g dy c (Node₁.seed c w b t g dy))
    (CP-tr p (Node₁.to-branch c w b t g dy c (Node₁.seed c w b t g dy))))
ψ₀-position x (lc (suc (suc k)) c w b t g) dx dy (fst p) = ⊥-elim (proj₁ dy)
ψ₀-position x (lc (suc (lim f)) c w b t g) dx dy (fst p) = ⊥-elim (proj₁ dy)
ψ₀-position x (lc (suc (lc k c₀ w₀ b₀ t₀ g₀)) c w b t g) dx dy (fst p) =
  ⊥-elim (proj₁ dy)
ψ₀-position x (lc (lim f) c w b t g) dx dy (fst p) = ⊥-elim (proj₁ dy)
ψ₀-position x (lc (lc k c₀ w₀ b₀ t₀ g₀) c w b t g) dx dy (fst p) =
  ⊥-elim (proj₁ dy)

ψ₁-position .zero zero dx dy self = inj₁ refl
ψ₁-position .(suc y) (suc y) dx dy self = inj₁ refl
ψ₁-position x (suc y) dx dy (suc p) =
  inj₂ (zero , ψ₁-position x y dx (dom-pred y dy) p)
ψ₁-position .(lim f) (lim f) dx dy self = inj₁ refl
ψ₁-position x (lim f) dx dy (lim n p) =
  inj₂ (n , ψ₁-position x (f n) dx (dom-at f dy n) p)
ψ₁-position .(lc k c w b t g) (lc k c w b t g) dx dy self = inj₁ refl
ψ₁-position x (lc zero c w b t g) dx dy (fst p) =
  inj₂ (ψ₁-position x t dx (Node₀.first c w b t g dy) p)
ψ₁-position x (lc (suc zero) c w b t g) dx dy (fst p) =
  inj₂ (zero , ψ₁-position x (g c (Node₁.seed c w b t g dy)) dx
    (Node₁.branch c w b t g dy c (Node₁.seed c w b t g dy))
    (CP-tr p (Node₁.to-branch c w b t g dy c (Node₁.seed c w b t g dy))))
ψ₁-position x (lc (suc (suc k)) c w b t g) dx dy (fst p) = ⊥-elim (proj₁ dy)
ψ₁-position x (lc (suc (lim f)) c w b t g) dx dy (fst p) = ⊥-elim (proj₁ dy)
ψ₁-position x (lc (suc (lc k c₀ w₀ b₀ t₀ g₀)) c w b t g) dx dy (fst p) =
  ⊥-elim (proj₁ dy)
ψ₁-position x (lc (lim f) c w b t g) dx dy (fst p) = ⊥-elim (proj₁ dy)
ψ₁-position x (lc (lc k c₀ w₀ b₀ t₀ g₀) c w b t g) dx dy (fst p) =
  ⊥-elim (proj₁ dy)
```

各行用到证书的哪一项：

| 行 | 相关地用 | 只在无关位置用 |
|---|---|---|
| `ψ₁` 保留行 | 无 | 第一支与分支的 `Dom` |
| `ψ₀` 回灌行，`ψ₁` 的 gt 行 | 无 | 分支的 `Dom`；结点里的 `w`, `b` (起点)；`ψ₁-legal`, `ψ₁-nested` (下一点的守卫) |
| `ψ₁-legal` 保留行 | `Legal` 的 `tg`, `dir`；第一支与分支的 `Dom` | |
| `ψ₁-nested` 保留行 | `Seedᶠ` 的根分量 (`Lgl 0 c`, `Nested 0 c`) | |
| `ψ₀-legal` 回灌行，`ψ₁-legal` 的 gt 行 | `Legal.dir`；分支的 `Dom`；`Seedᶠ` 的根分量 (`Lgl 1 c`, `Nested 1 c`) | |
| 位置保持，折叠结点 | `Legal.tg`；`Seedᶠ` 的根分量；下界自身那一支的 `Dom` | |
| 位置保持，保留结点 | 第一支的 `Dom` | |

```agda
certificate-free₀ : ∀ x (d d′ : Dom x) → ψ₀ x d ≡ ψ₀ x d′
certificate-free₀ x d d′ = refl

certificate-free₁ : ∀ x (d d′ : Dom x) → ψ₁ x d ≡ ψ₁ x d′
certificate-free₁ x d d′ = refl
```

## 2 接口实填

```agda
next₀ : ∀ c .(w : Lgl zero c) .(b : Nested zero c) t
  (g : (η : R) → .(Gd zero c η) → LF) →
  .(Dom (lc zero c w b t g)) → Point c → Point c
next₀ c w b t g d =
  Chain.next c
    (λ η e → ψ₀ (g η e) (Node₀.branch c w b t g d η e))
    (λ η e → ψ₀-legal (g η e) (Node₀.branch c w b t g d η e))
    (λ η e → ψ₀-positive (g η e) (Node₀.branch c w b t g d η e))

next₀-grow : ∀ c .(w : Lgl zero c) .(b : Nested zero c) t
  (g : (η : R) → .(Gd zero c η) → LF)
  .(d : Dom (lc zero c w b t g)) (p : Point c) →
  Dn zero (coordinate p) (coordinate (next₀ c w b t g d p))
next₀-grow c w b t g d =
  Chain.grow c
    (λ η e → ψ₀ (g η e) (Node₀.branch c w b t g d η e))
    (λ η e → ψ₀-legal (g η e) (Node₀.branch c w b t g d η e))
    (λ η e → ψ₀-positive (g η e) (Node₀.branch c w b t g d η e))

next₁ : ∀ c .(w : Lgl L1 c) .(b : Nested L1 c) t
  (g : (η : R₁) → .(Gd L1 c η) → LF) →
  .(Dom (lc L1 c w b t g)) → Pt L1 c → Pt L1 c
next₁ c w b t g d =
  Chain₁.next c
    (λ η e → ψ₁ (g η e) (Node₁.branch c w b t g d η e))
    (λ η e → ψ₁-legal (g η e) (Node₁.branch c w b t g d η e))
    (λ η e → ψ₁-nested (g η e) (Node₁.branch c w b t g d η e))
    (λ η e → ψ₁-positive (g η e) (Node₁.branch c w b t g d η e))

next₁-grow : ∀ c .(w : Lgl L1 c) .(b : Nested L1 c) t
  (g : (η : R₁) → .(Gd L1 c η) → LF)
  .(d : Dom (lc L1 c w b t g)) (p : Pt L1 c) →
  Dn L1 (at p) (at (next₁ c w b t g d p))
next₁-grow c w b t g d =
  Chain₁.grow c
    (λ η e → ψ₁ (g η e) (Node₁.branch c w b t g d η e))
    (λ η e → ψ₁-legal (g η e) (Node₁.branch c w b t g d η e))
    (λ η e → ψ₁-nested (g η e) (Node₁.branch c w b t g d η e))
    (λ η e → ψ₁-positive (g η e) (Node₁.branch c w b t g d η e))

fb-rows : FbRows
fb-rows = record
  { Dom = Dom
  ; dom-pred = dom-pred
  ; dom-at = dom-at
  ; dom-first = λ c w b t g → Node₀.first c w b t g
  ; dom-branch₀ = λ c w b t g → Node₀.branch c w b t g
  ; dom-branch₁ = λ c w b t g → Node₁.branch c w b t g
  ; dom-only = λ x d → proj₁ d
  ; dom-legal = λ x d → proj₁ (proj₂ d)
  ; dom-Ω₂ = dom-Ω₂
  ; ψ₀ = ψ₀
  ; ψ₁ = ψ₁
  ; next₀ = λ c w b t g d → next₀ c w b t g d
  ; next₁ = λ c w b t g d → next₁ c w b t g d
  ; zero-row₀ = λ d → refl
  ; suc-row₀ = λ x d → refl
  ; lim-row₀ = λ f d → refl
  ; next₀-additive = λ c w b t g d p → refl
  ; next₀-grow = λ c w b t g d p → next₀-grow c w b t g d p
  ; gt-row₀ = λ c w b t g d → refl
  ; next₁-additive = λ c w b t g d p → refl
  ; next₁-grow = λ c w b t g d p → next₁-grow c w b t g d p
  ; feedback-row = λ c w b t g d → refl
  ; zero-row₁ = λ d → refl
  ; suc-row₁ = λ x d → refl
  ; lim-row₁ = λ f d → refl
  ; keep-row = λ c w b t g d → refl
  ; gt-row₁ = λ c w b t g d → refl
  ; fold-legal₀ = ψ₀-legal
  ; fold-positive₀ = λ x d → ψ₀-positive x d
  ; position₀ = ψ₀-position
  ; fold-legal₁ = ψ₁-legal
  ; fold-nested₁ = ψ₁-nested
  ; fold-grow₁ = λ x d η → grow¹ η (ψ₁ x d) (ψ₁-positive x d)
  ; position₁ = ψ₁-position
  }
```

## 3 输出读回后仍在定义域里

`ψ₁` 的输出合法并带嵌套证据，所以它的读回有证书：折叠的输出可以再作折叠的输入，对 `Dom` 里的一切树，一步。
回灌行用的就是这一条在链点处的情形 (那里证书经分支的 `Dom` 给出)。

```agda
feedback-dom : ∀ x (d : Dom x) → Dom (up L1 (ψ₁ x d) (ψ₁-nested x d))
feedback-dom x d = up1-dom (ψ₁ x d) (ψ₁-legal x d) (ψ₁-nested x d)

feedback-twice : ∀ x (d : Dom x) → Lgl zero
  (ψ₀ (up L1 (ψ₁ x d) (ψ₁-nested x d)) (feedback-dom x d))
feedback-twice x d =
  ψ₀-legal (up L1 (ψ₁ x d) (ψ₁-nested x d)) (feedback-dom x d)
```
