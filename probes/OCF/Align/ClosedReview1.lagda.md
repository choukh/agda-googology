# 闭项设计审查 (一): 位置代替层号, 选择性更新不判定, 按层号读才判定

> 不含记号. 配合 [Survey/ClosedTermReview.md](../../Survey/ClosedTermReview.md) §2 的方案 D1. 抽象实验: 层号类型 `L` 任意 (可以有函数分支, 如 `LFReTy.LH` 或 `HtTowerTy.HB S`), 每层的高度 `H ℓ` 与第一位置 `⊲` 任意, 只假设 "合法公共上界之下可比" (`cmp`, 即 `HtTowerTy.cmpB` 的形状).
>
> 世界不是 $\prod_{\ell : L} H\,\ell$, 而是**有限的望远镜** `Tel lvs`: 层号列表 `lvs` 放在**类型里**, 每个位置一个界. 种类 (折叠要升高的那一层) 由**位置** `Pos lvs` 指认, 位置的层号 `lv p` 由查表**定义地**给出, 从头到尾没有一个 `ℓ ≡ ℓ′`.
>
> - `upd`, `at`, `off`: 恰好改一个位置的界、其余不动, 是定义; `off` 只用位置的不等 (位置可判定, `decPos`). 对照 `DiagKLev.upd→wdec`: 那里下标是高度, 同样的 `at`/`off` 推出高度相等的弱判定; 这里下标是位置, 层号只在类型里.
> - `push`, `wk`: 推入新层 (长塔) 与旧位置的弱化, 旧界原样 (`bnd-wk`, `refl`).
> - `cmpK`: 同一位置之下的两个坐标可比, 只要该位置的界合法.
> - **`find→dec`** (反面): 若能**按层号找位置** (对一切 `lvs`, `ℓ` 答 "有这一层" 或 "没有"), 则 `L` 的相等可判定. 所以望远镜世界把判定从 "写" 挪到了 "读": $\prod_\ell$ 世界按层读免费、选择性写要判定 (`DiagKLev`); 望远镜世界选择性写免费、按层读要判定 (本篇). 折叠若要在望远镜世界上走, 就不能按层号找, 只能沿路径**携带位置**.
>
> 另一个写法 (上下文是 `List (Σ L H)`, 有界的证据带一个 `ℓ ≡ ℓ′`) 在 `--without-K` 下写不下去: 同一条目被两次引用时要把两个 `ℓ ≡ ℓ` 认同, 报 `Cannot eliminate reflexive equation ℓ = ℓ of type L because K has been disabled` (判断: `L` 有函数分支, 没有 Hedberg). 这说明证据必须是**定义的** (位置), 不能是命题相等. 这正是把层号放进类型里的理由.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ClosedReview1 where

open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

module Tele
  (L : Set) (H : L → Set)
  (_⊲_ : ∀ {ℓ} → H ℓ → H ℓ → Set)
  (Lg : ∀ {ℓ} → H ℓ → Set)
  (cmp : ∀ {ℓ} {b c c′ : H ℓ} → Lg b → c ⊲ b → c′ ⊲ b → c ⊲ c′ ⊎ c′ ⊲ c)
  where

  -- 望远镜: 层号在类型里, 每个位置一个界
  data Tel : List L → Set where
    []  : Tel []
    _∷_ : ∀ {ℓ lvs} → H ℓ → Tel lvs → Tel (ℓ ∷ lvs)

  data Pos : List L → Set where
    z : ∀ {ℓ lvs} → Pos (ℓ ∷ lvs)
    s : ∀ {ℓ lvs} → Pos lvs → Pos (ℓ ∷ lvs)

  lv : ∀ {lvs} → Pos lvs → L
  lv (z {ℓ}) = ℓ
  lv (s p) = lv p

  bnd : ∀ {lvs} → Tel lvs → (p : Pos lvs) → H (lv p)
  bnd (b ∷ Γ) z = b
  bnd (b ∷ Γ) (s p) = bnd Γ p

  -- 有界: 坐标是该位置的界的第一位置. 层号由位置定义地给出
  Bd : ∀ {lvs} (p : Pos lvs) → H (lv p) → Tel lvs → Set
  Bd p c Γ = c ⊲ bnd Γ p

  -- 恰好改一个位置
  upd : ∀ {lvs} (p : Pos lvs) → H (lv p) → Tel lvs → Tel lvs
  upd z x (b ∷ Γ) = x ∷ Γ
  upd (s p) x (b ∷ Γ) = b ∷ upd p x Γ

  at : ∀ {lvs} (p : Pos lvs) x (Γ : Tel lvs) → bnd (upd p x Γ) p ≡ x
  at z x (b ∷ Γ) = refl
  at (s p) x (b ∷ Γ) = at p x Γ

  s-inj : ∀ {ℓ lvs} {p q : Pos lvs} → s {ℓ} p ≡ s q → p ≡ q
  s-inj refl = refl

  off : ∀ {lvs} (p : Pos lvs) x (Γ : Tel lvs) q → ¬ (p ≡ q) → bnd (upd p x Γ) q ≡ bnd Γ q
  off z x (b ∷ Γ) z ne = ⊥-elim (ne refl)
  off z x (b ∷ Γ) (s q) ne = refl
  off (s p) x (b ∷ Γ) z ne = refl
  off (s p) x (b ∷ Γ) (s q) ne = off p x Γ q (λ e → ne (cong s e))

  -- 位置相等可判定 (不看 L)
  decPos : ∀ {lvs} (p q : Pos lvs) → (p ≡ q) ⊎ ¬ (p ≡ q)
  decPos z z = inj₁ refl
  decPos z (s q) = inj₂ (λ ())
  decPos (s p) z = inj₂ (λ ())
  decPos (s p) (s q) with decPos p q
  ... | inj₁ refl = inj₁ refl
  ... | inj₂ ne = inj₂ (λ e → ne (s-inj e))

  -- 长塔: 推入新层, 旧位置弱化, 旧界原样
  push : ∀ {ℓ lvs} → H ℓ → Tel lvs → Tel (ℓ ∷ lvs)
  push = _∷_

  wk : ∀ {ℓ lvs} → Pos lvs → Pos (ℓ ∷ lvs)
  wk = s

  bnd-wk : ∀ {ℓ lvs} (b : H ℓ) (Γ : Tel lvs) p → bnd (push b Γ) (wk p) ≡ bnd Γ p
  bnd-wk b Γ p = refl

  -- 同一位置之下可比 (cmpK 的形状)
  cmpK : ∀ {lvs} (Γ : Tel lvs) p {c c′} → Lg (bnd Γ p) → Bd p c Γ → Bd p c′ Γ → c ⊲ c′ ⊎ c′ ⊲ c
  cmpK Γ p l e e′ = cmp l e e′

  -- 反面: 按层号找位置 ⇒ L 的相等可判定
  Find : Set
  Find = ∀ (lvs : List L) (ℓ : L) → (Σ (Pos lvs) (λ p → lv p ≡ ℓ)) ⊎ (∀ (p : Pos lvs) → ¬ (lv p ≡ ℓ))

  find→dec : Find → ∀ (ℓ ℓ′ : L) → (ℓ ≡ ℓ′) ⊎ ¬ (ℓ ≡ ℓ′)
  find→dec f ℓ ℓ′ with f (ℓ ∷ []) ℓ′
  ... | inj₁ (z , q) = inj₁ q
  ... | inj₁ (s () , q)
  ... | inj₂ none = inj₂ (none z)
```
