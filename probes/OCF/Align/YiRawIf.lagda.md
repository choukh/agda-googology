# YiRaw 接口：写在第 K 层的树上的折叠，派发读树里的位置

**档位：定义、编译定理 (派发完全且不多保留)、规范实例检查、一个接口记录。没有折叠，没有值。** 构造路 (`YiRawFold*`) 与否定路
(`YiRawNeg*`) 共用本文件；定稿后只增不改。输入是 `Raw K` 的树：结点 `G.lc r …` 自带它在 `K` 里的位置 `r`，公共上界就是字面的 `K`；
派发用规范比较 [YiLvNegCanon](YiLvNegCanon.lagda.md) 的 `ccompare`，读相关的 `Legal K`。上一步的接口是 [YiLvIf](YiLvIf.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiRawIf where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck
open import OCF.Align.YiIrrIf
open import OCF.Align.YiLvIf
open import OCF.Align.YiLvNegCompare using (At; no-both; no-same; branch₃)
open import OCF.Align.YiLvNegCanon using (ccompare)
open import OCF.Align.YiLvFoldBase using (Way; keep; fold)
open import OCF.Align.YiLvFoldFin using (IsKeep; ω; ω-plain; ω-legal)
```

## 1 目标

在公共上界 `K` 里，折叠的目标层有三种：第 0 层；`K` 自己；`K` 里的一个位置上的层号。
链的推进用结点自己那一层的折叠，所以目标必须能取到 `K` 的每个位置。

```agda
data Tgt (K : LF) : Set where
  base : Tgt K
  self : Tgt K
  at   : Pre K → Tgt K

tlev : ∀ K → Tgt K → LF
tlev K base = zero
tlev K self = K
tlev K (at q) = lev K q
```

## 2 派发

目标 `τ`，结点在位置 `r`。第 0 层之下没有位置，一律折叠；目标是 `K` 自己时，位置 `r` 本身就是槽位；
目标在位置 `q` 时问规范比较，只有 "结点层在目标层之下" 保留。"相等" 与 "之上" 都折叠。

```agda
tri→way : ∀ {i j} → Tri i j → Way i j
tri→way (below s e) = keep s e
tri→way (above s e) = fold
tri→way (same e) = fold

dispatch : ∀ K → Plain K → Legal K → (τ : Tgt K) (r : Pre K) → Way (tlev K τ) (lev K r)
dispatch K pl L base r = fold
dispatch K pl L self r = keep r refl
dispatch K pl L (at q) r = tri→way (ccompare K pl L q r)
```

派发完全：结点层在目标层的某个位置上，就保留。派发不多保留：保留时交出的就是这样一个位置。
这两条是强度所在；输出合法对任意派发都成立 ([YiLvFold](YiLvFold.lagda.md))，不说明强度。

```agda
tri-complete : ∀ {i j} (t : Tri i j) → At i j → IsKeep (tri→way t)
tri-complete (below s e) a = tt
tri-complete (above s e) a = no-both a (s , e)
tri-complete (same e) a = no-same a e

dispatch-complete : ∀ K pl L τ r → At (tlev K τ) (lev K r) → IsKeep (dispatch K pl L τ r)
dispatch-complete K pl L base r (() , e)
dispatch-complete K pl L self r a = tt
dispatch-complete K pl L (at q) r a = tri-complete (ccompare K pl L q r) a

way-sound : ∀ {i j} (y : Way i j) → IsKeep y → At i j
way-sound (keep s e) h = s , e

dispatch-sound : ∀ K pl L τ r → IsKeep (dispatch K pl L τ r) → At (tlev K τ) (lev K r)
dispatch-sound K pl L τ r = way-sound (dispatch K pl L τ r)
```

## 3 规范实例检查

上一步只读裸层号的派发在目标层 `suc ω` 上漏掉层号 ω (`YiLvFoldLim.bare-incomplete`)。
这里取公共上界 `suc (suc ω)`：目标在根的位置 (层号 `suc ω`)，结点在它下面一格 (层号 ω)，派发保留，槽位是根。

```agda
K₂ : LF
K₂ = suc (suc ω)

test-keep-ω : dispatch K₂ ω-plain ω-legal (at (inj₁ tt)) (inj₂ (inj₁ tt)) ≡ keep (inj₁ tt) refl
test-keep-ω = refl

test-fold-same : IsKeep (dispatch K₂ ω-plain ω-legal (at (inj₁ tt)) (inj₁ tt)) → ⊥
test-fold-same ()

-- 极限处两个不同分支上的位置: 目标层号 3 (第 4 支的根), 结点层号 1 (第 2 支的根).
test-cross : IsKeep (dispatch ω ω-plain ω-legal (at (4 , inj₁ tt)) (2 , inj₁ tt))
test-cross = tt
```

塔的第 3 项与它的各支都是 `top` 的读回。所以它们的折叠可以陈述成 `Raw` 上的折叠在 `top` 处的值：
第 η 支用公共上界 `read0 η`，整个 `tw 3` 用公共上界 `tw 2`。

```agda
tw₃-is-top : tw 3 ≡ up (tw 2) G.top tt
tw₃-is-top = refl

branch-is-top : ∀ η .(e : Gd zero raw1 η) →
  branch₃ η e ≡ up (up zero η (proj₂ (proj₂ e))) G.top tt
branch-is-top η e = refl
```

## 4 接口记录

`Φ K pl L τ ξ` 把 `Raw K` 的树 `ξ` 折到目标 `τ`。`K` 的合法性是相关参数 (比较要读它)；`ξ` 的证书是块自己的
`Lgl K ξ` 与 `Nested K ξ`，无关。记录只写两条携带强度的律与两条合法性的律：

- `keep-law`：结点层在目标层的位置上，输出是保留结点 (`YiLvIf.Kept`)；
- `fold-law`：否则输出是 ℕ 极限；
- `position`：输入是字面第一位置，输出也是 (两份证书各自任意，它们无关)；
- `legal`：输出合法。

链的行 (下一点是这一点加上结点自己那一层的折叠在这一点的分支上的输出) 由构造路按自己的加法写出并交代；记录里不写，免得把加法定死。

```agda
IsLim : ∀ {m} → Raw m → Set
IsLim (G.lim f) = ⊤
IsLim _ = ⊥

record RawFold : Set where
  field
    Φ : ∀ K → Plain K → Legal K → (τ : Tgt K) (ξ : Raw K) →
      .(Lgl K ξ) → .(Nested K ξ) → Raw (tlev K τ)
    keep-law : ∀ K pl L τ r c t g
      (l : Lgl K (G.lc r c t g)) (nb : Nested K (G.lc r c t g)) →
      At (tlev K τ) (lev K r) →
      Kept (tlev K τ) (lev K r) (Φ K pl L τ (G.lc r c t g) l nb)
    fold-law : ∀ K pl L τ r c t g
      (l : Lgl K (G.lc r c t g)) (nb : Nested K (G.lc r c t g)) →
      (At (tlev K τ) (lev K r) → ⊥) →
      IsLim (Φ K pl L τ (G.lc r c t g) l nb)
    position : ∀ K pl L τ ξ ξ′ (l : Lgl K ξ) (nb : Nested K ξ)
      (l′ : Lgl K ξ′) (nb′ : Nested K ξ′) → Cp K ξ ξ′ →
      Cp (tlev K τ) (Φ K pl L τ ξ l nb) (Φ K pl L τ ξ′ l′ nb′)
    legal : ∀ K pl L τ ξ (l : Lgl K ξ) (nb : Nested K ξ) →
      Lgl (tlev K τ) (Φ K pl L τ ξ l nb)
```

记录有没有实例，本文件没有证，也没有否定。`legal` 若还需要 `K` 的证书一致 ([YiLvNegRestrict](YiLvNegRestrict.lagda.md) 的 `Coh` 一类)，
构造路把前提加在自己的陈述里并说明，否定路可以去证这个前提是否必要。
