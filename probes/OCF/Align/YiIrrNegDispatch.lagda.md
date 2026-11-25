# YiIrrNeg 第 5 项（预告）：派发的位置证据何时必须是数据

**判决。** 编译定理两条，其余是判断。目标层 1：三路由层号的构造子形状判定，保留结点的位置数据唯一，所以位置证据不必作为数据给折叠。
一般的目标层：保留结点里的位置 `r : Pre y` 不能由无关证据恢复（`locate→irr-search`），那里它必须是数据。
不否定第一次回灌；没有写目标层 1 的折叠，也没有测塔上的目标层 `tw n`（n ≥ 2）。入口 [YiIrrNeg](YiIrrNeg.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiIrrNegDispatch where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck
open import OCF.Align.YiIrrIf
open import OCF.Align.YiIrrNegWide
  using (Found; IrrSearch; seen; seen-hit; seen-found; mark; high; high-legal)
```

目标层 1 是 `suc zero`。结点层号为 0 则保留，为 1 则折叠，其余不属于这一层的片段。
`Pre (suc zero)` 只有一个元素，保留结点的分支仍以无关的守卫为参数。

```agda
data Way : Set where
  retain collapse other : Way

way₁ : LF → Way
way₁ zero = retain
way₁ (suc zero) = collapse
way₁ (suc (suc k)) = other
way₁ (suc (lim f)) = other
way₁ (suc (lc k c w b t g)) = other
way₁ (lim f) = other
way₁ (lc k c w b t g) = other

way₁-retain : ∀ k → way₁ k ≡ retain → k ≡ zero
way₁-retain zero p = refl
way₁-retain (suc zero) ()
way₁-retain (suc (suc k)) ()
way₁-retain (suc (lim f)) ()
way₁-retain (suc (lc k c w b t g)) ()
way₁-retain (lim f) ()
way₁-retain (lc k c w b t g) ()

way₁-collapse : ∀ k → way₁ k ≡ collapse → k ≡ suc zero
way₁-collapse zero ()
way₁-collapse (suc zero) p = refl
way₁-collapse (suc (suc k)) ()
way₁-collapse (suc (lim f)) ()
way₁-collapse (suc (lc k c w b t g)) ()
way₁-collapse (lim f) ()
way₁-collapse (lc k c w b t g) ()

Pre₁-unique : (r r′ : Pre (suc zero)) → r ≡ r′
Pre₁-unique (inj₁ tt) (inj₁ tt) = refl
Pre₁-unique (inj₁ tt) (inj₂ ())
Pre₁-unique (inj₂ ()) r′

retain₁ : (c : R) → Raw (suc zero) →
  ((η : R) → .(Gd zero c η) → Raw (suc zero)) → Raw (suc zero)
retain₁ c t g = G.lc (inj₁ tt) c t g

retain₁-read : ∀ c t g (nb : Nested (suc zero) (retain₁ c t g)) →
  up (suc zero) (retain₁ c t g) nb ≡
  lc zero c (proj₁ nb) (proj₁ (proj₂ nb))
    (up (suc zero) t (proj₁ (proj₂ (proj₂ nb))))
    (λ η e → up (suc zero) (g η e) (proj₂ (proj₂ (proj₂ nb)) η e))
retain₁-read c t g nb = refl
```

一般的目标层。`high α = lim (mark (seen α m))` 是合法的层号；它的位置集合 `Pre (high α)`
非空当且仅当 `α` 有见证。所以凭无关证据交出位置，就是无关证据的搜索。
`high α` 不在规范塔的读回域内；这条只说明 "位置是数据" 在一般层号上不能省。

```agda
pre-mark : ∀ x → x ≡ true → Pre (mark x)
pre-mark .true refl = inj₁ tt

mark-pre : ∀ x → Pre (mark x) → x ≡ true
mark-pre true r = refl
mark-pre false ()

found→pre : ∀ α → Found α → Pre (high α)
found→pre α (n , p) = n , pre-mark (seen α n) (seen-hit α n p)

target-legal : ∀ α → Legal (high α)
target-legal = high-legal

locate→irr-search : (∀ α → .(Pre (high α)) → Pre (high α)) → IrrSearch
locate→irr-search loc α s with loc α (found→pre α s)
... | m , r = seen-found α m (mark-pre (seen α m) r)
```

判断（未测）：塔上的目标层 `tw n`（n ≥ 2）里，给定结点层号找它在目标层里的位置，
要在无穷分支里搜索并比较层号，同样要数据；这一条没有写成定理。
