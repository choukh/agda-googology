# 纯可数层读回后的字段界

本篇只补充分支相对路径所需的树侧辅助结论，不改树、守卫或不变量。
Small 表示只有零、后继、ℕ极限的层号树；它不额外假定合法性。
Fields B t 则把 t 的全部语法字段派发位置都放在 B 下，包含下标内部与所有合法分支。
结论只在 Small 层成立，不推广成任意层的单一公共界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiRCountable where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_)
open import OCF.Align.LevelFixCore using (LF; Raw; Pre; Low; GdL; Kid; KidR)
import OCF.Align.LevelFixCore as F
open F using (module G)
open import OCF.Align.LevelFixVal using (CP; CP-tr)
import OCF.Align.LevelFixVal as V
open import OCF.Align.YiCtxBase using (Field)
import OCF.Align.YiCtxBase as K

data Small : LF → Set where
  small-zero : Small F.zero
  small-suc : ∀ {x} → Small x → Small (F.suc x)
  small-lim : ∀ {f} → (∀ n → Small (f n)) → Small (F.lim f)

Fields : LF → LF → Set
Fields B t = ∀ {k} → Field k t → CP (F.suc k) B

fields-mono : ∀ {a b t} → CP a b → Fields a t → Fields b t
fields-mono q p f = CP-tr (p f) q

small-no-field : ∀ {t} → Small t → ∀ {k} → Field k t → ⊥
small-no-field small-zero ()
small-no-field (small-suc s) (K.in-suc p) = small-no-field s p
small-no-field (small-lim s) (K.in-lim n p) = small-no-field (s n) p

raw0-small : (η : Raw F.zero) → Small (V.up F.zero η)
raw0-small G.zero = small-zero
raw0-small (G.suc η) = small-suc (raw0-small η)
raw0-small (G.lim f) = small-lim (λ n → raw0-small (f n))
raw0-small (G.lc () c t g)
raw0-small (G.em () t)
raw0-small G.top = small-suc small-zero
```

下面的结点辅助律把下标内部字段排除：Small 下标本身不含 Ω 结点。
第一支和所有分支的字段都由调用者给出同一个 ambient 界。
upN 沿 Pre 位置下降时，结点的派发字段始终是原 Small 层的 CP。

```agda
node-fields : ∀ {B j c t g} → Small j → CP (F.suc j) B →
  Fields B t → (∀ η e → Fields B (g η e)) → Fields B (F.lc j c t g)
node-fields sj q pt pg K.at = q
node-fields sj q pt pg (K.in-index p) = ⊥-elim (small-no-field sj p)
node-fields sj q pt pg (K.in-first p) = pt p
node-fields sj q pt pg (K.in-branch η e p) = pg η e p

upN-fields : ∀ {B} (y : LF) → Small y → (r : Pre y) (c : Low y r)
  (t : LF) (g : (η : Low y r) → GdL y r c η → LF) →
  CP y B → Fields B t → (∀ η e → Fields B (g η e)) →
  Fields B (V.upN y r c t g)
upN-fields F.zero small-zero ()
upN-fields (F.suc y) (small-suc sy) (inj₁ _) c t g q pt pg =
  node-fields sy q pt pg
upN-fields (F.suc y) (small-suc sy) (inj₂ r) c t g q pt pg =
  upN-fields y sy r c t g (CP-tr (V.suc V.self) q) pt pg
upN-fields (F.lim f) (small-lim sf) (n , r) c t g q pt pg =
  upN-fields (f n) (sf n) r c t g (CP-tr (V.lim n V.self) q) pt pg
```

读回、嵌入读回与结构 Ω 的三条结论互相递归。
Raw 的 top 调用结构 Ω；结构 Ω 的后继支调用下一低层的读回。
它们保持全部字段的界，不要求读回值本身位于这个界，也不要求坐标之间全局可比。

```agda
mutual
  omega-fields : ∀ x → Small x → Fields x (V.Ω̂ x)
  omega-fields F.zero small-zero (K.in-suc ())
  omega-fields (F.suc y) (small-suc sy) =
    node-fields sy V.self
      (fields-mono (V.suc V.self) (omega-fields y sy))
      (λ η e → fields-mono (V.suc V.self) (up-fields y sy η))
  omega-fields (F.lim f) (small-lim sf) (K.in-lim n p) =
    CP-tr (omega-fields (f n) (sf n) p) (V.lim n V.self)

  up-fields : ∀ y → Small y → (η : Raw y) → Fields y (V.up y η)
  up-fields y sy G.zero ()
  up-fields y sy (G.suc η) (K.in-suc p) = up-fields y sy η p
  up-fields y sy (G.lim f) (K.in-lim n p) = up-fields y sy (f n) p
  up-fields y sy (G.lc r c t g) =
    upN-fields y sy r c (V.up y t) (λ η e → V.up y (g η e)) V.self
      (up-fields y sy t) (λ η e → up-fields y sy (g η e))
  up-fields y sy (G.em i t) = upK-fields y sy i t
  up-fields y sy G.top = omega-fields y sy

  upK-fields : ∀ y → Small y → (i : Kid y) → (t : KidR y i) →
    Fields y (V.upK y i t)
  upK-fields F.zero small-zero ()
  upK-fields (F.suc y) (small-suc sy) i t =
    fields-mono (V.suc V.self) (up-fields y sy t)
  upK-fields (F.lim f) (small-lim sf) n t =
    fields-mono (V.lim n V.self) (up-fields (f n) (sf n) t)
```

前提并不为空。除最小后继层外，任意零层 raw 坐标的读回都提供 Small 实例，
故下条推论覆盖原 Ω_Ω 的每个零层坐标，而不需要把 rawNat 函数识别成 natF。
构造合法分支的界时，合法性仍由原守卫及 lgl→Legal 提供。

```agda
one-small : Small (F.suc F.zero)
one-small = small-suc small-zero

one-omega-fields : Fields (F.suc F.zero) (V.Ω̂ (F.suc F.zero))
one-omega-fields = omega-fields (F.suc F.zero) one-small

raw0-omega-fields : ∀ η → Fields (V.up F.zero η) (V.Ω̂ (V.up F.zero η))
raw0-omega-fields η = omega-fields (V.up F.zero η) (raw0-small η)
```

这些 Fields 结论可供每支单独选界使用，并不为外层所有分支制造公共界。
fields-mono 只运输 Fields；没有假设或证明新 Path 在扩界下单调。
本篇也没有定义 γ 或 ψ。
