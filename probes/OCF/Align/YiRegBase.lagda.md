# 树侧正则性：每个 Ω 字段的后继在结点下出现

按本轮候选形状定义 Reg，不改 LF、Legal、Raw、Gd 或 Below。
它保存位置证据，递归覆盖字段、第一支及原 Gd 的每个合法分支；不是判定器。
ℕ极限只递归要求各支 Reg，暂不增加其它正则性条件。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiRegBase where

open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product.Base using (_×_; _,_)
open import OCF.Align.LevelFixCore using (LF)
import OCF.Align.LevelFixCore as F
open import OCF.Align.YiDispBase using (Edge; Below; one; more; e-suc; e-lim; e-first; e-branch; below-trans)
import OCF.Align.YiCtxBase as K
import OCF.Align.YiLevelBase as Y
open import OCF.Align.YiRCountable using (Small; small-zero; small-suc; small-lim)
import OCF.Align.YiDispHigher as N

Reg : LF → Set
Reg F.zero = ⊤
Reg (F.suc x) = Reg x
Reg (F.lim f) = ∀ n → Reg (f n)
Reg (F.lc k c t g) =
  Below (F.suc k) (F.lc k c t g) × Reg k × Reg t × (∀ η e → Reg (g η e))

small-reg : ∀ {x} → Small x → Reg x
small-reg small-zero = tt
small-reg (small-suc r) = small-reg r
small-reg (small-lim r) = λ n → small-reg (r n)

reg-fields : ∀ {x} → Reg x → ∀ {k} → K.Field k x → Below (F.suc k) x
reg-fields r (K.in-suc p) = more (reg-fields r p) e-suc
reg-fields r (K.in-lim n p) = more (reg-fields (r n) p) (e-lim n)
reg-fields (bound , rk , rt , rg) K.at = bound
reg-fields (bound , rk , rt , rg) (K.in-index p) =
  below-trans (reg-fields rk p) (below-trans (one e-suc) bound)
reg-fields (bound , rk , rt , rg) (K.in-first p) = more (reg-fields rt p) e-first
reg-fields (bound , rk , rt , rg) (K.in-branch η e p) = more (reg-fields (rg η e) p) (e-branch η e)

edge-reg : ∀ {a b} → Edge a b → Reg b → Reg a
edge-reg e-suc r = r
edge-reg (e-lim n) r = r n
edge-reg e-first (bound , rk , rt , rg) = rt
edge-reg (e-branch η e) (bound , rk , rt , rg) = rg η e

below-reg : ∀ {a b} → Below a b → Reg b → Reg a
below-reg (one e) r = edge-reg e r
below-reg (more p e) r = below-reg p (edge-reg e r)

no-old-counter : Reg (Y.tree N.j) → ⊥
no-old-counter (bound , rk , rt , rg) = N.no-below-j bound
```

reg-fields 在 lc.k 情况不把字段自动当成下界：先用该结点显式的 bound，
再接 k→suc k 的路径。no-old-counter 则准确排除第九轮退化 Ω 结点。
Reg 的形状来自编译否定 no-next-ev 所揭露的字段界缺口，不读记号。
