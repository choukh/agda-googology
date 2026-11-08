# 裸数据下降不能无条件删除

同一实际有限高度段、同一界为 2 的世界。omk 的两部分特意取不同值：
原解释选第二部分 qs q0，下降先读取第一部分 q0。注意原 ψ̄ 的零读成 1，
后继读成重复极限；因此底输出是 lim 与 suc zero，不能误说成输出 1 与 0。
这里只否定共享 RawDownErase；
原 Ω̇ 的生成节点满足另一种关联，不能由此否定其生成域上的改写。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeEmitNegRaw where

open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import OCF.Free.Level
open import OCF.Free.Floor using (Ev; flo; toFlo)
open import OCF.Free.Tree using (Fl)
open import OCF.Free.Eq using (_≅ˢ_)
open import OCF.Align.LadderOrdPos using (HB; cs; cz; end; low)
import OCF.Align.LadderOrdTree
import OCF.Align.TreeEmitIf

module T = OCF.Align.LadderOrdTree (HB (cs cz))
module I = OCF.Align.TreeEmitIf (HB (cs cz))
open T

w : Ht → Ordᴵ
w _ = suc (suc zero)

ok : Ok w
ok _ = tt , (λ { zero → suc zero })

e₀ : Eh h₀ (low end) w (κ Fl)
e₀ i h r = ok i

e₁ : Eh h₀ end w (cap (κ Fl) (low end) (flo (suc zero)))
e₁ (low end) h r = toFlo (suc zero) (λ { zero → suc zero })
e₁ (low (low ())) h r
e₁ end h ()

x : Q (low end) (suc zero) Fl (κ Fl)
x = omk zero q0 (qs q0)

ev : Ev (suc zero) Fl
ev = tt , (λ { zero → zero })

no-instance : ¬ (ψ̄ᵠ ok e₀ x ev zero ≅ˢ
  ψ̄ᵠ ok e₁ (ι↓ {α = zero} tt x) ev zero)
no-instance ()

no-raw-down-erase : ¬ I.RawDownErase
no-raw-down-erase law = no-instance
  (I.RawDownErase.erase law tt ok e₀ e₁ x ev)
```
