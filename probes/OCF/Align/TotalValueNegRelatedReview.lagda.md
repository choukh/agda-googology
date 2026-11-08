# 关系 marker 全生成域与搬运的独立审查

marker 的 body Core 来自原 body 子树递归，不是预先要求折叠保持。
低坐标 Gen 按较低 OrdI/HtB 递归；整个域未把待证 ψ/Ψ 闭包放入定义。
下列入口复核全部 Ω̇ 与实际 HBω² 端点，并加载后继/极限两向搬运。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TotalValueNegRelatedReview where
open import OCF.Align.LadderOrdBase using (HtB)
open import OCF.Free.Level
import OCF.Align.LadderOrdTree as T
import OCF.Align.TotalValueBuildRelatedGenIf as I
import OCF.Align.TotalValueBuildRelatedGenFloor as F
import OCF.Align.TotalValueBuildRelatedGenUp as U
import OCF.Align.TotalValueBuildRelatedGenDown as D
import OCF.Align.TotalValueBuildRelatedGenOps as Ops
import OCF.Align.TotalValueTransportSuccessor as Succ
import OCF.Align.TotalValueTransportLimit as Lim
import OCF.Align.TotalValueTransportMarker as Marker

module At (S : HtB) where
  open T S
  open I S
  whole : ∀ m a → Gen m a (Ω̇ m a)
  whole = F.omega-gen S
  raised : ∀ {m a b φ χ} (r : a ◃ b) {x : Q m a φ χ} →
    Gen m a x → Gen m b (ι r x)
  raised = U.raise S
  lowered : ∀ {m m′ a b φ χ} (δ : m <ᴸ m′) {x : Q m a φ χ} →
    Gen m a x → Gen m′ b (ι↓ δ x)
  lowered = D.descend S
  open Ops S public using (add; repeat; chain-gen)
  open Succ S public using (successor-marker; successor-marker-back)
  open Lim S public using (limit-marker; limit-marker-back)
  open Marker S public using (erase-tr-marker)

open import OCF.Align.LadderOrdCode using (ω²ᶜ)
open import OCF.Align.LadderOrdPos using (HB; end)
module Actual where
  module Tree = T (HB ω²ᶜ)
  module Domain = I (HB ω²ᶜ)
  original : ∀ a → Domain.Gen end a (Tree.Ω̇ end a)
  original = At.whole (HB ω²ᶜ) end
```

Ops.chain-gen 的回调保持仍是显式条件，并没有以自己证明自己。
Floor 的零行由 base 的 tl 自相关、clos 的真实下降、chain 的全部
原分量组成；后继与极限 marker 的 body Core 由 raise 实填，Rq
由 R-ι 实填。所得证书非空，仍不自动证明运行恢复或值比较。
