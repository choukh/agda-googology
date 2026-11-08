# 获准遗传生成域的独立实例复核

本篇是正面审查入口，不是否定定理。五个冻结模块保持原 Q 与原
Ω̇；这里重新陈述全部高度、全部 OrdI 参数的生成证书，并给出
实际 HBω² 端点实例。它不声明 ψ、Ψ 或新 run 已经保持该域。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TotalValueNegAdmittedReview where
open import OCF.Align.LadderOrdBase using (HtB)
open import OCF.Free.Level using (Ordᴵ; zero; suc)
import OCF.Align.LadderOrdTree as Tree
import OCF.Align.TotalValueBuildAdmittedGenIf as I
import OCF.Align.TotalValueBuildAdmittedGenFloor as F
import OCF.Align.TotalValueBuildAdmittedGenUp as U
import OCF.Align.TotalValueBuildAdmittedGenDown as D

module At (S : HtB) where
  open Tree S
  open I S

  all-floor : ∀ m a → Gen m a (Ω̇ m a)
  all-floor = F.omega-gen S

  raised : ∀ {m a b φ χ} (r : a OCF.Free.Level.◃ b)
    {x : Q m a φ χ} → Gen m a x → Gen m b (ι r x)
  raised = U.raise S

  lowered : ∀ {m m′ a b φ χ} (δ : m <ᴸ m′)
    {x : Q m a φ χ} → Gen m a x → Gen m′ b (ι↓ δ x)
  lowered = D.descend S

open import OCF.Align.LadderOrdCode using (ω²ᶜ)
open import OCF.Align.LadderOrdPos using (HB; end)
module Actual where
  module T = Tree (HB ω²ᶜ)
  module G = I (HB ω²ᶜ)
  module Check = At (HB ω²ᶜ)

  whole : ∀ a → G.Gen end a (T.Ω̇ end a)
  whole = Check.all-floor end

  original-zero : G.Gen end zero (T.Ω̇ end zero)
  original-zero = whole zero

  nonzero : G.Gen end (suc zero) (T.Ω̇ end (suc zero))
  nonzero = whole (suc zero)
```

qi 的坐标域是原结构自相关坐标，不是所有 raw 函数；tl-core 用输入的
结构关系给出这一域的真实实例。marker 低字段也需 Gen，并保 body 的
字面 ι 方程。整个关系是验收用证书，没有修改树构造子或坐标算法。
它既不提供全局下标比较，也不推出坐标同值即相容。恢复折叠仍须另外
证明实际反馈坐标及搬运后的 marker 继续满足相应关系。
