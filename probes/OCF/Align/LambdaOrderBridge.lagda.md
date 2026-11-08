# 终点接口两种值序的连接

验收专用，导入 Value 的记号依赖，不进入候选定义。
上一轮通用接口使用 OCFSpecBase，EBO 草案使用 Value；两者不能靠
构造子同名混用。这里逐推导转换，消除这一接口缺口。不提供强度下界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LambdaOrderBridge where

open import OCF.Align.Level using (Ordᶜ)
import OCF.Align.OCFSpecBase as S
import OCF.Align.Value as V

forward : ∀ {i j} {a : Ordᶜ i} {b : Ordᶜ j} → a S.≼ b → a V.≼ b
forward S.z≼ = V.z≼
forward (S.s≼s p) = V.s≼s (forward p)
forward (S.≼l n p) = V.≼l n (forward p)
forward (S.l≼ p) = V.l≼ (λ n → forward (p n))
forward (S.≼i x e p) = V.≼i x e (forward p)
forward (S.i≼ p) = V.i≼ (λ x e → forward (p x e))
forward (S.≼u p) = V.≼u (forward p)
forward (S.u≼ p) = V.u≼ (forward p)

backward : ∀ {i j} {a : Ordᶜ i} {b : Ordᶜ j} → a V.≼ b → a S.≼ b
backward V.z≼ = S.z≼
backward (V.s≼s p) = S.s≼s (backward p)
backward (V.≼l n p) = S.≼l n (backward p)
backward (V.l≼ p) = S.l≼ (λ n → backward (p n))
backward (V.≼i x e p) = S.≼i x e (backward p)
backward (V.i≼ p) = S.i≼ (λ x e → backward (p x e))
backward (V.≼u p) = S.≼u (backward p)
backward (V.u≼ p) = S.u≼ (backward p)
```

翻译账：只增加验收推导的转换；不修改树、折叠或合法性。
