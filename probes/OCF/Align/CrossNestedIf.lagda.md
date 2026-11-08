# 高基座上的第一次嵌套绑定反馈

> **草稿状态（2026-11-07）：两次 12G 检查均退出 251，尚未编译通过。停止于历史审查；本接口不得当作已编译结果。继续该义务不构成当前研究决定。**

固定旧算法的实际高起点，不重造低站。first是CrossNext所指α=1
首反馈的同一原表达式，世界参数取已有ω²码。接口同时要求合法
求值证书及继承旧高基座的值界；只填其中一项不算通过本检查。
它不是整个EBO终点，且没有假设该原表达式一定能取得证书。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CrossNestedIf where
open import Data.Product using (_,_)
open import OCF.Free.Level using (zero; suc; Ordᶜ)
open import OCF.Free.Prefix using (Z; toZ)
open import OCF.Free.Floor using (Ev; Fl; _⊔_)
open import OCF.Free.Force using (Goodᴺ; forceᴺ)
open import OCF.Align.LadderOrdPos using (Code)
open import OCF.Align.LadderOrdCode using (ω²ᶜ)
open import OCF.Align.CrossMTop using (ψ̄ᵀ; ψᵀ; ιT; Ω̇ᵀ; module 𝕎; ok₁)
open import OCF.Align.CrossMClosed using (T⊤ᶜ)
open import OCF.Align.ValueJudgeBase using (_≼_)

first : Code → Z
first M = toZ (ψ̄ᵀ {M = M} 𝕎.ok₀ (λ i → 𝕎.ok₀ i , 𝕎.ok₀ i)
  (ψᵀ zero (ιT zero (Ω̇ᵀ M zero))) (ok₁ , ok₁) zero)

record First (M : Code) : Set where
  field
    certificate : Goodᴺ (first M)
    inherits : T⊤ᶜ M ≼ forceᴺ (first M) certificate

HighFirst : Set
HighFirst = First ω²ᶜ
```

该接口不涉及不同裸下标的比较；索引运算均沿原CrossMTop的实际
公共码世界。若此精确旧表达式失败，须给对应否定或保留未走通，
不能以另一条较弱算法满足自身方程代替它。
