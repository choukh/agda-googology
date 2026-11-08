# 高起点原反馈：显式类型参数

> **状态（2026-11-07）：子代理记录显式程序 6G 检查退出 0，主审未在停止后重编；没有合法证书和值定理，不计新强度。相关 CrossNestedIf 未通过；本组已停止续建，先作历史审查。**

仅把原 `first` 表达式的隐参数写出，隔离类型推断成本。
没有改树、初值、分支或回灌链；本篇不导入待检查的共享接口。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CrossNestedBuildTerm where
open import Data.Product using (_,_)
open import OCF.Free.Level using (zero; suc)
open import OCF.Free.Prefix using (Z; toZ)
open import OCF.Free.Floor using (_⊔_)
open import OCF.Free.Tree using (Fl)
open import OCF.Align.LadderOrdPos using (Code)
open import OCF.Align.CrossMTop using (ψ̄ᵀ; ψᵀ; ιT; Ω̇ᵀ; module 𝕎; ok₁; κ′)

first : Code → Z
first M = toZ (ψ̄ᵀ {M = M} {α = zero} {φ = Fl ⊔ Fl}
  {χ = 𝕎.Z* (κ′ Fl)} {w = 𝕎.w₀}
  𝕎.ok₀ (λ i → 𝕎.ok₀ i , 𝕎.ok₀ i)
  (ψᵀ {M = M} {α = suc zero} {t = zero} zero
    {φ = Fl} {χ = κ′ Fl}
    (ιT {M = M} {a = zero} {b = suc zero} zero
      {φ = Fl} {χ = κ′ Fl} (Ω̇ᵀ M zero)))
  (ok₁ , ok₁) zero)
```
