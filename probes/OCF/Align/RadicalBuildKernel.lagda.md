# 单字段执行核与原生成分支

这里没有调用 GᴺTᵠ。全上下文精确方程从原 sh≡E 实填；后继与极限
实例覆盖原 FΩ 的全部参数，不限某一个标记。尚未把反馈坐标 Q 重写
为新容器，所以这只是可执行的第一切口，不算自产高闭项或成本下降。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.RadicalBuildKernel (𝕊 : HtB) where

open import Data.Nat using (ℕ)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; subst)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Ordˢ)
open import OCF.Free.Floor using (Flr; Ev)
open import OCF.Free.Tree using (Fl)
open import OCF.Align.LadderOrdTree 𝕊
open import OCF.Align.LadderOrdCx 𝕊
open import OCF.Align.LadderOrdStrict 𝕊 using (Up; sh; dh)
open import OCF.Align.LadderOrdOmega 𝕊 using (sh≡E)
open import OCF.Align.RadicalBuildIf 𝕊

execute : ∀ {m k ℓ φ χ} {r : k ◃₁ ℓ} → Cx m ℓ φ χ → Mark m r φ χ → Ordˢ zero
execute {r = r} C (mark z) = runᶜ (sh r C) z

exact : ∀ {m k ℓ φ χ} (r : k ◃₁ ℓ) (C : Cx m ℓ φ χ) (z : Q m k φ χ) → execute {r = r} C (mark z) ≡ runᶜ C (Up r z)
exact r C z = sh≡E r C (dh C) z

contract : MarkExecution
contract = record { execute = execute ; exact = exact }

-- 原后继 Ω̇ 的所有低层回调坐标，含不可数节点的任意 z。
module Successor (m : Ht) (k : Ordᴵ) (ξ : Flr) (ζ : Fv) where
  lower : Sub m (lo m ζ ∪ κ Fl) ζ
  lower i q e = subst (Ev _) (lo-lt ζ q) (proj₁ e)

  old : Q m k ξ ζ → Q m (suc k) (ξ OCF.Free.Floor.⊔ Fl) (lo m ζ ∪ κ Fl)
  old z = qwk proj₁ lower (omk zero z (ι zero z))

  read : (C : Cx m (suc k) (ξ OCF.Free.Floor.⊔ Fl) (lo m ζ ∪ κ Fl)) → Q m k ξ ζ → Ordˢ zero
  read C z = execute {r = zero} (wkC proj₁ lower C) (mark z)

  read-exact : ∀ C z → read C z ≡ runᶜ C (old z)
  read-exact C z = trans (exact zero (wkC proj₁ lower C) z)
    (run-wkC proj₁ lower C (Up zero z))

-- 原极限 Ω̇ 的全部分支；mark 不存原来的 ι(self i)副本。
module Limit (m : Ht) (f : ℕ → Ordᴵ) (s : ∀ n → f n ⊑ᴵ f (Data.Nat.suc n)) where
  branch : (i : ℕ) → Mark m (self {f = f} {s = s} i) Fl (κ Fl)
  branch i = mark (Ω̇ m (f i))

  read-exact : ∀ i (C : Cx m (lim f s) Fl (κ Fl)) → execute C (branch i) ≡
    runᶜ C (omk (self i) (Ω̇ m (f i)) (ι (self i) (Ω̇ m (f i))))
  read-exact i C = exact (self i) C (Ω̇ m (f i))
```

剩余不是 equality 或 FE：新的 mark 坐标目前仍是原 Q。若改成新容器，
qΩ/chain 的输入和所有 ψ、Ψ、搬运也须整体改为该容器，并独立产生
合法证书；本篇未把旧 GᴺTᵠ 包成新证书，也未宣称此整体改写已完成。
