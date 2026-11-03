# 无记号主线: 桥 (验收)

> **验收文件, 不在主线闭包内.** 记号与标签只在这里和 [Lab/](Lab/) 里出现. 结论先说:
>
> 1. **标签的重新检查 (`OCF.Free.Lab.*`).** 原标签链 `UniformNF5Accept` 的定义级切片, 去掉主线已有的块, 代码行逐字, 导入改指 `OCF.Free.*`, 在主线的定义上重新通过类型检查 (50 个模块). 所以 `FA.ATΩ·2.label-TΩ·2 : Lab (forceᴺ _ (GᴺTΩ·2 ev z)) tΩ·2` 说的就是主线的树, 不是副本. 只有 `OCF.Align.EBO` 没有复制: 两个世界共用同一个记号类型 `T`.
> 2. **`bridge`: 主线的树就是原来带标签的树.** 主线与 `OCF.Align` 的数据类型是两份, 字面相同但不是同一个类型, 所以 `refl` 不适用; 这里用 `⟦_⟧` 把第 0 层的树搬过去, 结论是 $\cong$, 对两边的任意环境成立. 证明是 `Lab-uniq` 的跨世界形式 `cross`: 两棵树带同一个标签 (`same-t` 是 `refl`), 就互模拟.
> 3. **`label-on-free`, `fgh-bridge`:** 原世界的 `Lab` 能直接贴在主线的树上; FGH 跨世界逐点相等. 这说明提取没有改变任何东西.
> 4. **有限测试:** `fgh-0` 跨世界 `refl`. 不是证明.
>
> 依赖是"原标签链仍然通过" (`UniformNF5Accept`), 而不是对树的逐构造子比较: 如果主线的定义被改动而标签仍然成立, `bridge` 依然成立, 这正是 $\cong$ 的本意.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.Bridge where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)

-- 主线
import OCF.Free.Level as F
import OCF.Free.Floor as FF
import OCF.Free.Tree as FT
import OCF.Free.Force as FG
import OCF.Free.Main as FM
import OCF.Free.Closed as FC
-- 主线之上重新检查的标签
import OCF.Free.Lab.Correspond as FL
import OCF.Free.Lab.Uniform4TwoWalk as FW
import OCF.Free.Lab.UniformNF5Accept as FA
-- 原来的标签世界
import OCF.Align.Level as A
import OCF.Align.Uniform3Base as AF
import OCF.Align.Uniform4Base as AB
import OCF.Align.NotFree as AG
import OCF.Align.UniformNF5Main as AM
import OCF.Align.Correspond as AL
import OCF.Align.Uniform4TwoWalk as AW
import OCF.Align.UniformNF5Accept as AA
```

## §1 跨世界的搬运

第 0 层没有 `limᵢ`, `up`, 所以 `⟦_⟧` 是结构递归, `⟦≅⟧` 把主线的 $\cong$ 搬到原世界. `FGH-⟦⟧`: FGH 不变.

```agda
⟦_⟧ : F.Ordᶜ F.zero → A.Ordᶜ A.zero
⟦ F.zero ⟧ = A.zero
⟦ F.suc x ⟧ = A.suc ⟦ x ⟧
⟦ F.lim f ⟧ = A.lim (λ n → ⟦ f n ⟧)
⟦ F.limᵢ () f ⟧
⟦ F.up () x ⟧

⟦≅⟧ : ∀ {x y : F.Ordᶜ F.zero} → x F.≅ y → ⟦ x ⟧ A.≅ ⟦ y ⟧
⟦≅⟧ F.z≅     = A.z≅
⟦≅⟧ (F.s≅ e) = A.s≅ (⟦≅⟧ e)
⟦≅⟧ (F.l≅ h) = A.l≅ (λ n → ⟦≅⟧ (h n))
⟦≅⟧ (F.lᵢ≅ {p = ()} e h)
⟦≅⟧ (F.upˡ {r = ()} e)
⟦≅⟧ (F.upʳ {r = ()} e)

FGH-⟦⟧ : ∀ x n → F.FGH x n ≡ A.FGH ⟦ x ⟧ n
FGH-⟦⟧ F.zero     n = refl
FGH-⟦⟧ (F.suc x)  n = F.iter-ext (FGH-⟦⟧ x) n n
FGH-⟦⟧ (F.lim f)  n = FGH-⟦⟧ (f n) n
FGH-⟦⟧ (F.limᵢ () f) n
FGH-⟦⟧ (F.up () x)   n
```

## §2 同一个标签, 同一棵树

`cross` 是 Stage2 的 `Lab-uniq` 换成两个世界: `Lab` 的基本列方程读的是同一个 `T`.

```agda
cross : ∀ {X Y t} → FL.Lab X t → AL.Lab Y t → ⟦ X ⟧ A.≅ Y
cross (FL.l0 c e) (AL.l0 c′ e′) = A.≅-trans (⟦≅⟧ e) (A.≅-sym e′)
cross (FL.l0 c e) (AL.l1 c′ e′ l′) with trans (sym c) c′
... | ()
cross (FL.l0 c e) (AL.lω c′ e′ h′) with trans (sym c) c′
... | ()
cross (FL.l1 c e l) (AL.l0 c′ e′) with trans (sym c) c′
... | ()
cross (FL.l1 c e l) (AL.l1 c′ e′ l′) = A.≅-trans (⟦≅⟧ e) (A.≅-trans (A.s≅ (cross l l′)) (A.≅-sym e′))
cross (FL.l1 c e l) (AL.lω c′ e′ h′) with trans (sym c) c′
... | ()
cross (FL.lω c e h) (AL.l0 c′ e′) with trans (sym c) c′
... | ()
cross (FL.lω c e h) (AL.l1 c′ e′ l′) with trans (sym c) c′
... | ()
cross (FL.lω c e h) (AL.lω c′ e′ h′) = A.≅-trans (⟦≅⟧ e) (A.≅-trans (A.l≅ (λ n → cross (h n) (h′ n))) (A.≅-sym e′))

same-t : FW.tΩ·2 ≡ AW.tΩ·2
same-t = refl
```

## §3 桥

```agda
module _ {ℓ} (ev : FF.Ev ℓ (FT.Fl FF.⊔ FF.fk F.zero)) (z : F.zero F.<ᴵ ℓ)
         {ℓ′} (ev′ : AF.Ev ℓ′ (AB.Fl AF.⊔ AF.fk A.zero)) (z′ : A.zero A.<ᴵ ℓ′) where

  bridge : ⟦ FG.forceᴺ _ (FM.GᴺTΩ·2 ev z) ⟧ A.≅ AG.forceᴺ _ (AM.GᴺTΩ·2 ev′ z′)
  bridge = cross (FA.ATΩ·2.label-TΩ·2 ev z) (AA.ATΩ·2.label-TΩ·2 ev′ z′)

  label-on-free : AL.Lab ⟦ FG.forceᴺ _ (FM.GᴺTΩ·2 ev z) ⟧ AW.tΩ·2
  label-on-free = AL.Lab-≅ bridge (AA.ATΩ·2.label-TΩ·2 ev′ z′)

  fgh-bridge : ∀ n → F.FGH (FG.forceᴺ _ (FM.GᴺTΩ·2 ev z)) n ≡ A.FGH (AG.forceᴺ _ (AM.GᴺTΩ·2 ev′ z′)) n
  fgh-bridge n = trans (FGH-⟦⟧ _ n) (A.FGH-≅ bridge n)
```

## §4 闭项

`FC.TΩ₂` 就是 §3 在 `FC.ev₀` 上的实例; 原世界一侧取同样的环境.

```agda
aev₀ : AF.Ev (A.suc A.zero) (AB.Fl AF.⊔ AF.fk A.zero)
aev₀ = (tt , (λ q → q)) , (λ q → q)

TΩ₂ᴬ : A.Ordᶜ A.zero
TΩ₂ᴬ = AG.forceᴺ _ (AM.GᴺTΩ·2 aev₀ A.zero)

TΩ₂-bridge : ⟦ FC.TΩ₂ ⟧ A.≅ TΩ₂ᴬ
TΩ₂-bridge = bridge FC.ev₀ F.zero aev₀ A.zero

TΩ₂-label : AL.Lab ⟦ FC.TΩ₂ ⟧ AW.tΩ·2
TΩ₂-label = label-on-free FC.ev₀ F.zero aev₀ A.zero

fgh-all : ∀ n → FC.fgh n ≡ A.FGH TΩ₂ᴬ n
fgh-all = fgh-bridge FC.ev₀ F.zero aev₀ A.zero

fgh-0 : FC.fgh 0 ≡ A.FGH TΩ₂ᴬ 0
fgh-0 = refl
```
