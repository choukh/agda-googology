# TreeLevels O8：SumOne 原闭项的上界义务

本篇是第 4 层验收文件。对象固定为原 `SumOneClosed.T₁`，参照固定为
`CtxMonoAccept.Ref`，不改原折叠、合法性或闭项，不由估计读法推出值。
参照的标签是现有 `label-Ref`：ψ₀(Ω_{Ω+1})。本篇先把真实闭项的
上界精确分解到它自身的部分和；这一步不是上界已经成立。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeLevelsO8 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; l≼; ≼l; ≼-refl; ≼-trans; ≅→≼)
open import OCF.Align.CumReadCF using (A; Lg; azero)
open import OCF.Align.TLRuleVar using (trA)
open import OCF.Align.SumOneTree using (pt; Lg-pt)
import OCF.Align.SumOneClosed as S
open import OCF.Align.CumUpAcceptSim using (fr)
import OCF.Align.CtxMonoAccept as C
import OCF.Free.Lab.Correspond as Lab
import OCF.Free.Level as FL
import OCF.Align.Correspond as ALab
open import OCF.Align.Stage2 using (sq; sqLab; Lab-uniq)
open import OCF.Align.Label using (BTBO-label)
open import OCF.Align.NoCumsum using (BTBOᴵ)
open import OCF.Align.SumOneAccept using (T₀≈)
open import OCF.Free.Lab.Uniform3Base using (ψ₀ᵗ)
open import OCF.Free.Lab.Uniform5Label using (Ωs₊)
open import OCF.Align.EBO using (natT)

reference-label : Lab.Lab C.Ref (ψ₀ᵗ (Ωs₊ (natT 1)))
reference-label = C.label-Ref

fr-cong : ∀ {X Y : FL.Ordᶜ FL.zero} → X FL.≅ Y → fr X L.≅ fr Y
fr-cong FL.z≅ = L.z≅
fr-cong (FL.s≅ e) = L.s≅ (fr-cong e)
fr-cong (FL.l≅ h) = L.l≅ (λ n → fr-cong (h n))
fr-cong (FL.lᵢ≅ {p = ()} e h)
fr-cong (FL.upˡ {r = ()} e)
fr-cong (FL.upʳ {r = ()} e)

fr-label : ∀ {X t} → Lab.Lab X t → ALab.Lab (fr X) t
fr-label (Lab.l0 c e) = ALab.l0 c (fr-cong e)
fr-label (Lab.l1 c e h) = ALab.l1 c (fr-cong e) (fr-label h)
fr-label (Lab.lω c e h) = ALab.lω c (fr-cong e) (λ n → fr-label (h n))

reference-label-value : ALab.Lab (fr C.Ref) (ψ₀ᵗ (Ωs₊ (natT 1)))
reference-label-value = fr-label reference-label

sq-below : ∀ (x : L.Ordᶜ L.zero) n → sq x n ≼ x
sq-below L.zero n = ≼-refl _
sq-below (L.suc x) n = ≼-refl _
sq-below (L.lim f) n = ≼l n (≼-refl _)
sq-below (L.limᵢ () f) n
sq-below (L.up () x) n

base-in-reference : BTBOᴵ ≼ fr C.Ref
base-in-reference = ≼-trans
  (≅→≼ (L.≅-sym (Lab-uniq (sqLab reference-label-value refl 0) BTBO-label)))
  (sq-below (fr C.Ref) 0)

prefix : ℕ → A
prefix n = pt S.T₀ S.E₁ n

prefix-legal : ∀ n → Lg (prefix n)
prefix-legal n = Lg-pt S.T₀ S.E₁ n S.Lg-T₀

closed-shape : trA S.T₁ ≡ L.lim (λ n → trA (prefix n))
closed-shape = refl

Upper : Set
Upper = trA S.T₁ ≼ fr C.Ref

upper-from-prefixes : (∀ n → trA (prefix n) ≼ fr C.Ref) → Upper
upper-from-prefixes h = l≼ h

prefixes-from-upper : Upper → ∀ n → trA (prefix n) ≼ fr C.Ref
prefixes-from-upper h n = ≼-trans (≼l n (≼-refl (trA (prefix n)))) h

upper-obligation : ((∀ n → trA (prefix n) ≼ fr C.Ref) → Upper) ×
  (Upper → ∀ n → trA (prefix n) ≼ fr C.Ref)
upper-obligation = upper-from-prefixes , prefixes-from-upper

prefix-zero-upper : trA (prefix zero) ≼ fr C.Ref
prefix-zero-upper = ≼-trans (proj₁ T₀≈) base-in-reference

upper-from-positive-prefixes : (∀ n → trA (prefix (suc n)) ≼ fr C.Ref) → Upper
upper-from-positive-prefixes h = upper-from-prefixes λ
  { zero → prefix-zero-upper
  ; (suc n) → h n
  }
```

`upper-obligation` 是同一个具体闭项上界的双向重述，没有把别的候选的
`Up` 当作这里的前提已证。`CtxMonoAccept.Up` 比较的是 `NoCumNode` 的
另一条链，`SumOneAccept.Up` 比较的是无 `nκ` 基座的 u n，都没有在
本篇被当作 prefix n 的上界。

## 本轮止点

**O8 上界未走通，暂停；没有否定 SumOne。** 已有值前沿仍是
ψ₀(Ω_{Ω·ω²})，本轮没有新增候选闭项或无条件高值下界。

不是把旧 `Rl` 直接套到 `nκ` 后因构造子不符停止：
[TreeLevelsO8Cell](TreeLevelsO8Cell.lagda.md) 已按原 `RunK` 展开闭包，
证明非空上下文里一整格 `κΔ` 的准确模拟，包括极限世界。它仍要求
实际状态满足旧 `Inv`。该条件有具体非空前缀的整格实例
`nonempty-cell`，不是空前提。

接下一外层原轨道时需要原完整 Y₁ = Y₀ ⊕ Δ₀ 的状态模拟。
[TreeLevelsO8State](TreeLevelsO8State.lagda.md) 的
`no-seed-old-Inv` 已证：任给 one ⊲ M、Lg M 和 b : O M，这个
实际 `Y₁` 都不具有旧 `Inv`。其目标 1 分量保留 `nκ`，而旧状态关系
的每个目标分量必须给出不含此构造子的准确 `Rel` 轨道。

因此本轮缺的是**覆盖实际含闭包状态的单向值模拟，并与参照 γ 链的
回灌步相容**。整格的后继与极限世界已经处理；尚未证明错位取项、
上下文吸收或受限的值单调足以代替准确轨道。不增设这些东西为未填
接口字段，不把候选专属上界义务的重述算成上界。

## 实际复用失败

先前第一个 `Step` 的 `Inv-Y′` 不能直接充当完整 `Δ₀` 后的 `Y₁`
的初值。以下 scratch 文件使用同一库选项，编译退出 **42**。
没有洞、公设或跳过检查的指示；失败源只在本文的 text 块保留：

```text
{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns #-}
module TreeLevelsO8Attempt where

open import OCF.Align.SumOneSim using (Inv)
open import OCF.Align.SumOneClosed using (one; Y₁)
open import OCF.Align.SumOneTop using (Inv-Y′; z₁)

seed-inv : Inv {one} Y₁ (z₁ one)
seed-inv = Inv-Y′ one
```

错误原文（仅绝对路径替换为实验目录占位符）：

```text
<scratch>/TreeLevelsO8Attempt.agda:9.12-22: error: [UnequalTerms]
OCF.Align.SumOneTree.D₊.nl
(λ _ →
   OCF.Align.SumOneTree.Ωd t OCF.Align.CumReadCF._⊲_.self lt
   OCF.Align.SumOneTree._.D₊.⨾
   OCF.Align.SumOneFold.Df.yc
   (OCF.Align.SumOneFold.St.d OCF.Align.SumOneClosed.Y₀) τ lt)
!=
OCF.Align.SumOneFold.Df.yc
(OCF.Align.SumOneClosed.Run OCF.Align.SumOneClosed.accTop
 OCF.Align.SumOneTree.D₊.n1 (OCF.Align.CumReadCF.z⊲ one)
 Agda.Builtin.Unit.tt Agda.Builtin.Unit.tt OCF.Align.SumOneClosed.A₁
 OCF.Align.SumOneTree.D₊.n0 OCF.Align.SumOneClosed.Y₀)
τ lt
OCF.Align.SumOneTree._.D₊.⨾
OCF.Align.SumOneFold.Df.yc
(OCF.Align.SumOneClosed.Run OCF.Align.SumOneClosed.accTop
 (OCF.Align.SumOneTree.D₊.nκ Agda.Builtin.Unit.tt
  (λ {c} _ _ →
     OCF.Align.SumOneTree.D₊.ni OCF.Align.CumReadCF._⊲_.self
     (λ _ _ _ → OCF.Align.SumOneTree.D₊.n1)))
 (OCF.Align.CumReadCF.z⊲ one) Agda.Builtin.Unit.tt
 Agda.Builtin.Unit.tt OCF.Align.SumOneClosed.A₁
 (OCF.Align.SumOneTree.D₊.n0 OCF.Align.SumOneTree._.D₊.⨾
  OCF.Align.SumOneTree.D₊.nw (OCF.Align.CumReadCF.z⊲ one)
  OCF.Align.SumOneTree.D₊.n1)
 (OCF.Align.SumOneClosed.Y₀ OCF.Align.SumOneClosed.⊕
  OCF.Align.SumOneClosed.Run OCF.Align.SumOneClosed.accTop
  OCF.Align.SumOneTree.D₊.n1 (OCF.Align.CumReadCF.z⊲ one)
  Agda.Builtin.Unit.tt Agda.Builtin.Unit.tt OCF.Align.SumOneClosed.A₁
  OCF.Align.SumOneTree.D₊.n0 OCF.Align.SumOneClosed.Y₀))
τ lt
of type
OCF.Align.SumOneTree.D₊ (λ _ k → OCF.Align.CumReadCF.Strict k t)
(λ {_} → OCF.Align.SumOneTree.Ws t) (OCF.Align.SumOneTree.NZ t)
(OCF.Align.SumOneClosed.wm τ)
when checking that the expression Inv-Y′ one has type
Inv Y₁ (z₁ one)
```

这个失败本身只说明该复用未通过检查；`no-seed-old-Inv` 进一步把它
加强成对这个旧 `Inv` 的定理。两者都不是所求上界的否定。

## 复现与成本

从仓库根目录，三份成功文件分别运行：

```sh
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/TreeLevelsO8.lagda.md +RTS -M6G -RTS
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/TreeLevelsO8Cell.lagda.md +RTS -M6G -RTS
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/TreeLevelsO8State.lagda.md +RTS -M6G -RTS
```

失败复现另用仓库外实验目录：

```sh
agda --library-file=<库文件> -i src -i probes -i <实验目录> <实验目录>/TreeLevelsO8Attempt.agda +RTS -M6G -RTS
```

这批只增加第 4 层的关系与定理，不增加树构造子或闭项，不改原定义。
`add-Rl` 继承旧和关系的证明形状，整格证明按原 `Walk` / `WRp`
的结构扩展固定前缀；不读记号的基本列规则来添加树字段。
