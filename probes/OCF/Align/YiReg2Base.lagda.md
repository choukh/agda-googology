# Reg₂：给 ℕ 极限增加严格第一位置证据

按作者指定形状另定义 Reg₂，不改 Reg 或其它已有定义。
lc 行相同，lim 行增加相邻项的 Y.Proper；这是携带的树路径，不是值比较或判定器。
本接口固定后不因后续反例修补形状。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiReg2Base where

open import Data.Unit.Base using (⊤; tt)
open import Data.Product.Base using (_×_; _,_)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (suc)
open import Relation.Binary.PropositionalEquality using (_≡_)
import OCF.Align.LevelFixCore as F
import OCF.Align.YiLevelBase as Y
open import OCF.Align.YiDispBase using (Below; DispEv; choice; keep; RetainedDomain)
import OCF.Align.YiRegBase as R
import OCF.Align.YiRegCover as C
import OCF.Align.YiDispHigher as N

Reg₂ : F.LF → Set
Reg₂ F.zero = ⊤
Reg₂ (F.suc x) = Reg₂ x
Reg₂ (F.lim f) =
  (∀ n → Y.Proper (f n) (f (suc n))) × (∀ n → Reg₂ (f n))
Reg₂ (F.lc k c t g) =
  Below (F.suc k) (F.lc k c t g) × Reg₂ k × Reg₂ t × (∀ η e → Reg₂ (g η e))

forget : ∀ x → Reg₂ x → R.Reg x
forget F.zero r = tt
forget (F.suc x) r = forget x r
forget (F.lim f) (step , rf) = λ n → forget (f n) (rf n)
forget (F.lc k c t g) (bound , rk , rt , rg) =
  bound , forget k rk , forget t rt , (λ η e → forget (g η e) (rg η e))

no-proper-zero : Y.Proper F.zero F.zero → ⊥
no-proper-zero ()

no-zero-limit : Reg₂ (F.lim (λ _ → F.zero)) → ⊥
no-zero-limit (step , rf) = no-proper-zero (step 0)

no-old-node : Reg₂ (Y.tree N.j) → ⊥
no-old-node r = R.no-old-counter (forget (Y.tree N.j) r)

all-retained-reg₂ : (i j : Y.Level) → Reg₂ (Y.tree j) →
  (ev : DispEv (Y.tree i) (Y.tree j)) →
  choice ev ≡ keep → RetainedDomain (Y.tree i) j
all-retained-reg₂ i j r = C.all-retained-reg i j (forget (Y.tree j) r)
```

forget 直接删去新严格性证据，故沿用第十轮全层保留覆盖，不复制或改动旧证明。
它仍只给派发位置，不给 Ω 封闭、输出 Reg₂ 或回灌保持。

已读 [BrwViewNeg.strict→LPO](BrwViewNeg.lagda.md)：该定理要求值映射 val 的
后继值满足 asuc(val(f n))≤val(f(n+1))，并有任意二进制序列的 Enc 族。
本篇只有语法第一位置 Proper，没有到上述值关系的转换、值上的严格 View 或 Enc；
因此没有实填该定理的前提，也不据 Proper 字段声称值上严格递增。
严格性字段来自 no-omega-preservation 暴露的常零极限缺口，未从记号规则取字段。
