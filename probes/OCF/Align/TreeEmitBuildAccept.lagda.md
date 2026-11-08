# 新底输出继承已验的高值闭项

这是单独的值验收文件，读既有标签参照。新程序与证书不导入本篇。
所接的是完整 ω² 码闭项，不是一个较低首分量。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeEmitBuildAccept where

open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Free.Level
open import OCF.Align.LadderOrdBase using (HtB)
open import OCF.Align.LadderOrdPos using (HB; end)
open import OCF.Align.LadderOrdCode using (ω²ᶜ)
import OCF.Align.LadderOrdMain as G
import OCF.Align.ValLabLadder as V
open import OCF.Align.TreeEmitBuildClosed
open import OCF.Align.ValLabPos using (VV)
open import OCF.Align.OrdLabRead using (tω²)
open import OCF.Align.EmbVVInstO2 using (vv-ω²)
open import OCF.Align.ValueJudgeBase using (≼-trans; ≅→≼)

module All (S : HtB) where
  module N = Rows S
  module O = V S
  new-old : ∀ m a → N.tree m a ≅ O.V m a
  new-old m a = ≅-trans (≅-sym (N.old-new m a))
    (O.V-G m a (G.GᴺTᵠ S m a ev₀ zero))

  fgh-agrees : ∀ m a n → FGH (N.tree m a) n ≡ FGH (O.V m a) n
  fgh-agrees m a = FGH-≅ (new-old m a)

module A = All (HB ω²ᶜ)

transport-value : ∀ {X Y t} → X ≅ Y → VV Y t → VV X t
transport-value eq (Z , lab , old≤Z , Z≤old) = Z , lab ,
  ≼-trans (≅→≼ eq) old≤Z , ≼-trans Z≤old (≅→≼ (≅-sym eq))

closed-value : VV closed tω²
closed-value = transport-value (A.new-old end zero) vv-ω²
```

closed-value 继承 ψ₀(Ω_{Ω·ω²}) 的完整双向值验收；All.new-old 对任意
HtB、全部 m/α 给同形，FGH 也逐点一致。没有把非零参数的 ι↓ 删除
当成已证，没有声明此融合已经达到 EBO 或缩减了多少行。
