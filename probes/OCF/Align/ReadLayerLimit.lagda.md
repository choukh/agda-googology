# 读回包在有种类覆盖的 ℕ-极限处闭合

后继读回包现已能生成自己的编码。本篇在极限处也返回同一种记录：
每一分支的新增种类须有实际嵌入，放进共同目标结构。该嵌入可由
ReadLayerCofinal 的后继覆盖构造，不从“极限合法”自动推出。

复用原 NdI/RG、种类嵌入和后继扩张，不重写运行器。下面的 omega
实际使用新后继族生成全分支及编码；已有 ω 读回是前例，不算新高度。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ReadLayerLimit where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (Ht; Wd₂; LgW₂; D; sl; ss)
open import OCF.Align.FamFoldIf using (Sk)
open import OCF.Align.FamFoldRead using (ly)
open import OCF.Align.LvRdEmb using (Emb; ιE; compE)
open import OCF.Align.LvRdPkg using (NdI)
import OCF.Align.UniformReaderStep as Step
open import OCF.Align.UniformReaderReify hiding (round; round-legal)
open import OCF.Align.ReadLayerCofinal using (SuccessorCover; new-kind)

module Join (F : ℕ → KS) (L : ℕ → Ht)
  (P : ∀ n → RenderingReader (F n) (L n))
  (coverage : ∀ n → Emb (step (F n)) (sup ℕ F)) where

  module At {V : KS} (e : Emb (sup ℕ F) V) where
    next : ∀ n → NdI V (hs (L n))
    next n = Step.Extend.next (Read.context (P n)) (compE (coverage n) e)

    base : NdI V (L zero)
    base = RenderingReader.nodes (P zero) (compE (ιE zero) e)

    nodes : NdI V (hl L)
    nodes = record
      { ndR = λ { (sl n p) b s → NdI.ndR (next n) (ss p) b s }
      ; fsR = λ { (sl n p) b s → NdI.fsR (next n) (ss p) b s }
      ; lgR = λ { (sl n p) fs lb ls → NdI.lgR (next n) (ss p) fs lb ls }
      ; eA = NdI.eA base ; eM = NdI.eM base }

  joined : RenderingReader (sup ℕ F) (hl L)
  joined = record
    { nodes = At.nodes
    ; render = λ { p (n , κ) g W →
        RenderingReader.render (P n) (⊲ᴮ-tr (hlim n hself) p) κ g W } }

-- 由树侧的字面后继覆盖提供 coverage，不要求比较两个裸高度。
cofinal : ∀ {S : KS} {f : ℕ → HB S} {w : Wd S}
  (L : ℕ → Ht) → SuccessorCover ℕ f w →
  (∀ n → RenderingReader (Lev (f n)) (L n)) →
  RenderingReader (sup ℕ (λ n → Lev (f n))) (hl L)
cofinal {f = f} L c P = Join.joined (λ n → Lev (f n)) L P (new-kind c)

Gω : KS
Gω = sup ℕ (λ n → Sk (suc n))

Lω : Ht
Lω = hl (λ n → ly (suc (suc n)))

omega : RenderingReader Gω Lω
omega = Join.joined (λ n → Sk (suc n)) (λ n → ly (suc (suc n))) family
  (λ n → ιE (suc n))

-- 极限的包仍可输入同一个后继扩张；不是只交了单向 reader。
omega-successor : RenderingReader (step Gω) (hs Lω)
omega-successor = Successor.next omega

round : ∀ {W} → LgW₂ W → HB Gω → HB Gω
round {W} lW x = Read.read omega lW hz (Read.encodeAt omega hself x W)

round-legal : ∀ {W} (lW : LgW₂ W) x → LgB (round lW x)
round-legal {W} lW x = Read.legal omega lW hz (Read.encodeAt omega hself x W) tt
```

## 对任意已实现读回包的一条 ω 闭包

不是为 ω、ω+1 分别增加专属编码。给任意已实现的起包，同一后继
递归及同一 Join 形成新的极限包，起包可以包含已经形成的极限。

```agda
module Climb (T : KS) (L : Ht) (P : RenderingReader T L) where
  kinds : ℕ → KS
  kinds zero = T
  kinds (suc n) = step (kinds n)

  layers : ℕ → Ht
  layers zero = L
  layers (suc n) = hs (layers n)

  packages : ∀ n → RenderingReader (kinds n) (layers n)
  packages zero = P
  packages (suc n) = Successor.next (packages n)

  closed : RenderingReader (sup ℕ kinds) (hl layers)
  closed = Join.joined kinds layers packages (λ n → ιE (suc n))

  layers-legal : LgB L → ∀ n → LgB (layers n)
  layers-legal l zero = l
  layers-legal l (suc n) = layers-legal l n

  closed-layer-legal : LgB L → LgB (hl layers)
  closed-layer-legal l = (λ _ → hsuc hself) , layers-legal l
```

joined 的 coverage、全部分支包和编码均有实例。它没有把未来原世界
改成全种类事件世界：仍是 Wd₂；render 也仍只接受对全部世界成立
的源层路径。Ω-极限的准入、世界局部路径、读回保值与实际全事件
运行的连接均未由此推出，不能将本结果称为 ψ₀Λ 闭项或强度下界。
