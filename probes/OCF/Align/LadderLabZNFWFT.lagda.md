> **机械克隆, 验收用.** 由 `LadderNFWFT` 经 `Survey/scripts/ladderlab/mkworld.py` 复制, 只改模块名; 见 [LadderLab](LadderLab.lagda.md). 下面的文字是原文.

# 标签世界的名字表 (Tree)

> 验收用. 把 `OCF.Free.Tree` 的名字指向标签阶梯世界的原定义. 见 [LadderNFAccept](LadderNFAccept.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderLabZNFWFT where

open import OCF.Align.LadderLabZUniform4Two public using (<◃; RestrO; TΩ·2; resO; restrO; res⁻O; trO; tr⁻O)
open import OCF.Align.LadderLabZUniform4Base public using (Fl; O; Us; asl; asr; chainᵒ; dupr2; intoU; outU; repᵒ; swp; tl; Ω̇; ι; ψ̄; ψᵒ)
open import OCF.Align.LadderLabZUniform3Base public using (_⊕_)
```
