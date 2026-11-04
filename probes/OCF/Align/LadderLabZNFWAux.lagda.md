> **机械克隆, 验收用.** 由 `LadderNFWAux` 经 `Survey/scripts/ladderlab/mkworld.py` 复制, 只改模块名; 见 [LadderLab](LadderLab.lagda.md). 下面的文字是原文.

# 标签世界的名字表 (Aux)

> 验收用. 把 `OCF.Free.Aux` 的名字指向标签阶梯世界的原定义. 见 [LadderNFAccept](LadderNFAccept.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderLabZNFWAux where

open import OCF.Align.Symbolic public using (Fs; Fst; Mlev)
open import OCF.Align.LadderLabZUniformS public using (kd; kd-≅; tf; ≅ᴵ→⊑ᴵ; ⊑ᴵ-≅ʳ; ⊑ᴵ-≅ˡ)
open import OCF.Align.LadderLabZDecouple public using (one⁰)
open import OCF.Align.LadderLabZOmegaExpBase public using (σ⊥)
```
