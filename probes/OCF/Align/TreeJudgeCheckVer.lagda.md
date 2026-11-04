# 树侧判据: `ver` 的树上 Bachmann 取样 (拒绝不了)

> **检验旧树的文件, 读记号的项 `tA`** (只用它算两棵树). 判据的定义不在这里. 结论写在 [TreeJudge](TreeJudge.lagda.md). **有限测试.** `ver` 的树在 `tA` 上偏离 EBO (`ver-dev`), 路径 $[1,0,0,1,0,0,0]$. 这个取样 (深 6) 够不到那条路径的深度, `Reg⁰` 也不报. 所以 `ver` 的拒绝靠 `Vis` (`reject-ver`), 不靠 `Reg⁰`. 这里只记录这一条拒绝不了, 不说更深也拒绝不了.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeJudgeCheckVer where

open import Data.List using (List; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.InaccTreeBase as B using (Ordᴸ; Tree; ver)
open import OCF.Align.InaccStrikeAccept using (tA)
open import OCF.Align.InaccTreeAccept using (module Tr⁰)
open import OCF.Align.InaccStrikeOracle using (D★)
open import OCF.Align.TreeJudgeObs

open Tr⁰ D★ using () renaming (⟦_⟧⁰ to ⟪_⟫)
open Tr⁰ ver using () renaming (⟦_⟧⁰ to ⟦_⟧ᵛ)

rdL : Ordᴸ B.zero → Obs
rdL Tree.zero = o0
rdL (Tree.suc x) = os (rdL x)
rdL (Tree.lim f) = ol (λ n → rdL (f n))

reg-ver : reg 6 30 4 2 [] (rdL ⟦ tA ⟧ᵛ) ≡ okv 96 22
reg-ver = refl

reg-D★ : reg 6 30 4 2 [] (rdL ⟪ tA ⟫) ≡ okv 96 22
reg-D★ = refl
```
