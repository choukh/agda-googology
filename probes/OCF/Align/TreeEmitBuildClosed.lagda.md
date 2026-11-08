# 直接底输出的全部行及高值闭项

本模块不读标签。运行先 emit 实际 Ω̇ 源，证书沿原轨道运输；没有将
已求出的 V 外包成程序。证书仍继承原 Ladder 闭包，不声称全部脚手架已消。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeEmitBuildClosed where

open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; toZ)
open import OCF.Free.Floor using (Ev)
open import OCF.Free.Tree using (Fl)
open import OCF.Free.Force using (Goodᴺ; forceᴺ; forceᴺ-HS)
open import OCF.Free.OrbitRewriteBuild using (move)
open import OCF.Align.LadderOrdBase using (HtB)
open import OCF.Align.LadderOrdPos using (HB; end)
open import OCF.Align.LadderOrdCode using (ω²ᶜ)
import OCF.Align.LadderOrdTree as T
import OCF.Align.LadderOrdMain as G
import OCF.Align.TreeEmitBuild as E

ev₀ : Ev (suc zero) Fl
ev₀ = tt , (λ q → q)

module Rows (S : HtB) where
  open T S
  module B = E S
  raw : Ht → Ordᴵ → Z
  raw m a = B.emit ok₀ (λ i h r → ok₀ i) (Ω̇ m a) ev₀ zero

  opaque
    good : ∀ m a → Goodᴺ (raw m a)
    good m a = proj₁ (move (B.sound ok₀ (λ i h r → ok₀ i) (Ω̇ m a) ev₀ zero) (G.GᴺTᵠ S m a ev₀ zero))

    tree : Ht → Ordᴵ → Ordᶜ zero
    tree m a = forceᴺ (raw m a) (good m a)

    legal : ∀ m a → HS (tree m a)
    legal m a = forceᴺ-HS (raw m a) (good m a)

    old-new : ∀ m a → forceᴺ _ (G.GᴺTᵠ S m a ev₀ zero) ≅ tree m a
    old-new m a = proj₂ (move (B.sound ok₀ (λ i h r → ok₀ i) (Ω̇ m a) ev₀ zero) (G.GᴺTᵠ S m a ev₀ zero))

module High = Rows (HB ω²ᶜ)

closed : Ordᶜ zero
closed = High.tree end zero

closed-legal : HS closed
closed-legal = High.legal end zero

fgh : ℕ → ℕ
fgh = FGH closed
```

这里 closed 是原 ω² 码全部行机制的新解释结果；已验值的具体强度只在
独立验收文件连接，不让标签进入 raw/good/closed 的依赖。
