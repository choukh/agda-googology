# 冻结折叠合法性的实际输入族接口

接口定稿 2026-11-06。先解决上一轮非恒定闭项的中间合法性，而不要求
任意受限树自动合法。`BaseAction` 精确针对 `FrozenOmegaClosed.base`。
它的坐标可以含旧 Ω 节点，并不是纯可数片段。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.FrozenLegalIf where
open import OCF.Lean.CRwBase
open import OCF.Lean.FrozenOmegaIf
open import OCF.Lean.FrozenOmegaClosed using (U; w; M; module F; base)

act : HB U → HB (SafeTw U w hz)
act c = F.fold hz (z⊲ᴮ M) (base c)

record BaseAction : Set₁ where
  field
    position : ∀ {a b v} → a ⊲[ v ] b → act a ⊲[ v ] act b
    legal : ∀ c → LgB c → LgB (act c)
```

这里公共界是右侧 b，路径显式给出；没有裸下标比较。对于一般输入，
Fold1 的模式需要输入世界 `ext v W`，而非当前接口固定的 v：保留
节点分支的 Bd/Pr 必须沿 ext 对齐，坍缩坐标链还要合法。
本接口只证明本例不需要这些额外跨分量搬运，不把它当作一般 ext。
