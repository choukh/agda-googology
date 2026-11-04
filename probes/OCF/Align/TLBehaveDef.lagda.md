# 对象在折叠下怎么行动 (一): 判据的定义

> 入口 [TLBehave](TLBehave.lagda.md). **只有定义, 导入闭包不含记号.** 语言是 `WorldTH` 的数据树 `𝓞 p a u`.
>
> **时间线.** 写这个文件时读了 `WorldTHW`, `WorldTHLe`, `WorldTHGrow`, `WorldTHInst`, `CumReadBase`, `CumReadCF`, `ValueJudgeBase`. 这一轮没有打开 `*Accept`, `EBO`. **不盲:** 前两轮看过 `fs-1`, `fs-2`, `lt-b`; `WorldTH` 的正文写了读法; 任务书提示了 "左极限" 这个方向.
>
> 判据有两半.
>
> - **`Abs₁ p` (折叠一次被吸收).** 第 $p$ 行折叠一次的对象 `Ω̇ p one`, 是语言里某一行第 0 层 `Ω̇ p′ azero` 的第一位置. 这句话只提第一位置, 不提绑定.
> - **`Ad y` (读到的高度跟着世界走).** 沿第一位置走, 能走到一个闭包节点, 它的每个分支读到的高度都盖住这个分支所在的世界 (`Cov`). 世界又盖住上一个输出 (`next`), 所以读到的高度高过已经产生的值 (`read-above`, [TLBehaveThm](TLBehaveThm.lagda.md)).
>
> **这一层走到头** 读作: 每一行折叠一次都被吸收 (`Abs₁`), 而且语言里没有哪一行 `Ad`. **不循环的程度要如实说:** `Abs₁` 不提绑定. `Ad` 不提 `top`, 也不按构造子名字判断新旧, 但它说的 "高度依赖世界" 就是绑定做的事, 只是换成了可以在任何对象上检验的性质. 见入口的判断.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLBehaveDef where

open import Data.Product using (Σ)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; _≪_; ≪S; Strict)
open import OCF.Align.CumReadW using (one; Gw)
open import OCF.Align.WorldTHW
open import OCF.Align.WorldTHLe using (_⊴_)

-- 折叠一次被吸收: 是某一行第 0 层的第一位置
Abs₁ : Hg → Set
Abs₁ p = Σ Hg λ p′ → Ω̇ p one ⊴ Ω̇ p′ azero

-- 对象读到的高度: 只拆世界的包装和低层的包装
hOf : ∀ {p a u} → 𝓞 p a u → Hg
hOf {p} (ow w g x) = hOf x
hOf (oL {h = h} i k e x) = h
hOf {p} x = p

-- 分支读到的高度盖住分支的世界
Cov : ∀ {p a u} → (∀ {v} → u ⊲ v → Gw v → 𝓞 p a v) → Set
Cov {u = u} h = ∀ {v} (q : u ⊲ v) (g : Gw v) → v ⊲ hA (hOf (h q g))

-- 沿第一位置走到一个 Cov 的闭包节点
data Ad : ∀ {p a u} → 𝓞 p a u → Set where
  ad-c : ∀ {p a u} {x : 𝓞 p a u} {h : ∀ {v} → u ⊲ v → Gw v → 𝓞 p a v} → Cov h → Ad (oc x h)
  ad-x : ∀ {p a u} {x : 𝓞 p a u} {h : ∀ {v} → u ⊲ v → Gw v → 𝓞 p a v} → Ad x → Ad (oc x h)
  ad-s : ∀ {p a u} {x : 𝓞 p a u} → Ad x → Ad (os x)
  ad-l : ∀ {p a u} {F : _ → 𝓞 p a u} n → Ad (F n) → Ad (ol F)
  ad-i : ∀ {p a u k} {r : k ≪ a} {h : ∀ {v} → u ⊲ v → Gw v → Vs p a (≪S r) v → 𝓞 p a v} →
         (∀ {v} (q : u ⊲ v) (g : Gw v) → Ad (h q g (inS (≪S r) (Ω̇at p k g)))) → Ad (oi r h)
  ad-d : ∀ {p a u h₀ k} {i : h₀ <ᴴ p} {r} {h : ∀ {v} → u ⊲ v → Gw v → Low p i k v → 𝓞 p a v} →
         (∀ {v} (q : u ⊲ v) (g : Gw v) → Ad (h q g (inL i (Ω̇at h₀ k g)))) → Ad (od i k r h)
  ad-e : ∀ {p a b u} {R : Strict b a} {stp : Stp R} {y : Vs p a R u} → Ad (outS R y) → Ad (oe stp y)
  ad-L : ∀ {p a h₀ k u} {i : h₀ <ᴴ p} {e} {y : Low p i k u} → Ad (outL i y) → Ad {a = a} (oL i k e y)
  ad-w : ∀ {p a u v} {w : u ⊲ v} {g : Gw u} {x : 𝓞 p a u} → Ad x → Ad (ow w g x)
```
