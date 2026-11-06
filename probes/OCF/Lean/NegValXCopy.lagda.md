# NegValX (五): 不同分量里的两个拷贝, 跨底折叠后字面相同

> 不含记号. 入口 [NegValX](NegValX.lagda.md). 本篇**不依赖**接口. 只导入 [CRwBase](CRwBase.lagda.md), [CRwFold](CRwFold.lagda.md), [CRw](CRw.lagda.md) (实例 `I₁`), [NegValXSelf](NegValXSelf.lagda.md) (`pickS`, `F`). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **问题.** [NegValXSelf](NegValXSelf.lagda.md) 说明 $\Omega_1$ 本身与拷贝不能按层比较成 "本身 ≤ 拷贝". 构造一路于是改为 "`Ω≤Ω` 要求同一个种类" (ValXRel 草稿). 本篇给这个选择配一条盲定理的折叠一侧: 分量 $1$ 与分量 $2$ 里 $\Omega_1$ 的两个拷贝 `κc = (1, inj₁ (inj₂ tt))`, `κc₂ = (2, inj₁ (inj₁ (inj₂ tt)))` (层都是 $0$, 策略都是 `poF`, 坐标类型都是 `Cd`), 同一分支 $h$ 与同一分支路径, 跨底折叠到第 $0$ 层的输出**字面相等** (`copies-same`, 对一切世界, 目标证据, 界, 分支).
>
> **读法 (判断).** 所以 "同种类" 的关系比折叠的值同一更细: 两个折叠后相等的合法输入, 只按同种类比较时不可比 (在构造一路的关系定稿后可写成定理: 没有 $\Omega$-结点的分支下, `hΩ κc h ≤X hΩ κc₂ h` 无推导). 这不妨碍 `X-mono` (单调只要求一个方向的蕴含), 只说明关系对这类输入是盲的.
>
> **前提实例.** 全称: 一切合法世界 $B$ 带 $3\lhd B$ (例如 $\hat\omega$: `hlim 2 hself`), 一切 $h$ 与路径 `pg`.
>
> **只否定什么.** 没有否定. 只说明折叠在这两个拷贝上不读分量.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegValXCopy where

open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (I₁)
open import OCF.Lean.CRwFold I₁
open import OCF.Lean.ValCRel I₁ using (lvK)
open import OCF.Lean.NegValXSelf using (pickS; F; κc; ω̂)

κc₂ : K XS
κc₂ = hs (hs hz) , inj₁ (inj₁ (inj₂ tt))

lvc₂ : lvK (hs (hs (hs hz))) (inj₁ (inj₁ (inj₂ tt))) ≡ hz
lvc₂ = refl

polc₂ : pX (hs (hs hz)) (inj₁ (inj₁ (inj₂ tt))) ≡ poF
polc₂ = refl

module _ (B : Cd) (lB : LgB B) (pt : hz ⊲ B) (b : Cd) (h : Cd → HB XS)
         (pg : ∀ e → ⊤ → PH PSX B (h e)) where
  -- 两边共同的值: 从界 b 出发的链, 在世界 B 里读 h b′
  T : Cd
  T = hl (chain b (λ b′ → F B lB pt b′ (h b′) (pg b′ tt)))

  copy₁ : (ev : hs (hs hz) ⊲ B) → F B lB pt b (hΩ κc h) (ev , pg) ≡ T
  copy₁ ev = pickS (λ z → z ≡ T) _ _ _ refl

  copy₂ : (ev : hs (hs (hs hz)) ⊲ B) → F B lB pt b (hΩ κc₂ h) (ev , pg) ≡ T
  copy₂ ev = pickS (λ z → z ≡ T) _ _ _ refl

  copies-same : (ev₁ : hs (hs hz) ⊲ B) (ev₂ : hs (hs (hs hz)) ⊲ B) →
                F B lB pt b (hΩ κc h) (ev₁ , pg) ≡ F B lB pt b (hΩ κc₂ h) (ev₂ , pg)
  copies-same ev₁ ev₂ = trans (copy₁ ev₁) (sym (copy₂ ev₂))
```

## 结论 (按档)

- **[定理, 实例 `I₁`, 对一切合法世界, 目标证据, 界, 分支与分支路径]** `copy₁`, `copy₂`, `copies-same`: 两个分量里的 $\Omega_1$ 拷贝, 跨底折叠到第 $0$ 层后字面相等 (都是从界出发、在同一世界里读分支的链).
- **[判断]** 只按同种类比较的关系看不见这一对的值相同 (待构造一路的关系定稿后写成定理).
