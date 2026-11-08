# 固定输入类型本身不能给折叠值上界

对实际 `WorldFoldRun.run` 给出统一值下界：嵌入任意可数布劳威尔树后
运行，值不低于原树。因此虽然输入只有固定类型 `W hz`，所有输入的
运行结果没有共同的可数树上界。此结论不否定给特定闭项的上界，
不声称任意输入来自有限记号无关闭项，也不提供 ψ₀Λ 候选。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LambdaCollapseNoTypeBound where

open import Data.Nat using (zero; suc)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_)
open import OCF.Lean.Fab6Base using (Cd; hz; hs; hl)
open import OCF.Lean.NegFab6Idx using (W)
open import OCF.Lean.WorldFoldRun using (run)
open import OCF.Lean.WorldFoldIf using (partial)
open import OCF.Lean.WorldFoldClosed using (embed)
open import OCF.Lean.NegFab6Sim using
  (_≼_; z≼; s≼s; ≼s; l≼; ≼l; ≼-refl; ≼-tr; ≼⊞r)

term≤partial : ∀ f n → f n ≼ partial f n
term≤partial f zero = ≼-refl _
term≤partial f (suc n) = ≼⊞r (partial f n) (f (suc n))

embed-lower : ∀ {B} (a : Cd) → a ≼ run (embed {B} a)
embed-lower hz = z≼
embed-lower (hs a) = s≼s (embed-lower a)
embed-lower {B} (hl f) = l≼ (λ n → ≼l n
  (≼-tr (embed-lower {B} (f n)) (term≤partial (λ k → run (embed {B} (f k))) n)))

s-invert : ∀ {a b : Cd} → hs a ≼ hs b → a ≼ b
s-invert (s≼s p) = p
s-invert {a} (≼s p) = ≼-tr (≼s (≼-refl a)) p

s-lim : ∀ {a : Cd} {f} → hs a ≼ hl f → Σ _ (λ n → hs a ≼ f n)
s-lim (≼l n p) = n , p

irrefl : ∀ (a : Cd) → hs a ≼ a → ⊥
irrefl hz ()
irrefl (hs a) p = irrefl a (s-invert p)
irrefl (hl f) p with s-lim p
... | n , q = irrefl (f n) (≼-tr (s≼s (≼l n (≼-refl (f n)))) q)

no-fixed-type-bound : (b : Cd) → (∀ (x : W hz) → run x ≼ b) → ⊥
no-fixed-type-bound b bound = irrefl b (≼-tr (embed-lower (hs b)) (bound (embed (hs b))))
```

## 对旧结论的审阅

`Survey/SkeletonAudit.md` §1.3 明说固定 `Ht` 上折叠的公共上界
ψ₀(Ω_{Ω₃}) 是判断，而且没有值定理；其 `fac-*` 只证明定义分解。
`ThirdVal.rk-⊲` 是第一位置保序，不是折叠的值上界。
`RecB` 入口从底的自然数指标推到 Ω·ω 的读法，也不是值上界。
因此不能把“固定类型”或“代表坐标”直接用成所有旧路线到不了 Λ 的定理。

本文件提供一个实际的反例于**一般推理模式**：固定输入类型仍可承载
任意可数树。若要给具体路线封顶，必须证明其闭项生成过程的语义
不变量，而不只是检查输入类型的名字或构造子数量。

翻译账：无新定义层字段；值下界来自原嵌入和运行器。
