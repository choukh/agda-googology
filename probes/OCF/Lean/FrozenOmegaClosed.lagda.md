# 第一个 Ω 高度上的非恒定分支闭项

本文件交可运行的受限输入和最终合法可数树。中间输出的合法性未证，
因此不是完成了内部 View 的成品候选，也没有 ψ₀Λ 强度声明。
最终合法性来自已证明的最低一步 total fold，而非冒称高层折叠保合法。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.FrozenOmegaClosed where
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecFl using (up-⊲; Lg-up)
open import OCF.Lean.ThirdIf using (Tw)
open import OCF.Lean.ThirdTw using (emb; posE; frE)
open import OCF.Lean.FrozenOmegaIf
open import OCF.Lean.FrozenOmegaRun
import OCF.Lean.TowerCollapseRun as Low
import OCF.Lean.TowerCollapseClosed as LowC

U : KS
U = step S⊥
w : Wd U
w = tt , hs hz
M : HB U
M = hΩ (inj₂ tt) up

legal-M : LgB M
legal-M = (λ lw e e′ p → up-⊲ p) , (λ lw e → Lg-up _ (lgB⊲ e (Data.Product.proj₁ lw) (Data.Product.proj₂ lw)))

base : HB U → HB (SafeTw U w M)
base hz = hz
base (hs a) = hs (base a)
base (hl f) = hl (λ n → base (f n))
base (hΩ κ g) = hΩ ((hs hz , inj₁ κ) , (hself , tt)) (λ c → base (g c))

base-position : ∀ {a b V} → a ⊲[ proj₁ (V (hs hz)) ] b → base a ⊲[ V ] base b
base-position hself = hself
base-position (hsuc p) = hsuc (base-position p)
base-position (hlim n p) = hlim n (base-position p)
base-position (hLim e p) = hLim e (base-position p)

base-legal : ∀ c → LgB c → LgB (base c)
base-legal hz l = tt
base-legal (hs c) l = base-legal c l
base-legal (hl f) (s , l) = (λ n → base-position (s n)) , (λ n → base-legal (f n) (l n))
base-legal (hΩ κ g) (s , l) =
  (λ {v} lv e e′ p → base-position (s (proj₁ (lv (hs hz))) e e′ p)) ,
  (λ {v} lv e → base-legal (g _) (l (proj₁ (lv (hs hz))) e))

input : HB (SafeTw U w M)
input = hΩ ((hs hz , inj₂ tt) , (hself , tt)) base

legal-input : LgB input
legal-input = (λ lv e e′ p → base-position p) ,
  (λ {v} lv e → base-legal _ (lgB⊲ e (proj₁ (lv (hs hz))) (proj₂ (lv (hs hz)))))

module F = Run U w (tt , tt) M legal-M
intermediate : HB U
intermediate = erase (F.fold hz (z⊲ᴮ M) input)
T : Cd
T = Low.Run.fold S⊥ intermediate
legal-T : LgB T
legal-T = LowC.legal-fold intermediate
```

`base` 逐构造子读取坐标且保留旧 Ω 节点；`input` 的坐标类型为 HB U，
不是只有自然数或可数构造子的坐标。中间值与源地板的关系、高层输出合法性及最终大小都仍待证明，不能由最终 legal-T 倒推出。

本例只使用固定可入分量 1，没有利用 Ω 高度的无界分量。
坐标含 Ω 与高度写成 M 都不构成强度提升的证明。
