# NoAcc (一): 逐点的折叠

> 不含记号. 入口 [NoAcc](NoAcc.lagda.md), 接口 [NoAccIf](NoAccIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延. 对任一满足 [CRwIf](CRwIf.lagda.md) 的 `I` 一条定义.
>
> **这一篇做什么.** 把 [CRwFold](CRwFold.lagda.md) 的折叠 `Φ` 的 ℕ-极限子句从部分和 (`hl (Σ⁺ …)`) 改成**逐点** (`hl (λ n → Φ (f n))`), 其余子句 (后继取 `mul`, 坍缩取回灌链 `chain`, 在上取两段折法, 跨底的世界移动) 一字不动, 层号、种类、决定、地板、路径都从 `CRwFold` 导入. 这样得到的 `Φᴾ` 与 `Φ` 只差一个子句, 用来单独检验 "去掉 ℕ-极限子句的累加" 这一步.
>
> **为什么跨底仍用 `CRwIf` 而不用 `NoAccIf`.** 跨底的决定 `dcx` 用 `cmpB`, 以世界的界为公共上界, 所以**折叠的定义**要求新世界合法 (不只是证书要求). `NoAccIf` 的回灌 `sh₀ B c = B ⊞ c` 只在坐标 $c$ 合法时给出合法的新世界 (`lg-nx` 读 `LgB e`), 而留下的 $\Omega_1$ 结点的分支是对一切坐标 $c$ 的全函数, 链的坐标是折叠自己的输出 (合法与否是证书的事). 所以在 `NoAccIf` 上写不出 `dcx` 那一步 (判断; 卡点写在入口). 本篇的跨底部分沿用 `CRwIf` (实例 `CRw.I₁` 的回灌含部分和 `leg`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Lean.CRwIf
module OCF.Lean.NoAccFold (I : CRwIf) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRwFold I
open CRwIf I
open Po
```

## 逐点的折叠 `Φᴾ`

与 `CRwFold.Φ` 逐子句相同, 只有 `hl f` 一行不同.

```agda
Φᴾ : ∀ s m → Acc s m → LgB m → ∀ s′ t (tg : Tg s m s′ t) → HB (Lev s′ t) → (h : HB (Lev s m)) → Nd tg h → HB (Lev s′ t)
Φᴾ s m a lm s′ t tg b hz nd = hs hz
Φᴾ s m a lm s′ t tg b (hs h) nd = hl (mul (Φᴾ s m a lm s′ t tg b h (ndS tg h nd)))
Φᴾ s m a lm s′ t tg b (hl f) nd = hl (λ n → Φᴾ s m a lm s′ t tg b (f n) (ndL tg f nd n))
Φᴾ s m (acc rs) lm _ t (sm pt) b (hΩ κ g) nd = caseDc (dcl pt lm (cl m κ))
  (λ κ′ fr → hΩ κ′ (λ c → Φᴾ s m (acc rs) lm s t (sm pt) b (g (fr c)) tt))
  (λ to → hl (chain b (λ b′ → Φᴾ s m (acc rs) lm s t (sm pt) b′ (g (to b′)) tt)))
  (λ i pi q to → Φᴾ s i (rs s i (lt pi)) (lg↓ pi lm) s t (sm q) b
     (hl (chain (top s i) (λ b′ → Φᴾ s m (acc rs) lm s i (sm (⊏⊑ pi)) b′ (g (to b′)) tt))) tt)
Φᴾ _ _ (acc rs) lm _ t (cx B lB pt) b (hΩ (c , κ) g) (ev , pg) = caseDc (dcx lB pt ev (cl (hs c) κ))
  (λ κ′ fr → hΩ κ′ (λ c′ →
     Φᴾ bX hz (acc rs) tt b⊥ t
       (cx (pnx P B (psh P B (fr c′)) (pad-sh P (fr c′) lB)) (plg P (pad-sh P (fr c′) lB) lB)
           (⊲ᴮ-tr pt (pnx↑ P (pad-sh P (fr c′) lB))))
       b (g (psh P B (fr c′))) (pg (psh P B (fr c′)) (pad-sh P (fr c′) lB))))
  (λ to → hl (chain b (λ b′ →
     Φᴾ bX hz (acc rs) tt b⊥ t
       (cx (pnx P B (psh P B (to b′)) (pad-sh P (to b′) lB)) (plg P (pad-sh P (to b′) lB) lB)
           (⊲ᴮ-tr pt (pnx↑ P (pad-sh P (to b′) lB))))
       b′ (g (psh P B (to b′))) (pg (psh P B (to b′)) (pad-sh P (to b′) lB)))))
  (λ i pi q to → Φᴾ b⊥ i (rs b⊥ i lx) (lg↓ pi lB) b⊥ t (sm q) b
     (hl (chain (top b⊥ i) (λ b′ →
        Φᴾ bX hz (acc rs) tt b⊥ i
          (cx (pnx P B (psh P B (to b′)) (pad-sh P (to b′) lB)) (plg P (pad-sh P (to b′) lB) lB)
              (⊲ᴮ-tr (⊏⊑ pi) (pnx↑ P (pad-sh P (to b′) lB))))
          b′ (g (psh P B (to b′))) (pg (psh P B (to b′)) (pad-sh P (to b′) lB))))) tt)
  where P = pX c κ
```

**逐点 (定理, `refl`).** 这是 `NegCRwAcc.pt-shape→chain` 与接口 `PtFold.F-pt` 的前提.

```agda
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

Φᴾ-pt : ∀ s m a lm s′ t (tg : Tg s m s′ t) b f nd →
        Φᴾ s m a lm s′ t tg b (hl f) nd ≡ hl (λ n → Φᴾ s m a lm s′ t tg b (f n) (ndL tg f nd n))
Φᴾ-pt s m a lm s′ t tg b f nd = refl
```
