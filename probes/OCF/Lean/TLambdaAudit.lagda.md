# 原 Third.TΛ 的估值审计：先分清世界参数与附加塔高

本篇不改原闭项，不读记号定义。下面严格区分编译定理与估值判断。

## 旧估计的实际依据与缺项

`Third` §2 的 ψ₀(Ω_{Ω·ω}) 读法只有结构依据，尚不是上下界。
`ThirdVal.Stage.rk-⊲` 证明固定世界、合法共同高度中的第一位置保序，
没有证明 `Φ`、`ΦX` 或 `desc` 的值由这个秩控制；`rk` 的输出仍是任意
可数树，不能仅由其类型给统一序数界。对 n 取极限及将前项回灌 c₀，
都需要另一个统一的闭包估计，不能从每站固定世界省去。

更具体的两处差别来自原代码：

* `ThirdTm.Cn.TN c₀ n` 直接下降 `fl(suc n)`；`RecB.TN n m` 先将
  `top(suc n)m` 同底折成 `inp n m`，再下降。c₀ 是底世界参数，m 是
  额外塔高。两者不能逐字当作同一个参数。`ThirdCmp` 只有有限节点数测试。
* `ThirdLeg.W.bnd 0=c₀`，但 `bnd(suc n)=legS(suc n)(fl(suc n))`。
  高底固定界自身随 n 变化，并非所有站共用一个已知可数值界。

因此更精准的当前判断应写成两参数增长问题，而不是给旧猜测加上
“上界”二字：需同时控制 `c₀ ↦ TN c₀ n` 与底提升 n，再证明实际
`yΛ(suc k)=yΛ k⊞TN(hs(yΛ k))k` 留在所猜的闭包内。
ψ₀(Ω_{Ω·ω}) 仍可作待检验候选读法；本篇没有证据把它提升为界，
也没有足够依据宣称一个更大的具名读法。以下记录全部底上的原指标反馈链，供后续值比较直接消费。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.TLambdaAudit where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; s≤s; l≤; ≤l)
open import OCF.Lean.NegFold1Base using (≤ᵛ-refl)
import OCF.Lean.ThirdTm as T
import OCF.Lean.ThirdLeg as Leg
import OCF.Lean.ThirdFold as Fold
import OCF.Lean.ThirdX as Cross
open import OCF.Lean.ThirdTw using (Sb; fl; gtX)

zero-left : ∀ (a : Cd) → a ≤ᵛ hz ⊞ a
zero-left hz = z≤
zero-left (hs a) = s≤s (zero-left a)
zero-left (hl f) = l≤ (λ n → ≤l n (zero-left (f n)))
zero-left (hΩ () _)

-- 实际首站进入最终对角；不将它认作 RecB.TN 的同名参数站。
first-in-terminal : T.Cn.TN (hs hz) tt zero ≤ᵛ T.TΛ
first-in-terminal = ≤l 1 (zero-left (T.Cn.TN (hs hz) tt zero))

module Root (c₀ : Cd) (lc₀ : LgB c₀) (n : ℕ) where
  module C = T.Cn c₀ lc₀
  module W = Leg.W c₀ lc₀
  module F = Fold (Sb n) (W.wS n) (W.lwS n)
  module R = F.F (C.St.Er n)
  module X = Cross (Sb n) (W.wS n) (W.lwS n) (C.St.Er n)
    (Leg.legS n) (Leg.Lg-legS n) (W.pkS n) (W.pk-bd n)

  one : HB (Sb n)
  one = hs hz

  -- 实际链的每步保留原高层种子，不用 Cd 替代它。
  advance : F.GT hz → F.GT hz
  advance b = X.ΦX hz (hs (X.sh₀ one (proj₁ b)))
    (proj₂ (X.aS (proj₁ b) tt))
    (X.⊲tr (hsuc hself) (X.↑S (proj₁ b))) b
    (gtX (Sb n) (fl n) (X.sh₀ one (proj₁ b)))
    (C.Fl.PH-gt n (X.sh₀ one (proj₁ b)) (hs (X.sh₀ one (proj₁ b))) (hsuc hself))
    where open import Data.Product using (proj₂)

  root-chain : C.stp n (fl (suc n)) (C.Fl.PH-fl n one hself) ≡
    hl (λ k → proj₁ (F.chainG (C.b₀ n) advance k))
  root-chain = refl
```

`root-chain` 是原跨底第一轮的完整无界反馈列，并非已完成后续 `desc` 的
值比较。其初值是 `fl n`，每次通过原 `legS` 后回灌；旧指标的 `pk` 取枝
与 Er 仍在下一调用中执行。后续若比较 RecB，须比较这个真实生成域
及其所有下层观察，不能把此式或固定世界秩单独读成 ψ₀(Ω_x) 的界。
