# 从槽位值读出计数化候选
不读记号；合法构造：四种值构造读成层号，合法值给出该层号的证据，再以默认底折叠其 Ω 树。
实际第 2 站的槽位值满足前提，得到合法闭项 `candidate₁`；`ChildLow₁` 的值比较未证，第 0 步未完成。
来源：路径与合法性证明改写自 `YiRWPath.◃→⊑`、`OkO↑`；原实际对象取自 `YiSLStart`，未改折叠与合法性。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTCValue where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps using (Tr⁺; Ωt)
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (B₀)
open import OCF.Lean.YiTBRow using (ψ)
open import OCF.Lean.YiMTTab using (rbᶻ)
import OCF.Lean.YiVWVal as V
import OCF.Lean.YiSLStart as S

↑ᵛ : (k : L) → V.V k → L
↑ᵛ k V.zero = zero
↑ᵛ k (V.suc x) = nd sS (λ _ → ↑ᵛ k x)
↑ᵛ k (V.lim f) = nd sL (λ n → ↑ᵛ k (f n))
↑ᵛ k (V.Ω p g) = nd (sΩ (at k p)) (λ c → ↑ᵛ k (g (fromBr k p c)))

◁→⊑ᵛ : (k : L) {x y : V.V k} → x V.◁ y → ↑ᵛ k x ⊑ ↑ᵛ k y
◁→⊑ᵛ k V.◁s = inc tt self
◁→⊑ᵛ k (V.◁l n) = inc n self
◁→⊑ᵛ k V.◁w = inc zero self
◁→⊑ᵛ k (V.◁t d e) = ◁→⊑ᵛ k d ∙ ◁→⊑ᵛ k e

OkOᵛ : (a k : L) → Ok k → k ≤ a → (v : V.V k) → V.LegV k v → OkO a (↑ᵛ k v)
OkOᵛ a k o w V.zero hv = tt
OkOᵛ a k o w (V.suc v) hv = tt , λ _ → OkOᵛ a k o w v hv
OkOᵛ a k o w (V.lim f) (hf , adj) = (λ n → ◁→⊑ᵛ k (adj n)) , λ n → OkOᵛ a k o w (f n) (hf n)
OkOᵛ a k o w (V.Ω p g) hv = (posW k p ∙ w , Ok-at k o p) , λ c → OkOᵛ a k o w (g (fromBr k p c)) (hv (fromBr k p c))

childᵛ : (k : L) → V.V k → L
childᵛ k v = k ⊕ ↑ᵛ k v

ok-childᵛ : (k : L) → Ok k → (v : V.V k) → V.LegV k v → Ok (childᵛ k v)
ok-childᵛ k o v hv = Ok⊕ k (↑ᵛ k v) o (OkOᵛ k k o self v hv)

collapseᵛ : (k : L) → Ok k → (v : V.V k) → V.LegV k v → Tr⁺ zero
collapseᵛ k o v hv = ψ (childᵛ k v) (ok-childᵛ k o v hv) (rbᶻ (childᵛ k v))
  (B₀ (childᵛ k v)) zero (z≤ (childᵛ k v)) (Ωt zero) (proj₁ (Ωt (childᵛ k v)))

v₁ : V.V (tw 1)
v₁ = V.val (tw 1) (S.Step.chain 1 1)

hv₁ : V.LegV (tw 1) v₁
hv₁ = V.val-leg (tw 1) (S.Step.chain 1 1)

candidate₁ : Tr⁺ zero
candidate₁ = collapseᵛ (tw 1) (Ok-tw 1) v₁ hv₁

ChildLow₁ : Set
ChildLow₁ = V.val zero (proj₁ candidate₁) V.≼ V.val zero (proj₁ (S.Step.out 1 (S.Step.chain 1 1)))
```
