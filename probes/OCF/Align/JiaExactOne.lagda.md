# 第三轮实际反例处的新版实例

只验证被改动的原实例，不重算低站的值下界。
整个新折叠输出逐项对应原 EBO ψ₀(Ω)，γ 链每一步都有相关标准形包；
不是只算前几项的有限测试。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.JiaExactOne where

open import Data.Nat.Base using (ℕ)
open import Data.List.Base using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.EboLeanDef using (T; ψ; Ωt; Ωs; []<)
open import OCF.Align.EboLeanBase using (n[]; nf-Ω)
open import OCF.Align.EboLean3Omega using (Acc′; acc; wf)
open import OCF.Align.JiaBase using (Tree; Below; below; Low)
open import OCF.Align.JiaFold using (lift; regular)
open import OCF.Align.JiaRep using (Rep)
open import OCF.Align.JiaRepMove using (rep-lift)
open import OCF.Align.JiaRepOmega using (rep-regular)
open import OCF.Align.JiaAuditClosure using (normal-a)
open import OCF.Align.JiaExactFold using (module Fold)
open import OCF.Align.JiaExactSeeds using (one-seeds; one-spec)
open import OCF.Align.JiaExactRep using (module Sound)
open import OCF.Align.JiaExactFeedback using (Related; related; label; module Chain)

one Ω : T
one = Ωt []
Ω = Ωs []

target : Below [] one
target = below n[] []<

regular-exact : ∀ (a₁ : Acc′ one) (a₀ : Acc′ []) →
  Rep a₀ (Fold.ψ one-seeds a₁ a₀ target (regular a₁ n[])) (ψ [] Ω ∷ [])
regular-exact a₁ a₀ = Sound.ψ-rep one-seeds a₁ a₀ target one-spec (rep-regular a₁ n[])

-- 当前实际 regular 的分支就是原 lift；不是另造一个模拟函数。
lower : Acc′ one → Acc′ []
lower (acc h) = h n[] []<

regular-chain : (a₁ : Acc′ one) → (n : ℕ) → Related [] (lower a₁)
regular-chain (acc h) n = Chain.pack-chain one-seeds (acc h) target target one-spec
  (lift (h n[] []<) (acc h) target) Ω
  (rep-lift (h n[] []<) (acc h) target) refl normal-a refl n

make : (a₁ : Acc′ one) (a₀ : Acc′ []) → Related [] a₀
make a₁ a₀ = related (ψ [] Ω ∷ []) normal-a
  (Fold.ψ one-seeds a₁ a₀ target (regular a₁ n[])) (regular-exact a₁ a₀)

-- 先在任意可及证明上装包，再关闭；不逐项比较具体闭树。
opaque
  closed : Related [] (wf n[])
  closed = make (wf (nf-Ω n[])) (wf n[])

  closed-code : label closed ≡ (ψ [] Ω ∷ [])
  closed-code = refl

```

先将具体闭树与通用证明直接比较的实验在 6G 退出 251，未算通过；
正式版本先在任意可及证明上生成 `Related`，再关闭整个记录。
这不是 T甲，没有全塔或终点强度结论。
