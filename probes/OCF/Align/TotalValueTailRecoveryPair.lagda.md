# 实际恢复所用低坐标的双端生成域

本篇把原结构关系与两端生成证书同时保留。原 chainᵠ 的种子仍是
完整 Ω̇，后继仍是原回调，没有替换实际轨道。它为受限恢复提供
坐标准入；不声称已将任意参数的 Ω̇ 与 ι↓ 读回配对。

尤其不能只缩小 Cross 的回调量词，再沿用输出为旧 Rq 的恢复定理：
旧 Rq 的 keep 分支要求全部 raw 相关坐标，未附带下面的 Gen。
下面不把这种量词缺口包装成已证恢复。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.TotalValueTailRecoveryPair (S : HtB) where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import OCF.Free.Level
open import OCF.Free.Floor using (Ev)
open import OCF.Free.Tree using (Fl)
open import OCF.Align.LadderOrdTree S
open import OCF.Align.LadderOrdRel S
open import OCF.Align.TotalValueBuildRelatedGenIf S using (Gen)
open import OCF.Align.TotalValueBuildRelatedGenFloor S using (omega-gen)
open import OCF.Align.TotalValueBuildRelatedGenTransport S using (transport; transport-back)

Pair : ∀ m a b {φ χ ψ ρ} → Q m a φ χ → Q m b ψ ρ → Set
Pair m a b x y = Rq m a b x y × Gen m a x × Gen m b y

floor-pair : ∀ m {a b} → a ≅ᴵ b → Pair m a b (Ω̇ m a) (Ω̇ m b)
floor-pair m {a} {b} e = RΩ̇ m e , omega-gen m a , omega-gen m b

move-pair : ∀ {m a b a′ b′ φ χ ψ ρ} (ea : a ≅ᴵ a′) (eb : b ≅ᴵ b′)
  {x : Q m a φ χ} {y : Q m b ψ ρ} → Pair m a b x y →
  Pair m a′ b′ (trQ ea x) (trQ eb y)
move-pair ea eb (r , gx , gy) = R-trʳ eb (R-trˡ ea r) , transport ea gx , transport eb gy

back-pair : ∀ {m a b a′ b′ φ χ ψ ρ} (ea : a ≅ᴵ a′) (eb : b ≅ᴵ b′)
  {x : Q m a′ φ χ} {y : Q m b′ ψ ρ} → Pair m a′ b′ x y →
  Pair m a b (tr⁻Q ea x) (tr⁻Q eb y)
back-pair ea eb (r , gx , gy) = R-tr⁻ʳ eb (R-tr⁻ˡ ea r) , transport-back ea gx , transport-back eb gy

chain-pair : ∀ {m a b φ χ ψ ρ}
  (fe : ∀ {L} → Ev L φ → Ev L Fl) (fc : Sub m χ (κ Fl))
  (fe′ : ∀ {L} → Ev L ψ → Ev L Fl) (fc′ : Sub m ρ (κ Fl))
  (f : Q m a φ χ → Q m a φ χ) (g : Q m b ψ ρ → Q m b ψ ρ) →
  a ≅ᴵ b →
  (∀ x y → Pair m a b x y → Pair m a b (f x) (g y)) →
  ∀ n → Pair m a b (chainᵠ fe fc f n) (chainᵠ fe′ fc′ g n)
chain-pair {m} {a} {b} fe fc fe′ fc′ f g e step zero =
  rwk (RΩ̇ m e) , (rwk (proj₁ (omega-gen m a)) , proj₂ (omega-gen m a)) ,
  (rwk (proj₁ (omega-gen m b)) , proj₂ (omega-gen m b))
chain-pair fe fc fe′ fc′ f g e step (suc n) =
  step _ _ (chain-pair fe fc fe′ fc′ f g e step n)
```

floor-pair 的参数可为任意原 Ordᴵ，包括非有限层；它没有把整个
回调闭包当假设。chain-pair 的一步条件将在各实际 ψ/Ψ 回调中消费，
目前本篇只证明全轨道的组合律，不把该一步条件默认为真。
