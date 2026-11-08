# 原生成 marker 的完整观察重写

原 ι↓ 在 marker 处读取低坐标，而原 ψ/Ψ/ψ̄ 读取 body。
生成证书正好记录 body 与低坐标的原 ι 在旧 Rq 下相容。
下面把该字段用于全部实际观察，包括新 run；不假设任意 callback
都尊重新增的关系，也不把它算成全参数跨高度恢复。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.TotalValueTailRecoveryMarker (S : HtB) where
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Free.Level
open import OCF.Free.Prefix using (toZ)
open import OCF.Free.Eq using (_≈ᴿ_; toZ-≅)
open import OCF.Free.Floor using (Ev)
open import OCF.Align.LadderOrdTree S
open import OCF.Align.LadderOrdRel S
open import OCF.Align.TotalValueBuildRelatedGenIf S
open import OCF.Align.TotalValueBuildRelatedGenUp S using (raise)
open import OCF.Align.TotalValueBuildRelatedGenFloor S using (omega-gen)
open import OCF.Align.TotalValueTailCongruence using (run-cong)
import OCF.Free.TotalOrbitRun as R

body-related : ∀ {m a k φ χ} (r : k ◃₁ a)
  {z : Us m k (◃₁→◃ r) φ χ} {x : Q m a φ χ} →
  Gen m a (omk r z x) →
  Rq m a a x (ι (◃₁→◃ r) (outU (◃₁→◃ r) z))
body-related r g = proj₂ (proj₂ (proj₂ g))

psi-marker : ∀ {m a k t φ χ} (r : k ◃₁ a) (q : t <ᴵ a)
  {z : Us m k (◃₁→◃ r) φ χ} {x : Q m a φ χ} →
  Gen m a (omk r z x) →
  Rq m t t (ψᵠ q (omk r z x))
    (ψᵠ q (ι (◃₁→◃ r) (outU (◃₁→◃ r) z)))
psi-marker r q g = R-ψᵠ q q (≅ᴵ-refl _) (body-related r g)

height-marker : ∀ {H m a k t φ χ w} (r : k ◃₁ a)
  (qH : H <ᴸ m) (ok : Ok w) (e : Eh H m w χ) (p : t <ᴵ w H)
  {z : Us m k (◃₁→◃ r) φ χ} {x : Q m a φ χ} →
  Gen m a (omk r z x) →
  Rq H t t (Ψ qH ok e p (omk r z x))
    (Ψ qH ok e p (ι (◃₁→◃ r) (outU (◃₁→◃ r) z)))
height-marker r qH ok e p g = R-Ψ qH ok e p ok e p (≅ᴵ-refl _) (body-related r g)

observe-marker : ∀ {m a k φ χ w w′} (r : k ◃₁ a)
  {z : Us m k (◃₁→◃ r) φ χ} {x : Q m a φ χ} →
  Gen m a (omk r z x) →
  (ok : Ok w) (e : Eh h₀ m w χ) (ok′ : Ok w′) (e′ : Eh h₀ m w′ χ) →
  ψ̄ᵠ ok e (omk r z x) ≈ᴿ
  ψ̄ᵠ ok′ e′ (ι (◃₁→◃ r) (outU (◃₁→◃ r) z))
observe-marker r g ok e ok′ e′ = R→≈ᵠ (body-related r g) ok e ok′ e′

run-marker : ∀ {m a k φ χ w w′ ℓ ℓ′} (r : k ◃₁ a)
  {z : Us m k (◃₁→◃ r) φ χ} {x : Q m a φ χ} →
  Gen m a (omk r z x) →
  (ok : Ok w) (e : Eh h₀ m w χ) (ok′ : Ok w′) (e′ : Eh h₀ m w′ χ) →
  (ev : Ev ℓ φ) (p : zero <ᴵ ℓ) (ev′ : Ev ℓ′ φ) (p′ : zero <ᴵ ℓ′) →
  R.run (toZ (ψ̄ᵠ ok e (omk r z x) ev p)) ≅ᴵ
  R.run (toZ (ψ̄ᵠ ok′ e′ (ι (◃₁→◃ r) (outU (◃₁→◃ r) z)) ev′ p′))
run-marker r g ok e ok′ e′ ev p ev′ p′ = run-cong
  (toZ-≅ (observe-marker r g ok e ok′ e′ ev p ev′ p′ (≅ᴵ-refl zero)))

-- 原 FΩ 后继的实际 marker，包含任意已生成低坐标的整棵树。
-- 不是人为换成零坐标；Ω̇ m a 为所有 a 给出实际实例。
successor-mark : ∀ m a {φ χ} (z : Q m a φ χ) → Gen m a z →
  Gen m (suc a) (omk zero z (ι zero z))
successor-mark m a z gz =
  rob (≅ᴵ-refl a) (proj₁ gz) (R-ι zero zero (proj₁ gz)) ,
  gz , proj₂ (raise zero gz) , R-ι zero zero (proj₁ gz)

floor-marker : ∀ m a → Gen m (suc a) (omk zero (Ω̇ m a) (ι zero (Ω̇ m a)))
floor-marker m a = successor-mark m a (Ω̇ m a) (omega-gen m a)
```

这把完整原 marker 的 ψ、Ψ、底观察与新累计运行统一接到原 ι。
实际 FΩ 外层的 qwk 仅改变所用环境，不删分支；上述 observe-marker
已经量化双方各自的合法环境。尚缺的跨高度结论是：在真实生成的
低坐标上，将这里的 ι 与目标侧的 ι↓ 相比较，并在后继反馈整链中
保持该比较。这里没有用旧 Rq 的 raw 回调量词冒充此项保持。
