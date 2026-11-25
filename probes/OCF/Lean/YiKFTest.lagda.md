# 候选折叠 (A)+(B)+(C) 在三个障碍点上的测试

> 不读记号; 不改树、折叠、合法性. 编译定理 (对一切 d): 同步对象孩子 `a₁ (d+2)` 里读回结点的下标槽位 `pᵍ d` 在 `kpʳ` 下保留在目标层 `h₁ (d+1)` 自己的槽位上, 换型是恒等 (`kpᵍ`); 同一孩子里前缀 tw 1 的下标槽位与原判定相同 (`kp₀ᵍ`).
> 有限测试: `p*`, `p₂`, `p₂′` 保留; d = 1、2 时顶槽位回灌的输出里, 第 1 个链点的折叠起头是 Ω 结点 (`syncᶜ`, `sync₂ᶜ`), d = 2 时 (A)+(B) 下同一处是 ℕ 极限 (`sync₂ᴬᴮ`); `YiTFTw1` 那一点输出的第一项是保留的 Ω 结点 (`tw1ᶜ`, 与 (A)+(B) 同形).
> 不给出值的定理 (值在 [YiKFValue](YiKFValue.lagda.md)); 证据是 `pvT 2` 在同步对象处的孩子 `pvᵈ`, 对象取自 `YiDXTest`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiKFTest where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; Keep; kp; B₀)
open import OCF.Lean.YiMTTab using (rbᶻ)
open import OCF.Lean.YiDXFold using (module FAB)
open import OCF.Lean.YiDXTest
open import OCF.Lean.YiKFKeep
open import OCF.Lean.YiKFFold
```

## 保留判定

```agda
pvᵈ : Pv (nd (sΩ zero) a₁)
pvᵈ = proj₂ (pvT 2) (proj₁ (Ωt (tw 1)))

kp*ᶜ : IsJust (kpᶜ (a₁ n2) (proj₂ oᵈ n2) (proj₂ pvᵈ n2) p* (ink self) (org-no _ _))
kp*ᶜ = tt

kp₀ᶜ : kpᶜ (a₁ n2) (proj₂ oᵈ n2) (proj₂ pvᵈ n2) p₀ (ink self) (org-no _ _) ≡ kp (a₁ n2) (proj₂ oᵈ n2) p₀ (ink self)
kp₀ᶜ = refl

kp₂ᶜ : kpᶜ (a₁ n3) (proj₂ oᵈ n3) (proj₂ pvᵈ n3) p₂ (ink self) (org-no _ _) ≡ just (q′ , (λ z → z) , refl)
kp₂ᶜ = refl

kp₂′ᶜ : IsJust (kpᶜ (a₁ n3) (proj₂ oᵈ n3) (proj₂ pvᵈ n3) p₂′ (ink self) (org-no _ _))
kp₂′ᶜ = tt
```

对一切 d (变量, 不限于字面自然数): 孩子 `Ω_{h₁ (d+1)}` 里读回的顶结点, 下标槽位的来源是 `h₁ (d+1)` 的槽位 `qᵍ` (它的孩子层 `h₁ d`). d = 0 是 `p*`, d = 1 是 `p₂`.

```agda
zᵍ : (d : Tr zero) → Tr (h₁ (suc d))
zᵍ d = proj₁ (Ωt (h₁ (suc d)))

pᵍ p₀ᵍ : (d : Tr zero) → Pos (a₁ (suc (suc d)))
pᵍ d  = inj₂ (zᵍ d , inj₂ (inj₂ (tt , inj₂ (inj₁ (inj₁ tt)))))
p₀ᵍ d = inj₂ (zᵍ d , inj₂ (inj₂ (tt , inj₂ (inj₂ (zero , inj₂ (inj₂ (tt , inj₂ (inj₁ (inj₁ tt)))))))))

qᵍ : (d : Tr zero) → Pos (h₁ (suc d))
qᵍ d = inj₂ (tt , inj₁ tt)

kpᵍ : ∀ d → kpʳ (a₁ (suc (suc d))) (proj₂ oᵈ (suc (suc d))) (proj₂ pvᵈ (suc (suc d))) (pᵍ d) (ink self)
          ≡ just (qᵍ d , (λ z → z) , refl)
kpᵍ d = refl

kpᵍᶜ : ∀ d → kpᶜ (a₁ (suc (suc d))) (proj₂ oᵈ (suc (suc d))) (proj₂ pvᵈ (suc (suc d))) (pᵍ d) (ink self) (org-no _ _)
           ≡ just (qᵍ d , (λ z → z) , refl)
kpᵍᶜ d = refl

kp₀ᵍ : ∀ d → kpᶜ (a₁ (suc (suc d))) (proj₂ oᵈ (suc (suc d))) (proj₂ pvᵈ (suc (suc d))) (p₀ᵍ d) (ink self) (org-no _ _)
           ≡ kp (a₁ (suc (suc d))) (proj₂ oᵈ (suc (suc d))) (p₀ᵍ d) (ink self)
kp₀ᵍ d = refl
```

## 输出的形状

顶槽位回灌 (朝下标层, 路径 `ink self`, 标准底) 分支 `gᵍ d (zᵍ d)`; 探针与 `YiDXTest.Sync.probe` 相同: 第 1 个部分和里第 1 个链点的折叠.

```agda
gᵍ : (d : Tr zero) → Tr (h₁ (suc d)) → Tr (a₁ (suc (suc d)))
gᵍ d z = proj₁ (upz {s = sΩ (h₁ (suc d))} {h = hh (suc d)} z (Ωt (hh (suc d) z)))

outᶜ : (d : Tr zero) → Tr (h₁ (suc d))
outᶜ d = proj₁ (FC.ψ (a₁ (suc (suc d))) (proj₂ oᵈ (suc (suc d))) (rbᶻ (a₁ (suc (suc d)))) (proj₂ pvᵈ (suc (suc d)))
  (B₀ (a₁ (suc (suc d)))) (h₁ (suc d)) (ink self) (org-no _ _) (Ωt (h₁ (suc d))) (gᵍ d (zᵍ d)))

outᴬᴮ : (d : Tr zero) → Tr (h₁ (suc d))
outᴬᴮ d = proj₁ (FAB.ψ (a₁ (suc (suc d))) (proj₂ oᵈ (suc (suc d))) (rbᶻ (a₁ (suc (suc d))))
  (B₀ (a₁ (suc (suc d)))) (h₁ (suc d)) (ink self) (Ωt (h₁ (suc d))) (gᵍ d (zᵍ d)))

pr : ∀ {S} → T S → T S
pr t = el (el (el t 1) 0) 0

syncᶜ : HeadΩ (pr (outᶜ zero))
syncᶜ = tt

sync₂ᶜ : HeadΩ (pr (outᶜ n1))
sync₂ᶜ = tt

sync₂ᴬᴮ : HeadLim (pr (outᴬᴮ n1))
sync₂ᴬᴮ = tt
```

`YiTFTw1` 那一点 (塔第 1 项, 下标层是第 0 层, 没有来源条目): 形状与 (A)+(B) 相同 (`YiDXTest.tw1ᴬᴮ`); 值见 `YiKFValue.out-abc`.

```agda
out₁ᶜ : Tr (at (tw 1) p₁)
out₁ᶜ = proj₁ (FC.ψ (tw 1) (Ok-tw 1) (rbᶻ (tw 1)) (pvT 1) (B₀ (tw 1)) (at (tw 1) p₁) (posW (tw 1) p₁) (org-no _ _)
                 (B₀ (tw 1) (at (tw 1) p₁) (posW (tw 1) p₁)) (g₁ z*))

tw1ᶜ : FirstLimΩ (el out₁ᶜ 0)
tw1ᶜ = tt
```
