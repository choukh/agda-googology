# 紧界树比值 (三): 验收, 上确界严格变小

> [TightVal](TightVal.lagda.md) 的第三篇. **验收文件: 读标签.** 把 [TightValCap](TightValCap.lagda.md) 的 $B$ 实例化为 `TΩ₂ᴸ` (带标签 $\psi_0(\Omega_\Omega\cdot\Omega_2)$ 的树, 也是紧界树自己在 $\Omega_2$ 处的计值), 再与 [Uniform3Full](Uniform3Full.lagda.md) 带标签 $\psi_0(\Omega_\Omega^2)$ 的树比.
>
> 结论:
>
> | 名字 | 陈述 |
> |---|---|
> | `tight-cap` | `TΩ2′ˢ` 的任何 `Goodᴺ` 计值 $\preccurlyeq$ `TΩ₂ᴸ` |
> | `tight-capΩ` | 一切 $\eta$, 一切环境: `ψᵉ′ ∅ˢ` 在 $\Omega_\eta$ 处的任何 `Goodᴺ` 计值 $\preccurlyeq$ `TΩ₂ᴸ` |
> | `above-gap` | 带标签 $v$, 标准形, $\psi_0(\Omega_\Omega\cdot\Omega_2)<v$ 的树都严格 $\succ$ `TΩ₂ᴸ` |
> | `tight-drop` | `TΩ2-label` 的树 $X$ 不 $\preccurlyeq$ `TΩ2′ˢ` 的任何计值; 反方向 `tight≼X` |
> | `drop-at` | 一切带标签 $v>\psi_0(\Omega_\Omega\cdot\Omega_2)$ 的树, 都不 $\preccurlyeq$ `ψᵉ′ ∅ˢ` 在任何 $\Omega_\eta$ 处的计值 |
> | `low-true` | `low-term` 的记号点 $\psi_0(\psi_\Omega(\Omega_2+1))$ 在 $X$ 里真的出现, 带这个标签的树 $\succ$ `TΩ₂ᴸ`. 紧界树在同一位置是 $0$ (`low-tree`) |
> | `agree-Ω₂` | $\Omega_2$ 处紧界树与新树同标签, 所以 $\cong$: 紧界树到这里没有掉值 |
>
> `tight-cap`, `tight-drop`, `tight≼X` 在 `TΩ2′ˢ` 上是空真的: 它没有证书 ([TightValGlobal](TightValGlobal.lagda.md) 的 `no-T`). 这里证的是: 证书存在也没用. 单调占位的同一上界见 [TightValPh](TightValPh.lagda.md).
>
> 所以占位**没有被吸收**. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示. 读记号: `Lab`, `Lab-oc`, `cmpᵀ`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TightValAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Empty using (⊥)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Align.Level
open import OCF.Align.Prefix using (Z; Ord₊ˢ; Ordˢ; toZ; Ωˢ)
import OCF.Align.EBO as E
open E using (T; natT; cmpᵀ; lt; 𝟏) renaming (ψ to ψᵗ)
open import OCF.Align.Correspond using (Lab)
open import OCF.Align.Closure using (lt→<)
open import OCF.Align.StandardOmega using (NF₁; NF₁-fsn)
open import OCF.Align.Stage2 using (Lab-uniq; Lab-walk; walk)
open import OCF.Align.Stage2Label using (Lab-oc)
open import OCF.Align.UniformS using (z≅; _≅ˢ_; _≅ᶻ_; toZ-≅; Ωˢ-refl; ≅→Rˢ; R→≅ˢ; two)
open import OCF.Align.GoodLBase using (Goodᴸ; forceᴸ; lz; ls)
open import OCF.Align.NotFree using (Goodᴺ; forceᴺ; forceᴺ-≅; ofL; ofL-≅)
open import OCF.Align.Value using (_≼_; ≺→s≼; ≅→≼; ≼-suc; ≼-refl; ≼-trans)
open import OCF.Align.OmegaExpBase using (Stk; ∅ˢ; _▹Ω̂; Good∅; hR; ▹Ω̂-≈; σ⊥)
open import OCF.Align.OmegaExp using (ψΩ₀; tΩ1; tΩ1-NF)
open import OCF.Align.OmegaKBase using (tΩ2; tΩ2-NF)
open import OCF.Align.OmegaSqBase using (ψᵉ′; ψᵉ′-≅; lo0; lo1; liE; ZE₀; ZE₁; Ω₂+1; low-NF; low-tree; pathLow)
open import OCF.Align.OmegaSq using (TΩ2′ˢ; TΩ₂ˢ; TΩ₂ᴸ; TΩ₂-label; tΩ₂; tΩ₂-NF; ZΩ₂; LΩ1)
open import OCF.Align.TightValBase
open import OCF.Align.TightValCap
import OCF.Align.Uniform3Base as U3
open import OCF.Align.Uniform3Full using (TΩ2-label)
open import OCF.Align.Uniform3 using (TΩ₂-label′)
open import OCF.Align.Uniform3SqA using (TΩ₃-label)
open import OCF.Align.OmegaSqA using (tΩ₃; tΩ₃-NF)
```

## §1 四个低处的值都在 `TΩ₂ᴸ` 以下

`A = TΩ₂ᴸ`. 带标签 $v<t_{\Omega_2}$ 的树由 `Lab-oc` 严格在下面. `viaL`: 自互模拟的树的任何 `Goodᴺ` 计值, 与它的带标签证书的计值 $\cong$.

```agda
A : Ordᶜ zero
A = TΩ₂ᴸ

lab≼A : ∀ {Y v} → Lab Y v → NF₁ v → cmpᵀ v tΩ₂ ≡ lt → Y ≼ A
lab≼A {Y} l nv c = ≼-trans (≼-suc (≼-refl Y)) (≺→s≼ (Lab-oc TΩ₂-label tΩ₂-NF l nv (lt→< _ _ c)))

viaL : ∀ {x : Ordˢ zero} {v} → toZ x ≅ᶻ toZ x → (Σ (Goodᴸ (toZ x)) λ G → Lab (forceᴸ _ G) v) →
      (∀ Y → Lab Y v → Y ≼ A) → Cp A (toZ x)
viaL e (G′ , l) h G = ≼-trans (≅→≼ (forceᴺ-≅ e G (ofL G′))) (≼-trans (≅→≼ (ofL-≅ G′)) (h _ l))

ψΩ₀1-NF : NF₁ (ψΩ₀ (natT 1))
ψΩ₀1-NF = NF₁-fsn tΩ1-NF refl 0

ψΩ₀0-NF : NF₁ (ψΩ₀ [])
ψΩ₀0-NF = NF₁-fsn ψΩ₀1-NF refl 1

h∅ : ∀ {ℓ} (z p : zero <ᴵ ℓ) → Cp A (toZ ((∅ˢ ▹Ω̂) z p))
h∅ z p = viaL (toZ-≅ (▹Ω̂-≈ (hR Good∅) z p z p (≅ᴵ-refl zero)))
             (ZE₀ Good∅ (lz refl) z≅ z p σ⊥ ψΩ₀0-NF) (λ Y l → lab≼A l ψΩ₀0-NF refl)

hΩ₀ : ∀ {ℓ} (z p : zero <ᴵ ℓ) (σ : Simᴵ zero ℓ) → Cp A (toZ (ψᵉ′ ∅ˢ z p σ (Ωˢ zero)))
hΩ₀ z p σ = viaL (toZ-≅ (ψᵉ′-≅ (hR Good∅) lo0 lo0 (≅ᴵ-refl zero) (Ωˢ-refl zero)))
                (ZE₀ Good∅ (ls refl (lz refl)) (Ωˢ-refl zero) z p σ ψΩ₀1-NF) (λ Y l → lab≼A l ψΩ₀1-NF refl)

hΩ₁ : ∀ {ℓ} (z p : zero <ᴵ ℓ) (σ : Simᴵ (suc zero) ℓ) → Cp A (toZ (ψᵉ′ ∅ˢ z p σ (Ωˢ (suc zero))))
hΩ₁ z p σ = viaL (toZ-≅ (ψᵉ′-≅ (hR Good∅) lo1 lo1 (≅ᴵ-refl zero) (Ωˢ-refl (suc zero))))
                (ZE₁ Good∅ LΩ1 (Ωˢ-refl (suc zero)) z p σ tΩ1-NF) (λ Y l → lab≼A l tΩ1-NF refl)

selfΩ₂ : ∀ {ℓ} (z p : zero <ᴵ ℓ) (σ : Simᴵ two ℓ) → ψᵉ′ ∅ˢ z p σ (Ωˢ two) ≅ˢ ψᵉ′ ∅ˢ z p σ (Ωˢ two)
selfΩ₂ z p σ = liE {q = zero} {q′ = zero} (≅ᴵ-refl zero) (≅ᴵ-refl (suc zero))
  (λ x y d → ψᵉ′-≅ (hR Good∅) lo1 lo1 (≅ᴵ-refl zero) (R→≅ˢ zero d))
  (λ x y d → ψᵉ′-≅ (hR Good∅) lo1 lo1 (≅ᴵ-refl (suc zero)) (R→≅ˢ zero d))

hΩ₂ : ∀ {ℓ} (z p : zero <ᴵ ℓ) (σ : Simᴵ two ℓ) → Cp A (toZ (ψᵉ′ ∅ˢ z p σ (Ωˢ two)))
hΩ₂ z p σ = viaL (toZ-≅ (selfΩ₂ z p σ)) (ZΩ₂ Good∅ z p σ tΩ₂-NF) (λ Y l → ≅→≼ (Lab-uniq l TΩ₂-label))

open Cap A h∅ hΩ₀ hΩ₁ hΩ₂ public using (capΩ; cap-T)
```

## §2 上确界严格变小

`X` 是 `TΩ2-label` 在最小环境上的树. 紧界树所有 $\Omega_\eta$ 处的计值都在 `A` 以下, 而 `A` 严格在 `X` 以下. 反方向 `tight≼X`: `X` 是上界, 所以两棵树的上确界比较有定向的答案.

```agda
tight-cap : (G : Goodᴺ (toZ TΩ2′ˢ)) → forceᴺ _ G ≼ A
tight-cap = cap-T

tight-capΩ : ∀ η {ℓ} (z p : zero <ᴵ ℓ) (σ : Simᴵ η ℓ) (G : Goodᴺ (toZ (ψᵉ′ ∅ˢ z p σ (Ωˢ η)))) → forceᴺ _ G ≼ A
tight-capΩ = capΩ

above-gap : ∀ {Y v} → Lab Y v → NF₁ v → cmpᵀ tΩ₂ v ≡ lt → suc A ≼ Y
above-gap l nv c = ≺→s≼ (Lab-oc l nv TΩ₂-label tΩ₂-NF (lt→< _ _ c))

evX₃ : U3.Ev (suc (suc (suc zero))) (U3.fz U3.⊔ (U3.fk zero U3.⊔ U3.flo (suc (suc (suc zero)))))
evX₃ = tt , ((λ q → suc (suc q)) , (λ q → q))

evX : U3.Ev (suc zero) (U3.fz U3.⊔ (U3.fk zero U3.⊔ (U3.fk zero U3.⊔ U3.fz)))
evX = tt , ((λ q → q) , ((λ q → q) , tt))

GX : U3.Lab₀ (U3.ψᵀ (U3.Ψ (U3.Ψ U3.∅ᵀ)) evX zero) tΩ2
GX = TΩ2-label evX zero

not-below : ∀ {Y W : Ordᶜ zero} → suc A ≼ Y → W ≼ A → ¬ (Y ≼ W)
not-below {Y} {W} a w yw = s≼-irrefl A (≼-trans a (≼-trans yw w))

drop-at : ∀ {Y v} → Lab Y v → NF₁ v → cmpᵀ tΩ₂ v ≡ lt →
          ∀ η {ℓ} (z p : zero <ᴵ ℓ) (σ : Simᴵ η ℓ) (G : Goodᴺ (toZ (ψᵉ′ ∅ˢ z p σ (Ωˢ η)))) → ¬ (Y ≼ forceᴺ _ G)
drop-at l nv c η z p σ G = not-below (above-gap l nv c) (capΩ η z p σ G)

module Vs (X : Ordᶜ zero) (X-label : Lab X tΩ2) where

  A≺X : suc A ≼ X
  A≺X = above-gap X-label tΩ2-NF refl

  tight-drop : (G : Goodᴺ (toZ TΩ2′ˢ)) → ¬ (X ≼ forceᴺ _ G)
  tight-drop G = not-below A≺X (tight-cap G)

  tight≼X : (G : Goodᴺ (toZ TΩ2′ˢ)) → forceᴺ _ G ≼ X
  tight≼X G = ≼-trans (tight-cap G) (≼-trans (≼-suc (≼-refl A)) A≺X)
```

**带参数的写法.** 所有比较只用 `X-label`, 所以 `X` 作参数. 第一版把 `X` 写成顶层定义并在证明里直接用, 编译时堆耗尽 (退出码 251, 上限 10G), 原因没有查. 下面 `Vs` 的 `X` 取 `GX` 的计值, 就是定理的实例.

```agda
open Vs (forceᴸ _ (proj₁ GX)) (proj₂ GX) public

Ω₃-above : ∀ {Y} → Lab Y tΩ₃ → suc A ≼ Y
Ω₃-above l = above-gap l tΩ₃-NF refl

Ω₃-tree : Ordᶜ zero
Ω₃-tree = forceᴸ _ (proj₁ (TΩ₃-label evX₃ (suc (suc zero))))

Ω₃-tree-above : suc A ≼ Ω₃-tree
Ω₃-tree-above = Ω₃-above (proj₂ (TΩ₃-label evX₃ (suc (suc zero))))

agree-Ω₂ : ∀ {ℓ} ev (z : zero <ᴵ ℓ) → A ≅ forceᴸ _ (proj₁ (TΩ₂-label′ {ℓ} ev z))
agree-Ω₂ ev z = Lab-uniq TΩ₂-label (proj₂ (TΩ₂-label′ ev z))

X′ : Ordᶜ zero
X′ = forceᴸ _ (proj₁ GX)

X-label′ : Lab X′ tΩ2
X-label′ = proj₂ GX
```

## §3 `low-term` 这条路径

`pathLow` 从 $t_{\Omega_\Omega^2}$ 走到 $\psi_0(\psi_\Omega(\psi_2(1)))$, 再走 $[2,0,0]$ 到 $\psi_0(\psi_\Omega(\Omega_2+1))$. `TΩ2-label` 的树带标签, 所以沿这条路有子树, 带同一个记号; 它严格在 `A` 之上. 紧界树的 `lowˢ` 在同一个记号位置字面是 $0$ (`low-tree`, `kind … ≡ kz`).

```agda
module Low (X : Ordᶜ zero) (X-label : Lab X tΩ2) where

  low-Y : Ordᶜ zero
  low-Y = walk X (1 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 3 ∷ 1 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 2 ∷ 0 ∷ 0 ∷ [])

  low-Y-label : Lab low-Y (ψΩ₀ Ω₂+1)
  low-Y-label = Lab-walk (1 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 3 ∷ 1 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 2 ∷ 0 ∷ 0 ∷ []) X-label
    (refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , tt)

  low-true : suc A ≼ low-Y
  low-true = above-gap low-Y-label low-NF refl

  low-true≼X : low-Y ≼ X
  low-true≼X = ≼-trans (≼-suc (≼-refl low-Y)) (≺→s≼ (Lab-oc X-label tΩ2-NF low-Y-label low-NF (lt→< _ _ refl)))
```

```agda
open Low X′ X-label′ public
```
