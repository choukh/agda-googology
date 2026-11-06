# UIP 条件下的回灌 (二): 第一级的闭项

> 不含记号. 入口 [UipFb](UipFb.lagda.md). 把 [UipFbChain](UipFbChain.lagda.md) 的升界链实例化在 `Slot` 的第一级新种类上: 坐标 $c_0=1$ (`fin 1`), 坐标类型 `HB (G₀ 1) = HB S₁` (第二个新种类的高度, `UipFbChain.E-κ₂`). 读回取两种种类的折叠在第 2 层目标上的输出, 读成 `HB S₁` 的高度 ([HtTowerNFb](HtTowerNFb.lagda.md) 的 `O.out₂` 与 [HtTowerNRead](HtTowerNRead.lagda.md) 的 `rd₂`, 不改): $\delta(h)=\mathrm{rd}_2(1,\mathrm{out}_2\,h)$. 槽从 $0$ 起: $x_0=0$, $x_{n+1}=x_n\boxplus\delta(x_n)$.
>
> - **外层世界 $(0, 2)$** (`w₂`): 可入坐标只有 $0,1,2$, 每个只有一条证据 (`uniq₂`), 所以**一切以它为外层的世界都相干, 无条件** (`coh-b₂`), 坐标比较无条件 (`cmp-b₂`). 链在这里不需要 `UIPᴴ`.
> - **闭项 `Tᵁ = T⁺ (hl x)`**: 两种种类的折叠 (`HtTowerFClosed.T⁺`, 不改) 作用在槽的 ℕ-极限上. 无模块参数, 无前提; 合法 `Lg-Tᵁ` (由形状给出), FGH `fghᵁ`. 值在 `A` 里 (布劳威尔树).
> - **第一格** (`x₁≡`, `refl`): $x_1 = 0\boxplus\Lambda_1$, $\Lambda_1$ 就是 `HtTowerNFb.Λs₂ 1` (`Fb₂ 0`). 它的最外是新种类的 $\Omega$-极限 (`x₁-ΩH`), 含新种类节点 (`x₁-new`), 与任何 $H_0$ 高度的嵌入都不互模拟 (`¬x₁≈up`). 它在第 1 个世界里有界 (`bd-x₁`). 所以 `TdPlusVal.top-bd` 的同形物 (级顶种类有界的坐标都是 $H_0$ 的嵌入) 在这条链上不成立 (`¬top-bd₁`).
> - **外层世界 $(0,\omega)$** (`wω`): 一切有限坐标同时可入 (`all-adm`), 证据不唯一. 同一条链 (坐标 $1$, 证据 `hlim 1 hself`) 在这里的相干是**条件定理** (`cohω`, 条件 `UIPᴴ`), 坐标比较同样 (`cmpω`). 这是本路唯一实际用到 `UIPᴴ` 的地方. 链的槽与 $(0,2)$ 上的逐格相等 (`same`, 连同合法性), 闭项的输入互模拟 (`inω≈`): `UIPᴴ` 不改闭项.
>
> **范围.** `Tᵁ` 的回灌在折叠之外 (同 `HtOut.Fb`, `HtTowerNFb.Fb₂`): 槽的值作为**层**进 `T⁺`, 不作为某个种类的**坐标**. 在折叠之内回灌 (对照 `RunM`: 以 `HB S₁` 为坐标的种类的闭包, 读第 2 层输出升它的界) 要三种种类的折叠, 没有写 (入口第一个障碍). 闭项本身不依赖 `UIPᴴ`; `UIPᴴ` 只进相干.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延 (`UIPᴴ` 只作模块参数).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UipFbClosed where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Bool using (Bool; true)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import OCF.Align.CumReadCF using (A; azero; Lg)
import OCF.Free.Level as FL
open import OCF.Align.HtTowerTy
open import OCF.Align.AdmWIf
open import OCF.Align.AdmWCoh using (fin; lg-fin; ω₀; Lg-ω₀; wz; lg-wz; UIPᴴ; coh≡→cmpK)
open import OCF.Align.DiagK3One using (NoNew; up-noNew)
open import OCF.Align.DiagK3Zero using (_≈_; ≈z; ≈s; ≈l; ≈Ω)
open import OCF.Align.HtTowerFTree using (Ht; H₀)
open import OCF.Align.HtTowerFClosed using (T⁺; Lg-T⁺; ord)
open import OCF.Align.HtTowerNRead using (rd₂; Lg-rd₂)
open import OCF.Align.HtTowerNFb using (module O; Λs₂; isΩH)
open import OCF.Align.UipFbChain using (module Chain; uip→RC)
open Slot
```

## §1 起点: 全 0 的分量

```agda
vz : ∀ w → Cmp w
vz w c p = wz (up c) , hz

lgvz : ∀ w → LgO w → LgWᴮ (w , vz w)
lgvz w lo = lo , λ c p → lg-wz (up c) , tt

cohvz : ∀ w → Coh≡ (w , vz w)
cohvz w c p p′ = refl
```

## §2 外层世界 $(0,2)$: 证据唯一, 相干无条件

```agda
w₂ : Out
w₂ = azero , fin 2

lo₂ : LgO w₂
lo₂ = tt , lg-fin 2

uniq₂ : ∀ {a c} (p p′ : c ⊲[ a ] fin 2) → p ≡ p′
uniq₂ hself hself = refl
uniq₂ hself (hsuc (hsuc ()))
uniq₂ (hsuc hself) (hsuc hself) = refl
uniq₂ (hsuc hself) (hsuc (hsuc ()))
uniq₂ (hsuc (hsuc hself)) (hsuc (hsuc hself)) = refl

coh-b₂ : ∀ {a} (v : Cmp (a , fin 2)) → Coh≡ ((a , fin 2) , v)
coh-b₂ v c p p′ = cong (v c) (uniq₂ p p′)

cmp-b₂ : ∀ {a} (v : Cmp (a , fin 2)) → LgWᴮ ((a , fin 2) , v) → ∀ {k y y′} →
         Bdᴮ k y ((a , fin 2) , v) → Bdᴮ k y′ ((a , fin 2) , v) →
         Prᴮ k ((a , fin 2) , v) y′ y ⊎ Prᴮ k ((a , fin 2) , v) y y′
cmp-b₂ v lW by by′ = coh≡→cmpK (step S₀) (inj₂ tt) (λ c → step (G₀ c)) by by′ lW (coh-b₂ v)
```

## §3 读回与链

```agda
δ⋆ : (h : Ht) → LgB h → Ht
δ⋆ h lh = rd₂ (tt , tt) (hs hz) (O.out₂ h lh)

lδ⋆ : ∀ h lh → LgB (δ⋆ h lh)
lδ⋆ h lh = Lg-rd₂ (tt , tt) (hs hz) (O.out₂ h lh) tt

p₁ : AdmE w₂ (fin 1)
p₁ = hsuc hself

module C₁ = Chain w₂ lo₂ (vz w₂) (lgvz w₂ lo₂) (fin 1) p₁ δ⋆ lδ⋆
```

## §4 闭项

```agda
Tᵁ : A
Tᵁ = T⁺ C₁.Λᶜ C₁.lΛᶜ

Lg-Tᵁ : Lg Tᵁ
Lg-Tᵁ = Lg-T⁺ C₁.Λᶜ C₁.lΛᶜ

fghᵁ : ℕ → ℕ
fghᵁ = FL.FGH (ord Tᵁ)

-- 链上每个世界相干, 坐标可比, 都无条件
coh₂ : ∀ n → Coh≡ (w₂ , C₁.V n)
coh₂ n = coh-b₂ (C₁.V n)

cmp₂ : ∀ n {k y y′} → Bdᴮ k y (w₂ , C₁.V n) → Bdᴮ k y′ (w₂ , C₁.V n) →
       Prᴮ k (w₂ , C₁.V n) y′ y ⊎ Prᴮ k (w₂ , C₁.V n) y y′
cmp₂ n = cmp-b₂ (C₁.V n) (C₁.chain-lg n)
```

## §5 第一格: 新种类的节点, 有界

```agda
x₁≡ : C₁.x 1 ≡ hz ⊞ proj₁ (Λs₂ 1)
x₁≡ = refl

x₁-ΩH : isΩH (C₁.x 1) ≡ true
x₁-ΩH = refl

x₁-new : ¬ NoNew (C₁.x 1)
x₁-new ()

noNew-≈ : ∀ {S} {a b : HB (step S)} → a ≈ b → NoNew b → NoNew a
noNew-≈ ≈z n = tt
noNew-≈ (≈s p) n = noNew-≈ p n
noNew-≈ (≈l p) n = λ k → noNew-≈ (p k) (n k)
noNew-≈ (≈Ω {κ = inj₁ κ} p) n = λ c → noNew-≈ (p c) (n c)

¬x₁≈up : ∀ (h : H₀) → ¬ (C₁.x 1 ≈ up h)
¬x₁≈up h e = x₁-new (noNew-≈ e (up-noNew h))

bd-x₁ : Bdᴮ (fin 1 , inj₂ tt) (C₁.x 1) (w₂ , C₁.V 1)
bd-x₁ = p₁ , hself

-- TdPlusVal.top-bd 的同形物在这条链上不成立
¬top-bd₁ : ¬ (∀ y → Bdᴮ (fin 1 , inj₂ tt) y (w₂ , C₁.V 1) → Σ H₀ (λ h → y ≡ up h))
¬top-bd₁ tb with tb (C₁.x 1) bd-x₁
... | h , e = x₁-new (subst NoNew (sym e) (up-noNew h))
```

## §6 外层世界 $(0,\omega)$: 一切有限坐标同时可入, 相干要 `UIPᴴ`

```agda
wω : Out
wω = azero , ω₀

loω : LgO wω
loω = tt , Lg-ω₀

all-adm : ∀ n → AdmE wω (fin n)
all-adm n = hlim n hself

module Cω = Chain wω loω (vz wω) (lgvz wω loω) (fin 1) (all-adm 1) δ⋆ lδ⋆

-- 同一个读回, 同一条链: 槽与它的合法性逐格相等, 输入互模拟
Fₓ : Σ Ht LgB → Σ Ht LgB
Fₓ (h , lh) = h ⊞ δ⋆ h lh , Lg-⊞ h (δ⋆ h lh) lh (lδ⋆ h lh)

same : ∀ n → _≡_ {A = Σ Ht LgB} (Cω.x n , Cω.lx n) (C₁.x n , C₁.lx n)
same zero = refl
same (suc n) = cong Fₓ (same n)

≈-refl′ : ∀ {S} (y : HB S) → y ≈ y
≈-refl′ hz = ≈z
≈-refl′ (hs y) = ≈s (≈-refl′ y)
≈-refl′ (hl f) = ≈l (λ n → ≈-refl′ (f n))
≈-refl′ (hΩ κ g) = ≈Ω (λ c → ≈-refl′ (g c))

inω≈ : Cω.Λᶜ ≈ C₁.Λᶜ
inω≈ = ≈l (λ n → subst (λ z → z ≈ C₁.x n) (sym (cong proj₁ (same n))) (≈-refl′ (C₁.x n)))

module _ (u : UIPᴴ) where
  cohω : ∀ n → Coh≡ (wω , Cω.V n)
  cohω = Cω.chain-coh (uip→RC u) (cohvz wω)

  cmpω : ∀ n {k y y′} → Bdᴮ k y (wω , Cω.V n) → Bdᴮ k y′ (wω , Cω.V n) →
         Prᴮ k (wω , Cω.V n) y′ y ⊎ Prᴮ k (wω , Cω.V n) y y′
  cmpω = Cω.chain-cmp (uip→RC u) (cohvz wω)
```
