# 统一形 (五): $\psi_0(\Omega_{\Omega_\Omega})$ 的第一堵墙

> 接 [Uniform5Top](Uniform5Top.lagda.md), [Uniform5SynPsi](Uniform5SynPsi.lagda.md). 记号与检验在这里; 树的定义不导入记号. 结论先说:
>
> 1. **记号链 (§1, 全部 `refl`).** $\psi_0(\Omega_{\Omega_\Omega})[0]=\psi_0(\Omega_\Omega)$ 已有标签. $[1]=\psi_0(\Omega_{\Omega_{\psi_0(\Omega_\Omega)}})$. 沿 9 步路径 `p₁` 到 $\psi_0(\Omega_{\Omega_2})\to\psi_0(\Omega_{\psi_1(\Omega_\Omega)})\to\psi_0(\Omega_{\psi_1(1)})=\psi_0(\Omega_{\Omega\cdot\omega})\to\psi_0(\Omega_{\Omega\cdot3})\to\psi_0(\Omega_{\Omega\cdot2+1})$. **所以第一个超出 $\Omega+\eta$ 的项不是 $\Omega_\Omega$ 下标, 是 $\Omega\cdot2+1$.** 下标是数据树的问题在 $\psi_1(\Omega_\Omega)$ 才出现, 在那之前先撞上 §2.
> 2. **需要比较却没有字面界的第一处 (§2).** 再走 31 步 (`p₂`) 到 $W=\psi_0(\psi_{\Omega\cdot2}(\Omega_{\Omega\cdot2}+\psi_{\Omega+1}(\Omega_{\Omega\cdot2})))$, 这是标准形. $W[n]$ 含 $\psi_{\Omega+1}(\Omega_{\Omega+\gamma_n})$: 目标 $\Omega+1$, 节点下标 $\Omega+\gamma_n$, 其中 $\gamma_n$ 来自外面的闭包, 与目标毫无字面关系. `¬tri`: `Ordᴵ` 上没有全局三歧 ($\omega$ 与 $\omega'=[1,2,3,\dots]$ 互不可比), 所以 `ψᵒ` 不可能在定义时比较, 这是 `noBT` 在 `Ordᴵ` 上的形式.
> 3. **这个比较可以躲: 环境给公共上界 (§3).** Uniform5Syn/SynPsi 编译通过: 目标带地板 `fk τ`, 节点带 `ac`, 两者都 $<\ell$, `<ᴵ-dec` 在 $\ell$ 之下判定, 比较推迟到 `oev`. 树 `TQ 1 (suc zero)` ($\psi_0(\Omega_{\Omega\cdot2+1})$) 与 `TQ 2 zero` ($\psi_0(\Omega_{\Omega\cdot3})$) 是定义. 检验: 宽 3 深 9 对 $\psi_0(\Omega_{\Omega\cdot2+1})$ 无偏离, 深 6 对另外两项无偏离; `bx` 直接看 $W$ 的那一处比较, $\eta=1,2,3$ 三种结果都对. 这些是有限检验. `firstBad` 走不到 $W$ 本身: 符号树在闭包第 $\ge1$ 个链点要证书.
> 4. **标签的第一个停点是 `NF₁`, 不是树 (§4).** `¬NF-t₁`, `¬NF-W`: 这些项不在 `NF₁`, `limᴸ`/`L0`/`Lab-oc` 全部以 `NF₁` 为前提; Uniform5Clo 的顶层绕行对 `fsn t₁ 1` 这种基本列本身就不在 `NF₁` 的情形无效 (`¬NF-t₁[1]`). 所以 $\psi_0(\Omega_{\Omega_\Omega})[0]$ 有标签 (`tΩΩ0-label`), $[1]$ 没有.
> 5. **`Syn` 的边界 (§5).** $\psi_0(\Omega_{\Omega\cdot\omega})$ 的树是 `TQω` (`limA`). 再往上, 路径的第 5 站 $\psi_0(\Omega_{\psi_1(\Omega_\Omega)})$ 的基本列是 $\theta\mapsto\psi_0(\Omega_{\psi_1(\Omega_\theta)})$: 下标族对 $\theta$ 一致. $\theta=2$ 时 $\psi_1(\Omega_2)[n]$ 就是 $\psi_1$ 的迭代 ($\varepsilon_{\Omega+1}$), 所以 `Syn` 不能是固定长度的元组; 见 [Uniform5Assess](Uniform5Assess.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Uniform5Wall where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Align.Level
open import OCF.Align.Prefix using (Ord₊ˢ; Ordˢ; walkˢ; kind; Kind; kz; ks; kl; kĉ; kc; sqˢ)
import OCF.Align.EBO as E
open E using (T; PT; fsn; cof; c0; c1; cω; cΩ; sucT; 𝟏; Ωt; natT) renaming (ψ to ψᵗ)
open import OCF.Align.StandardOmega using (walk; NF₁; n∷; nψ; sC; sΩ)
open import OCF.Align.Stage2 using (Ωᵗ)
open import OCF.Align.Uniform3Base using (Flr; fz; fk; _⊔_; Ev; ψ₀ᵗ; Run)
open import OCF.Align.Uniform4Base using (Fl)
open import OCF.Align.Uniform4Head using (Ωp)
open import OCF.Align.Uniform4Expt using (one)
open import OCF.Align.Uniform4TwoWalk using (agree; firstBad)
open import OCF.Align.Uniform3Base using (flo)
open import OCF.Align.Uniform4Base using (_<ᴸ_; zero; suc)
open import OCF.Align.Uniform5Syn using (Q; _⊕_; ι↓; Ω̇; owk; oev; oΩ; ol)
open import OCF.Align.Uniform5SynPsi using (TQ; ψᵒ; td)
open import OCF.Align.Uniform3Base using (limA; Lab₀)
import OCF.Align.Uniform4Label as U4
import OCF.Align.Uniform4Base as U4B
import OCF.Align.Uniform4Two as U2
```

## §1 记号链

```agda
tΩΩ : T
tΩΩ = ψ₀ᵗ (Ωt (Ωt Ωᵗ))

_ : fsn tΩΩ 0 ≡ ψ₀ᵗ (Ωt Ωᵗ)
_ = refl

_ : fsn tΩΩ 1 ≡ ψ₀ᵗ (Ωt (Ωt (ψ₀ᵗ (Ωt Ωᵗ))))
_ = refl

Ω·2 : T
Ω·2 = Ωp ∷ Ωp ∷ []

t₁ : T
t₁ = ψ₀ᵗ (Ωt (sucT Ω·2))

t₃ : T
t₃ = ψ₀ᵗ (Ωt (Ωp ∷ Ωp ∷ Ωp ∷ []))

p₁ : List ℕ
p₁ = 1 ∷ 0 ∷ 0 ∷ 2 ∷ 1 ∷ 0 ∷ 0 ∷ 3 ∷ 0 ∷ []

_ : walk tΩΩ p₁ ≡ t₁
_ = refl

ψ₁ : T → T
ψ₁ a = ψᵗ (natT 1) a ∷ []

-- 路径上的前几站
_ : walk tΩΩ (1 ∷ 0 ∷ 0 ∷ 2 ∷ []) ≡ ψ₀ᵗ (Ωt (Ωt (natT 2)))
_ = refl
_ : walk tΩΩ (1 ∷ 0 ∷ 0 ∷ 2 ∷ 1 ∷ []) ≡ ψ₀ᵗ (Ωt (ψ₁ (Ωt Ωᵗ)))
_ = refl
_ : walk tΩΩ (1 ∷ 0 ∷ 0 ∷ 2 ∷ 1 ∷ 0 ∷ 0 ∷ []) ≡ ψ₀ᵗ (Ωt (ψ₁ (natT 1)))
_ = refl
_ : walk tΩΩ (1 ∷ 0 ∷ 0 ∷ 2 ∷ 1 ∷ 0 ∷ 0 ∷ 3 ∷ []) ≡ t₃
_ = refl
```

## §2 没有字面界的比较

```agda
ΩΩ·2 : PT
ΩΩ·2 = ψᵗ Ω·2 []

Ω+1 : T
Ω+1 = sucT (Ωp ∷ [])

Ω+2 : T
Ω+2 = sucT Ω+1

W : T
W = ψ₀ᵗ (ψᵗ Ω·2 (ΩΩ·2 ∷ ψᵗ Ω+1 (ΩΩ·2 ∷ []) ∷ []) ∷ [])

p₂ : List ℕ
p₂ = 2 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 2 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 2 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 1 ∷ []

_ : walk t₁ p₂ ≡ W
_ = refl

-- W[0] 的内层: 目标 Ω+1, 节点下标 Ω+1 (γ₀ = 1)
_ : fsn W 0 ≡ ψ₀ᵗ (ψᵗ Ω·2 (ΩΩ·2 ∷ ψᵗ Ω+1 (Ωt Ω+1) ∷ []) ∷ [])
_ = refl

-- W[1] 的内层: 目标 Ω+1, 节点下标 Ω+γ₁, γ₁ = W[0]
_ : fsn W 1 ≡ ψ₀ᵗ (ψᵗ Ω·2 (ΩΩ·2 ∷ ψᵗ Ω+1 (Ωt (Ωp ∷ fsn W 0)) ∷ []) ∷ [])
_ = refl

-- Ordᴵ 上没有全局三歧: ω 与 ω₁ = [1,2,3,…]
ω₁ : Ordᴵ
ω₁ = lim (λ n → natᴵ (suc n)) (λ n → natᴵ-step (suc n))

nl : ∀ m {f s} → lim f s <ᴵ natᴵ m → ⊥
nl zero ()
nl (suc zero) (suc ())
nl (suc (suc m)) (suc q) = nl (suc m) q

¬tri : (∀ a b → a ≺ᴵ b ⊎ b ≺ᴵ a ⊎ a ≅ᴵ b) → ⊥
¬tri t with t ωᴵ ω₁
... | inj₁ (via (l≅ h) (lim n q)) = nl (suc n) q
... | inj₂ (inj₁ (via (l≅ h) (lim n q))) = nl n q
... | inj₂ (inj₂ (l≅ h)) with h 0
...   | ()
```

## §3 树: 路径检验

`T₁`, `T₃`: `Uniform5SynPsi` 的树在封闭环境 $\ell=1$ 处的计值. `firstBad` 同 Uniform4TwoWalk. `chk`: 沿给定路径逐点比较树的种类与记号的共尾度.

```agda
ev₁ : Ev one Fl
ev₁ = tt , (λ q → q)

T₁ T₃ T₂ : Ordˢ zero
T₁ = TQ 1 (suc zero) ev₁ zero
T₃ = TQ 2 zero ev₁ zero
T₂ = TQ 1 zero ev₁ zero

_ : firstBad 6 T₂ (ψ₀ᵗ (Ωt Ω·2)) ≡ []
_ = refl

_ : firstBad 6 T₁ t₁ ≡ []
_ = refl

_ : firstBad 6 T₃ t₃ ≡ []
_ = refl

_ : firstBad 9 T₁ t₁ ≡ []
_ = refl
```

**`oev` 的比较, 直接看 `Q`.** `firstBad` 走不过闭包节点的 $n\ge1$ 孩子 (符号树在第 $\ge1$ 个链点要证书 `forceᴸ`, 而证书要标签, 标签要 §4 的标准形). 所以 $W$ 的关键比较在 `Q` 上直接检验: `bx η` 是闭包分支 $\eta$ 处的 $\psi_{\Omega+1}(\Omega_{\Omega+\eta})$. 记号: $\eta=1$ 时穿透 (节点 $\Omega<$ 目标 $\Omega+1$), $\eta=2,3$ 时折叠 (节点 $\ge$ 目标).

```agda
data Hd : Set where
  hΩ hl hother : Hd

hd : ∀ {m c φ ℓ} → Q m c φ → Ev ℓ φ → Hd
hd (owk le x) e = hd x (le e)
hd (oev f) e = hd (f e) e
hd (oΩ fe q h) e = hΩ
hd (ol F) e = hl
hd _ e = hother

num : ℕ → Ordᴵ
num = natᴵ

bx : ∀ η → Q 0 (num 1) ((Fl ⊔ fk (num 1)) ⊔ (Fl ⊔ flo η))
bx η = ψᵒ (td {α = zero} zero (num 1)) (ι↓ zero (Ω̇ 0 η))

evη : ∀ a → (∀ {c} → c <ᴵ suc (num a) → c <ᴵ num 5) → Ev (num 5) ((Fl ⊔ fk (num 1)) ⊔ (Fl ⊔ fk (num a)))
evη a σ = ((tt , (λ q → suc (suc (suc (suc q))))) , (λ q → suc (suc (suc q)))) , ((tt , (λ q → suc (suc (suc (suc q))))) , σ)

-- η = 3: 节点 Ω+2 > 目标 Ω+1: 折叠
_ : hd (bx (num 3)) (evη 2 (λ q → suc (suc q))) ≡ hl
_ = refl

_ : cof (ψᵗ Ω+1 (Ωt (sucT Ω+2)) ∷ []) ≡ cω
_ = refl

-- η = 2: 节点 Ω+1 = 目标 Ω+1: ν+1 = Ω+2 > Ω+1, 折叠
_ : hd (bx (num 2)) (evη 1 (λ q → suc (suc (suc q)))) ≡ hl
_ = refl

_ : cof (ψᵗ Ω+1 (Ωt Ω+2) ∷ []) ≡ cω
_ = refl

-- η = 1: 节点 Ω < 目标 Ω+1: 穿透
_ : hd (bx (num 1)) (evη 0 (λ q → suc (suc (suc (suc q))))) ≡ hΩ
_ = refl

_ : cof (ψᵗ Ω+1 (Ωt Ω+1) ∷ []) ≡ cΩ (Ωp ∷ [])
_ = refl
```

## §4 标签的停点: `NF₁`

`Sb` 只含可数与 $\Omega+$可数, 所以下面每一项都不在 `NF₁`. 顶层绕行 (`clo†`) 只有在基本列本身落回 `NF₁` 时才有用; 这里基本列不落回.

```agda
¬NF-t₁ : NF₁ t₁ → ⊥
¬NF-t₁ (n∷ (nψ _ _ (n∷ (nψ _ (sC ()) _ _) _ _) _) _ _)
¬NF-t₁ (n∷ (nψ _ _ (n∷ (nψ _ (sΩ ()) _ _) _ _) _) _ _)

¬NF-W : NF₁ W → ⊥
¬NF-W (n∷ (nψ _ _ (n∷ (nψ _ (sC ()) _ _) _ _) _) _ _)
¬NF-W (n∷ (nψ _ _ (n∷ (nψ _ (sΩ ()) _ _) _ _) _) _ _)

-- 基本列的项仍不在 NF₁ (顶层绕行不够): ψ₀(Ω_{Ω·2+1})[1]
¬NF-t₁[1] : NF₁ (fsn t₁ 1) → ⊥
¬NF-t₁[1] (n∷ (nψ _ _ (n∷ (nψ _ (sC ()) _ _) _ _) _) _ _)
¬NF-t₁[1] (n∷ (nψ _ _ (n∷ (nψ _ (sΩ ()) _ _) _ _) _) _ _)
```

`tΩΩ[0]` 已有标签, 且树与 Uniform4 相同.

```agda
tΩΩ0-label : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → Lab₀ (U4B.ψ̄ (U4B.Ω̇ 0) ev z) (fsn tΩΩ 0)
tΩΩ0-label = U4.TΩ-label 0
```

## §5 `Syn` 的边界

```agda
-- ψ₀(Ω_{Ω·ω}): 对 m 取极限
TQω : Run Fl
TQω = limA 0 (λ n → TQ n zero)

Ω·ω : T
Ω·ω = ψ₁ (natT 1)

_ : fsn (ψ₀ᵗ (Ωt Ω·ω)) 2 ≡ ψ₀ᵗ (Ωt Ω·2)
_ = refl

-- 第 5 站的基本列: 下标 ψ₁(Ω_θ) 对 θ 一致
_ : ∀ θ → E.fsT (Ωt (ψ₁ (Ωt Ωᵗ))) θ ≡ Ωt (ψ₁ (Ωt θ))
_ = λ θ → refl

_ : cof (ψ₁ (Ωt Ωᵗ)) ≡ cΩ []
_ = refl

-- θ = 2: ψ₁(Ω₂) 是 ψ₁ 的迭代, 下标共尾度 ω
_ : cof (ψ₁ (Ωt (natT 2))) ≡ cω
_ = refl

_ : fsn (ψ₁ (Ωt (natT 2))) 1 ≡ ψ₁ (ψ₁ (Ωt (natT 1)))
_ = refl
```
