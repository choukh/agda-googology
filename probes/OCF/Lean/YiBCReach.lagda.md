# ℕ 极限孩子里，嵌入的块到达换基行
编译定理，形状档（`refl` 与 `kp-z`），不读记号：同步对象的孩子 `a₁ ω`（ω 代替真实链点，同 `YiRKCell` 取 d = ω；真实链孩子同为 ℕ 极限形状，`YiRKChain.child-L`）上，孩子 1 的底把孩子 0 的左加项经 `way` 嵌进孩子 1（`way-row`，对任意 Ok），在孩子 1 顶的 Ω 结点上走换基行的 `seen` 一支（`rebase-row`，对任意 Ok 与块）；`oₛ` 下块是 `yₑ`（`reach`），顶是嵌入，不在码域里（`yₑ∉`）。
`R1`、`R2`、`R2₀`、`R3`：`Ωt (a₁ ω)` 第二个部分和朝第 0 层折时，这个底值就是孩子 1 第 0 支里那条回灌链的起点。
不否定什么：不涉及值；`a₁ (chain m)` 本身未展开（链点的分量未知），是否同样到达是判断。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBCReach where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀; node⁺)
open import OCF.Lean.YiRWCheck using (kp-z)
open import OCF.Lean.YiTBRow using (h₁; nat)
open import OCF.Lean.YiTBTab using (ωᶜ)
open import OCF.Lean.YiBSBase
import OCF.Lean.YiBSFold as BS
open import OCF.Lean.YiBSRead using (Domain)
open import OCF.Lean.YiRKChain using (a₁)
open import OCF.Lean.YiBCCover using (IsJust; oₛ; rbₛ)
open import OCF.Lean.YiBCNeg using (IsUp; ∉dom)
```

## 层号的形状

`a₁ ω = nd sL G`；`G 1` 的顶是下标为第 0 层的 Ω 结点，孩子 `H₁ c` 是后继形状，`H₁ 0` 的孩子就是 `G 0`。

```agda
one : L
one = nd sS (λ _ → zero)

ℓω : L
ℓω = a₁ ωᶜ

G : ℕ → L
G n = tw 1 ⊕ (zero ⊕ ↑ (h₁ ωᶜ) (cum (λ n → proj₁ (upz {s = sL} {h = λ n → h₁ (nat n)} n (Ωt (h₁ (nat n))))) n))

H₁ : Tr zero → L
H₁ c = nd sS (λ _ → tw 1 ⊕ (zero ⊕ (one ⊕ (zero ⊕ ↑ zero c))))

ℓω-shape : ℓω ≡ nd sL G
ℓω-shape = refl

G1 : G 1 ≡ nd (sΩ zero) H₁
G1 = refl

H₁0 : H₁ zero ≡ nd sS (λ _ → G 0)
H₁0 = refl

oω : Ok ℓω
oω = proj₂ oₛ ωᶜ

rω : Rb ℓω
rω = proj₂ rbₛ ωᶜ

fromJust : {A : Set} (m : Maybe A) → IsJust m → A
fromJust (just a) _ = a

S₁ : Schema zero H₁
S₁ = fromJust (proj₁ (proj₂ rω 1)) tt

top₁ : proj₁ (proj₂ rω 1) ≡ just S₁
top₁ = refl

floor₁ : floor S₁ ≡ tw 1
floor₁ = refl
```

## 嵌入与换基行

`x₀` 是 `Ωt ℓω` 的第一个部分和（孩子 0 的块）；目标 `G 0` 经孩子 1、孩子 1 顶的分支 0、再经后继孩子到达。

```agda
x₀ : Tr ℓω
x₀ = proj₁ (upz {s = sL} {h = G} 0 (Ωt (G 0)))

w₀ : G 0 ≤ ℓω
w₀ = inc 1 (inc zero (inc tt self))

way-row : (o : Ok ℓω) (r : Rb ℓω) (B : Base ℓω) (β : Tr⁺ (G 0))
  → BS.ψ ℓω o r B (G 0) w₀ β x₀
  ≡ BS.ψ (G 1) (proj₂ o 1) (proj₂ r 1) (λ i u → B i (inc 1 u)) (G 0) (inc zero (inc tt self)) β
      (proj₁ (emb (G 1) (proj₂ o 1) (self ∙ proj₁ o 0) (Ωt (G 0))))
way-row o r B β = refl

rebase-row : (o′ : Ok (G 1)) (B′ : Base (G 1)) (β : Tr⁺ (G 0)) (c : Tr zero) (y : Tr (H₁ c)) (e : H₁ c ⊢ zero ◃ y)
  → BS.ψ (G 1) o′ (proj₂ rω 1) B′ (G 0) (inc zero (inc tt self)) β (up zero c y e)
  ≡ seen S₁ (G 0) (downOk (H₁ zero) (proj₂ o′ zero) (G 0) (inc tt self)) (lift (tw 1) one) β c
      ⊞ BS.ψ (H₁ c) (proj₂ o′ c) (proj₂ (proj₂ rω 1) c) (B₀ (H₁ c)) zero (z≤ (H₁ c)) (Ωt zero) y
rebase-row o′ B′ β c y e = refl

yₑ : Tr (H₁ zero)
yₑ = proj₁ (upz {s = sS} {h = λ _ → G 0} tt (Ωt (G 0)))

o₁ : Ok (H₁ zero)
o₁ = proj₂ (proj₂ oω 1) zero

reach : (B : Base ℓω) (β : Tr⁺ (G 0)) → BS.ψ ℓω oω rω B (G 0) w₀ β x₀
  ≡ seen S₁ (G 0) (downOk (H₁ zero) o₁ (G 0) (inc tt self)) (lift (tw 1) one) β zero
      ⊞ BS.ψ (H₁ zero) o₁ (proj₂ (proj₂ rω 1) zero) (B₀ (H₁ zero)) zero (z≤ (H₁ zero)) (Ωt zero) yₑ
reach B β = refl

yₑ-up : IsUp yₑ
yₑ-up = tt

yₑ∉ : Domain S₁ zero yₑ → ⊥
yₑ∉ = ∉dom S₁ zero yₑ tt
```

## 这一格在折叠里被用到

`x₁` 是 `Ωt ℓω` 的第二个部分和。`R1`：孩子 1 的底是折 `x₀`；`R2`、`R2₀`：孩子 1 顶不保留（朝第 0 层），链从分支 0 起；`R3`：`H₁ 0` 里那条回灌链的起点是底在 `(G 0, inc tt self)` 的值，即 `reach` 的左边（β 取 `B (G 0) w₀`）。

```agda
x₁ : Tr ℓω
x₁ = x₀ + proj₁ (upz {s = sL} {h = G} 1 (Ωt (G 1)))

x₁-eq : x₁ ≡ cum (λ n → proj₁ (upz {s = sL} {h = G} n (Ωt (G n)))) 1
x₁-eq = refl

base₁ : (o : Ok ℓω) (r : Rb ℓω) → Base ℓω → Base (G 1)
base₁ o r B i u = BS.ψ ℓω o r B i (inc 1 u) (B i (inc 1 u)) x₀

R1 : (o : Ok ℓω) (r : Rb ℓω) (B : Base ℓω) (β : Tr⁺ zero)
  → BS.ψ ℓω o r B zero (z≤ ℓω) β x₁
  ≡ BS.ψ (G 1) (proj₂ o 1) (proj₂ r 1) (base₁ o r B) zero (z≤ (G 1)) (BS.ψ ℓω o r B zero (z≤ ℓω) β x₀) (proj₁ (Ωt (G 1)))
R1 o r B β = refl

g₁ : Tr zero → Tr (G 1)
g₁ z = proj₁ (upz {s = sΩ zero} {h = H₁} z (Ωt (H₁ z)))

s₁ : Ok (G 1) → Rb (G 1) → Base (G 1) → Tr zero → Tr zero
s₁ o′ r′ B′ z = proj₁ (BS.ψ (G 1) o′ r′ B′ zero (ink self) (B′ zero (ink self)) (g₁ z))

R2 : (o′ : Ok (G 1)) (r′ : Rb (G 1)) (B′ : Base (G 1)) (β : Tr⁺ zero)
  → BS.ψ (G 1) o′ r′ B′ zero (z≤ (G 1)) β (proj₁ (Ωt (G 1)))
  ≡ limc⁺ (λ n → BS.ψ (G 1) o′ r′ B′ zero (z≤ (G 1)) β (g₁ (iter (s₁ o′ r′ B′) zero n)))
R2 o′ r′ B′ β = cong (λ m → node⁺ m (λ z → BS.ψ (G 1) o′ r′ B′ zero (z≤ (G 1)) β (g₁ z)) (s₁ o′ r′ B′))
  (kp-z (G 1) o′ (inj₁ (inj₁ tt)) (z≤ (G 1)))

R2₀ : (o′ : Ok (G 1)) (r′ : Rb (G 1)) (B′ : Base (G 1)) (β : Tr⁺ zero)
  → BS.ψ (G 1) o′ r′ B′ zero (z≤ (G 1)) β (g₁ zero)
  ≡ BS.ψ (H₁ zero) (proj₂ o′ zero) (proj₂ r′ zero) (λ i u → B′ i (inc zero u)) zero (z≤ (H₁ zero)) β (proj₁ (Ωt (H₁ zero)))
R2₀ o′ r′ B′ β = refl

g₂ : Tr (G 0) → Tr (H₁ zero)
g₂ c = proj₁ (upz {s = sS} {h = λ _ → G 0} tt (suc c , z◃ c ◃s))

s₂ : Ok (H₁ zero) → Rb (H₁ zero) → Base (H₁ zero) → Tr (G 0) → Tr (G 0)
s₂ o₂ r₂ B₂ z = proj₁ (BS.ψ (H₁ zero) o₂ r₂ B₂ (G 0) (inc tt self) (B₂ (G 0) (inc tt self)) (g₂ z))

R3 : (o₂ : Ok (H₁ zero)) (r₂ : Rb (H₁ zero)) (B₂ : Base (H₁ zero)) (β : Tr⁺ zero)
  → BS.ψ (H₁ zero) o₂ r₂ B₂ zero (z≤ (H₁ zero)) β (proj₁ (Ωt (H₁ zero)))
  ≡ limc⁺ (λ n → BS.ψ (H₁ zero) o₂ r₂ B₂ zero (z≤ (H₁ zero)) β (g₂ (iter (s₂ o₂ r₂ B₂) zero n)))
R3 o₂ r₂ B₂ β = refl

start : (B : Base ℓω) → (λ i u → base₁ oω rω B i (inc zero u)) (G 0) (inc tt self)
  ≡ BS.ψ ℓω oω rω B (G 0) w₀ (B (G 0) w₀) x₀
start B = refl
```
