# 差树上的值关系 (六): 实例

> 不含记号. 入口 [DVal](DVal.lagda.md).
>
> 1. **动作.** `StepV₀`: `Step` 在目标第 0 层满足 `DValSound.HA₁`, 对一切世界. $\psi_0(\Omega_{\Omega+1})$ 里顶层节点 `ni {k = 1}` 在目标第 0 层上升时, 第 1 层链的动作 `Ai accTop … (λ _ _ _ → n1) … A₁` 在 `C.self` 处字面归约到 `Step` (`HA-ai`, 由检查器归约). 所以 `snd` 的前提对那条链成立.
> 2. **`L1Val` 的场景.** `mono-L1`: 在 [L1ValBase](L1ValBase.lagda.md) §4 的场景 (世界 1, 动作 `Step`, 起点 `Ys`) 里, $x\sqsubseteq^{\mathsf d}x'$ ⇒ `val x ≤ val x′`. 推论: `L1Val` 的三对反例都**不**在关系里 (`¬rel-sup`, `¬rel-shape`, `¬rel-κ`). 那里否定的是 `toB` 读法; 这里的关系把它们排除了, 是定理.
> 3. **无节点部分按值比** (`cong↑`): 第 0 层树 $z$ 抬到第 1 层 (`up`) 之后, $\mathrm{toA}\,z\le\mathrm{toA}\,z'$ ⇒ `up z ⊑ᵈ up z′`. 这是 `DValCanon.Gen` 的第二个实例, 下标只有一个; 规则全部来自 `⊑ᵈ` 的构造子. 这就是 `L1Val` §2 第三条 "第 0 层的部分按值比, 经规范形".
> 4. **折叠产出的树满足判据** (`Rf`): $\Omega_1$ 的差树 `Ωd one`, `Step` 在目标第 1 层的输出 (状态的第 1 层差自比时), `mid₁` 的第一段 `CvFoldInst.Aᵐ`.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.DValInst where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; asuc; _⊲_; Lg; ss; z⊲; Tg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl)
open import OCF.Align.SumOneTree using (D; D̂; n0; n1; _⨾_; nl; ni; nκ; nw; sum; pt; cnt; top; Ωd)
import OCF.Align.SumOneClosed as F
open import OCF.Align.LayerTrOne using (one)
open import OCF.Align.BrwMidZero using (toA)
open import OCF.Align.DValTree
open import OCF.Align.DValCanon using (pre; module Gen)
import OCF.Align.DValSound as S
import OCF.Align.L1ValBase as LB
import OCF.Align.L1ValSup as LS
import OCF.Align.L1ValShape as LH
import OCF.Align.L1ValKappa as LK
open import OCF.Align.CvFoldInst using (Aᵐ)
```

## §1 `Step` 满足 `HA₁`

```agda
module _ {W : A} (lW : Lg W) (ll : one ⊲ W) where
  open S lW ll

  StepA : Act₁
  StepA _ _ _ Y = F.Step Y

  StepV₀ : HA₁ StepA
  StepV₀ w w′ c c′ Y Y′ cb r = l≤ (λ n → ≤l n (go n))
    where
    s  = F.yc (F.d Y) Z.τ₀ tt
    s′ = F.yc (F.d Y′) Z.τ₀ tt
    go : ∀ n → pt c (λ _ → Ωd azero C.self tt ⨾ s) n ≤ pt c′ (λ _ → Ωd azero C.self tt ⨾ s′) n
    go zero = cb
    go (suc n) = Z.smono (s≤ (go n)) (toV0 s s′ r)

  -- 顶层分支 n1 经 Ai 归约到 Step: 第 1 层链的动作, 对顶层节点的一切位置
  HA-ai : ∀ {W₀} (r : one ⊲ W₀) (q₀ : W₀ ⊲ W) (kW : one ⊲ W) (w : D̂ W) →
          HA₁ (F.Ai F.accTop r (λ _ _ _ → n1) q₀ kW tt F.A₁ w)
  HA-ai r q₀ kW w = StepV₀
```

## §2 `L1Val` 的场景

```agda
module S₁ = S {one} tt C.self

mono-L1 : ∀ {x x′ : D one one} → x ⊑ᵈ x′ → LB.val x ≤ LB.val x′
mono-L1 h = S₁.snd h LB.StepA₁ (StepV₀ tt C.self) C.self C.self n0 n0 azero azero LB.Ys LB.Ys z≤ (≤-refl _)

¬rel-sup : ¬ (LS.x₁ ⊑ᵈ LS.x₂)
¬rel-sup h = LS.fold-sep (mono-L1 h)

¬rel-shape : ¬ (LH.xb ⊑ᵈ LH.x0)
¬rel-shape h = LH.fold-sep (mono-L1 h)

¬rel-κ : ¬ (LK.xκ ⊑ᵈ LK.x′κ)
¬rel-κ h = LK.fold-sep (mono-L1 h)
```

## §3 无节点部分按值比

```agda
up : ∀ {W} → D azero W → D one W
up n0 = n0
up n1 = n1
up (x ⨾ y) = up x ⨾ up y
up (nl d) = nl (λ n → up (d n))
up (ni () u)
up (nκ () u)
up (nw p x) = nw p (up x)

rf↑ : ∀ {W} (x : D azero W) → Rf (up x)
rf↑ n0 = n0⊑
rf↑ n1 = n1⊑
rf↑ (x ⨾ y) = ⨾⊑ (rf↑ x) (rf↑ y)
rf↑ (nl d) = nl⊑ (λ n → rf↑ (d n))
rf↑ (ni () u)
rf↑ (nκ () u)
rf↑ (nw p x) = nwˡ (nwʳ (rf↑ x))

pu : ∀ {W} (d : ℕ → D azero W) k → up (pre d k) ⊑ᵈ pre₁ (λ n → up (d n)) k
pu d zero = n0⊑
pu d (suc k) = ⨾⊑ (pu d k) (rf↑ (d k))

pu′ : ∀ {W} (d : ℕ → D azero W) k → pre₁ (λ n → up (d n)) k ⊑ᵈ up (pre d k)
pu′ d zero = n0⊑
pu′ d (suc k) = ⨾⊑ (pu′ d k) (rf↑ (d k))

R↑ : ⊤ → ⊤ → ∀ {V₁ V₂} → D azero V₁ → D azero V₂ → Set
R↑ _ _ z z′ = up z ⊑ᵈ up z′

private
  module G↑ = Gen {⊤} (λ _ _ → ⊤) R↑ (λ _ → n1⊑) (λ z → n0⊑) ⨾⊑ nl⊑ nwˡ nwʳ trˡ trʳ
    (λ _ x → u0ˡ (rf↑ x) , u0ʳ (rf↑ x))
    (λ _ x → u1ˡ (rf↑ x) , u1ʳ (rf↑ x))
    (λ _ x y z → asʳ (rf↑ z) (rf↑ ((x ⨾ y) ⨾ z)) , asʳ′ (rf↑ z) (rf↑ (x ⨾ (y ⨾ z))))
    (λ x x′ d d′ hx hd k → trˡ (⨾⊑ (rf↑ x) (pu d k)) (pre⊑ hx hd k))
    (λ _ x d z h → lim⊑ (λ n → rf↑ (d n)) (λ k → trˡ (⨾⊑ (rf↑ x) (pu′ d k)) (h k)))

cong↑ : ∀ {W₀ W₀′} (z : D azero W₀) (z′ : D azero W₀′) → V0 z ≤ V0 z′ → up z ⊑ᵈ up z′
cong↑ = G↑.Two.cong0 {tt} {tt} tt tt tt
```

## §4 折叠产出的树自比

```agda
rf-Ω : ∀ {W} → Rf (Ωd one {L = one} {W = W} C.self tt)
rf-Ω = ⨾⊑ n1⊑ (⨾⊑ n0⊑ (rf-ni (λ q q′ l z z′ le → n1⊑)))

-- Step 在目标第 1 层: 状态的第 1 层差自比, 输出就自比
rf-Step : ∀ {W} (Y : F.St W) (t1 : one ⊲ W) → Rf (F.yc (F.d Y) (inj₁ t1) tt) → Rf (F.yc (F.Step Y) (inj₁ t1) tt)
rf-Step Y t1 h = nl⊑ (λ _ → ⨾⊑ rf-Ω h)

rf-A : Rf Aᵐ
rf-A = rf-Step F.Y₀ C.self n0⊑
```
