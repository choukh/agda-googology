# ValX (六): `TX + 1 ≤ TU 1` 归约到根上的一条假设

> 不含记号. 入口 [ValX](ValX.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, **不用 UIP**. 实例 `I₁`.
>
> **做什么.** `TX` 与 `TU 1` 的根都是 $\Omega_1$ 结点, 跨底折叠在根上取回灌链 (目标 0, 世界 $W_0=1$): `TX` 是 $\lim\,\mathrm{chain}(0, k_L)$, `TU 1` 的第 0 个部分和是 $\lim\,\mathrm{chain}(0, k_R)$, 其中
>
> - $k_L\,b$ = 在世界 $\mathrm{nxt}_0(\mathrm{sh}_0\,W_0\,b)$ 里以界 $b$ 折 `gt (sh₀ W₀ b)` (地板的分支),
> - $k_R\,b$ = 同一世界、同一界, 折 $\Phi_{1\to0,\mathrm{topL}}(\mathrm{up}(\mathrm{gt}(\mathrm{sh}_0\,W_0\,b)))$ (`TU 1` 的回灌链第 0 点的分支).
>
> **定理 `goal-if`.** 若 `Hyp`: 对第 0 层的一切 $b_1\le b_2$, $k_L\,b_1\le k_R\,b_2$, 则 $\mathrm{TX}+1\le\mathrm{TU}\,1$ (落到 `TLRuleSpec._≤_`; `goal₁-if`: 接口 §4 的 `Goal₁`, 路径取 `CRw` 的 `PH-topL`, `PH-inU`). 证明只用回灌链的比较 (`chLe-hl`), 部分和与 `oneX`; 不用跨底单调, 不用 UIP.
>
> **`Hyp` 分两半.** (P1) 同一坐标处 $k_L\,b\le k_R\,b$: 已证 ([ValXP1](ValXP1.lagda.md) `P1`, 条件 UIP; 由 `ValXMono.monoX`, `MoX-gt` 与嵌入再折回不降值 `U-infl`). (P2) $k_R$ 对坐标值单调: 经 $\Omega_1$ 层的值合法去证, 正是 [ValXObs](ValXObs.lagda.md) `floor-block` 挡住的那一步 (分量随坐标的结构变), 要层号的值搬运; P2 本身是第 0 层输出的陈述, 没有被否定.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.ValXGoal where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; subst₂; sym)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (I₁; W₀; TX; TU; TU1; inU; PH-inU; PH-topL)
open import OCF.Lean.CRwFold I₁
open import OCF.Lean.ValCRel I₁
open import OCF.Lean.ValCBase I₁
open import OCF.Lean.ValXRel I₁
open import OCF.Lean.ValXTm using (shLaw₁; sound₀)
open import OCF.Lean.ValXBase I₁ shLaw₁
open import OCF.Lean.ValCIf I₁ using (toA)
open import OCF.Lean.ValXIf I₁ using (Goal₁)
open import OCF.Align.CumReadCF using (asuc)
import OCF.Align.TLRuleSpec as TL
```

## §1 $\Omega_1$ 结点在 $W_0$ 里折到第 0 层就是回灌链

$\Omega_1$ 的层是 $0$, 目标是 $0$: 比较的结果只能是 "同层" (另两种由构造子冲突排除, 不用 UIP).

```agda
κΩ : K XS
κΩ = hz , inj₂ tt

pickZ : ∀ {X : Cd} {A : Set} (to : H hz → A) (pk : hs hz ⊲ X) (r : (hz ⊲ hs hz) ⊎ (hs hz ⊲ hz)) → pick S⊥ to pk r ≡ same to
pickZ to pk (inj₁ (hsuc hself)) = refl
pickZ to pk (inj₂ ())

Ω₁-same : ∀ (a : Acc bX hz) (g : E XS κΩ → HX) ev (pg : PGt W₀ κΩ g) b →
          FXa a W₀ tt (z⊲ᴮ W₀) b (hΩ κΩ g) (ev , pg) ≡ hl (chain b (λ b′ → br a tt (z⊲ᴮ W₀) κΩ g pg b′ b′))
Ω₁-same (acc rs) g ev pg b =
  ΦΩX rs tt (z⊲ᴮ W₀) b κΩ g ev pg (λ z → z ≡ hl (chain b (λ b′ → br (acc rs) tt (z⊲ᴮ W₀) κΩ g pg b′ b′)))
    (subst (λ d → caseDc d (KcX rs tt (z⊲ᴮ W₀) b κΩ g pg) (ScX rs tt (z⊲ᴮ W₀) b κΩ g pg) (AcX rs tt (z⊲ᴮ W₀) b κΩ g pg)
                  ≡ hl (chain b (λ b′ → br (acc rs) tt (z⊲ᴮ W₀) κΩ g pg b′ b′)))
      (sym (pickZ (toX κΩ) (pkX κΩ ev) (cmpB (pkX κΩ ev) (z⊲ᴮ W₀) tt tt))) refl)
```

## §2 两族分支

```agda
-- TU 1 的回灌链 (Ω₁ ⊕ 1 层的地板折到 Ω₁ 层, 界 topL) 的第 0 点的分支
g₀ : E XS κΩ → HX
g₀ c = Φ bX (hs hz) (wf bX (hs hz)) tt bX hz (sm (hsuc hself)) topL (up (gt c)) tt

kU : HX → HX
kU b′ = Φ bX (hs hz) (wf bX (hs hz)) tt bX hz (sm (hsuc hself)) b′ (up b′) tt

inU₁≡ : inU (hs hz) tt ≡ hl (chain topL kU)
inU₁≡ = refl

u₀≡ : chain topL kU 0 ≡ hΩ κΩ g₀
u₀≡ = refl

nd₀ : PH PSX W₀ (hΩ κΩ g₀)
nd₀ = PH-inU (hs hz) tt 0

kL kR : Cd → Cd
kL b = br (wf bX hz) tt (z⊲ᴮ W₀) κΩ gt (proj₂ (PH-topL W₀ hself)) b b
kR b = br (wf bX hz) tt (z⊲ᴮ W₀) κΩ g₀ (proj₂ nd₀) b b

TX≡ : TX ≡ hl (chain hz kL)
TX≡ = Ω₁-same (wf bX hz) gt hself (proj₂ (PH-topL W₀ hself)) hz

F₀≡ : FXa (wf bX hz) W₀ tt (z⊲ᴮ W₀) hz (hΩ κΩ g₀) nd₀ ≡ hl (chain hz kR)
F₀≡ = Ω₁-same (wf bX hz) g₀ (proj₁ nd₀) (proj₂ nd₀) hz

-- `Fn` 放进 opaque: 否则比较 `Σ⁺ Fn 1` 与 `Fn 0 ⊞ Fn 1` 时 Agda 要把 `Fn 1` 算到弱头范式 (6G 内堆耗尽, 退出码 251)
opaque
  Fn : ℕ → Cd
  Fn n = FXa (wf bX hz) W₀ tt (z⊲ᴮ W₀) hz (chain topL kU n) (PH-inU (hs hz) tt n)

opaque
  unfolding Fn

  TU1≡ : TU1 ≡ hl (Σ⁺ Fn)
  TU1≡ = refl

  Fn0≡ : Fn 0 ≡ hl (chain hz kR)
  Fn0≡ = F₀≡

  one≤Fn : ∀ n → LeAt hz (hs hz) (Fn n)
  one≤Fn n = oneX (wf bX hz) tt (z⊲ᴮ W₀) hz (chain topL kU n) (PH-inU (hs hz) tt n)
```

## §3 归约

```agda
Hyp : Set
Hyp = ∀ b₁ b₂ → LeAt hz b₁ b₂ → LeAt hz (kL b₁) (kR b₂)

kpZ : ∀ (k : Cd → Cd) → Ac0.KP hz k
kpZ k b _ _ = moZ (k b)

chainLR : Hyp → LeAt hz (hl (chain hz kL)) (Fn 0)
chainLR hyp = subst (LeAt hz (hl (chain hz kL))) (sym Fn0≡)
  (Ac0.chLe-hl hz kL kR (Ac0.bnd-refl hz tt Rel.z≤) (kpZ kL) (kpZ kR) (λ {b₁} {b₂} B → hyp b₁ b₂ (proj₂ (proj₂ (proj₂ B)))))

step₁ : LeAt hz (hs (Fn 0)) (Fn 0 ⊞ Fn 1)
step₁ = L.⊞-monoʳ hz (Fn 0) {hs hz} {Fn 1} (one≤Fn 1)

goal-if′ : Hyp → LeAt hz (hs (hl (chain hz kL))) (hl (Σ⁺ Fn))
goal-if′ hyp = Rel.≤l {a = hs (hl (chain hz kL))} {g = Σ⁺ Fn} 1
  (L.≤-trans hz {hs (hl (chain hz kL))} {hs (Fn 0)} {Fn 0 ⊞ Fn 1} (Rel.s≤s (chainLR hyp)) step₁)

goal-if : Hyp → LeAt hz (hs TX) TU1
goal-if hyp = subst₂ (λ u v → LeAt hz (hs u) v) (sym TX≡) (sym TU1≡) (goal-if′ hyp)

goal-ifᴬ : Hyp → asuc (toA TX) TL.≤ toA TU1
goal-ifᴬ hyp = sound₀ (goal-if hyp)

-- 接口 §4 的目标陈述
goal₁-if : Hyp → Goal₁ (PH-topL W₀ hself) (PH-inU (hs hz) tt)
goal₁-if = goal-ifᴬ
```

## 结论 (按档)

- **[定理, 不用 UIP]** `pickZ`, **`Ω₁-same`** ($\Omega_1$ 结点在 $W_0$ 里折到第 0 层就是回灌链), `inU₁≡`, `u₀≡`, `TX≡`, `F₀≡`, `TU1≡`, `Fn0≡`, `one≤Fn`, `chainLR`, `step₁`; **`goal-if`**, `goal-ifᴬ`, `goal₁-if`: `Hyp` ⟹ $\mathrm{TX}+1\le\mathrm{TU}\,1$ (`TLRuleSpec._≤_`). 严格只是 "多一个后继" 档.
- **[判断]** `Hyp` 本身没有证, 也没有否定. P1 已证 (条件 UIP, [ValXP1](ValXP1.lagda.md)); P2 未证, 卡点见本篇开头.
- 工程: `Fn` 放在 `opaque` 里; 透明时比较 `Σ⁺ Fn 1` 与 `Fn 0 ⊞ Fn 1` 要把 `Fn 1` 算到弱头范式, 6G 内堆耗尽 (退出码 251).
