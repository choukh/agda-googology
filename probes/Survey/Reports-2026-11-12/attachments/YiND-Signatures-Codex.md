# YiND 完整定理陈述
所有下列声明均为本路冷编通过的定理；一般引理的前提实例见完整回报。源码别名与导入保持原样，陈述逐字提取。

## YiNDTower.tω≼twᵗ

档：编译定理。本路冷编退出 0；主审尚待独立复核。

第 0 步：全部 n 的新标准塔第 n+2 项均支配全部 HC tω 证书。

源码：`<repository>/probes/OCF/Lean/YiNDTower.lagda.md:17`。

```agda
tω≼twᵗ : (n : ℕ) (h : HC tω) → R2.Rt h ≼ readRW (twᵗ (suc (suc n)))
```

## YiNDTower.inst

档：编译定理。本路冷编退出 0；主审尚待独立复核。

以已有闭证书 hΩω 实例化，证明 HC tω 的量化域非空。

源码：`<repository>/probes/OCF/Lean/YiNDTower.lagda.md:20`。

```agda
inst : R2.Rt hΩω ≼ readRW (twᵗ 2)
```

## YiNDTop.upA

档：编译定理。本路冷编退出 0；主审尚待独立复核。

根表任意而孩子表为 rbᶻ 时，零左项嵌入折到第 0 层的模拟。

源码：`<repository>/probes/OCF/Lean/YiNDTop.lagda.md:33`。

```agda
upA : ∀ {k h k′ h′ o ε ρ} {tb : RbS (sΩ k) h} → RelE (nd (sΩ k) h) (F.Ωₗ k′ h′) o ε ρ
    → (B : Base (nd (sΩ k) h)) (B′ : F.Base (F.Ωₗ k′ h′)) → RelBase (nd (sΩ k) h) (F.Ωₗ k′ h′) B B′
    → (β : Tr⁺ zero) → RelT zero F.zero (proj₁ β) (F.b⊥ B′) → RelD zero F.zero (proj₂ β) (F.n⊥ B′)
    → {x : Tr (nd (sΩ k) h)} {x′ : F.Tr (F.Ωₗ k′ h′)} → U0 x → RelT (nd (sΩ k) h) (F.Ωₗ k′ h′) x x′
    → RelT zero F.zero (proj₁ (ψ (nd (sΩ k) h) o (tb , λ c → rbᶻ (h c)) B zero (z≤ (nd (sΩ k) h)) β x)) (F.ψ⊥ (F.Ωₗ k′ h′) ε ρ B′ x′)
    × RelD zero F.zero (proj₂ (ψ (nd (sΩ k) h) o (tb , λ c → rbᶻ (h c)) B zero (z≤ (nd (sΩ k) h)) β x)) (F.nz⊥ (F.Ωₗ k′ h′) ε ρ B′ x′)
```

## YiNDTop.upS

档：编译定理。本路冷编退出 0；主审尚待独立复核。

同一零左项嵌入沿下标层侧路径折叠的模拟。

源码：`<repository>/probes/OCF/Lean/YiNDTop.lagda.md:43`。

```agda
upS : ∀ {k h k′ h′ o ε ρ} {tb : RbS (sΩ k) h} → RelE (nd (sΩ k) h) (F.Ωₗ k′ h′) o ε ρ
    → (B : Base (nd (sΩ k) h)) (B′ : F.Base (F.Ωₗ k′ h′)) → RelBase (nd (sΩ k) h) (F.Ωₗ k′ h′) B B′
    → ∀ {j j′} {v : j ≤ k} {w′ : F._≤_ j′ (F.Ωₗ k′ h′)} → RelW (ink {h = h} v) w′
    → (β : Tr⁺ j) {β′ : F.Tr j′} {nβ : F._⊢_◃_ j′ F.zero β′} → RelT j j′ (proj₁ β) β′ → RelD j j′ (proj₂ β) nβ
    → {x : Tr (nd (sΩ k) h)} {x′ : F.Tr (F.Ωₗ k′ h′)} → U0 x → RelT (nd (sΩ k) h) (F.Ωₗ k′ h′) x x′
    → RelT j j′ (proj₁ (ψ (nd (sΩ k) h) o (tb , λ c → rbᶻ (h c)) B j (ink v) β x)) (F.ψs (F.Ωₗ k′ h′) ε ρ B′ j′ w′ β′ nβ x′)
    × RelD j j′ (proj₂ (ψ (nd (sΩ k) h) o (tb , λ c → rbᶻ (h c)) B j (ink v) β x)) (F.nzs (F.Ωₗ k′ h′) ε ρ B′ j′ w′ β′ nβ x′)
```

## YiNDTop.topΩ

档：编译定理。本路冷编退出 0；主审尚待独立复核。

上述分支的 Ω 树模拟，连同回灌链与非零证明。

源码：`<repository>/probes/OCF/Lean/YiNDTop.lagda.md:54`。

```agda
topΩ : ∀ {k h k′ h′ o ε ρ} {tb : RbS (sΩ k) h} → RelE (nd (sΩ k) h) (F.Ωₗ k′ h′) o ε ρ
     → (B : Base (nd (sΩ k) h)) (B′ : F.Base (F.Ωₗ k′ h′)) → RelBase (nd (sΩ k) h) (F.Ωₗ k′ h′) B B′
     → (β : Tr⁺ zero) → RelT zero F.zero (proj₁ β) (F.b⊥ B′) → RelD zero F.zero (proj₂ β) (F.n⊥ B′)
     → {t : Pos⁼ k} {g : Br (nd (sΩ k) h) (inj₁ t) → Tr (nd (sΩ k) h)} {x′ : F.Tr (F.Ωₗ k′ h′)}
     → ((z : Br (nd (sΩ k) h) (inj₁ t)) → U0 (g z)) → RelT (nd (sΩ k) h) (F.Ωₗ k′ h′) (Ω (inj₁ t) g) x′
     → RelT zero F.zero (proj₁ (ψ (nd (sΩ k) h) o (tb , λ c → rbᶻ (h c)) B zero (z≤ (nd (sΩ k) h)) β (Ω (inj₁ t) g))) (F.ψ⊥ (F.Ωₗ k′ h′) ε ρ B′ x′)
     × RelD zero F.zero (proj₂ (ψ (nd (sΩ k) h) o (tb , λ c → rbᶻ (h c)) B zero (z≤ (nd (sΩ k) h)) β (Ω (inj₁ t) g))) (F.nz⊥ (F.Ωₗ k′ h′) ε ρ B′ x′)
```

## YiNDBridge.emb-zlift

档：编译定理。本路冷编退出 0；主审尚待独立复核。

两条零层嵌入路径在嵌入的结果上相等，不要求路径函数相等。

源码：`<repository>/probes/OCF/Lean/YiNDBridge.lagda.md:33`。

```agda
emb-zlift : (a : L) (o : Ok (zero ⊕ a)) (y : Tr⁺ zero)
  → emb (zero ⊕ a) o (z≤ (zero ⊕ a)) y ≡ emb (zero ⊕ a) o (lift zero a) y
```

## YiNDBridge.base1-same

档：编译定理。本路冷编退出 0；主审尚待独立复核。

新旧第 1 支的孩子路径底逐点相等。

源码：`<repository>/probes/OCF/Lean/YiNDBridge.lagda.md:37`。

```agda
base1-same : ∀ c j (v : j ≤ CT.hᵗ 0 c) → C.baseᴱ 1 j (inc c v) ≡ GI.baseᴱ 1 j (inc c v)
```

## YiNDBridge.old-rB1

档：编译定理。本路冷编退出 0；主审尚待独立复核。

旧第 1 支底与带表 F2 底的关系；复用已有 cL。

源码：`<repository>/probes/OCF/Lean/YiNDBridge.lagda.md:42`。

```agda
old-rB1 : RelBase (tw 1) (F.tw 1) (GI.baseᴱ 1) (VT.dB 1)
```

## YiNDBridge.rB1

档：编译定理。本路冷编退出 0；主审尚待独立复核。

新第 1 支实际底与带表 F2 底的关系，无未填前提。

源码：`<repository>/probes/OCF/Lean/YiNDBridge.lagda.md:44`。

```agda
rB1 : RelBase (tw 1) (F.tw 1) (C.baseᴱ 1) (VT.dB 1)
```

## YiNDAccept.same-local

档：编译定理。本路冷编退出 0；主审尚待独立复核。

新旧终点第 2 支、零孩子以下的实际继承底逐点相等。

源码：`<repository>/probes/OCF/Lean/YiNDAccept.lagda.md:46`。

```agda
same-local : ∀ i (u : i ≤ tw 1) → C.baseᴱ 2 i (inc zero u) ≡ GI.baseᴱ 2 i (inc zero u)
```

## YiNDAccept.old-rB2

档：编译定理。本路冷编退出 0；主审尚待独立复核。

旧第 2 支实际底与带表 F2 的底的关系。

源码：`<repository>/probes/OCF/Lean/YiNDAccept.lagda.md:48`。

```agda
old-rB2 : RelBase (tw 2) (F.tw 2) (GI.baseᴱ 2) (VT.dB 2)
```

## YiNDAccept.rBr0

档：编译定理。本路冷编退出 0；主审尚待独立复核。

新第 2 支零孩子的实际底与旧证明所用 F2 Br0 的关系。

源码：`<repository>/probes/OCF/Lean/YiNDAccept.lagda.md:50`。

```agda
rBr0 : RelBase (tw 1) (F.tw 1) (λ i u → C.baseᴱ 2 i (inc zero u)) VE.Br0
```

## YiNDAccept.beta1-R

档：编译定理。本路冷编退出 0；主审尚待独立复核。

新第 1 支的实际起点及其非零证明的关系。

源码：`<repository>/probes/OCF/Lean/YiNDAccept.lagda.md:54`。

```agda
beta1-R : RelT zero F.zero (proj₁ (C.betaᴱ 1)) (F.b⊥ (VT.dB 1)) × RelD zero F.zero (proj₂ (C.betaᴱ 1)) (F.n⊥ (VT.dB 1))
```

## YiNDAccept.beta2-R

档：编译定理。本路冷编退出 0；主审尚待独立复核。

新第 2 支的实际起点及其非零证明的关系。

源码：`<repository>/probes/OCF/Lean/YiNDAccept.lagda.md:56`。

```agda
beta2-R : RelT zero F.zero (proj₁ (C.betaᴱ 2)) (F.b⊥ VE.Br0) × RelD zero F.zero (proj₂ (C.betaᴱ 2)) (F.n⊥ VE.Br0)
```

## YiNDAccept.out0-R

档：编译定理。本路冷编退出 0；主审尚待独立复核。

新第 2 支实际零孩子输出与旧 tN 证明所用局部 F2 输出相关。

源码：`<repository>/probes/OCF/Lean/YiNDAccept.lagda.md:59`。

```agda
out0-R : RelT zero F.zero (proj₁ (C.Step.out 1 zero)) (F.ψ⊥ (F.tw 1) VE.ε′ VE.ρ′ VE.Br0 (F.Ωt (F.tw 1)))
```

## YiNDAccept.tN≼out0

档：编译定理。本路冷编退出 0；主审尚待独立复核。

全部 tN 的全部 HC 证书均不高于新第 2 支实际零孩子输出。

源码：`<repository>/probes/OCF/Lean/YiNDAccept.lagda.md:62`。

```agda
tN≼out0 : ∀ m (h : HC (AN.tN m)) → R2.Rt h ≼ readRW (proj₁ (C.Step.out 1 zero))
```

## YiNDAccept.tN≼EBOᵗ

档：编译定理。本路冷编退出 0；主审尚待独立复核。

全部 tN 的全部 HC 证书均不高于新终点读回。

源码：`<repository>/probes/OCF/Lean/YiNDAccept.lagda.md:64`。

```agda
tN≼EBOᵗ : ∀ m (h : HC (AN.tN m)) → R2.Rt h ≼ readRW CT.EBOᵗ
```

## YiNDAccept.tω≼EBOᵗ

档：编译定理。本路冷编退出 0；主审尚待独立复核。

目标：全部 HC tω 证书均不高于新终点读回。

源码：`<repository>/probes/OCF/Lean/YiNDAccept.lagda.md:67`。

```agda
tω≼EBOᵗ : (h : HC AL.tω) → R2.Rt h ≼ readRW CT.EBOᵗ
```

## YiNDAccept.inst

档：编译定理。本路冷编退出 0；主审尚待独立复核。

以已有闭证书 hΩω 实例化，证明 HC tω 的量化域非空。

源码：`<repository>/probes/OCF/Lean/YiNDAccept.lagda.md:71`。

```agda
inst : R2.Rt AL.hΩω ≼ readRW CT.EBOᵗ
```
