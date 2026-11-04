# 主线直接标: 克隆与主线的连接是定理

> **验收文件.** 结论写在 [OrdLab](OrdLab.lagda.md). 主线 (`OCF.Free.*`, `LadderInf*`) 与克隆世界 (`OCF.Align.Level`, `LadderLabZInfW*`) 的数据类型是两份, 字面相同但不是同一个类型. [LadderLabAccept](LadderLabAccept.lagda.md) §4 只比较了三个点的 FGH. 这里:
>
> - `⟦_⟧`: 第 0 层的树搬到克隆世界, 结构递归.
> - `lab⟦⟧`: 主线的 `Lab` 搬到克隆世界的 `Lab`, 记号一侧不动 ($T$ 是同一个类型).
> - `cross`: 同一个标签的两棵树互模拟, 跨世界的 `Lab-uniq`.
> - `clone-top`, `clone-∞`, `clone-fin₂`: 主线的证书计值与克隆的证书计值 $\cong$, 对一切带标签的输入, 两边的环境任意. `fgh-top` 等: FGH 逐点相等.
>
> 范围: $\alpha$ 要 $\cong$ 一棵带标签的树的层号, $\theta$ 低于上界, 与 `label-top` 相同. 其余 $\alpha$ 上这里不说话.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.OrdLabCross where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (_∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
import OCF.Align.EBO as E
open E using (T; Ωt) renaming (_<ᵀ_ to _<ᵗ_)
open import OCF.Align.LadderLabZStandardOmega using (NF₁; Ω₁; Ωᵐ; ψ¹)
-- 主线
import OCF.Free.Level as F
import OCF.Free.Floor as FF
import OCF.Free.Tree as FT
import OCF.Free.Force as FG
import OCF.Align.OrdLabZCorrespond as FL
import OCF.Align.OrdLabZUniform3Base as FU
import OCF.Align.OrdLabAccept as FA
-- 克隆世界
import OCF.Align.Level as A
import OCF.Align.Correspond as AL
import OCF.Align.LadderLabZUniform3Base as AU
import OCF.Align.LadderLabZUniform4Base as AB
import OCF.Align.LadderLabZNFWForce as AG
import OCF.Align.LadderLabAccept as AA
import OCF.Align.LadderLabZInfWTop as AT
import OCF.Align.LadderLabZInfWTop2 as AT2
import OCF.Align.LadderInfTop as MT
import OCF.Align.LadderInfTop2 as MT2
```

## §1 搬运

```agda
⟦_⟧ : F.Ordᶜ F.zero → A.Ordᶜ A.zero
⟦ F.zero ⟧ = A.zero
⟦ F.suc x ⟧ = A.suc ⟦ x ⟧
⟦ F.lim f ⟧ = A.lim (λ n → ⟦ f n ⟧)
⟦ F.limᵢ () f ⟧
⟦ F.up () x ⟧

⟦≅⟧ : ∀ {x y : F.Ordᶜ F.zero} → x F.≅ y → ⟦ x ⟧ A.≅ ⟦ y ⟧
⟦≅⟧ F.z≅     = A.z≅
⟦≅⟧ (F.s≅ e) = A.s≅ (⟦≅⟧ e)
⟦≅⟧ (F.l≅ h) = A.l≅ (λ n → ⟦≅⟧ (h n))
⟦≅⟧ (F.lᵢ≅ {p = ()} e h)
⟦≅⟧ (F.upˡ {r = ()} e)
⟦≅⟧ (F.upʳ {r = ()} e)

FGH-⟦⟧ : ∀ x n → F.FGH x n ≡ A.FGH ⟦ x ⟧ n
FGH-⟦⟧ F.zero     n = refl
FGH-⟦⟧ (F.suc x)  n = F.iter-ext (FGH-⟦⟧ x) n n
FGH-⟦⟧ (F.lim f)  n = FGH-⟦⟧ (f n) n
FGH-⟦⟧ (F.limᵢ () f) n
FGH-⟦⟧ (F.up () x)   n

lab⟦⟧ : ∀ {X t} → FL.Lab X t → AL.Lab ⟦ X ⟧ t
lab⟦⟧ (FL.l0 c e) = AL.l0 c (⟦≅⟧ e)
lab⟦⟧ (FL.l1 c e l) = AL.l1 c (⟦≅⟧ e) (lab⟦⟧ l)
lab⟦⟧ (FL.lω c e h) = AL.lω c (⟦≅⟧ e) (λ n → lab⟦⟧ (h n))
```

## §2 同一个标签, 同一棵树

```agda
cross : ∀ {X Y t} → FL.Lab X t → AL.Lab Y t → ⟦ X ⟧ A.≅ Y
cross (FL.l0 c e) (AL.l0 c′ e′) = A.≅-trans (⟦≅⟧ e) (A.≅-sym e′)
cross (FL.l0 c e) (AL.l1 c′ e′ l′) with trans (sym c) c′
... | ()
cross (FL.l0 c e) (AL.lω c′ e′ h′) with trans (sym c) c′
... | ()
cross (FL.l1 c e l) (AL.l0 c′ e′) with trans (sym c) c′
... | ()
cross (FL.l1 c e l) (AL.l1 c′ e′ l′) = A.≅-trans (⟦≅⟧ e) (A.≅-trans (A.s≅ (cross l l′)) (A.≅-sym e′))
cross (FL.l1 c e l) (AL.lω c′ e′ h′) with trans (sym c) c′
... | ()
cross (FL.lω c e h) (AL.l0 c′ e′) with trans (sym c) c′
... | ()
cross (FL.lω c e h) (AL.l1 c′ e′ l′) with trans (sym c) c′
... | ()
cross (FL.lω c e h) (AL.lω c′ e′ h′) = A.≅-trans (⟦≅⟧ e) (A.≅-trans (A.l≅ (λ n → cross (h n) (h′ n))) (A.≅-sym e′))

fgh-of : ∀ {X Y} → ⟦ X ⟧ A.≅ Y → ∀ n → F.FGH X n ≡ A.FGH Y n
fgh-of e n = trans (FGH-⟦⟧ _ n) (A.FGH-≅ e n)
```

## §3 主线与克隆的证书

下面左边是主线的 `I₂.GᴺTᵠ`, 右边是克隆的 `I₂.GᴺTᵠ`. 这就把 [LadderLabAccept](LadderLabAccept.lagda.md) §4 的三个点的测试换成了定理, 输入带标签的范围内. 标签 `θ` 两边相同, 树 `Y`, `Y′` 各在各的世界.

```agda
clone-top : ∀ n {θ} (Y : F.Ordᶜ F.zero) (hY : F.HS Y) → FL.Lab Y θ → (Y′ : A.Ordᶜ A.zero) (hY′ : A.HS Y′) → AL.Lab Y′ θ → NF₁ θ → θ <ᵗ FU.ψ₀ᵗ (Ωt (ψ¹ ∷ Ω₁ ∷ Ωᵐ n [])) →
            ∀ {α α′} → α F.≅ᴵ F.toLevel Y hY → α′ A.≅ᴵ A.toLevel Y′ hY′ →
            ∀ {ℓ ℓ′} (ev : FF.Ev ℓ FT.Fl) (p : F.zero F.<ᴵ ℓ) (ev′ : AU.Ev ℓ′ AB.Fl) (p′ : A.zero A.<ᴵ ℓ′) →
            ⟦ FG.forceᴺ _ (FA.I₂.GᴺTᵠ (MT2.top n) α ev p) ⟧ A.≅ AG.forceᴺ _ (AA.I₂.GᴺTᵠ (AT2.top n) α′ ev′ p′)
clone-top n Y hY lY Y′ hY′ lY′ nθ pm e e′ ev p ev′ p′ = cross (FA.label-top n Y hY lY nθ pm e ev p) (AA.label-top n Y′ hY′ lY′ nθ pm e′ ev′ p′)

fgh-top : ∀ n {θ} (Y : F.Ordᶜ F.zero) (hY : F.HS Y) → FL.Lab Y θ → (Y′ : A.Ordᶜ A.zero) (hY′ : A.HS Y′) → AL.Lab Y′ θ → NF₁ θ → θ <ᵗ FU.ψ₀ᵗ (Ωt (ψ¹ ∷ Ω₁ ∷ Ωᵐ n [])) →
          ∀ {α α′} → α F.≅ᴵ F.toLevel Y hY → α′ A.≅ᴵ A.toLevel Y′ hY′ →
          ∀ {ℓ ℓ′} (ev : FF.Ev ℓ FT.Fl) (p : F.zero F.<ᴵ ℓ) (ev′ : AU.Ev ℓ′ AB.Fl) (p′ : A.zero A.<ᴵ ℓ′) →
          ∀ k → F.FGH (FG.forceᴺ _ (FA.I₂.GᴺTᵠ (MT2.top n) α ev p)) k ≡ A.FGH (AG.forceᴺ _ (AA.I₂.GᴺTᵠ (AT2.top n) α′ ev′ p′)) k
fgh-top n Y hY lY Y′ hY′ lY′ nθ pm e e′ ev p ev′ p′ = fgh-of (clone-top n Y hY lY Y′ hY′ lY′ nθ pm e e′ ev p ev′ p′)

clone-∞ : ∀ {θ} (Y : F.Ordᶜ F.zero) (hY : F.HS Y) → FL.Lab Y θ → (Y′ : A.Ordᶜ A.zero) (hY′ : A.HS Y′) → AL.Lab Y′ θ → NF₁ θ → θ <ᵗ FA.B∞ →
          ∀ {α α′} → α F.≅ᴵ F.toLevel Y hY → α′ A.≅ᴵ A.toLevel Y′ hY′ →
          ∀ {ℓ ℓ′} (ev : FF.Ev ℓ FT.Fl) (p : F.zero F.<ᴵ ℓ) (ev′ : AU.Ev ℓ′ AB.Fl) (p′ : A.zero A.<ᴵ ℓ′) →
          ⟦ FG.forceᴺ _ (FA.I∞.GᴺTᵠ MT.∞ α ev p) ⟧ A.≅ AG.forceᴺ _ (AA.I∞.GᴺTᵠ AT.∞ α′ ev′ p′)
clone-∞ Y hY lY Y′ hY′ lY′ nθ pm e e′ ev p ev′ p′ = cross (FA.label-∞ Y hY lY nθ pm e ev p) (AA.label-∞ Y′ hY′ lY′ nθ pm e′ ev′ p′)

clone-fin : ∀ m {θ} (Y : F.Ordᶜ F.zero) (hY : F.HS Y) → FL.Lab Y θ → (Y′ : A.Ordᶜ A.zero) (hY′ : A.HS Y′) → AL.Lab Y′ θ → NF₁ θ → θ <ᵗ FU.ψ₀ᵗ (Ωt (Ω₁ ∷ Ω₁ ∷ Ωᵐ m [])) →
            ∀ {α α′} → α F.≅ᴵ F.toLevel Y hY → α′ A.≅ᴵ A.toLevel Y′ hY′ →
            ∀ {ℓ ℓ′} (ev : FF.Ev ℓ FT.Fl) (p : F.zero F.<ᴵ ℓ) (ev′ : AU.Ev ℓ′ AB.Fl) (p′ : A.zero A.<ᴵ ℓ′) →
            ⟦ FG.forceᴺ _ (FA.I∞.GᴺTᵠ (MT.fin m) α ev p) ⟧ A.≅ AG.forceᴺ _ (AA.I∞.GᴺTᵠ (AT.fin m) α′ ev′ p′)
clone-fin m Y hY lY Y′ hY′ lY′ nθ pm e e′ ev p ev′ p′ = cross (FA.label-fin m Y hY lY nθ pm e ev p) (AA.label-fin m Y′ hY′ lY′ nθ pm e′ ev′ p′)
```
