# `T⊤` 的值: 约化到逐分支的界

> 验收文件, 读记号. **判决: 约化 (条件定理, 编译过); 值定理未走通 (暂停).** `vv-T⊤-iff`: `VV T⊤` $\psi_0(\Omega_{\Omega^2})$ 当且仅当 `Up` (`T⊤` 的每个分支 $\preccurlyeq$ 参照树) 与 `Low` (参照树的每一项 $\preccurlyeq$ `T⊤`); `low-iff`: 下界单独也是这样. 实例: 第 0 项两向都成立 (`up₀`, `low₀`, 分支与参照项 $\cong$).
> 不否定 `T⊤` 读 $\psi_0(\Omega_{\Omega^2})$; 第 $n\ge1$ 项缺什么见 [TTopValReach](TTopValReach.lagda.md). 参照树在 [TTopValRef](TTopValRef.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TTopVal where

open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (_∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Free.Level hiding (up)
open import OCF.Free.Force using (forceᴺ)
import OCF.Align.EBO as E
open E using (fsn)
open import OCF.Align.OrdLabZCorrespond using (Lab; l0)
open import OCF.Align.LadderLabZStandardOmega using (n[])
open import OCF.Align.ValueJudgeBase using (_≼_; ≼l; l≼; ≼-refl; ≼-trans; ≅→≼)
open import OCF.Align.ValLabPos using (VV)
open import OCF.Align.LadderOrdPos using (HB; end)
open import OCF.Align.LadderOrdCode using (ωᶜ)
open import OCF.Align.LadderOrdCert using (ev₀)
import OCF.Align.LadderOrdMain
open import OCF.Align.CrossMNode using (Node; C; Gbr; νT)
open import OCF.Align.CrossMInst using (𝒯)
open import OCF.Align.CrossMClosed using (T⊤)
open import OCF.Align.CrossMAccept using (tψΩ)
open import OCF.Align.OrdLabAccept using (ord-∞)
open import OCF.Align.TTopValRef using (Z⊤; Z⊤-lab; Y⊤; Y⊤-lab; Lab-uniq)
```

## §1 闭包节点的分支

对变量 `𝒩`, `M₀` 证, 检查器不展开证书.

```agda
ν≼ : ∀ 𝒩 M₀ {b : Ordᶜ zero} → (∀ n → forceᴺ _ (Gbr 𝒩 (C 𝒩 M₀ n)) ≼ b) → νT 𝒩 M₀ ≼ b
ν≼ 𝒩 M₀ h = l≼ h

≼ν : ∀ 𝒩 M₀ {a : Ordᶜ zero} n → a ≼ forceᴺ _ (Gbr 𝒩 (C 𝒩 M₀ n)) → a ≼ νT 𝒩 M₀
≼ν 𝒩 M₀ n h = ≼l n h

br≼ν : ∀ 𝒩 M₀ n → forceᴺ _ (Gbr 𝒩 (C 𝒩 M₀ n)) ≼ νT 𝒩 M₀
br≼ν 𝒩 M₀ n = ≼l n (≼-refl _)

br-def : ∀ M → forceᴺ _ (Gbr 𝒯 M) ≡ forceᴺ _ (OCF.Align.LadderOrdMain.GᴺTᵠ (HB M) end zero ev₀ zero)
br-def M = refl
```

## §2 约化

```agda
Up : Set
Up = ∀ n → forceᴺ _ (Gbr 𝒯 (C 𝒯 ωᶜ n)) ≼ Y⊤

Low : Set
Low = ∀ n → Z⊤ n ≼ T⊤

low-if : Low → Y⊤ ≼ T⊤
low-if lo = l≼ lo

low-only-if : Y⊤ ≼ T⊤ → Low
low-only-if b n = ≼-trans (≼l n (≼-refl (Z⊤ n))) b

vv-T⊤-if : Up → Low → VV T⊤ tψΩ
vv-T⊤-if up lo = Y⊤ , Y⊤-lab , ν≼ 𝒯 ωᶜ up , l≼ lo

-- 参照树换成任何同标签的树, 结论不变 (Lab-uniq)
vv-T⊤-only-if : VV T⊤ tψΩ → Up × Low
vv-T⊤-only-if (Y , lY , a , b) =
  (λ n → ≼-trans (br≼ν 𝒯 ωᶜ n) (≼-trans a (≅→≼ e))) ,
  (λ n → ≼-trans (≼l n (≼-refl (Z⊤ n))) (≼-trans (≅→≼ (≅-sym e)) b))
  where
  e : Y ≅ Y⊤
  e = Lab-uniq lY Y⊤-lab
```

## §3 第 0 项

`T⊤` 的第 0 个分支就是码 `ωᶜ` 的顶 (`OrdLabAccept.ord-∞`), 与参照树的第 0 项同标签 $\psi_0(\Omega_{\psi_1(1)})$.

```agda
lab-B₀ : Lab (forceᴺ _ (Gbr 𝒯 (C 𝒯 ωᶜ 0))) (fsn tψΩ 0)
lab-B₀ = subst (λ X → Lab X (fsn tψΩ 0)) (sym (br-def ωᶜ)) (ord-∞ Ord₊.zero hz (l0 refl z≅) n[] E.[]< z≅ ev₀ zero)

e₀ : forceᴺ _ (Gbr 𝒯 (C 𝒯 ωᶜ 0)) ≅ Z⊤ 0
e₀ = Lab-uniq lab-B₀ (Z⊤-lab 0)

up₀ : forceᴺ _ (Gbr 𝒯 (C 𝒯 ωᶜ 0)) ≼ Y⊤
up₀ = ≼l 0 (≅→≼ e₀)

low₀ : Z⊤ 0 ≼ T⊤
low₀ = ≼ν 𝒯 ωᶜ 0 (≅→≼ (≅-sym e₀))
```
