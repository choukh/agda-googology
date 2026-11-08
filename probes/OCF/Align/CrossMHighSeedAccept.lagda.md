# 旧跨段算法从已验收的高基座起步

> 编译状态：首次 6G 检查退出 251；将证书转换与验收运输对变量证明后，
> 经协调单路 12G 检查退出 0。没有删除或改动旧模块接口。

验收文件。只取原 `CrossMClosed.T⊤ᶜ` 的已有参数实例，起点为
`ω²ᶜ`；没有新造树、增加基座常量或改变反馈算法。
既有 `EmbVVInstO2` 已验收此码的第零行为
$\psi_0(\Omega_{\Omega\cdot\omega^2})$。这里把原证书计值接到该验收，
再取原累加轨道的第零项，证明原闭包严格超过这一行。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CrossMHighSeedAccept where

open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import OCF.Free.Level using (Ordᶜ; zero; suc; _≅_; _≺_; ≅-sym)
open import OCF.Free.Force using (forceᴺ)
open import OCF.Align.LadderOrdPos using (Code; Pos; cs; HB; end)
open import OCF.Align.LadderOrdCode using (ω²ᶜ)
open import OCF.Align.LadderOrdCert using (Gᵖ; ev₀)
import OCF.Align.ValLabLadder as Rows
open import OCF.Align.ValueJudgeBase using (_≼_; ≼-trans; s≼s; ≅→≼; ≺→s≼)
open import OCF.Align.ValLabPos using (VV)
open import OCF.Align.OrdLabZCorrespond using (Lab)
open import OCF.Align.OrdLabRead using (tω²)
open import OCF.Align.EmbVVInstO2 using (vv-ω²-via)
open import OCF.Align.CrossMInst using (𝒯)
open import OCF.Align.CrossMNode using (C; νT)
open import OCF.Align.CrossMClosed using (T⊤ᶜ)
open import OCF.Align.TLOneThm using (below-chain)

-- 对变量证明，避免检查器展开具体的整条高层证书。
opaque
  row-shape : ∀ M (p : Pos (cs M)) a →
    forceᴺ _ (Gᵖ M p a) ≅ Rows.V (HB M) p a
  row-shape M p a = Rows.V-G′ (HB M) p a ev₀ (Gᵖ M p a)

transport-accept : ∀ {X Y t} → X ≅ Y → VV Y t → VV X t
transport-accept e (R , lab , xy , yx) =
  R , lab , ≼-trans (≅→≼ e) xy ,
  ≼-trans yx (≅→≼ (≅-sym e))

opaque
  original-row-accept : VV (forceᴺ _ (Gᵖ ω²ᶜ end zero)) tω²
  original-row-accept = transport-accept (row-shape ω²ᶜ end zero) vv-ω²-via

-- 原算法全部轨道的包含定理；M₀、C 和原 Gᵖ 都显式保留。
original-chain-strict : ∀ M₀ n (p : Pos (cs (C 𝒯 M₀ n))) →
  forceᴺ _ (Gᵖ (C 𝒯 M₀ n) p zero) ≺ νT 𝒯 M₀
original-chain-strict = below-chain

high-seed-strict : forceᴺ _ (Gᵖ ω²ᶜ end zero) ≺ T⊤ᶜ ω²ᶜ
high-seed-strict = original-chain-strict ω²ᶜ 0 end

opaque
  labelled-strict-lower : Σ (Ordᶜ zero) λ R →
    Lab R tω² × (suc R ≼ T⊤ᶜ ω²ᶜ)
  labelled-strict-lower =
    proj₁ original-row-accept ,
    proj₁ (proj₂ original-row-accept) ,
    ≼-trans (s≼s (proj₂ (proj₂ (proj₂ original-row-accept))))
      (≺→s≼ high-seed-strict)
```

这是旧高构造与旧值定理的串接，不是新增 EBO 阶段。
结论不涉及原 `ωᶜ` 起点与此起点的比较，也不声称
$\psi_0(\Omega_{\Omega_\Omega})$ 或完整 EBO 的下界。
参照及标签仅留在本验收文件；原闭项的定义与证书不变。
