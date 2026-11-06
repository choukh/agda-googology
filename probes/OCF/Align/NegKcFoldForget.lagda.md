# 种类塔上的一级折叠, 否定一路 (二): 桥与下降不能是种类的嵌入

> 不含记号. 入口 [NegKcFold](NegKcFold.lagda.md). 对着接口 [KcFoldIf](KcFoldIf.lagda.md) ("接口定稿 2026-11-05", 变更记录: 无) 写, 导入它, 不另造接口. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP.
>
> 接口的桥 `ForgetK` 与下降 `DnTower` 只要求 "保合法的映射", 常数 $0$ 就满足 (接口自己说了 "盲"). 有内容的写法是**逐结点搬种类**: 种类映到种类, 坐标来回换 (`LvRdEmb.Emb`, 构造一路的前任 `LvRd`, `LvOm` 都这样搬). 本篇说这种写法在哪里不可能.
>
> 1. **桥在极限与 $\Omega$-结点处不能是嵌入 (定理, `no-embForget`, `no-embForgetΩ`).** `LvW a` 在极限与 $\Omega$-结点的每一支多取一层后继 (`step`), 接口的 `Lev` 不取. 取层号 $c_\ell=\mathrm{hl}(n\mapsto0)$ (合法, `lg-cℓ`): `LvW a cℓ` 有坐标是 `HB S₀` 的种类, `Lev cℓ` 的种类坐标全是 `A`. 嵌入要 `HB S₀` 收缩进 `A`, 撞 `no-retract`. $\Omega$-结点 $\mathrm{h\Omega}\,\kappa\,(x\mapsto0)$ 同样 (外层世界里只要有一个可入坐标, 基世界的 `bot` 就是). 对照 (`fin-same`): 有限层号上两者逐字相同.
> 2. **下降在第 2 级不能是嵌入 (定理, `no-embDn`).** 对一切站 $s$, `Lev {Kc s} 2 = step S₁` 的新种类坐标是 `Ht = HB S₁`; 嵌入进 `S₁` 要 `HB S₁` 收缩进 `S₁` 的某个坐标类型, 撞 `no-retract`. 所以 `DnTower` 的实例在 $b\ge2$ 的级上必须把高度坐标的 $\Omega$-结点压掉 (换成 ℕ-极限或取某一支).
>
> **只否定什么.** 只否定 "桥/下降由一个 `Emb` 逐结点给出" (坐标映射有左逆). **不否定** `ForgetK`, `DnTower` (常数实例; 也不否定有损的结构映射, 例如把高度坐标的 $\Omega$-结点限制到 `A` 的像上, 判断: 可写, 读法降一级).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegKcFoldForget where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (S₁; Ht)
open import OCF.Align.HtTowerNeg using (no-retract)
open import OCF.Align.LvRdEmb using (Emb; lk; vc; cv; cv-vc)
open import OCF.Align.ColimWIf using (finH)
open import OCF.Align.LvKtIf using (Kc)
open import OCF.Align.KcFoldIf
```

## §1 桥: 极限与 $\Omega$-结点

```agda
cℓ : ∀ {𝕂 : KS} → HB 𝕂
cℓ = hl (λ _ → hz)

lg-cℓ : ∀ {𝕂 : KS} → LgB {𝕂} cℓ
lg-cℓ = (λ n → hself) , (λ n → tt)

-- LvW a cℓ 的种类 (0, 新) 坐标是 HB S₀; Lev cℓ 的种类坐标都是 A
no-embForget : ∀ {𝕂 : KS} (a : Wd 𝕂) → ¬ Emb (LvW a (cℓ {𝕂})) (Lev (cℓ {𝕂}))
no-embForget a M = no-retract {S = S₀} tt (vc M {0 , inj₂ tt}) (cv M {0 , inj₂ tt}) (cv-vc M {0 , inj₂ tt})

-- Ω-结点: 只要外层世界里有一个可入坐标
cΩ : ∀ {𝕂 : KS} (κ : K 𝕂) → HB 𝕂
cΩ κ = hΩ κ (λ _ → hz)

no-embForgetΩ : ∀ {𝕂 : KS} (a : Wd 𝕂) (κ : K 𝕂) (x : E 𝕂 κ) (e : Bd 𝕂 κ x a) → ¬ Emb (LvW a (cΩ {𝕂} κ)) (Lev (cΩ {𝕂} κ))
no-embForgetΩ {𝕂} a κ x e M = no-retract {S = S₀} tt (vc M {(x , e) , inj₂ tt}) (cv M {(x , e) , inj₂ tt}) (cv-vc M {(x , e) , inj₂ tt})

-- 前提可满足: 基世界里 bot 可入
botAdm : ∀ {𝕂 : KS} (κ : K 𝕂) (a : Wd 𝕂) → Bd 𝕂 κ (bot 𝕂 κ) a
botAdm {𝕂} κ a = botBd 𝕂 κ a

-- 对照: 有限层号上逐字相同
fin-same : ∀ {𝕂 : KS} (a : Wd 𝕂) n → LvW a (finH {𝕂} n) ≡ Lev (finH {𝕂} n)
fin-same a zero = refl
fin-same a (suc n) = cong step (fin-same a n)
```

## §2 下降: 第 2 级

```agda
two : ∀ {𝕂 : KS} → HB 𝕂
two = hs (hs hz)

no-embDn : ∀ s → ¬ Emb (Lev {Kc s} two) S₁
no-embDn s M = no-retract {S = S₁} (lk M (inj₂ tt)) (vc M {inj₂ tt}) (cv M {inj₂ tt}) (cv-vc M {inj₂ tt})
```

## §3 只否定什么

- **否定** (编译的): 桥 `HB (LvW a c) → HB (Lev c)` 由 `Emb (LvW a c) (Lev c)` 给出, 在 $c=c_\ell$ (一切 `K`, 一切 $a$) 与 $c=\mathrm{h\Omega}\,\kappa\,(x\mapsto0)$ (有可入坐标的一切 $a$) 上; 下降 `HB (Lev 2) → Ht` 由 `Emb (Lev 2) S₁` 给出 (一切站).
- **不否定**: 接口的 `ForgetK`, `DnK`, `DnTower`, `DnLim` (常数实例合法); 不要求坐标往返的结构映射; 有限层号上的桥 (`fin-same`: 类型逐字相同, 恒等就是).
- 为什么构造一路需要: 接口 §5 "有了它, `FoldAllKW` 给出 `FoldAllK` 的读回"; 读回的 $\Omega$-结构要原样进下一站的层号 (`LvKtTower.B-suc` 的 `injL`), 桥若不是逐结点的嵌入, 读回进塔之前就在极限与 $\Omega$-结点处被压过一次. 下降同理 (`DnTower` 把第 $b$ 级的读回降到 `Ht` 作回灌输出).
