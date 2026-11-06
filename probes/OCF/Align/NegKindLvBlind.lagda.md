# 按级回灌, 否定一路 (四): 接口的盲区

> 不含记号. 入口 [NegKindLv](NegKindLv.lagda.md). 对着接口 [KindLvIf](KindLvIf.lagda.md) ("接口定稿 2026-11-05 18:33 (首次编译通过)", 含 18:48 只增的 §5 `CollLvFbTy`) 写, 导入它, 不另造接口. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP.
>
> 接口文件头自述 "接口不管什么" 三条 (读回恒取起点, 一切有损, 折叠不用 `rs-top`). 本篇把它们写成定理, 并补一条接口没说的:
>
> 1. **`lossyAll`, `collC` (定理, 反模型).** `LvFb` 被 "一切种类有损" 满足, 对一切 $T$; `CollLvTy` 与只增的 `CollLvFbTy` 有常数实例 (闭项 $0$; `collC`, `collCFb`).
> 2. **`relevel` (定理, 反模型; 新).** 任何 `KLv T tp Λ κ` 都能改成级层 $\ell=0$ 且读回**不看级层数据**的 `KLv` (`relevel-ℓ`, `relevel-blind`), 其余字段 (`rs`, `rs≤`, `rsLg`, `rs-top`) 原样. 所以接口**不把种类的级层绑到它的级上**: `KLv` 的字段里, $\kappa$ 只经 `E T κ`, `Pr T κ`, `top tp κ`, `LgE T κ` 出现 (`rs-top` 把升界绑到 $\kappa$ 上, 这一点比 `GenFoldIf.FBA` 强, 对照 `NegGenFoldBlind.fba-swap`), 而 $\ell$ 与 `rd` 只要 "$\ell$ 是 $\Lambda$ 的第一位置" 与 "读回不降". "每个种类按**自己的**级回灌" (级层是 `lyL c`, 坐标是 `HB (Lev c)`) 不是接口的律, 只能是对构造一路实例的形状定理.
> 3. **`constRd` (定理, 反模型).** 种类的第一位置自反时 (`Lev c` 的一切种类都是, `prRefl`), 读回恒取起点也是 `KLv` (接口文件头的第一条盲区).
>
> **只否定什么.** 只否定推断 "有 `KLv`/`LvFb`/`CollLvTy` 的实例, 所以读回进了闭项" 与 "有 `KLv` 实例, 所以种类按自己的级回灌". **不否定** 接口的任何记录; 构造一路的具体实例 (见 [NegKindLvInst](NegKindLvInst.lagda.md)).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegKindLvBlind where

open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.GenFoldIf using (TopG; DK; n0)
open import OCF.Align.KindLvIf
```

## §1 一切有损; 常数坍缩

```agda
lossyAll : ∀ (T : KS) (tp : TopG T) (Λ : HB (step T)) → LvFb T tp Λ
lossyAll T tp Λ κ = inj₂ tt

collC : CollLvTy
collC G ld Λ lΛ one fb = azero , tt

-- 接口 §5 只增的 CollLvFbTy 同样
collCFb : CollLvFbTy
collCFb G ld fl Λ lΛ one fb = azero , tt
```

## §2 级层不绑到种类的级上

```agda
module _ {T : KS} {tp : TopG T} {Λ : HB (step T)} {κ : K T} where
  relevel : KLv T tp Λ κ → KLv T tp Λ κ
  relevel L = record
    { ℓ = hz ; ℓ⊲ = z⊲ᴮ Λ
    ; rd = λ lW b x → rd L lW b n0
    ; rd-fst = λ lW b x → rd-fst L lW b n0
    ; rd-lg = λ lW b x lb → rd-lg L lW b n0 lb
    ; rs = rs L ; rs≤ = rs≤ L ; rsLg = rsLg L ; rs-top = rs-top L }

  relevel-ℓ : ∀ L → ℓ (relevel L) ≡ hz
  relevel-ℓ L = refl

  relevel-blind : ∀ L {W} (lW : LgW (step T) W) b (x y : DK T hz W) → rd (relevel L) lW b x ≡ rd (relevel L) lW b y
  relevel-blind L lW b x y = refl

  relevel-rs : ∀ L → rs (relevel L) ≡ rs L
  relevel-rs L = refl
```

## §3 读回恒取起点

```agda
  constRd : (∀ {w b} → Pr T κ w b b) → KLv T tp Λ κ → KLv T tp Λ κ
  constRd pr L = record
    { ℓ = ℓ L ; ℓ⊲ = ℓ⊲ L
    ; rd = λ lW b x → b
    ; rd-fst = λ lW b x → pr
    ; rd-lg = λ lW b x lb → lb
    ; rs = rs L ; rs≤ = rs≤ L ; rsLg = rsLg L ; rs-top = rs-top L }

-- Lev c 的一切种类的第一位置都自反 (前提 pr 可满足)
prRefl : ∀ {S : KS} (c : HB S) (κ : K (Lev c)) {w b} → Pr (Lev c) κ w b b
prRefl hz κ = C.self
prRefl (hs c) (inj₁ κ) = prRefl c κ
prRefl (hs c) (inj₂ _) = hself
prRefl (hl f) (n , κ) = prRefl (f n) κ
prRefl (hΩ κ′ g) (e , κ) = prRefl (g e) κ
```

## §4 结论 (按档)

- **[定理, 反模型]** `lossyAll`, `collC`, `collCFb`; **`relevel`**, `relevel-ℓ`, `relevel-blind`, `relevel-rs`; `constRd`, `prRefl`.
- **[判断]** 接口里唯一绑到种类上的律是 `rs-top` (升界看见 $v$); 级层与读回的 "按自己的级" 要在构造文件里对实例证 (例如 "种类 $\kappa$ 的 $\ell$ 是 `lyL c` 且 `E T κ ≡ HB (Lev c)`, `rd` 是 `RdLTy` 的实例"). 建议构造一路把这条写成实例的 `refl` 定理.
