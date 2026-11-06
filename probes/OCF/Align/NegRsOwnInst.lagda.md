# 升界只剩一种? 否定一路 (三): 对构造一路实例的检查

> 不含记号. 入口 [NegRsOwn](NegRsOwn.lagda.md). 只读导入构造一路的 [RsOwnSh](RsOwnSh.lagda.md), [RsOwnSW](RsOwnSW.lagda.md), [RsOwnBd](RsOwnBd.lagda.md) (19:25 到 19:28 的版本), 不改它们; [RsOwnTm](RsOwnTm.lagda.md) 不导入, 只照抄它的种类 `κj` 的定义 (闭项 `TS` 用的就是 `SW GΛ shΛ`). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP.
>
> 构造一路的新形状有两种: **共享界** (`RsOwnSW.SW`: 世界带证据 `Uf` "一切底拷贝的界都 $\equiv a$", 升界 `invB` 把一切底拷贝置成 $v$) 与**有界取大** (`RsOwnBd.BD`: 世界带上界 $\Lambda$, 升界把每份底拷贝换成 $\max(a, v)$). 任务原话的三个检查: 它撞不撞已有定理, 是否真的升了别的分量, 是否只在可判定下标上成立.
>
> | 检查 | 共享界 (`SW`) | 有界取大 (`BD`) |
> |---|---|---|
> | 撞已有定理? | 不撞. `Uf` 推出 `NegRsOwnShape.ShJ` (`uf-shJ`), 所以 `no-same-rs` 的世界 `wS` 不在里面 (`wS-not-Uf`); `no-upAllR` 的 `w′` 也不在 (构造一路的 `w′-not-Uf`). 它是把这些世界**排除**掉, 不是绕开律. | 不撞. `rsᵇ-top` 只在旧顶 $\lhd v$ 时要, 而 `no-same-rs` 用的是无前提的 `rs-top`. 同一个升界同时服务两份下标不同的拷贝 (`bd-same-rs`, `refl`). |
> | 升了别的分量? | 是, 而且**精确地**置成 $v$: 在 `K₁` 上置 `κ₁ f` 就置了一切 `κ₁ f′` (`inst-all-top`); 在最终的 `KΛc` 上置第 1 站读回分量的拷贝 `κj f`, 第 0 站的原底种类 `(0 , tt)` 的界也恰成 $v$ (`Λ-moves0`). 两者在每个世界里界相同 (`Λ-same`, `bd-merge`). | 是: 升后每份底拷贝 $\unrhd v$ (构造一路的 `up-hi`). |
> | 只在可判定下标上? | 否, 对一切底拷贝 (含函数下标) 都成立, 不判定下标. 代价是世界类型变了 (`subW`). | 否, 同上. 代价是回灌值要带 $v\lhd\Lambda$ 的证据. |
>
> **结论.** 两种新形状都是 "一起升" (`RsOwnSh` 的 `rB`, `RaiseCBd` 的 `Rᵇ`) 加世界上的证据, 不是 "精确置自己, 别处不按自己动". 在共享界的世界里, 读回分量的底拷贝与第 0 站的底种类**分不开** (`bd-merge`): 判断: 最终坍缩里按它们回灌, 与只按第 0 站的底种类回灌, 在这一层上没有可区分的界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegRsOwnInst where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import OCF.Align.CumReadCF using (A; _⊲_)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (H₀)
open import OCF.Align.LvKtIf using (KΛc)
open import OCF.Align.GenFoldIf using (K₁; top; tpK)
open import OCF.Align.GenFoldInst using (genKc)
open import OCF.Align.NewTwrColl using (GΛ)
open import OCF.Align.NegGenFoldUpd using (jx; κ₁; fω)
open import OCF.Align.NegKindLvRaise using (tp₁)
open import OCF.Align.RsOwnIf
open import OCF.Align.RsOwnSh using (shKc; shΛ)
open import OCF.Align.RsOwnSW using (module SW)
open import OCF.Align.RsOwnBd using (module BD)
open import OCF.Align.NegRsOwnShape using (ShJ; sh-all-top; wS; wS-not-sh; f₁)
```

## §1 共享界在 `K₁` 上: 是 `ShJ`

```agda
module S1 = SW (genKc 1) (shKc 1)

uf-shJ : ShJ S1.Uf
uf-shJ {w} (a , al) f f′ = trans {i = w (inj₂ (jx f)) 0} (al (inj₂ (jx f)) 0) (sym (al (inj₂ (jx f′)) 0))

wS-not-Uf : ¬ S1.Uf wS
wS-not-Uf = wS-not-sh {S1.Uf} (λ {w} → uf-shJ {w})

-- 精确置 κ₁ f 就精确置了一切 κ₁ f′
inst-all-top : ∀ f {w} (p : S1.Uf w) v f′ → top tp₁ (κ₁ f′) (rsᴵ (S1.invB (κ₁ f) tt) w p v) ≡ v
inst-all-top f {w} p v f′ = sh-all-top {S1.Uf} (λ {w} → uf-shJ {w}) f (S1.invB (κ₁ f) tt) {w} p v f′
```

## §2 共享界在最终的 `KΛc` 上: 读回分量的拷贝与第 0 站的底种类分不开

`κj f = (1 , (inj₂ (jx f) , (0 , tt)))` (同 `RsOwnTm.κj`): 第 1 站读回分量 `jx f` 里的底拷贝. `(0 , tt)`: 第 0 站 (`S₀`) 的底种类.

```agda
module SΛ = SW GΛ shΛ

κj : (ℕ → H₀) → K KΛc
κj f = 1 , (inj₂ (jx f) , (0 , tt))

κ0 : K KΛc
κ0 = 0 , tt

Λ-same : ∀ f (w : Wd SΛ.TU) → top SΛ.tpU (κj f) w ≡ top SΛ.tpU κ0 w
Λ-same f (w , (a , al)) = trans (al 1 (inj₂ (jx f)) 0) (sym (al 0))

Λ-moves0 : ∀ f w v → top SΛ.tpU κ0 (rs (SΛ.rsB (κj f) tt) w v) ≡ v
Λ-moves0 f w v = trans (sym (Λ-same f (rs (SΛ.rsB (κj f) tt) w v))) (rs-top (SΛ.rsB (κj f) tt) {w} {v})

bd-merge : ∀ f {c} (w : Wd SΛ.TU) → Bd SΛ.TU (κj f) c w → Bd SΛ.TU κ0 c w
bd-merge f {c} w b = subst (c ⊲_) (Λ-same f w) b

bd-merge′ : ∀ f {c} (w : Wd SΛ.TU) → Bd SΛ.TU κ0 c w → Bd SΛ.TU (κj f) c w
bd-merge′ f {c} w b = subst (c ⊲_) (sym (Λ-same f w)) b

-- 不空: 基世界在 TU 里
w₀Λ : Wd SΛ.TU
w₀Λ = GenK′.w₀ SΛ.genU
  where module GenK′ = OCF.Align.GenFoldIf.GenK
```

## §3 有界取大: 同一个升界服务下标不同的两份拷贝

`BD` 的升界 `upᵇ` 只经 `toA b v` 看种类; 对 `κ₁ fω` 与 `κ₁ f₁` (第 1 项分别是 $0$, $1$, 可判定地不同), `toA` 都是恒等, 所以两份拷贝的升界逐字相同. 它不撞 `NegRsOwnShape.no-same-rs`, 因为 `rsᵇ-top` 只在旧顶 $\lhd v$ 时要.

```agda
module B1 = BD (shKc 1)

bd-same-rs : ∀ w u v q → B1.upᵇ (κ₁ fω) tt w u v q ≡ B1.upᵇ (κ₁ f₁) tt w u v q
bd-same-rs w u v q = refl
```

## §4 结论 (按档)

- **[定理]** `uf-shJ`, `wS-not-Uf`, **`inst-all-top`** (`K₁`: 共享界的升界精确置一切底拷贝); **`Λ-same`**, **`Λ-moves0`**, **`bd-merge`**, `bd-merge′` (`KΛc`: 读回分量的底拷贝与第 0 站的底种类在共享界的每个世界里界相同, 置一个就置了另一个); `bd-same-rs` (`refl`: 有界取大对两份下标不同的拷贝是同一个升界).
- **前提实例.** `inst-all-top`, `Λ-moves0` 的世界取基世界 (`w₀Λ`; 构造一路的 `al0` 给证据); `invB`, `rsB` 是构造一路的无条件构造.
- **只说什么.** 这些是关于构造一路实例的**形状**定理, 不是否定: 构造一路的 `RsInv`, `RsK`, `RsBd` 实例都成立, 闭项 `TS` 合法. 它们说的是: 这两种形状**不是** "精确置自己, 别处只增" (被挑战的那一种); 它们是 "一起升" 加世界证据.
- **[判断]** 值: `bd-merge` 说在 `TU` 里, 以 `κj f` 为种类的 $\Omega$-结点与以 `κ0` 为种类的 $\Omega$-结点在每个世界里有同样的分支域与同样的第一位置; 所以读回分量的底拷贝在 `TU` 里**不提供**第 0 站底种类之外的界. 这是否降低 `TS` 的序数值, 没有定理 (没有 `ord` 的比较).
