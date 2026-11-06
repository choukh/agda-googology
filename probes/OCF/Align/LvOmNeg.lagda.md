# Ω-极限坐标上的读回包 (五): 否定与 R2 的判定

> 不含记号. 入口 [LvOm](LvOm.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP.
>
> 1. **Ω-极限层的每个结点都带当前世界的可入证据 (定理, `sL-adm`).** 数据树 `D` 的结点 `ni r u` 在层 $\mathrm{h\Omega}\,\kappa_A\,G$ 里的位置 `r` 只能是 `sL e P`, $e : x\lhd W_A$. 这是数据树的构造子要的, 与闭包怎样走无关.
> 2. **`trKg`/`GF` 的形状在 Ω-极限层号上不成立 (定理, `no-unif-ΩA`).** 层号 $\mathrm{ΩA}$ 的读回层里, 过第 1 支本层的结点位置没有对一切世界成立的证据 (世界 $(0,0)$ 处). 外层世界 $a\rhd1$ 时 `Lv a ΩA` 有种类 $((1,e),\text{new})$, 它的结点就在这个位置; 所以对这样的 $a$, "对一切世界给出层证据" 的翻译 (`LvRdPkg.trKg` 的参数 `R`, `LvRdFold.GF` 的 `trO` 在一切世界上) 不能用这个位置的结点. **只否定**: 与世界无关的结点位置证据. **不否定**: 在 $a\lhd W_A$ 的世界上的翻译 (`LvOmRd.trK`, 有构造); 世界够大时证据存在 (`acc-1`).
> 3. **外层世界 $0$ 的代价 (定理, `only0`).** `Lv 0 (hΩ g)` 的种类下标只能是 $0$: Ω-结点只剩第 0 支. 这是 `LvOmRd.Z.rdcZ` (接口 `RdC` 的实例, 证据与世界无关) 的代价.
>
> **R2 (事件式走法) 的判定.** 问题: 照 `EvFold.WalkE`, 读回不进坐标内部, 只沿回灌事件逐个走, Ω-极限坐标上是否因此不需要层证据. 判定 (定理 + 判断): **不是.** (i) 证据是数据树的结点构造子要的 (`sL-adm`), 走法只管闭包结点 (`nκ`, `nμ`, 事件版的 `nε`), 不改结点构造子; (ii) R1 的读回 `LvOmRd.RW.rdW` 本来就不进坐标内部 (闭包读成 `nodeA`/`nodeH`, 坐标作数据, `nw` 往下嵌的子树按读的世界读, `rd-nw` 是 `refl`), 唯一的判定在过 Ω-层第 $x$ 支的结点上 (`dec⊲`, 有公共上界); (iii) `EvFold` 的种类证据不看折叠的 `A` 分量 (`EvFold.bd-indepA`) 是因为它的外层 `A`-世界是 $0$ 而外层界 $1$ 没有 Ω-结点; 在本篇的设置里, 外层世界 $0$ 时证据确实与世界无关 (`rdcZ`), 代价是 `only0`. 所以 R2 带来的 "不要层证据" 来自外层世界 $0$, 不来自走法 (判断; 依据是 (i), (iii) 两条定理与 `rdcZ` 的构造).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvOmNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; _⊲_)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (S₁; Ht; Wd₂; StH; sL; κA)
open import OCF.Align.LvOmLev
open import OCF.Align.LvOmFold using (hA₀; ΩA)
```

## §1 Ω-极限层的结点带可入证据

```agda
sL-adm : ∀ {W : Wd₂} {k : Ht} {G : A → Ht} → StH W k (hΩ κA G) → Σ A (λ x → (x ⊲ proj₁ W) × (k ⊲[ W ] G x))
sL-adm (sL {c = x} e P) = x , e , P
```

## §2 层号 ΩA: 第 1 支的结点位置没有与世界无关的证据

```agda
bad : ∀ {W : Wd₂} → ¬ (_⊲[_]_ {S₁} (hs (hs hz)) W (hs hz))
bad (hsuc ())

no-unif-ΩA : ¬ (∀ {W : Wd₂} → StH W (Ly (hA₀ (asuc azero))) (Ly ΩA))
no-unif-ΩA u = h (u {azero , hz})
  where
  h : StH (azero , hz) (Ly (hA₀ (asuc azero))) (Ly ΩA) → ⊥
  h (sL C.self P) = bad P

-- 前提的另一面: 世界的 A 分量在 1 之上时有
acc-1 : ∀ {W : Wd₂} → asuc azero ⊲ proj₁ W → StH W (Ly (hA₀ (asuc azero))) (Ly ΩA)
acc-1 e = sL {κ = κA} {c = asuc azero} e hself
```

## §3 外层世界 0: Ω-结点只剩第 0 支

```agda
only0 : ∀ (g : A → HB S₀) (κ : K (LvM.Lv azero (hΩ tt g))) → proj₁ (proj₁ κ) ≡ azero
only0 g ((x , e) , _) = adm₀ e
```
