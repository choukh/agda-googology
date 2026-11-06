# 对一般种类结构的折叠 (七): 与两种种类的数据树逐结点互译

> 不含记号. 入口 [GenFold](GenFold.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> $T=$ `S₀` 时, 层 `HB (step S₀)` 就是 `Ht`, 世界 `Wd (step S₀)` 就是 `Wd₂` (定义相等, `lay≡`, `wd≡`). 两种种类的数据树 `HtTowerFTree.D` 与本路的 `DK S₀` 逐结点互译: `τ` 把 `nκ` 译成 `nc κA` (坐标 $c$ 的分支在世界 $W'$ 里取 $c=W'_A$, 再 `nw` 进 $W'$), `nμ` 译成 `nc κH` (分支原样); `ρ` 反过来 (`nc κA` 的分支在世界 $(c, W_H)$ 里取, 要当前世界合法). 其余构造子 (`n0`, `n1`, `⨾`, `nl`, `nw`, `ni`) 一一对应, 结点证据只换构造子的名字 (`σ`, `σ⁻`). 对层的可达 `AccY` 与数据结构递归. 逐结点的式子是 `refl` (`τ-nμ`, `τ-nκ`, `ρ-nc₂`, `Ωd-κH`).
>
> **折叠不是逐结点一致的 (判断, 写明差在哪里).** `GenFoldRun.Run` 与 `HtTowerFFold.Run` 在 `n0`, `n1`, `⨾`, `nl`, `nw`, `ni` 的子句逐行相同 (`Rpt`, `RunNi`, `Ai`, `BNi`, `Chn`, `RKi` 照抄, 只换类型); 闭包结点不同: 本路不走前缀 (`Kp`, `Kp₁`, `Walk`, `Walk₁`), 回灌每格只折叠坐标 $v_n$ 的分支; 输入改写 `Int` 的闭包行同样不走前缀. 两个折叠的输出在不同的类型里 (`D` 与 `DK S₀`), 输出含 $\mathbb N$-极限的函数, 不经函数外延不能比较整个输出; 本文件只给数据树的逐结点互译.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GenFoldCmp where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
import OCF.Align.HtTowerFTree as F
open F using (Ht; Wd₂; LgW₂)
open import OCF.Align.GenFoldIf
open import OCF.Align.GenFoldTree using (module Tree)
open Tree S₀ using (outS; inS)

lay≡ : HB (step S₀) ≡ Ht
lay≡ = refl

wd≡ : Wd (step S₀) ≡ Wd₂
wd≡ = refl

DS : Ht → Wd₂ → Set
DS = DK S₀
```

## §1 结点证据与许可

```agda
σ : ∀ {W k L} → F.StH W k L → StH {step S₀} W k L
σ (F.ss P) = ss P
σ (F.sl n P) = sl n P
σ (F.sL e P) = sL e P

σ⁻ : ∀ {W k L} → StH {step S₀} W k L → F.StH W k L
σ⁻ (ss P) = F.ss P
σ⁻ (sl n P) = F.sl n P
σ⁻ (sL e P) = F.sL e P

nzc : ∀ L → F.NZ L → NZ {step S₀} L
nzc (hs _) _ = tt
nzc (hl _) _ = tt
nzc (hΩ _ _) _ = tt

nzc⁻ : ∀ L → NZ {step S₀} L → F.NZ L
nzc⁻ (hs _) _ = tt
nzc⁻ (hl _) _ = tt
nzc⁻ (hΩ _ _) _ = tt

nz₁c : ∀ L → F.NZ₁ L → NZ₁ {step S₀} L
nz₁c (hs b) z = nzc b z
nz₁c (hl _) _ = tt
nz₁c (hΩ _ _) _ = tt

nz₁c⁻ : ∀ L → NZ₁ {step S₀} L → F.NZ₁ L
nz₁c⁻ (hs b) z = nzc⁻ b z
nz₁c⁻ (hl _) _ = tt
nz₁c⁻ (hΩ _ _) _ = tt
```

## §2 互译

```agda
τ : ∀ {L W} → F.AccY L → F.D L W → DS L W
ρ : ∀ {L W} → F.AccY L → LgW₂ W → DS L W → F.D L W

τ a F.n0 = n0
τ a F.n1 = n1
τ a (x F.⨾ y) = τ a x ⨾ τ a y
τ a (F.nl d) = nl (λ n → τ a (d n))
τ (F.acc g) (F.ni r u) = ni (σ r) (λ p l y → τ (F.acc g) (u p l (F.inS r (ρ (g r) l (outS (σ r) y)))))
τ {L} a (F.nκ z u) = nc (inj₁ tt) (nzc L z) (λ {W′} q lW′ → nw (C.self , proj₂ q) (τ a (u (proj₁ q) (proj₁ lW′))))
τ {L} a (F.nμ z u) = nc (inj₂ tt) (nz₁c L z) (λ q l → τ a (u q l))
τ a (F.nw p x) = nw p (τ a x)

ρ a lW n0 = F.n0
ρ a lW n1 = F.n1
ρ a lW (x ⨾ y) = ρ a lW x F.⨾ ρ a lW y
ρ a lW (nl d) = F.nl (λ n → ρ a lW (d n))
ρ (F.acc g) lW (ni r u) = F.ni (σ⁻ r) (λ p l y → ρ (F.acc g) l (u p l (inS r (τ (g (σ⁻ r)) (F.outS (σ⁻ r) y)))))
ρ {L} {W} a lW (nc (inj₁ tt) z u) =
  F.nκ (nzc⁻ L z) (λ {c} p lc → ρ a (lc , proj₂ lW) (u {c , proj₂ W} (p , hself) (lc , proj₂ lW)))
ρ {L} a lW (nc (inj₂ tt) z u) = F.nμ (nz₁c⁻ L z) (λ q l → ρ a l (u q l))
ρ a lW (nw p x) = F.nw p (ρ a (F.lgW≤ p lW) x)
```

## §3 逐结点的式子

```agda
τ-nμ : ∀ {L W} (a : F.AccY L) z (u : ∀ {W′} → W F.≤ W′ → LgW₂ W′ → F.D L W′) →
       τ a (F.nμ z u) ≡ nc (inj₂ tt) (nz₁c L z) (λ q l → τ a (u q l))
τ-nμ a z u = refl

τ-nκ : ∀ {L W} (a : F.AccY L) z (u : ∀ {c} → proj₁ W ⊲ c → Lg c → F.D L (c , proj₂ W)) →
       τ a (F.nκ z u) ≡ nc (inj₁ tt) (nzc L z) (λ {W′} q lW′ → nw (C.self , proj₂ q) (τ a (u (proj₁ q) (proj₁ lW′))))
τ-nκ a z u = refl

ρ-nc₂ : ∀ {L W} (a : F.AccY L) (lW : LgW₂ W) z (u : ∀ {W′} → _≤w_ (step S₀) W W′ → LgW (step S₀) W′ → DS L W′) →
        ρ a lW (nc (inj₂ tt) z u) ≡ F.nμ (nz₁c⁻ L z) (λ q l → ρ a l (u q l))
ρ-nc₂ a lW z u = refl

-- Ω_L 的 Ω-行: 两种种类的 κH 一行译过来就是本路的 nc κH 一行的形状
Ωd-κH : ∀ {W} (g : F.H₀ → Ht) →
  τ (F.accL (hΩ (inj₂ tt) g)) (F.Ωd (hΩ (inj₂ tt) g) {W}) ≡
  (n1 ⨾ nc (inj₂ tt) tt (λ {W′} q l → τ (F.accL (hΩ (inj₂ tt) g)) (F.ni (F.sL {κ = F.κH} {c = proj₂ W′} hself hself) (λ _ _ _ → F.n1))))
Ωd-κH g = refl
```
