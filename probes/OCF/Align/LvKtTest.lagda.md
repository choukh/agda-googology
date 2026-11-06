# 层号换类型 (四): 有限测试

> 不含记号. 入口 [LvKt](LvKt.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示. **本篇全是有限测试** (具体输入上的 `refl`), 不是对一切输入的定理.
>
> 1. **截断版与 `LvTopInst.Tr` 逐站相同** (`t-Hs0`, `t-Hs1`, `t-Hs2`): 前三站的输出与 `LvTop` 截断版的输出定义相等. 比较器: 两个 `Ht` 项的 `refl`. 盲区: 只测了 $s=0,1,2$; 对一切 $s$ 没有定理 (两边的覆盖证据是不同的相等证明, 对变量 $s$ 不化成 `refl`).
> 2. **真回灌的第一站把新种类结点送进第 1 站的层号** (`t-new`): 起点 $b_0=1$, 第 0 站用 `foldFinK` 在码目标 $1$ 上折叠 (即第 2 级级顶的折叠), 读回 $r_0$ (类型 `HB (step S₀)`) 在有限搜索 (深 6, 每个 ℕ-极限看第 0, 1, 2 支, 每个旧种类 Ω-结点看坐标 $0$) 里含 1 个新种类 (`inj₂ tt`, 坐标是 `HB S₀`) 的结点. 这个读回原样注入第 1 站的层号 $B_1=\mathrm{emb}\,1\boxplus\mathrm{injL}\,1\,r_0$ (`HB (Kc 1)`): 第 1 站的层号含种类 `(inj₂ 1, inj₂ tt)` 的结点, 坐标取遍 `HB S₀`. 比较器: 计数函数 `nc` 的值 (`t-new-ne0` 说明计数器在这里不恒为 0, `t-zero` 说明它对 $0$ 给 $0$). 盲区: 搜索之外的结点不计; 没有说这个结点的分支是否随坐标增长.
> 3. **`Kt 1` 上的具体码** (`t-kfin2`): 目标是 `finK 2`.
> 4. **[定理] 第一个障碍** (§4, `no-covF₁`, `no-covΩ₁`): 真回灌的第 1 站层号 $B_1$ 不在 `foldFinK`, `foldωK` 的覆盖之内. 这两条是关于一个具体层号的定理 (由计算证明), 不是测试; `t-cells` 是测试.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvKtTest where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import OCF.Align.CumReadCF using (azero)
open import OCF.Align.HtTowerTy
open import OCF.Align.LvKtCode
open import OCF.Align.LvKtIf
open import OCF.Align.LvKtTower
open import OCF.Align.LvKtInst
import OCF.Align.LvTopInst as LT
```

## §1 截断版与 `LvTop` 截断版逐站相同

```agda
t-Hs0 : TrK.Hs 0 ≡ LT.Tr.Hs 0
t-Hs0 = refl

t-Hs1 : TrK.Hs 1 ≡ LT.Tr.Hs 1
t-Hs1 = refl

t-Hs2 : TrK.Hs 2 ≡ LT.Tr.Hs 2
t-Hs2 = refl
```

## §2 真回灌的第一站

```agda
-- 第 0 站: 层号 1, 在顶码上用有限码的折叠, 读回 r₀ : HB (Lev 1) = HB (step S₀)
r₀ : HB (Lev {S₀} (hs hz))
r₀ = rtTop cdS₀ (foldFinK S₀ cdS₀) (hs hz) tt (1 , refl)

-- 第 1 站的层号: 读回原样注入
B₁ : HB (Kc 1)
B₁ = emb (hs hz) ⊞ injL (hs hz) r₀

B₁-def : B₁ ≡ emb (hs hz) ⊞ injL (hs hz) r₀
B₁-def = refl

-- 有限搜索里新种类结点的个数
nc : ℕ → HB (step S₀) → ℕ
nc zero _ = 0
nc (suc k) hz = 0
nc (suc k) (hs x) = nc k x
nc (suc k) (hl f) = nc k (f 0) + (nc k (f 1) + nc k (f 2))
nc (suc k) (hΩ (inj₂ _) g) = 1 + nc k (g hz)
nc (suc k) (hΩ (inj₁ _) g) = nc k (g azero)

t-new : nc 6 r₀ ≡ 1
t-new = refl

t-new-ne0 : ¬ (nc 6 r₀ ≡ 0)
t-new-ne0 ()

t-zero : nc 6 hz ≡ 0
t-zero = refl
```

## §3 `Kt 1` 上的具体码

```agda
t-kfin2 : Codes.tgt ckt1 kfin2 ≡ finK 2
t-kfin2 = refl
```

## §4 第一个障碍: 真回灌后的第 1 站不在现有折叠的覆盖之内 (定理, 对这一个具体层号)

现有折叠只覆盖码目标字面地是 `finK n` (`CovFK`) 或逐项是 `finK n` 的 `hl f` (`CovΩK`) 的码. 真回灌的第 1 站层号 $B_1$ 的顶码目标就是 $B_1$ 自己. 它不是 `finK n` (`no-covF₁`: $B_1$ 的头是 ℕ-极限); 也不是逐项 `finK n` 的极限 (`no-covΩ₁`: 它的第 2 支里有 $\Omega$-结点, `finK n` 里没有). 只否定这一个层号在这两个覆盖之内; 不否定别的折叠能覆盖它.

```agda
-- 有限搜索里 Ω-结点 (任一种类) 的个数
ncΩ : ℕ → HB (Kc 1) → ℕ
ncΩ zero _ = 0
ncΩ (suc k) hz = 0
ncΩ (suc k) (hs x) = ncΩ k x
ncΩ (suc k) (hl f) = ncΩ k (f 0) + (ncΩ k (f 1) + ncΩ k (f 2))
ncΩ (suc k) (hΩ κ g) = 1 + ncΩ k (g (bot (Kc 1) κ))

ncΩ-fin : ∀ k n → ncΩ k (finK n) ≡ 0
ncΩ-fin zero n = refl
ncΩ-fin (suc k) zero = refl
ncΩ-fin (suc k) (suc n) = ncΩ-fin k n

cell : ∀ {S} → HB S → ℕ → HB S
cell (hl f) = f
cell _ = λ _ → hz

-- 第 0, 1 支在搜索里没有 Ω-结点, 第 2 支有一个 (有限测试)
t-cells : (ncΩ 7 (cell B₁ 0) ≡ 0) × (ncΩ 7 (cell B₁ 1) ≡ 0) × (ncΩ 7 (cell B₁ 2) ≡ 1)
t-cells = refl , refl , refl

no-covF₁ : ∀ n → ¬ (B₁ ≡ finK n)
no-covF₁ zero ()
no-covF₁ (suc n) ()

no-covΩ₁ : ¬ CovΩK (Kc 1) (ckc 1) B₁
no-covΩ₁ (f , e , ef) = bad (trans (cong (λ x → ncΩ 7 (cell x 2)) e) (trans (cong (ncΩ 7) (ef 2)) (ncΩ-fin 7 2)))
  where
  bad : ¬ (ncΩ 7 (cell B₁ 2) ≡ 0)
  bad ()
```
