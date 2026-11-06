# 层号换类型: 接口 `FoldAtK`, 换类型的塔的种类结构

> **接口定稿 2026-11-05 15:21 (首次编译通过).** 定稿之后只增不改; 若必须改, 在这里写变更记录. 变更记录: (无).
>
> 不含记号. 入口 [LvKt](LvKt.lagda.md). 作者此前选定的方向原话: "A3: 读回包 + 第 ω+1 级折叠"; 目标 (作者原话) "写出 ψ₀Λ 的候选闭项". 本路 (前缀 `LvKt`) 是 [LvTop](LvTop.lagda.md) 接手清单第 1 条 "层号换类型" 的构造一路; 否定一路 (前缀 `NegLvKt`) 导入本文件. 本篇只放类型, 记录与几个只由构造子组成的定义 (种类结构的塔, 嵌入), 不放证明. 依赖 [LvKtCode](LvKtCode.lagda.md) (对一般种类结构的码), [HtTowerTy](HtTowerTy.lagda.md) (`KS`, `HB`, `Lev`, `step`, `sup`, `ι`). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> **对象.**
>
> - **码与世界 (对一般种类结构 `K`).** 码的界 $b$ 在 `HB K` 里, 外层世界 $a$ 在 `Wd K` 里 (`LvTopIf` 把外层世界固定为 `A` 的 $0$; 这里是参数). 码 `CodeK ck a b = Codes.Code ck a b` (`LvKtCode`, 数据加命题, 同一 $(a,b)$ 之下相等可判定). 码 $k$ 的槽是第 `tgt k` 级的高度 `HB (Lev (tgt k))`; 世界 `WbK ck a b`: 每个码一个槽.
> - **`FoldAtK K ck Cov`** (`LvTopIf.FoldAt` 的推广): 输入: 外层世界 $a$ (合法), 界 $b$ (合法), $b$ 之下的码 $c$, 覆盖证据 `Cov (tgt c)`, 世界 $w$ (合法). 输出: 第 $\mathrm{tgt}\,c+1$ 级的级顶经这一级折叠的读回 `rt : HB (Lev (tgt c))`, 与降到 `Ht` 的回灌输出 `H`. 两条律只说输出合法. `FoldAllK K ck = FoldAtK K ck (λ _ → ⊤)`.
> - **换类型的塔 (种类结构).** `Kc 0 = S₀`, `Kc (s+1) = nxt (Kc s)`, 其中 `nxt K = sup (⊤ ⊎ HB K) (FN K)`, `FN K (inj₁ tt) = K`, `FN K (inj₂ c) = Lev c`: 下一站的种类是 "上一站自己" 加上 "以上一站的每个高度 $c$ 为层号的第 $c$ 级". 码 `ckc s` (由 `cdSup`, `cdLev` 给出). 极限 `KΛc = sup ℕ Kc`, 码 `ckΛ`.
> - **嵌入 (旧站的高度搬进新站)**: `emb = ι (inj₁ tt) : HB K → HB (nxt K)`. **读回进新站**: `injL c = ι (inj₂ c) : HB (Lev c) → HB (nxt K)`: 第 $s$ 站在层号 $c$ 处的读回 (`rt`, 类型 `HB (Lev c)`) 原样成为第 $s+1$ 站层号所在类型 `HB (Kc (s+1))` 里的高度. 两者都是并的分量注入, 不判定任何东西.
> - **闭项的类型.** 闭项是 `A` 的元素, 证书 `Lg`, FGH 是 `ℕ → ℕ` (同 `LvTop`); 一切站的回灌输出 `H` 都在 `Ht` 里, 闭项用 `HtTowerFClosed.T⁺`.
> - **条件版的前提** `FoldTower = ∀ s → FoldAllK (Kc s) (ckc s)` (每一站一切码上的折叠), `FoldLimK = FoldAllK KΛc ckΛ` (极限站).
>
> **与 `LvTopVal.Kt` 的差别 (写法的论证).** `Kt (s+1) = Lev (Ωtop (Kt s))` 按定义是 `sup (HB (Kt s)) (λ c → Lev (up c))` (`LvTopVal.Kt1`). 读回 `rt` 的类型是 `HB (Lev c)`, 不是 `HB (Lev (up c))`; 两者对变量 $c$ 不定义相等 (`Lev (up (hl f)) = sup ℕ (Lev ∘ up ∘ f)` 与 `sup ℕ (Lev ∘ f)` 的相等要沿族的函数外延), 所以照 `Kt` 写要一层逐结点的搬运 (`LvTopInst.Cvt` 那一类脚手架). `nxt` 直接以 `Lev c` 为分量, 读回原样注入. 另一处差别是多一个分量 `inj₁ tt ↦ K` 本身, 让嵌入成为分量注入 (字面保第一位置与合法, `ι-⊲`, `Lg-ι`); 不加它时, 把 `Kt s` 的高度搬进 `Kt (s+1)` 要先在 `Kt (s+1)` 里找一个包含 `Kt s` 一切种类的层号, 又是逐结点的搬运. [判断] 加这个分量不改变读法: `Kc s` 的种类本身就是一些 `Lev c′` (或 `S₀`), 它们在 `nxt` 的第二类分量里以更大的层号再出现一次. 没有写成定理.
>
> **律的定义域 (逐条).** 律里出现的每一对下标都带字面公共上界:
>
> - `rt`, `lrt`, `H`, `lgH`: 每条只出现**一个**码 $c$, 它带着字面的界 $b$ 与外层世界 $a$ (`Codes.pth c : tgt c ⊲[ a ] b` 是证据). 律不比较两个码, 不比较两个坐标, 不比较两站的层号. 没有更新律.
> - 码的相等: 只在同一 $(a,b)$ 之下判 (`Codes.code-≟`, 原始码 `RC` 是数据).
> - 嵌入: `emb`, `injL` 是分量注入, 不需要判定 (所以不写成律). 在塔里用到的 "嵌入保第一位置/合法" 是 `HtTowerTy.ι-⊲`, `Lg-ι` 的实例 (定理, 在 [LvKtTower](LvKtTower.lagda.md)), 它们只对**同一分量**里的一对高度说话, 公共上界是这个分量的世界.
> - 塔里的比较: 第 $s$ 站的层号与第 $s+1$ 站的层号不在同一类型里, 塔只说 `emb (B s) ⊲[ w ] B (s+1)` (同在 `HB (Kc (s+1))`, 公共上界是 `B (s+1)` 自己); 对角在 `KΛc` 里另写一列 (`Bᴧ`), 相邻项同在 `HB KΛc` 里.
>
> **`no-retract` 与壁垒 (检查).** `HtTowerNeg.no-retract`: 没有种类的坐标里装着同一个高度类型的全部高度. 这里 `Kc (s+1)` 的种类以 `HB (Kc s)` (前一站) 为下标, `KΛc` 的种类是各 `Kc s` 的种类, 没有一个种类以 `HB KΛc` 或 `HB (Kc (s+1))` 自身为坐标; 极限站的层号 `ΛB : HB KΛc` 只作 `Lev` 的参数 (种类结构 `Lev ΛB` 的坐标是 `KΛc` 的坐标, 都是某个 `Kc s` 的坐标). 壁垒 (`Barrier.barrier`): 下标类型不含 $\Omega$-共尾元加有界三歧; 本接口不要求任何下标类型上的三歧或判定, 只有码 (数据) 的相等判定. [判断] 不触壁垒; 否定一路若找到反例, 以它为准.
>
> **接口不管什么 (盲).** 记录只要求输出合法; 恒取 $0$ 的折叠是实例 (`LvKtVal.foldTrivK`). 所以接口不决定值.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvKtIf where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (Ht)
open import OCF.Align.LvKtCode
```

## §1 码与世界 (一般种类结构)

```agda
module _ {K : KS} (ck : CdK K) where
  open Codes ck

  CodeK : Wd K → HB K → Set
  CodeK = Code

  tgtK : ∀ {a b} → CodeK a b → HB K
  tgtK = tgt

  WbK : Wd K → HB K → Set
  WbK a b = (k : Code a b) → HB (Lev (tgt k))

  LgWbK : ∀ {a b} → WbK a b → Set
  LgWbK w = ∀ k → LgB (w k)
```

## §2 在码目标上的一级折叠

```agda
record FoldAtK (K : KS) (ck : CdK K) (Cov : HB K → Set) : Set where
  open Codes ck
  field
    rt  : ∀ {a b} → LgW K a → LgB b → (c : Code a b) → Cov (tgt c) → (w : WbK ck a b) → LgWbK ck w → HB (Lev (tgt c))
    lrt : ∀ {a b} (la : LgW K a) (lb : LgB b) c (cv : Cov (tgt c)) w (lw : LgWbK ck w) → LgB (rt la lb c cv w lw)
    H   : ∀ {a b} → LgW K a → LgB b → (c : Code a b) → Cov (tgt c) → (w : WbK ck a b) → LgWbK ck w → Ht
    lgH : ∀ {a b} (la : LgW K a) (lb : LgB b) c (cv : Cov (tgt c)) w (lw : LgWbK ck w) → LgB (H la lb c cv w lw)

FoldAllK : (K : KS) → CdK K → Set
FoldAllK K ck = FoldAtK K ck (λ _ → ⊤)
```

## §3 换类型的塔

```agda
FN : (K : KS) → ⊤ ⊎ HB K → KS
FN K (inj₁ _) = K
FN K (inj₂ c) = Lev c

nxt : KS → KS
nxt K = sup (⊤ ⊎ HB K) (FN K)

cdFN : ∀ {K} → CdK K → (i : ⊤ ⊎ HB K) → CdK (FN K i)
cdFN ck (inj₁ _) = ck
cdFN ck (inj₂ c) = cdLev c

cdNxt : ∀ {K} → CdK K → CdK (nxt K)
cdNxt {K} ck = cdSup (⊤ ⊎ HB K) (FN K) (cdFN ck)

Kc : ℕ → KS
Kc zero = S₀
Kc (suc s) = nxt (Kc s)

ckc : ∀ s → CdK (Kc s)
ckc zero = cdS₀
ckc (suc s) = cdNxt (ckc s)

KΛc : KS
KΛc = sup ℕ Kc

ckΛ : CdK KΛc
ckΛ = cdSup ℕ Kc ckc

-- 嵌入: 旧站的高度搬进新站 (分量注入)
emb : ∀ {K} → HB K → HB (nxt K)
emb {K} = ι {⊤ ⊎ HB K} {FN K} (inj₁ tt)

-- 读回进新站: 层号 c 处的高度成为下一站的高度
injL : ∀ {K} (c : HB K) → HB (Lev c) → HB (nxt K)
injL {K} c = ι {⊤ ⊎ HB K} {FN K} (inj₂ c)

-- 第 s 站进极限
ιΛ : ∀ s → HB (Kc s) → HB KΛc
ιΛ s = ι {ℕ} {Kc} s
```

## §4 条件版的前提

```agda
FoldTower : Set
FoldTower = ∀ s → FoldAllK (Kc s) (ckc s)

FoldLimK : Set
FoldLimK = FoldAllK KΛc ckΛ
```
