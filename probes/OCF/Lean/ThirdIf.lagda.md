# Third: 接口 (共享低层世界的塔与一层世界的移动)

> 不含记号. 入口 [Third](Third.lagda.md). 构造一路 Third, 否定一路 NegThird 共用. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示. 只导入 stdlib 与 [CRwBase](CRwBase.lagda.md).
>
> **接口定稿 2026-11-06 21:21 (首次编译通过).** 定稿后只增不改.
>
> **设计 (构造一路的计划, 不是接口的律).** 底对 $n:\mathbb N$ 递归; 第 $n+1$ 个底的分量由第 $n$ 个底的**值** $c$ 编号, 第 $c$ 个分量是第 $n$ 个底上高度 $c+1$ 的塔. 塔 `Tw U m` 的高度 $m$ 是 `HB U` 的值: 后继给 `step`, ℕ-极限给 `sup ℕ`, $\Omega$-结点 `hΩ κ g` 给 `sup (E U κ)` (分量由坐标编号; 底种类 $\kappa$ 留在塔里, 不另设内层指标种类).
>
> **公共上界.** 一切比较在一个世界的一层 $(w, B)$ 里做: $w$ 是低层世界, $B$ 是合法的界. 分量序号 $c$ 与目标高度 $t$ 都是 $B$ 在世界 $w$ 里的第一位置 (字面公共上界 $B$), 用 `CRwBase.cmpB`.
>
> **位置要世界.** 塔的种类穿过高度的 $\Omega$-结点时, 分量坐标要在世界的界之下: `Pos U w m κ` (§2). 这是 RecB 没有的新证据 (RecB 的高度是可数树, 位置与世界无关).
>
> **律.** `LayerMv U` 与 `LHRecIf` 对一层同形: 回灌的坐标可入 (`adm-sh`), 进入不缩小世界并带字面证据 (`nx-up`), 进入保合法 (`lg-nx`), 可入随世界变小 (`adm↓`), 初始世界带字面证据 $1\lhd$ 界.
>
> **没有对裸下标的比较律.** 律里出现的世界对只有 $(W, W')$ 与 $(W,$ `nxt W e a` $)$, 都带字面 `LeS` 证据; 坐标对不出现. `Pos` 只说分量坐标在界之下, 不比较两个坐标.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.ThirdIf where

open import Data.Nat using (ℕ)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_)
open import OCF.Lean.CRwBase
```

## §1 一层世界

```agda
WS : KS → Set
WS U = Wd (step U)

LeS : ∀ U → WS U → WS U → Set
LeS U = _≤w_ (step U)

LgS : ∀ U → WS U → Set
LgS U = LgW (step U)

record LayerMv (U : KS) : Set₁ where
  field
    Adm    : WS U → HB U → Set
    nxt    : (W : WS U) (e : HB U) → Adm W e → WS U
    sh     : WS U → HB U → HB U
    adm-sh : ∀ {W} c → LgS U W → Adm W (sh W c)
    nx-up  : ∀ {W e} (a : Adm W e) → LeS U W (nxt W e a)
    lg-nx  : ∀ {W e} (a : Adm W e) → LgS U W → LgS U (nxt W e a)
    adm↓   : ∀ {W W′} → LeS U W W′ → ∀ {e} (a′ : Adm W′ e) →
             Σ (Adm W e) (λ a → LeS U (nxt W e a) (nxt W′ e a′))
    W₀     : WS U
    o₀     : Bd (step U) (inj₂ tt) (hs hz) W₀   -- 字面证据: 1 ⊲ (W₀ 的界)
    lW₀    : LgS U W₀
```

## §2 高度是值的塔, 种类的位置

```agda
Tw : (U : KS) → HB U → KS
Tw U hz = U
Tw U (hs x) = step (Tw U x)
Tw U (hl f) = sup ℕ (λ n → Tw U (f n))
Tw U (hΩ κ g) = sup (E U κ) (λ e → Tw U (g e))

-- 种类 κ 在世界 w 里确实在第 m 层之下: 穿过 Ω-结点的分量坐标在界之下
Pos : ∀ U → Wd U → (m : HB U) → K (Tw U m) → Set
Pos U w hz κ = ⊤
Pos U w (hs x) (inj₁ κ) = Pos U w x κ
Pos U w (hs x) (inj₂ _) = ⊤
Pos U w (hl f) (n , κ) = Pos U w (f n) κ
Pos U w (hΩ κ₀ g) (e , κ) = Bd U κ₀ e w × Pos U w (g e) κ
```
