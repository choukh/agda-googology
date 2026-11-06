# 分层互递归塔 (三): 形状定理 (对照 `only-κ₁`, `head-lossy`)

> 不含记号. 入口 [StratTw](StratTw.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提. 第 4 层 (形状, 对照), 不进闭项.
>
> 否定一路对 KindLv 的实例证了 `NegKindLvInst.only-κ₁` (只有第 1 站读回分量的头种类有级回灌) 与 `head-lossy` (第 $s+2$ 站的头种类退回 `fbA`, 有损). 本篇对 [StratTwTw](StratTwTw.lagda.md) 的实例写对应的陈述, 全是 `refl` 或对种类的模式匹配:
>
> 1. **`all-heads`**: 对一切 $s$, 头种类 `hd s = (suc s , inj₂ tt)` 的回灌是 `inj₁ (KT s)`; **`head-fed`** 是 `head-lossy` 的同一位置 (第 $s+2$ 站).
> 2. **`KT-ℓ`, `KT-diag`**: 它的级层是 `lyL (Y s)`, 也就是 `up (Bᴧ s)` (层号对角第 $s$ 项, 定义相等); **`KT-ℓ⊲`**: 是最终层的第一位置, 证据是 `hlim s hself` (字面).
> 3. **`KT-rd`**: 读回就是沿同形 `sim s` 的级读回; **`KT-E`**: 坐标类型就是读回的输出类型 `HB (Lev (X s))`. **`KT-sees`**: 读回不恒取起点 (数据 `n1` 读成后继; 对照 `NegKindLvBlind.relevel`: 接口不管这一点, 实例管).
> 4. **`lossy-inner`** (对照 `only-κ₁`, 方向反过来): 没有级回灌的种类恰好是某个 `Lev (X s)` 内部的种类 `(suc s , inj₁ κ)`.
> 5. **`hd-occ`**: 头种类在对角里出现: `Y (s+1) = hs (Y s) ⊞ hΩ (hd s) g` (对一切 $s$, `refl`). 所以每一站按级回灌的那一行在坍缩里不是空的 (前提可满足).
> 6. **`start-hd`**: 起始世界里头种类的界是 $0$ (同 `NegKindLvInst.start-κ₁`; 坍缩从基世界起步).
> 7. **`Y-lim`, `KT-top-lossy`** (仍有损的一行, 定理): 第 $s+2$ 站的级 `Y (s+1)` 是头种类 `hd s` 的 $\Omega$-结点, 所以它的级读回在路径停在级顶的结点上读输入为 $0$ 的分支 (`refl`).
> 8. **`Sim-rf`**: 同形对恒等映射自反, 所以 `StratTwRd` 的读回包含 `KindLvRd` 的情形 ($M=$ 恒等, $c=X$); 逐结点等价没有写.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StratTwCmp where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.HtTowerTy
open import OCF.Align.GenFoldIf using (tpK; top; w₀; n0; n1; ni; ss)
open import OCF.Align.GenFoldTree using (module Tree)
open import OCF.Align.KindLvIf using (KLv; ℓ; ℓ⊲; rd; lyL)
open import OCF.Align.KindLvEv using (evK)
open import OCF.Align.StratTwIf using (KMap; Sim; Bᴧ) renaming (sz to σz; ss to σs; sl to σl; sΩ to σΩ)
open import OCF.Align.StratTwTw
import OCF.Align.StratTwRd as SRd
open SRd U LdU using (module SR; Br)
open Tree U using (≤rf; inS)
```

## §1 每站的头种类都有级回灌

```agda
all-heads : ∀ s → lvU (hd s) ≡ inj₁ (KT s)
all-heads s = refl

-- 与 NegKindLvInst.head-lossy 同一位置 (第 s+2 站的头种类)
head-fed : ∀ s → lvU (suc (suc s) , inj₂ tt) ≡ inj₁ (KT (suc s))
head-fed s = refl
```

## §2 级层是自己的级, 是对角的第一位置

```agda
KT-ℓ : ∀ s → ℓ (KT s) ≡ lyL (Y s)
KT-ℓ s = refl

KT-diag : ∀ s → ℓ (KT s) ≡ up (Bᴧ StU s)
KT-diag s = refl

KT-ℓ⊲ : ∀ s {w} → ℓ⊲ (KT s) {w} ≡ hlim s hself
KT-ℓ⊲ s = refl
```

## §3 读回沿同形, 输出类型就是坐标类型

```agda
KT-E : ∀ s → E U (hd s) ≡ HB (Lev (X s))
KT-E s = refl

KT-rd : ∀ s {W} (lW : LgW (step U) W) b x → rd (KT s) lW b x ≡ SR.readS (MP s) (sim s) lW b x
KT-rd s lW b x = refl

KT-sees : ∀ s {W} (lW : LgW (step U) W) (b : HB (Lev (X s))) → rd (KT s) lW b n1 ≡ hs b
KT-sees s lW b = refl
```

## §4 没有级回灌的种类

```agda
lossy-inner : ∀ κ → lvU κ ≡ inj₂ tt → Σ ℕ (λ s → Σ (K (Lev (X s))) (λ κ′ → κ ≡ (suc s , inj₁ κ′)))
lossy-inner (zero , tt) ()
lossy-inner (suc s , inj₂ tt) ()
lossy-inner (suc s , inj₁ κ′) e = s , κ′ , refl
```

## §5 头种类在对角里出现; 起始世界

```agda
hd-occ : ∀ s → Σ (E U (hd s) → HB U) (λ g → Y (suc s) ≡ hs (Y s) ⊞ hΩ (hd s) g)
hd-occ s = _ , refl

start-hd : ∀ s → top (tpK GU) (hd s) (w₀ GU) ≡ hz
start-hd s = refl
```

## §6 仍有损的一行: 第 $s+2$ 站的级是 $\Omega$-极限, 顶行读输入 $0$

`Y (s+1)` 的头是头种类 `hd s` 的 $\Omega$-结点 (`Y-lim`, 因为 `evK` 的头是新种类的 $\Omega$-结点, `⊞` 把它提到外面). 所以 `KT (s+1)` 的读回在路径停在级顶 (`hself`) 的结点上走 `sΩ` 的有损行 (`KT-top-lossy`): 读的是输入为 $0$ 的分支, 不是一个以这一层数据为坐标的种类 (第 $c$ 级在 $\Omega$-极限 $c$ 处没有这样的种类, `KindLvRd` 文件头). 路径进入分支 (`hLim`, 坐标 $e$ 在世界的界之下) 的结点不在这一行, 沿 $e$ 的分支往下读.

```agda
Y-lim : ∀ s → Σ (E U (hd s) → HB U) (λ g → Y (suc s) ≡ hΩ (hd s) g)
Y-lim s = _ , refl

KT-top-lossy : ∀ s {W} (lW : LgW (step U) W) (b : HB (Lev (X (suc s)))) (u : Br (Y (suc s)) {W} hself) →
  rd (KT (suc s)) lW b (ni (ss hself) u) ≡ rd (KT (suc s)) lW b (u ≤rf lW (inS (ss (hself {w = W})) n0))
KT-top-lossy s lW b u = refl
```

## §7 同形对恒等自反

```agda
idM : ∀ {S : KS} → KMap S S
idM = record { j = λ κ → κ ; cv = λ κ e → e }

Sim-rf : ∀ {S : KS} (c : HB S) → Sim idM c c
Sim-rf hz = σz
Sim-rf (hs c) = σs (Sim-rf c)
Sim-rf (hl f) = σl (λ n → Sim-rf (f n))
Sim-rf (hΩ κ g) = σΩ (λ e → Sim-rf (g e))
```
