# 层号一次封闭, 合法性由形状给出: 类型

> 不含记号. 入口 [LFRe](LFRe.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.
>
> 这一篇把 [LevelFixCore](LevelFixCore.lagda.md) 的 `LF` 重写成 [HtTowerTy](HtTowerTy.lagda.md) 的语言. 归纳-递归块只有两件: 层号 `LH` 与它的种类结构 `Lv : LH → KS`. `Lv` 就是 `HtTowerTy.Lev` 的形状, 只是定义在层号自己身上 (块内), 所以**以层号为下标的种类与层号在同一个类型里一次封闭**. 块里没有守卫, 没有 `Gd`, `Lgl`, `Cp`: 旧块里的守卫是为了让分支只取下界之上的值, 这里分支在一切坐标上都有, 下界由和的形状 ($b\boxplus c$) 给出.
>
> 高度是 `HB SL`, `SL = sup LH (step ∘ Lv)`: 与 `HtTowerU.U = sup ℕ (step ∘ L)` 同形, 下标集从 $\mathbb N$ 换成 `LH`. 第一位置、合法、比较都直接是 `HtTowerTy` 对一切 `S` 的那一套 (`_⊲[_]_`, `LgB`, `cmpB`), 这里一行也不新写.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LFReTy where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.HtTowerTy
```

## §1 底: 没有种类的种类结构

`S⊥` 的高度是只有 $0$, 后继, ℕ-极限的树, 即第 0 层的值 ($<\Omega_1$). 与 `HtTowerTy.S₀` 差一级: `S₀` 已经带一个以 `A` 为坐标的种类.

```agda
module Bot where
  E⊥ : ⊥ → Set
  E⊥ ()

  Bd⊥ : (κ : ⊥) → E⊥ κ → ⊤ → Set
  Bd⊥ ()

  Pr⊥ : (κ : ⊥) → ⊤ → E⊥ κ → E⊥ κ → Set
  Pr⊥ ()

  Bd↑⊥ : ∀ {κ c w w′} → ⊤ → Bd⊥ κ c w → Bd⊥ κ c w′
  Bd↑⊥ {()}

  cmp⊥ : ∀ {κ c c′ w} → Bd⊥ κ c w → Bd⊥ κ c′ w → ⊤ → Pr⊥ κ w c′ c ⊎ Pr⊥ κ w c c′
  cmp⊥ {()}

  LgE⊥ : (κ : ⊥) → E⊥ κ → Set
  LgE⊥ ()

  lgBd⊥ : ∀ {κ c w} → Bd⊥ κ c w → ⊤ → LgE⊥ κ c
  lgBd⊥ {()}

  bot⊥ : (κ : ⊥) → E⊥ κ
  bot⊥ ()

  botBd⊥ : ∀ κ w → Bd⊥ κ (bot⊥ κ) w
  botBd⊥ ()

S⊥ : KS
S⊥ = record
  { K = ⊥ ; E = E⊥ ; Wd = ⊤ ; LgW = λ _ → ⊤ ; _≤w_ = λ _ _ → ⊤ ; ≤w-rf = tt ; ≤w-tr = λ _ _ → tt
  ; Bd = Bd⊥ ; Pr = Pr⊥ ; Bd↑ = λ {κ} {c} {w} {w′} → Bd↑⊥ {κ} {c} {w} {w′} ; cmpK = λ {κ} {c} {c′} {w} → cmp⊥ {κ} {c} {c′} {w}
  ; LgE = LgE⊥ ; lgBd = λ {κ} {c} {w} → lgBd⊥ {κ} {c} {w} ; bot = bot⊥ ; botBd = botBd⊥ }
  where open Bot
```

## §2 块

`lΩ k g`: 共尾度 $\Omega_{k+1}$ 的层号, 坐标是第 $k$ 层的值 `HB (Lv k)` ($<\Omega_{k+1}$). `Lv x`: 第 $x$ 层的值用到的种类. 四行与 `Lev` 相同, 只有 `lΩ` 一行多放一个分量 `step (Lv k)`: 共尾度 $\Omega_{k+1}$ 的层上要有 $\Omega_{k+1}$ 这一种分支 (旧块 `Pre (lc k …)` 的 `inj₁ (inj₁ _)`). 块里只有这两个定义, 没有证明, 没有关系.

```agda
data LH : Set
Lv : LH → KS

data LH where
  lz : LH
  ls : LH → LH
  ll : (ℕ → LH) → LH
  lΩ : (k : LH) → (HB (Lv k) → LH) → LH

Lv lz = S⊥
Lv (ls x) = step (Lv x)
Lv (ll f) = sup ℕ (λ n → Lv (f n))
Lv (lΩ k g) = sup (⊤ ⊎ HB (Lv k)) [ (λ _ → step (Lv k)) , (λ c → Lv (g c)) ]′
```

**一次封闭.** 一切层号的种类结构都由这一个递归给出, 没有外部编号, 没有逐级的新类型. 对照 `HtTowerU`: 那里的级 `L k` 以 $\mathbb N$ 为下标, 塔 `U` 不封口 (`no-retract` 推出 `U` 里没有以 `HB U` 为坐标的种类). 这里下标是层号自己, 所以 $\Lambda$ 之上的 $\Omega_{\Lambda+1}$ 也是一个种类 (`LFReTower.ΩΛ+1`). `no-retract` 仍然成立 (`LFReNeg.no-retract-SL`): 种类 $k$ 的坐标是 `HB (Lv k)`, 不是全部高度.

## §3 高度与读回层

```agda
FL : LH → KS
FL k = step (Lv k)

SL : KS
SL = sup LH FL

ιL : ∀ k → HB (FL k) → HB SL
ιL k = ι {LH} {FL} k

-- 第 k 层的新种类, 即 Ω_{k+1}
νL : LH → K SL
νL k = k , inj₂ tt
```

`lvl k κ`: 第 $k$ 层的值里种类 $\kappa$ 的读回层 (它的坐标在哪一层). `node`: 以种类 $\kappa$ 为共尾度的层号节点. 两者对 $(k,\kappa)$ 递归, 与旧文件 `LevelFixVal.upN` 同形; 到底的那一步类型字面对上, 不要运输.

```agda
lvl : (k : LH) → K (Lv k) → LH
lvl lz ()
lvl (ls x) (inj₁ κ) = lvl x κ
lvl (ls x) (inj₂ _) = x
lvl (ll f) (n , κ) = lvl (f n) κ
lvl (lΩ k g) (inj₁ _ , inj₁ κ) = lvl k κ
lvl (lΩ k g) (inj₁ _ , inj₂ _) = k
lvl (lΩ k g) (inj₂ c , κ) = lvl (g c) κ

node : (k : LH) (κ : K (Lv k)) → (E (Lv k) κ → LH) → LH
node lz () h
node (ls x) (inj₁ κ) h = node x κ h
node (ls x) (inj₂ _) h = lΩ x h
node (ll f) (n , κ) h = node (f n) κ h
node (lΩ k g) (inj₁ _ , inj₁ κ) h = node k κ h
node (lΩ k g) (inj₁ _ , inj₂ _) h = lΩ k h
node (lΩ k g) (inj₂ c , κ) h = node (g c) κ h

-- SL 的每个种类都有读回层: HtTower 第一个障碍 (iv) 在这里是一个定义
rbl : K SL → LH
rbl (k , inj₂ _) = k
rbl (k , inj₁ κ) = lvl k κ

-- 高度读成层号, 层号读成高度
ofHB : HB SL → LH
ofHB hz = lz
ofHB (hs h) = ls (ofHB h)
ofHB (hl f) = ll (λ n → ofHB (f n))
ofHB (hΩ (k , inj₂ _) g) = lΩ k (λ c → ofHB (g c))
ofHB (hΩ (k , inj₁ κ) g) = node k κ (λ c → ofHB (g c))

toHB : LH → HB SL
toHB lz = hz
toHB (ls x) = hs (toHB x)
toHB (ll f) = hl (λ n → toHB (f n))
toHB (lΩ k g) = hΩ (νL k) (λ c → toHB (g c))

-- 层号的值读成层号 (旧文件的 up)
upL : (k : LH) → HB (Lv k) → LH
upL k hz = lz
upL k (hs c) = ls (upL k c)
upL k (hl f) = ll (λ n → upL k (f n))
upL k (hΩ κ h) = node k κ (λ c → upL k (h c))
```

**读回层对上坐标 (HtTower 第一个障碍 (iv)).** 每个种类的坐标类型就是它读回层的值的类型. 新种类 `νL k` 字面如此 (`E SL (νL k)` 归约到 `HB (Lv k)`); 重复的旧种类 `(k , inj₁ κ)` 是类型的 `≡`, 对 $(k,\kappa)$ 递归, 每一步 `refl` 或递归调用.

```agda
E-rbl : ∀ κ → E SL κ ≡ HB (Lv (rbl κ))
E-lvl : ∀ k κ → E (Lv k) κ ≡ HB (Lv (lvl k κ))
E-rbl (k , inj₂ _) = refl
E-rbl (k , inj₁ κ) = E-lvl k κ
E-lvl lz ()
E-lvl (ls x) (inj₁ κ) = E-lvl x κ
E-lvl (ls x) (inj₂ _) = refl
E-lvl (ll f) (n , κ) = E-lvl (f n) κ
E-lvl (lΩ k g) (inj₁ _ , inj₁ κ) = E-lvl k κ
E-lvl (lΩ k g) (inj₁ _ , inj₂ _) = refl
E-lvl (lΩ k g) (inj₂ c , κ) = E-lvl (g c) κ
```

`toHB`, `ofHB` 在构造子上互逆 (`ofHB (toHB x)` 与 `x` 逐构造子相同); 没有证明 `≡`, 那要函数外延, 这里用不到.
