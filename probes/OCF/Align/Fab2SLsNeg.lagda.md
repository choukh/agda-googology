# 配对否定: 第 2 站的层里以坐标为下标的分量, 点更新是分离子

> 不含记号. Fable 5.1, 2026-11-05. 对着 [Fab2SLs](Fab2SLs.lagda.md) 写 (导入它, 不另造接口). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延 (连前提也没有).
>
> **否定什么.** `Fab2SLs` 把站的下标换成 ℕ, 每站头种类的界可以 "升一份留别份" (`setH-top`, `setH-keep`, 定理). 本篇说: 每站**级里**的深种类不行. 第 2 站的层 `st 2 = lΩ lz g₂` 的种类结构 `L₂ = Lv (st 2) = sup (⊤ ⊎ HB S⊥) G₂` 的世界是以坐标 `HB S⊥` 为下标的积 (`L₂-form`, `refl`); 在它上面, 一个对一切世界、一切下标一致的点更新 (升: 分量 $i$ 的种类的界由新分量给出; 留: 别的分量 $k\neq i$ 的界不升) 推出分离子 `Sep₂` (`updD₂-sep`, 定理): 对一切 $\alpha:\mathbb N\to$ `Bool`, $\alpha$ 全假或两个下标 `jx (fα α)`, `jx fω` 不相等. 证明与 [NegGenFoldUpd](NegGenFoldUpd.lagda.md) 的 `upd₁-sep` 同一形状: 在基世界里把分量 `jx fω` 的第 0 个子分量 (它是 `step S⊥`, 新种类的界是 `HB S⊥`, 对一切 `f` 同一个类型) 的界升到 $1$, 看分量 `jx (fα α)` 的同一处是不是 $0$ (`HB S⊥` 的构造子, 可判定): 是 $0$ 则两下标不等 (由 "升"), 不是 $0$ 则两下标不能不等 (由 "留").
>
> **只否定什么.** 只否定 `L₂` 的世界上同时满足 "升" 与 "留" 的一致点更新. 不否定: `Fab2SLs` 的闭项与它的律 (`KLv` 只要 "升", 不要 "留"; 头种类在 ℕ 下标上两半同时成立); 深种类的有损回灌 (`deep-lossy`); 带证据的世界 (`RsOwn.subW`, 在跑的 `SLFb`) 或共享槽 (`Slot`) 上的升界. 与 [NegStratTw](NegStratTw.lagda.md) 的 `updD-sep` 同一结论, 对象换成一次封闭的 `Lv`. "留" 的那一半单独可满足 (`half-keep`: 世界不动). "升" 的那一半在这里**连类型都写不出**一致的形式: 分量 `inj₂ c` 的类型 `Wd (Lv (g₂ c))` 随 $c$ 变 (`c = hz` 时是 `Wd (step S⊥)`, `c = jx f` 时是 ℕ 上的积), 一个 $v$ 不能同时放进两个分量 (判断; `NegGenFoldUpd.half₁R` 那种 "一切底拷贝一起升" 要各分量同型).
>
> **对纲领与目标.** 这条定理把 C6 的位置钉在 "级里以坐标为下标的分量", 不在站: 站的下标是 ℕ 时站没有墙 (`Fab2SLs.setH-keep`), 墙全在层的内部. 这是树侧的判据 (以什么为下标), 不看记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Fab2SLsNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy using (LH; lz; ls; ll; lΩ; Lv; S⊥; ofHB; ιL)
open import OCF.Align.FabLFReGen using (w₀Lv)
open import OCF.Align.Fab2SLs using (st)
```

## §1 第 2 站的层: 以坐标为下标的积

```agda
g₂ : HB S⊥ → LH
g₂ c = ofHB (hs hz ⊞ ιL lz (up c))

G₂ : ⊤ ⊎ HB S⊥ → KS
G₂ = [ (λ _ → step S⊥) , (λ c → Lv (g₂ c)) ]′

L₂ : KS
L₂ = Lv (st 2)

-- st 2 = lΩ lz g₂, 它的种类结构是以 ⊤ ⊎ HB S⊥ 为下标的并
st2-form : st 2 ≡ lΩ lz g₂
st2-form = refl

L₂-form : L₂ ≡ sup (⊤ ⊎ HB S⊥) G₂
L₂-form = refl

W₂ : Set
W₂ = Wd L₂
```

## §2 下标的形状与分离子的输入

`jx f` 是第 0 项为 $0$ 的 ℕ-极限坐标. 分量 `inj₂ (jx f)` 的种类结构是 `Lv (ll …)`, 它的第 0 个子分量是 `Lv (ls lz) = step S⊥`, 对一切 `f` 同一个类型; 那里新种类 `(0 , inj₂ tt)` 的界是 `HB S⊥`.

```agda
jx : (ℕ → HB S⊥) → HB S⊥
jx f = hl (λ { zero → hz ; (suc n) → f n })

unhl : HB S⊥ → ℕ → HB S⊥
unhl (hl g) = g
unhl _ = λ _ → hz

jx-inj : ∀ {f f′} → jx f′ ≡ jx f → f′ ≡ f
jx-inj e = cong (λ x n → unhl x (suc n)) e

bit : Bool → HB S⊥
bit true = hs hz
bit false = hz

fα : (ℕ → Bool) → ℕ → HB S⊥
fα α n = bit (α n)

fω : ℕ → HB S⊥
fω _ = hz

bit≡ : ∀ b → bit b ≡ hz → b ≡ false
bit≡ false _ = refl
bit≡ true ()

eq→F : ∀ α → jx (fα α) ≡ jx fω → ∀ n → α n ≡ false
eq→F α e n = bit≡ (α n) (cong (λ f → f n) (jx-inj e))

Sep₂ : Set
Sep₂ = ∀ (α : ℕ → Bool) → (∀ n → α n ≡ false) ⊎ ¬ (jx (fα α) ≡ jx fω)

-- 分量 inj₂ (jx f) 的第 0 个子分量的类型, 对一切 f 都是 step S⊥ 的世界
sub-form : ∀ f → Wd (Lv (g₂ (jx f))) ≡ ((n : ℕ) → Wd (Lv (ofHB (hs hz ⊞ ιL lz (up (unhl (jx f) n))))))
sub-form f = refl

sub0-form : ∀ f → Wd (Lv (ofHB (hs hz ⊞ ιL lz (up (unhl (jx f) 0))))) ≡ Wd (step S⊥)
sub0-form f = refl

κ₀ : ∀ f → K (Lv (g₂ (jx f)))
κ₀ f = 0 , inj₂ tt

-- 它的界读法: 坐标在第 0 个子分量第二分量之下 (refl)
bd0-form : ∀ f (c : HB S⊥) (x : Wd (Lv (g₂ (jx f)))) → Bd (Lv (g₂ (jx f))) (κ₀ f) c x ≡ (c ⊲[ tt ] proj₂ (x 0))
bd0-form f c x = refl
```

## §3 点更新 (升 + 留) 与分离子

```agda
record PtUpd₂ : Set where
  field
    updD  : (w : W₂) (i : ⊤ ⊎ HB S⊥) → Wd (G₂ i) → W₂
    raise : ∀ w i x (κ : K (G₂ i)) c → Bd (G₂ i) κ c x → Bd L₂ (i , κ) c (updD w i x)
    keep  : ∀ w i x k → ¬ (k ≡ i) → ∀ (κ : K (G₂ k)) c → Bd L₂ (k , κ) c (updD w i x) → Bd L₂ (k , κ) c w
open PtUpd₂ public

-- 基世界, 与新分量 (第 0 个子分量的界升到 1, 其余同基世界)
w₀₂ : W₂
w₀₂ = w₀Lv (st 2)

x₁ : Wd (G₂ (inj₂ (jx fω)))
x₁ zero = tt , hs hz
x₁ (suc n) = w₀Lv (g₂ (jx fω)) (suc n)

-- 基世界在分量 inj₂ (jx f) 的第 0 个子分量的界是 0 (refl)
w₀₂-0 : ∀ f → proj₂ (w₀₂ (inj₂ (jx f)) 0) ≡ hz
w₀₂-0 f = refl

-- HB S⊥ 的构造子: 是不是 0 可判定; 1 不在 0 之下; 0 之下只有 0
is-hz : (h : HB S⊥) → (h ≡ hz) ⊎ ¬ (h ≡ hz)
is-hz hz = inj₁ refl
is-hz (hs _) = inj₂ (λ ())
is-hz (hl _) = inj₂ (λ ())
is-hz (hΩ () _)

no1 : ∀ {w : Wd S⊥} {h : HB S⊥} → h ≡ hz → ¬ (_⊲[_]_ {S⊥} (hs hz) w h)
no1 refl ()

⊲hz : ∀ {w : Wd S⊥} {h : HB S⊥} → _⊲[_]_ {S⊥} h w hz → h ≡ hz
⊲hz hself = refl

unj₂ : ⊤ ⊎ HB S⊥ → HB S⊥
unj₂ (inj₂ c) = c
unj₂ (inj₁ _) = hz

t≢f : ¬ (true ≡ false)
t≢f ()

nnF : ∀ α → ¬ ¬ (jx (fα α) ≡ jx fω) → ∀ n → α n ≡ false
nnF α nn n with α n in eq
... | false = refl
... | true = ⊥-elim (nn (λ e → t≢f (trans (sym eq) (eq→F α e n))))

module _ (P : PtUpd₂) where
  w′ : W₂
  w′ = updD P w₀₂ (inj₂ (jx fω)) x₁

  -- 分量 inj₂ (jx f) 的第 0 个子分量在升后世界里的界
  obs : (ℕ → HB S⊥) → HB S⊥
  obs f = proj₂ (w′ (inj₂ (jx f)) 0)

  Pω : (ℕ → HB S⊥) → Set
  Pω f = _⊲[_]_ {S⊥} (hs hz) tt (obs f)

  -- 由 "升": 分量 jx fω 处的界含 1
  bdω : Pω fω
  bdω = raise P w₀₂ (inj₂ (jx fω)) x₁ (κ₀ fω) (hs hz) hself

  updD₂-sep : Sep₂
  updD₂-sep α with is-hz (obs (fα α))
  ... | inj₁ z = inj₂ (λ e → no1 z (subst Pω (sym (jx-inj e)) bdω))
  ... | inj₂ nz = inj₁ (nnF α (λ ne → nz (⊲hz
        (keep P w₀₂ (inj₂ (jx fω)) x₁ (inj₂ (jx (fα α))) (λ e → ne (cong unj₂ e)) (κ₀ (fα α)) (obs (fα α)) hself))))

-- 模块参数提出来就是定理的陈述
updD₂-sep′ : PtUpd₂ → Sep₂
updD₂-sep′ = updD₂-sep
```

## §4 两半

"留" 单独可满足 (世界不动). "升" 单独的一致形式写不出类型 (文件头, 判断). 对照: 站的下标 ℕ 上两半同时成立 (`Fab2SLs.setH-top`, `setH-keep`).

```agda
half-keep : ∀ (w : W₂) (i : ⊤ ⊎ HB S⊥) (x : Wd (G₂ i)) k → ¬ (k ≡ i) → ∀ (κ : K (G₂ k)) c → Bd L₂ (k , κ) c w → Bd L₂ (k , κ) c w
half-keep w i x k ne κ c b = b
```

## 结论 (按档)

- **[定理]** `st2-form`, `L₂-form`, `sub0-form`, `bd0-form`, `w₀₂-0` (`refl`); `jx-inj`, `eq→F`, `nnF`; **`updD₂-sep : PtUpd₂ → Sep₂`** (点更新 ⇒ 分离子, 无条件, 不用外延); `half-keep`.
- **[判断]** "升" 的一致形式在 `L₂` 上写不出类型 (分量类型随坐标变); `Sep₂` 经典成立, 在 Agda 里证不出也否证不了 (与 `NegGenFoldUpd.Sep` 同档). 路线状态: 本篇没有关闭任何路线; 它把 C6 钉在级里的坐标下标上.
