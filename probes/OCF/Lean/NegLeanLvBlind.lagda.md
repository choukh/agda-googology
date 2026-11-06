# 头按自己的级读回, 否定一路 (三): 接口 `LeanLvIf` 的盲区与边界

> 不含记号. 入口 [NegLeanLv](NegLeanLv.lagda.md). 对着接口 [LeanLvIf](LeanLvIf.lagda.md) ("接口定稿 2026-11-05 22:11 (首次编译通过)", 变更记录: 无) 写, 导入它, 不另造接口. 另导入 [NegLeanLvPre](NegLeanLvPre.lagda.md) 与 `NegLeanFbBlind.rdConst`. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **结果.**
>
> 1. **盲 (§1).** **`simConst`** (定理, 对一切 $T,\Lambda,Q$): `LvSim T Λ Q` 有一个实例, 读回是 `rdConst` (常数 $1$, 不看数据), 级层 $0$, 同形 `sz`, 嵌入是空结构 `S⊥` 进 $Q$ (`emb⊥`). 所以 "有 `LvSim`" 不说明读回沿同形读, 也不说明读出任何种类. **`sim-any-k`** (定理): 层 `hΩ κ (λ _ → 0)` 与**一切**首项为任意 $k$ 的 `lΩ k (λ _ → lz)` 同形 (`cv` 取常值 $0$): `Sim` 不决定层号的首项, 所以 "$x$ 是这个种类的坐标的层号" 要单独验证.
> 2. **边界 (§2).**
>    - **正面 (定理)** `sim0`, `sim1`, **`sim2`**: $0\sim$ `st 0`, $S_0\sim$ `st 1`, $S_1\sim$ `st 2` (`cv` 是恒等). 头 $0,1,2$ 的自己的级层有 `Sim` 证据.
>    - **否定 (定理)** **`no-sim`**: 对一切 $n$, 一切在基世界里是 $\Lambda_F$ 第一位置的层 $\ell$: `¬ Sim SLs ℓ (st (3 + n))`, 对**任意**坐标映射 `cv`. 推论 **`no-own-sim`**: 接口 `LvSim SLs ΛF Q` 的任一实例, 层号 `x` 不是 `st (3 + n)`. 按接口头的定义 ("按自己的级 指 $x$ 就是这个种类的坐标的层号"), **头 $n\ge3$ 在 $\Lambda_F$ 里不能按自己的级读回**. 这比 `NegLeanLvPre.no-own` (只对规范读法 `ofL`) 强: `Sim` 允许任意 `cv`.
>    - 证据: 级层只能是 $0$, $S_m$, $\Lambda_F$ (`lvl-cases`). `st (3+n) = lΩ lz g`, 而 $g$ 的每个值都不是后继层号 (`g-not-ls`: $g\,c$ = `ofHB (Ω̂ⁿ⁺¹ (1 ⊞ c))`, $\hat\Omega$ 作用在非零高度上只给出极限). $S_{m+1}$ 在坐标 $1$ 处的分支是 $\mathrm{hs}\,S_m$ (定义相等), 与 $g$ 的任一值都不同形.
>
> **只否定什么.** `no-sim` 只否定: 级层在 $\Lambda_F$ 的基世界第一位置里, 且与 `st (3+n)` 有 `Sim`. **不否定**: 改 $\Lambda$ (加层); 级层是 $S_1$ 而层号是 `st 2`, 再经嵌入 `Emb (Lv (st 2)) (Lv (st n))` 放进头 $n$ 的坐标 (构造一路的计划; 它按接口的定义不是 "自己的级", 但接口允许); 头 $0,1,2$. 本篇没有关闭任何路线.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegLeanLvBlind where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Lean.LeanTBase
open import OCF.Lean.LeanTLv
open import OCF.Lean.LeanFbIf
open import OCF.Lean.LeanFbSt renaming (st to stL)
open import OCF.Lean.LeanLvIf
open import OCF.Lean.NegLeanFbBlind using (rdConst)
open import OCF.Lean.NegLeanLvPre using (L₀; Sg; lvl-cases; tw-shape; st-shape; Tg; tag; tz; ts; tl; tΩ)
```

## §1 盲

**空结构的嵌入.** `S⊥` 没有种类; 它嵌进任一 $Q$.

```agda
module _ {Q : KS} where
  j⊥ : K S⊥ → K Q
  j⊥ (() , _)

  cv⊥ : ∀ {κ : K S⊥} → E Q (j⊥ κ) → E S⊥ κ
  cv⊥ {κ = () , _} _

  vc⊥ : ∀ {κ : K S⊥} → E S⊥ κ → E Q (j⊥ κ)
  vc⊥ {κ = () , _} _

  cv-vc⊥ : ∀ {κ : K S⊥} (c : E S⊥ κ) → cv⊥ {κ} (vc⊥ c) ≡ c
  cv-vc⊥ {κ = () , _} _

  bd→⊥ : ∀ {κ : K S⊥} {e w} → Bd Q (j⊥ κ) e w → Bd S⊥ κ (cv⊥ e) (λ ())
  bd→⊥ {κ = () , _} _

  bd←⊥ : ∀ {κ : K S⊥} {c w} → Bd S⊥ κ c (λ ()) → Bd Q (j⊥ κ) (vc⊥ c) w
  bd←⊥ {κ = () , _} _

  pr→⊥ : ∀ {κ : K S⊥} {e e′ w} → Pr Q (j⊥ κ) w e e′ → Pr S⊥ κ (λ ()) (cv⊥ e) (cv⊥ e′)
  pr→⊥ {κ = () , _} _

  emb⊥ : Emb S⊥ Q
  emb⊥ = record { j = j⊥ ; cv = cv⊥ ; vc = vc⊥ ; cv-vc = cv-vc⊥ ; π = λ _ () ; lgπ = λ _ ()
                ; bd→ = bd→⊥ ; bd← = bd←⊥ ; pr→ = pr→⊥ }

simConst : ∀ (T : KS) (Λ : HB (step T)) (Q : KS) → LvSim T Λ Q
simConst T Λ Q = record { R = rdConst T Λ Q ; x = lz ; σ = sz ; em = emb⊥ }

-- 读回不看数据
simConst-blind : ∀ T Λ Q {W} (lW : LgW (step T) W) x y →
  LvRd.δ (LvSim.R (simConst T Λ Q)) lW x ≡ LvRd.δ (LvSim.R (simConst T Λ Q)) lW y
simConst-blind T Λ Q lW x y = refl
```

**`Sim` 不决定首项.**

```agda
sim-any-k : ∀ (T : KS) (κ : K (step T)) (k : LH) → Sim T (hΩ κ (λ _ → hz)) (lΩ k (λ _ → lz))
sim-any-k T κ k = sΩ (λ _ → hz) (λ _ → sz)
```

## §2 边界: 头 $0,1,2$ 有, 头 $n\ge3$ 在 $\Lambda_F$ 里没有

```agda
sim0 : Sim SLs hz (stL 0)
sim0 = sz

sim1 : Sim SLs (Sg 0) (stL 1)
sim1 = ss sz

sim2-br : ∀ (c : HB S⊥) → Sim SLs (up (hs hz ⊞ (hz ⊞ ιS 0 (up c)))) (ofHB (hs hz ⊞ ι {LH} {FL} lz (up c)))
sim2-br hz = ss sz
sim2-br (hs c) = ss (sim2-br c)
sim2-br (hl f) = sl (λ n → sim2-br (f n))
sim2-br (hΩ (() , _) g)

sim2 : Sim SLs (Sg 1) (stL 2)
sim2 = sΩ (λ e → e) sim2-br
```

**`st (3+n)` 的分支都不是后继.** `NZ y`: $y\ne0$ (构造子); `LO y`: $y$ 是 $\mathbb N$-极限或 $\Omega$-极限. $\hat\Omega$ 把非零高度送到极限.

```agda
data NZ : HB SL → Set where
  nzs : ∀ {h} → NZ (hs h)
  nzl : ∀ {f} → NZ (hl f)
  nzΩ : ∀ {κ g} → NZ (hΩ κ g)

data LO : HB SL → Set where
  lol : ∀ {f} → LO (hl f)
  loΩ : ∀ {κ g} → LO (hΩ κ g)

Ω̂-LO : ∀ {y} → NZ y → LO (Ω̂ y)
Ω̂-LO nzs = loΩ
Ω̂-LO nzl = lol
Ω̂-LO nzΩ = loΩ

LO→NZ : ∀ {y} → LO y → NZ y
LO→NZ lol = nzl
LO→NZ loΩ = nzΩ

h₀-NZ : ∀ (c : HB S⊥) → NZ (hs hz ⊞ ι {LH} {FL} lz (up c))
h₀-NZ hz = nzs
h₀-NZ (hs c) = nzs
h₀-NZ (hl f) = nzl
h₀-NZ (hΩ (() , _) g)

hn-NZ : ∀ n c → NZ (proj₁ (tw-shape n) c)
hn-NZ zero c = h₀-NZ c
hn-NZ (suc n) c = LO→NZ (Ω̂-LO (hn-NZ n c))

node-tag : ∀ k κ h → tag (node k κ h) ≡ tΩ
node-tag lz (() , _) h
node-tag (ls x) (inj₁ κ) h = node-tag x κ h
node-tag (ls x) (inj₂ _) h = refl
node-tag (ll f) (n , κ) h = node-tag (f n) κ h
node-tag (lΩ k g) (inj₁ _ , inj₁ κ) h = node-tag k κ h
node-tag (lΩ k g) (inj₁ _ , inj₂ _) h = refl
node-tag (lΩ k g) (inj₂ c , κ) h = node-tag (g c) κ h

LO-tag : ∀ {y} → LO y → ¬ (tag (ofHB y) ≡ ts)
LO-tag lol ()
LO-tag (loΩ {κ = k , inj₂ _}) ()
LO-tag (loΩ {κ = k , inj₁ κ} {g}) e with trans (sym (node-tag k κ (λ c → ofHB (g c)))) e
... | ()

g-not-ls : ∀ n c → ¬ (tag (proj₁ (st-shape (suc n)) c) ≡ ts)
g-not-ls n c = LO-tag (Ω̂-LO (hn-NZ n c))
```

**`no-sim`.**

```agda
simΩ⁻ : ∀ {T κ h k g} → Sim T (hΩ κ h) (lΩ k g) → Σ (E (step T) κ → HB (Lv k)) (λ cv → ∀ e → Sim T (h e) (g (cv e)))
simΩ⁻ (sΩ cv σg) = cv , σg

sim-hs : ∀ {T a y} → Sim T (hs a) y → tag y ≡ ts
sim-hs (ss σ) = refl

G3 : ℕ → HB (Lv lz) → LH
G3 n = proj₁ (st-shape (suc n))

no-simΩ : ∀ n {ℓ} → ℓ ⊲[ w₀ L₀ ] ΛF → ¬ Sim SLs ℓ (lΩ lz (G3 n))
no-simΩ n p σ with lvl-cases p
no-simΩ n p () | inj₁ refl
no-simΩ n p () | inj₂ (inj₁ refl)
no-simΩ n p () | inj₂ (inj₂ (zero , refl))
no-simΩ n p σ | inj₂ (inj₂ (suc m , refl)) with simΩ⁻ σ
... | cv , σg = g-not-ls n (cv (hs hz)) (sim-hs (σg (hs hz)))

no-sim : ∀ n {ℓ} → ℓ ⊲[ w₀ L₀ ] ΛF → ¬ Sim SLs ℓ (stL (suc (suc (suc n))))
no-sim n p σ = no-simΩ n p (subst (Sim SLs _) (proj₁ (proj₂ (st-shape (suc n)))) σ)

no-own-sim : ∀ n {Q} (L : LvSim SLs ΛF Q) → ¬ (LvSim.x L ≡ stL (suc (suc (suc n))))
no-own-sim n L e = no-sim n (LvRd.ℓ⊲ (LvSim.R L) {w₀ L₀}) (subst (Sim SLs _) e (LvSim.σ L))
```

**前提实例.** `no-own-sim` 的前提是任一 `LvSim SLs ΛF Q`: `simConst SLs ΛF Q` (对一切 $Q$). `no-sim` 的 $\ell$: `lvl-inst` (一切 $S_m$), `hz`, `ΛF`.

```agda
no-own-sim-inst : ∀ n → ¬ (LvSim.x (simConst SLs ΛF (Lv (stL (suc (suc (suc n)))))) ≡ stL (suc (suc (suc n))))
no-own-sim-inst n = no-own-sim n (simConst SLs ΛF _)
```

## §3 结论 (按档)

- **[定理, 盲]** **`simConst`**, `simConst-blind` (对一切 $T,\Lambda,Q$: `LvSim` 有不看数据的实例); `emb⊥`; **`sim-any-k`** (`Sim` 不决定层号首项).
- **[定理, 正面]** `sim0`, `sim1`, **`sim2`** (`cv` 恒等).
- **[定理, 否定]** **`no-sim`**, `no-simΩ`, **`no-own-sim`**: 头 $3+n$ 在 $\Lambda_F$ 里没有与自己的层号同形的级层 (任意 `cv`). 引理 `g-not-ls`, `node-tag`, `Ω̂-LO`.
- **[判断]** 头 $n\ge3$ 若要按接口的定义 "按自己的级" 读回, 只能改 $\Lambda$ (加与 `st n` 同形的层); 由 `NegLeanLvPre.st3-branch`, `no-station-at`, 这样的层在对应 `ls (ls lz)` 的位置要用站里的拷贝种类作头. 未研究.
