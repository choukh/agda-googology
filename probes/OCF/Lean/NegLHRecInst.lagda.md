# 底对 LH 递归, 否定一路 (三): 对构造一路实例与对象的检查

> 不含记号. 入口 [NegLHRec](NegLHRec.lagda.md). 只读导入构造一路的 [LHRecTy](LHRecTy.lagda.md), [LHRecIf](LHRecIf.lagda.md), [LHRecLeg](LHRecLeg.lagda.md), [LHRecLay](LHRecLay.lagda.md), [LHRecFl](LHRecFl.lagda.md), [LHRec](LHRec.lagda.md) (08:20 到 08:30 的版本), 与否定一路的 [NegRecBPre](NegRecBPre.lagda.md), [NegLHRecIf](NegLHRecIf.lagda.md) (都不改). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **构造一路交了什么.** 实例 `J₁` (Kripke 式可入, 回灌 $B\boxplus$ `leg k c`), 一切层号的合法化 `leg`, 一切层号的地板 `flL` 与 `Lg-flL`, 层号算术 `ΩL`, `twL`, `ΛL`, $\Lambda$ 层的地板 `flΛ`. **没有折叠, 没有 `Cd` 上的闭项, 没有 FGH** (构造一路自述; 本路读文件确认: 六个 `LHRec*` 文件里 `Cd` 不出现, `S⊥` 只出现在 `Lv lz = S⊥`. 这是读文件, 不是定理).
>
> **结果.**
>
> 1. **实例 (定理).** `nb-J₁`: `J₁` 进入后的界是 $e+1$ (refl), 所以 `NegLHRecIf.fb-must-legalize` 适用于它, 结论与 `Lg-leg` 一致 (`J₁-legal-fb`). **`J₁-sh-dep`**: `J₁` 的回灌依赖坐标 (第 $0$ 层, 坐标 $0$ 与 $1$ 的回灌不同), 不是盲实例 `kripkeC`. 
> 2. **$\Lambda$ 层的地板 (形状与否定).** `flΛ-shape`: `flΛ` 字面是部分和的极限 `hl (ΣF twL)`. **`Λ-naive-flL`**: 不累加的版本 ($\lim_n\iota_{n+1}\,$`flL (twL (n+1))`) 不合法 (`NegRecBPre.sup-diag-illegal`). 所以 `flL (ll f)` 的部分和是合法性逼出的, 不是选择. `fl-lΩ-succ`: `flL (lΩ k g)` 的分支在后继 $d+1$ 处字面是分支 $d$ 加上 $\iota_d$ `flL (g d)`. `tw2`, `tw3`: 层号 `twL 2`, `twL 3` 的字面形状.
> 3. **两难 (a), 分量世界独立 (构造一路 §4 第 1 条).** **`dilemma-a`**: 在层号 $X=$ `lΩ lz (λ _ → ls lz)` (每个分量都是第 $1$ 层) 的合法世界 `Wx` 里, 分量 $0\lhd1$; 同一对值 $(1,\Omega)$ 在分量 $0$ 里有 $1\lhd\Omega$, 搬进分量 $1$ 后没有; 两个分量的世界不相容 (`no-compat`). `Lv (lΩ k g)` 的世界是 `sup` 的 Π, 合法性不要求分量世界相容. 正面 **`compat-transport`**: 分量层号相同时, 若分量 $c$ 的世界不大于分量 $c'$ 的世界, 第一位置搬得过去; 相容条件可满足 (`compat-w₀`). **`no-kind-emb`**: `LH` 不要求 $g$ 沿第一位置单调; 对 $g\,0=1$, $g\,1=0$, 第 $g\,0$ 层的种类没有到第 $g\,1$ 层的映射. **`flL-blind`**: 这个层号的地板仍合法 (地板证书不检查层号).
> 4. **两难 (b), 按指标层共享世界 (构造一路 §4 第 2 条).** 路径谓词 `PHs`: 同一个界管指标种类 (按 `J₁` 的可入移动) 与分量种类 (证据 $c+1\lhd B$). **`shared-keep-fails`**: "留下指标结点, 坐标 $c'$ 的分支取输入在回灌坐标 `sh J₁ lz (tt,B) c′` 处的分支" (`keepFb`, RecB `ΦX` 留指标结点时的形状) 不保 `PHs`: 输入在界 $1$ 里带路径 (`in-ok`), 输出在坐标 $1$ 处进入界 $2$, 那一支是输入在回灌坐标 $1\boxplus$ `leg 1` $=2$ 处的分支, 它的分量种类要 $3\lhd2$ (`out-fails`). 这是 `NegRecBInst.ΦX↓M-fails` 在 `LHRec` 对象上的版本.
> 5. **合法化与地板 (构造一路的陈述).** `Lg-leg`, `Lg-flL` 是标准 `LgB`, 对一切输入 / 一切层号. **`leg-not-id`**: `leg` 改变合法的输入 (第 $1$ 层的 $\Omega$ 在坐标 $2$ 处的分支变成 $3$, θ 累加); **`leg-node`**: `leg` 留下每个结点的种类 (不塌缩). **`fl-coord-node`**: `flL (lΩ (ls lz) g)` 在 $\Omega$-坐标处的分支是指标分量旧种类的结点. 累加的位置: `leg` 的 ℕ-极限 (部分和) 与 $\Omega$-结点 (θ); `flL` 的指标分支 (θ) 与 `ll` 层 (部分和, 由 `Λ-naive-flL` 逼出).
> 6. **证书.** `Lg-flΛ` 的类型就是 `CRwBase.LgB` (标准); 但它是第 $\Lambda$ 层的值的证书, 不是闭项的证书 (没有闭项).
>
> **前提实例.** 2: 世界 `wΛ` (每层取 `w₀L`). 3: `lg-Wx` (世界合法), `compat-w₀` (相容条件可满足); `Lg-flL` 给出 `flL-blind`. 4: `in-ok` (输入带路径), 可入的证据 `(tt , tt , tt , hself , tt)` 写在 `out-fails` 里. 5: `Lg-flL (ls lz)` (输入合法).
>
> **只否定什么.** 2 只否定不累加的 $\Lambda$ 地板; 不否定 `flΛ`. 3 只否定: `sup` 的合法世界下跨分量搬运保给定世界里的第一位置; 一般 `LH` 层号沿分量下标有种类嵌入. **不否定**带相容条件的世界 (`compat-transport` 是正面), 也不否定在单调的 $g$ (如 `ΩL` 产生的层号) 上写嵌入. 4 只否定: 共享一个界 (指标种类移动它, 分量种类读它) 时, 留下指标结点并按 `J₁` 回灌的形状保路径. **不否定**构造一路 §4 的下一步设计 (留下的内层指标改成另一层世界里的底种类, RecB 的 `lift`/`triv` 的推广), 也不否定别的回灌. 5 不否定任何东西 (`leg-not-id` 只说基本列被改). 两难 (a), (b) 合起来**不是**穷尽: "世界只能按分量分开或按指标层共享" 是判断, 构造一路 §4 的设计就是第三种组织. 本篇没有关闭任何路线; 构造一路的折叠是 "未找到", 不是 "不存在".

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegLHRecInst where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecIf
open import OCF.Lean.LHRecLeg using (J₁; leg; Lg-leg; w₀L; lw₀L; rfL; θK; module New) renaming (here to hereC)
open import OCF.Lean.LHRecLay using (twL; ΛL; ΩL; upL; _⊕L_)
open import OCF.Lean.LHRecFl using (flL; ΣF; Lg-flL; ι-⊲; gcF; cxI)
open import OCF.Lean.LHRec using (flΛ; Lg-flΛ)
open import OCF.Lean.NegRecBPre using (Ωˢ; one; module Top; here; sup-diag-illegal; hz-only)
open import OCF.Lean.NegLHRecIf using (fb-must-legalize)
open LHRecIf
```

## §1 实例 `J₁`

```agda
nb-J₁ : ∀ k W e a → proj₂ (nxt J₁ k W e a) ≡ hs e
nb-J₁ k W e a = refl

J₁-legal-fb : ∀ k {W} → LgWL k W → ∀ c → LgB (sh J₁ k W c)
J₁-legal-fb k = fb-must-legalize J₁ k (nb-J₁ k)

noZ≡S : ¬ (hz {S⊥} ≡ hs hz)
noZ≡S ()

J₁-sh-dep : ¬ (sh J₁ lz (tt , hz) hz ≡ sh J₁ lz (tt , hz) (hs hz))
J₁-sh-dep = noZ≡S
```

## §2 $\Lambda$ 层的地板

```agda
FΛ : ℕ → KS
FΛ n = Lv (twL n)

flΛ-shape : flΛ ≡ hl (ΣF twL)
flΛ-shape = refl

wΛ : Wd (Lv ΛL)
wΛ n = w₀L (twL n)

one≢two : ¬ (1 ≡ 2)
one≢two ()

-- 不累加: 第 n 项是第 n+1 个分量的地板
Λ-naive-flL : ¬ LgB {Lv ΛL} (hl (λ n → ι {ℕ} {FΛ} (suc n) (flL (twL (suc n)))))
Λ-naive-flL = sup-diag-illegal {ℕ} {FΛ} suc (λ n → flL (twL (suc n))) wΛ here one≢two

-- 对照: 累加的地板合法
Λ-acc-flL : LgB flΛ
Λ-acc-flL = Lg-flΛ

fl-lΩ-succ : ∀ k g d →
  New.θ (cxI k g) (gcF (λ d → ι {IxL k} {FXL k g} (inj₂ d) (flL (g d)))) (hs d) ≡
  New.θ (cxI k g) (gcF (λ d → ι {IxL k} {FXL k g} (inj₂ d) (flL (g d)))) d ⊞ ι {IxL k} {FXL k g} (inj₂ d) (flL (g d))
fl-lΩ-succ k g d = refl

tw2 : twL 2 ≡ lΩ lz (λ c → ls lz ⊕L upL lz c)
tw2 = refl

tw3 : twL 3 ≡ lΩ lz (λ c → ΩL (ls lz ⊕L upL lz c))
tw3 = refl
```

## §3 两难 (a): 分量世界独立, 跨分量搬运要相容条件

层号 $X$: 指标层是第 $0$ 层, 每个分量都是第 $1$ 层 (`step S⊥`). 世界 `Wx`: 分量 $0$ 的界是 $1$, 其余分量的界是 $0$; 合法. 分量 $0\lhd 1$ (且 $0+1\lhd1$): 把分量 $0$ 里的值搬进分量 $1$.

```agda
gX : Cd → LH
gX _ = ls lz

X : LH
X = lΩ lz gX

wc : Cd → Cd
wc hz = hs hz
wc _ = hz

lg-wc : ∀ c → LgB (wc c)
lg-wc hz = tt
lg-wc (hs c) = tt
lg-wc (hl f) = tt
lg-wc (hΩ () _)

Wx : Wd (Lv X)
Wx (inj₁ _) = tt , hz
Wx (inj₂ c) = tt , wc c

lg-Wx : LgW (Lv X) Wx
lg-Wx (inj₁ _) = tt , tt
lg-Wx (inj₂ c) = tt , lg-wc c

ιX : (i : IxL lz) → HB (FXL lz gX i) → HB (Lv X)
ιX = ι {IxL lz} {FXL lz gX}

noS : ¬ (hs {Lv X} hz ⊲[ Wx ] hz)
noS ()

c₀ c₁ : Cd
c₀ = hz
c₁ = hs hz

in-c0 : ιX (inj₂ c₀) (one {step S⊥}) ⊲[ Wx ] ιX (inj₂ c₀) (Ωˢ {S⊥})
in-c0 = ι-⊲ {IxL lz} {FXL lz gX} {i = inj₂ c₀} (Top.in-top1 {S⊥} tt)

not-c1 : ¬ (ιX (inj₂ c₁) (one {step S⊥}) ⊲[ Wx ] ιX (inj₂ c₁) (Ωˢ {S⊥}))
not-c1 (hLim {c = d} b p) = noS (subst (λ (z : Cd) → hs {Lv X} hz ⊲[ Wx ] ιX (inj₂ c₁) (up {S⊥} z)) (hz-only {S⊥} b) p)

no-compat : ¬ (_≤w_ (step S⊥) (Wx (inj₂ c₀)) (Wx (inj₂ c₁)))
no-compat (_ , ())

dilemma-a : LgW (Lv X) Wx × (hs c₀ ⊲ c₁) ×
  (one {step S⊥} ⊲[ Wx (inj₂ c₀) ] Ωˢ {S⊥}) ×
  (ιX (inj₂ c₀) (one {step S⊥}) ⊲[ Wx ] ιX (inj₂ c₀) (Ωˢ {S⊥})) ×
  ¬ (ιX (inj₂ c₁) (one {step S⊥}) ⊲[ Wx ] ιX (inj₂ c₁) (Ωˢ {S⊥})) ×
  ¬ (_≤w_ (step S⊥) (Wx (inj₂ c₀)) (Wx (inj₂ c₁)))
dilemma-a = lg-Wx , hself , Top.in-top1 {S⊥} tt , in-c0 , not-c1 , no-compat

-- 旧名 (同一事实)
cross-comp-world : LgW (Lv X) Wx ×
  (ιX (inj₂ c₀) (one {step S⊥}) ⊲[ Wx ] ιX (inj₂ c₀) (Ωˢ {S⊥})) ×
  ¬ (ιX (inj₂ c₁) (one {step S⊥}) ⊲[ Wx ] ιX (inj₂ c₁) (Ωˢ {S⊥}))
cross-comp-world = lg-Wx , in-c0 , not-c1
```

**正面: 带相容条件就能搬.** 分量层号相同 ($g$ 是常值 $y$) 时, 若分量 $c$ 的世界不大于分量 $c_0$ 的世界, 分量 $c$ 里的第一位置搬进分量 $c_0$. 相容条件可满足: 每层的合法世界 `w₀L` 满足它 (`compat-w₀`).

```agda
compat-transport : ∀ y k (W : Wd (Lv (lΩ k (λ _ → y)))) c c′ {a b : HB (Lv y)} →
  _≤w_ (Lv y) (W (inj₂ c)) (W (inj₂ c′)) → a ⊲[ W (inj₂ c) ] b →
  ι {IxL k} {FXL k (λ _ → y)} (inj₂ c′) a ⊲[ W ] ι {IxL k} {FXL k (λ _ → y)} (inj₂ c′) b
compat-transport y k W c c′ q p = ι-⊲ {IxL k} {FXL k (λ _ → y)} {i = inj₂ c′} (⊲ᴮ↑ q p)

compat-w₀ : ∀ y k c c′ → _≤w_ (Lv y) (w₀L (lΩ k (λ _ → y)) (inj₂ c)) (w₀L (lΩ k (λ _ → y)) (inj₂ c′))
compat-w₀ y k c c′ = rfL y (w₀L y)
```

**层号不单调.** $g\,0=1$, 其余 $0$.

```agda
gbad : Cd → LH
gbad hz = ls lz
gbad _ = lz

no-kind-emb : (hs hz ⊲ hs hz) × ¬ (K (Lv (gbad hz)) → K (Lv (gbad (hs hz))))
no-kind-emb = hself , λ f → f (inj₂ tt)

flL-blind : LgB (flL (lΩ lz gbad))
flL-blind = Lg-flL (lΩ lz gbad)
```

## §4 两难 (b): 按指标层共享世界, 留下的指标结点带回灌, 路径断

"共享" 写成路径谓词 `PHs B`: 同一个界 $B$ (第 $0$ 层的值) 既管指标种类 (证据 $1\lhd B$; 按 `J₁` 的可入进入坐标 $e$ 后, 界换成 `J₁` 的新界 $e+1$), 也管第 $c$ 个分量的种类 (证据 $c+1\lhd B$, 不移动). 这是构造一路 §4 第 2 条与 `NegRecBInst.liftM` 的情形, 写在 `LHRec` 的对象 (`Lv X`, `J₁`) 上. `keepFb B h`: 指标结点留下, 输出在坐标 $c'$ 处的分支是输入在回灌坐标 `sh J₁ lz (tt, B) c′` 处的分支 (RecB `ΦX` 留下指标结点时的形状).

```agda
PHs : Cd → HB (Lv X) → Set
PHs B hz = ⊤
PHs B (hs h) = PHs B h
PHs B (hl f) = ∀ n → PHs B (f n)
PHs B (hΩ (inj₁ _ , inj₁ ()) h)
PHs B (hΩ (inj₁ _ , inj₂ _) h) =
  (hs hz ⊲ B) × (∀ e (a : Adm J₁ lz (tt , B) e) → PHs (proj₂ (nxt J₁ lz (tt , B) e a)) (h e))
PHs B (hΩ (inj₂ c , κ) h) = (hs c ⊲ B) × (∀ e → PHs B (h e))

ixX : K (Lv X)
ixX = inj₁ tt , inj₂ tt

keepFb : Cd → (Cd → HB (Lv X)) → HB (Lv X)
keepFb B h = hΩ ixX (λ c′ → h (sh J₁ lz (tt , B) c′))

-- 输入: 指标结点, 坐标 e 处是第 e 个分量的 Ω
hIn : Cd → HB (Lv X)
hIn e = ιX (inj₂ e) (Ωˢ {S⊥})

PH-upX : ∀ B e (d : Cd) → PHs B (ιX (inj₂ e) (up {S⊥} d))
PH-upX B e hz = tt
PH-upX B e (hs d) = PH-upX B e d
PH-upX B e (hl f) = λ n → PH-upX B e (f n)
PH-upX B e (hΩ () _)

in-ok : PHs (hs hz) (hΩ ixX hIn)
in-ok = hself , λ e a → hself , λ d → PH-upX (hs e) e d

no32 : ¬ (hs (hs (hs hz)) ⊲ hs (hs hz))
no32 (hsuc (hsuc ()))

-- 输出: 坐标 1 可入, 新界 2; 那一支是输入在回灌坐标 1 ⊞ leg 1 = 2 处的分支, 要 3 ⊲ 2
out-fails : ¬ PHs (hs hz) (keepFb (hs hz) hIn)
out-fails (_ , k) = no32 (proj₁ (k (hs hz) (tt , tt , tt , hself , tt)))

shared-keep-fails : ¬ (∀ B h → PHs B (hΩ ixX h) → PHs B (keepFb B h))
shared-keep-fails all = out-fails (all (hs hz) hIn in-ok)
```

## §5 合法化与地板: 陈述, 累加的位置, 是否塌缩

`Lg-leg x a : LgB (leg x a)` 对一切 $a$ (含不合法的) 成立, `Lg-flL x : LgB (flL x)` 对一切层号成立; 两者都是标准 `CRwBase.LgB` (读类型). **`leg` 改变合法的输入** (`leg-not-id`): 第 $1$ 层的 $\Omega$ (`flL (ls lz)`, 合法) 经 `leg` 后, 坐标 $2$ 处的分支是 $3$ 而不是 $2$ (θ 累加 $0\boxplus1\boxplus2$). 所以回灌 $B\boxplus$ `leg c` 对合法的坐标也改了基本列 (毛刺, 同 CRw 的 `leg`); 读值是否不变没有定理. **`leg-node`**: `leg` 留下每个 $\Omega$-结点的种类, 只改分支 (不塌缩). **`fl-coord-node`**: `flL (lΩ (ls lz) g)` 在 $\Omega$-结点坐标处的分支是指标分量的**旧种类** `(inj₁ tt , inj₁ (inj₂ tt))` 的结点 (不是底种类, 也不坍缩成极限).

```agda
brch : HB (step S⊥) → HB (step S⊥)
brch (hΩ (inj₁ ()) f)
brch (hΩ (inj₂ _) f) = f (hs (hs hz))
brch _ = hz

no3≡2 : ¬ (hs {step S⊥} (hs (hs hz)) ≡ hs (hs hz))
no3≡2 ()

leg-not-id : LgB (flL (ls lz)) × ¬ (leg (ls lz) (flL (ls lz)) ≡ flL (ls lz))
leg-not-id = Lg-flL (ls lz) , λ eq → no3≡2 (cong brch eq)

leg-node : ∀ x κ (h : E (Lv x) κ → HB (Lv x)) →
  leg x (hΩ κ h) ≡ hΩ κ (θK x hereC κ (λ e → leg x (h e)))
leg-node x κ h = refl

fl-coord-node : ∀ (g : HB (step S⊥) → LH) (h : Cd → HB (step S⊥)) →
  New.θ (cxI (ls lz) g) (gcF (λ d → ι {IxL (ls lz)} {FXL (ls lz) g} (inj₂ d) (flL (g d)))) (hΩ (inj₂ tt) h) ≡
  hΩ (inj₁ tt , inj₁ (inj₂ tt))
    (λ e → New.θ (cxI (ls lz) g) (gcF (λ d → ι {IxL (ls lz)} {FXL (ls lz) g} (inj₂ d) (flL (g d)))) (h e))
fl-coord-node g h = refl
```

## 结论 (按档)

- **[定理, 正面]** `nb-J₁`, `J₁-legal-fb`; `Λ-acc-flL`; `compat-transport`, `compat-w₀`; `flL-blind`; `in-ok`.
- **[定理, 形状]** `flΛ-shape`, `fl-lΩ-succ`, `tw2`, `tw3`, `leg-node`, `fl-coord-node`.
- **[定理, 否定]** `J₁-sh-dep` (实例不是盲的); **`Λ-naive-flL`**; **`dilemma-a`** (`cross-comp-world`, `no-compat`), **`no-kind-emb`**; **`shared-keep-fails`** (`out-fails`); `leg-not-id`.
- **[读文件]** 构造一路没有折叠, 没有 `Cd` 上的闭项, 没有 FGH. 所以 "是否真把 $\Lambda$ 层折下来": 没有; "决定是否正确": 没有决定可查; "证书是否标准": `Lg-leg`, `Lg-flL`, `Lg-flΛ` 是标准 `LgB`, 但不是闭项的证书.
- **[判断]** (a) 两难不是穷尽 (见上). (b) 构造一路 §4 的设计 (底对 $n$ 递归, 分量高度取上一个底的值, 世界对一切分量是同一个 $w$) 绕开 `dilemma-a` 的方式是让分量共享低层世界; 它是否绕开 `shared-keep-fails`, 取决于内层指标留下后在下层路径里是否平凡 (RecB 的 `no-lift` 对照), 未验证. (c) 读法 (`flΛ` 读 $\Lambda$) 没有定理.
