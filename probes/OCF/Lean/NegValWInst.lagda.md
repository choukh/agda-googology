# NegValW (二): 小实例上的两条否定 — 数据对世界不单调; 世界升高后结点的层与 `rkT` 的决定都变

> 不含记号. 入口 [NegValW](NegValW.lagda.md). 本篇**不依赖**构造一路的接口. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **实例.** `T₁ = step S⊥` (一个种类, 坐标 `HB S⊥`), 层的种类结构 `L₀ = step T₁`; 旧种类 `κo = inj₁ (inj₂ tt)` 的顶就是世界的 `T₁` 分量的界. 最高层 $\Lambda_1 = \mathrm{hΩ}\,\kappa_o\,G$, $G\,c = 1\boxplus c$ (经两次 `up` 嵌入). 折叠 `LeanTFold` 取一切旧种类有损. 两个世界 $W\le W'$: `T₁` 的界分别是 $0$ 与 $2$, 其余相同.
>
> - **`anti`** (定理): 同一份第 1 层数据 $x$ (一个 $\kappa_o$-闭包, 分支看世界的界), 同一个动作, 同一个状态, 在 $W$ 里折叠的第 0 层输出求和是 $\omega$, 在 $W'\ge W$ 里是 $0$ 的 $\omega$ 份; 前者**不** $\le$ 后者. 所以 "同一份数据在 $W\le W'$ 两个世界里跑, 右边的值 $\ge$ 左边" 对一切数据不成立: 模拟关系必须对数据加一个 "对世界单调" 的谓词, 并证 $\Omega_\Lambda$ 与输入改写 `Int` 保持它.
> - **`lvl-L`, `lvl-R`** (定理, `refl`): $\Omega_{\Lambda_1}$ 的闭包分支在 $W$ 里是过第 $G(0)=1$ 层的结点, 在 $W'$ 里是过第 $G(2)=3$ 层的结点. 回灌行 (`RKa`) 左边在 $W$ 里、右边在升高的世界里取同一个分支, 所以两边的结点**不在同一层**.
> - **`rk-split`** (定理, `refl`): 目标层 $t=G(1)=2$, 同一个目标世界 $W'$, 结点 `RunNi` 的决定 (`rkT`): 左边 (层 1) 是 `keep` (输出 `ni` 结点), 右边 (层 3) 是 `rise` (输出 `nl` 链). 两边输出的构造子不同.
>
> **只否定什么.** `anti` 只否定 "对一切数据" 的世界单调; 不说 $\Omega_\Lambda$ 一类数据不单调. `rk-split` 只否定 "两边输出逐构造子同形 (如 `ValNewRel.Mo` 的 `mi`)" 的关系能穿过回灌行之后的结点; 不否定把 `ni` 与 `nl` 相连的值关系, 也不否定层对第一位置单调的模拟.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegValWInst where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.LeanTBase
open import OCF.Lean.LeanTTree
import OCF.Lean.LeanTFold as Fold
import OCF.Lean.NegLeanLvVal as NV
```

## §1 实例

```agda
T₁ : KS
T₁ = step S⊥

open Tree T₁

bk₁ : BotK
bk₁ = record
  { aK = inj₂ tt ; frE = λ e → e
  ; frE-lg = λ lw e → lgB⊲ e (proj₁ lw) (proj₂ lw)
  ; frE-mono = λ _ _ _ p → ⊲ᴮ↑ (λ ()) p }

κo : K L₀
κo = inj₁ (inj₂ tt)

emb : HB S⊥ → HB L₀
emb c = up (up c)

G : HB S⊥ → HB L₀
G c = hs hz ⊞ emb c

Λ₁ : HB L₀
Λ₁ = hΩ κo G

lΛ₁ : LgB Λ₁
lΛ₁ = (λ lw e e′ p → ⊞-⊲ (hs hz) (up-⊲ (up-⊲ p))) ,
      (λ {w} {c} lw e → Lg-⊞ (hs hz) (emb c) tt (Lg-up (up c) (Lg-up c (lgB⊲ e (proj₁ (proj₁ lw)) (proj₂ (proj₁ lw))))))

one₁ : ∀ {w} → hs hz ⊲[ w ] Λ₁
one₁ {w} = hLim {κ = κo} {c = hz} (botBd L₀ κo w) hself

open FoldTy T₁ Λ₁
open Fold T₁ bk₁ Λ₁ lΛ₁ one₁ (λ _ → inj₂ tt)
```

**世界.** `w⊥` 是 `S⊥` 的唯一世界 (一个名字, 不重复写 `λ ()`). `Wb β`: `T₁` 的界是 $\beta$, 新种类的界是 $0$.

```agda
w⊥ : Wd S⊥
w⊥ ()

l⊥ : LgW S⊥ w⊥
l⊥ ()

q⊥ : _≤w_ S⊥ w⊥ w⊥
q⊥ ()

Wb : HB S⊥ → Wd L₀
Wb β = (w⊥ , β) , hz

W W′ : Wd L₀
W = Wb hz
W′ = Wb (hs (hs hz))

lW : LgW L₀ W
lW = (l⊥ , tt) , tt

lW′ : LgW L₀ W′
lW′ = (l⊥ , tt) , tt

q : W ≤ W′
q = (q⊥ , hsuc (hsuc hself)) , hself
```

## §2 数据对世界不单调 (`anti`)

第 1 层的数据 $x$: 一个 $\kappa_o$-闭包, 分支在界为 $0$ 的世界里是 `n1`, 否则是 `n0`. 动作 `A1` 对一切目标输出 `n1`; 状态是空的.

```agda
pick : ∀ {V} → HB S⊥ → D (hs hz) V
pick hz = n1
pick (hs _) = n0
pick (hl _) = n0
pick (hΩ (() , _) _)

x : D (hs hz) W
x = nc κo tt (λ {V} _ _ → pick (proj₂ (proj₁ V)))

A1 : ∀ {V} → Ig (hs hz) V
A1 _ _ _ _ = df (λ _ → n1)

Y0 : ∀ {V} → St V
Y0 = st zeroD n0 n0

outL : D hz W
outL = yc (Run accᴸ x ≤rf lW one₁ A1 n0 Y0) (τ₀ lW)

outR : D hz W′
outR = yc (Run accᴸ x q lW′ one₁ A1 n0 Y0) (τ₀ lW′)

outL≡ : outL ≡ nl (λ _ → n1)
outL≡ = refl

outR≡ : outR ≡ nl (λ _ → n0)
outR≡ = refl

zero-pt : ∀ {V} k → ¬ (hs hz NV.≤ pt {V} hz (λ _ → n0) k)
zero-pt zero ()
zero-pt (suc k) p = zero-pt k p

anti : ¬ (sum hz outL NV.≤ sum hz outR)
anti (NV.l≤ h) with h 1
... | NV.≤l k p = zero-pt k p
anti (NV.≤l k p) = zero-pt k (NV.≤-trans (NV.≤l 1 (NV.s≤ NV.z≤)) p)
```

## §3 结点的层与 `rkT` 的决定

$\Omega_{\Lambda_1}$ 的闭包分支在世界 $V$ 里是 `ni (sL (topBd …) hself) …`, 过第 $G(\mathrm{top}\,\kappa_o\,V)$ 层.

```agda
rL : StH W (G hz) Λ₁
rL = sL {κ = κo} {c = top L₀ κo W} (topBd L₀ κo W) hself

rR : StH W′ (G (hs (hs hz))) Λ₁
rR = sL {κ = κo} {c = top L₀ κo W′} (topBd L₀ κo W′) hself

lvl-L : top L₀ κo W ≡ hz
lvl-L = refl

lvl-R : top L₀ κo W′ ≡ hs (hs hz)
lvl-R = refl

-- Ωd Λ₁ 的闭包分支: 世界 V 里的结点证据就是上面的 rL / rR
br : ∀ {V} → D Λ₁ V
br {V} = ni (sL {κ = κo} {c = top L₀ κo V} (topBd L₀ κo V) hself) (λ _ _ _ → n1)

Ωd-br : Ωd Λ₁ {W} ≡ n1 ⨾ nc κo tt (λ {V} _ _ → br {V})
Ωd-br = refl
```

目标层 $t = G(1) = 2$, 目标世界 $W'$. 两边都按 `RunNi` 的写法算 `rkT`: 结点证据先经 `kk` (数据的层 $\Lambda_1$, `ll = hself`) 再升到目标世界.

```agda
t₂m : G (hs hz) ⊲[ W′ ] Λ₁
t₂m = hLim {κ = κo} {c = hs hz} (hsuc hself) hself

kmL : G hz ⊲[ W′ ] Λ₁
kmL = ⊲ᴮ↑ q (kk rL ≤rf hself)

kmR : G (hs (hs hz)) ⊲[ W′ ] Λ₁
kmR = ⊲ᴮ↑ ≤rf (kk rR ≤rf hself)

rk-L : rkT kmL t₂m lW′ ≡ keep (ss hself)
rk-L = refl

rk-R : rkT kmR t₂m lW′ ≡ rise
rk-R = refl

rk-split : (rkT kmL t₂m lW′ ≡ keep (ss hself)) × (rkT kmR t₂m lW′ ≡ rise)
rk-split = rk-L , rk-R
```

## §4 结论 (按档)

- **[定理]** `anti`: 同一份数据, 同一个动作与状态, 世界 $W\le W'$ (`q`), 第 0 层输出求和左 $\omega$ (`outL≡`), 右 $0$ 的 $\omega$ 份 (`outR≡`), 左 $\not\le$ 右.
- **[定理]** `lvl-L`, `lvl-R`, `Ωd-br`: $\Omega_{\Lambda_1}$ 的闭包分支在两个世界里的结点分别在第 $1$, $3$ 层. `rk-split`: 同一目标 $(2, W')$ 上, `rkT` 左 `keep`, 右 `rise`.
- **前提实例.** 本篇的一切前提都是具体的项 (`q`, `lW`, `lW′`, `lΛ₁`, `one₁`); 没有假设.
- **[判断]** 带 $W\le W'$ 的模拟要 (i) 一个数据的世界单调谓词 (`anti` 说明不能省), (ii) 关系允许两边结点在不同层 (`lvl-L/R`), (iii) 关系能把 `ni` 与 `nl` 相连 (`rk-split`), 即在第 $\ge1$ 层目标上不能是逐构造子同形的关系. (ii)(iii) 就是 `LeanLvVal` §3 卡点 1 的 (a), 这里写成了编译过的实例.
