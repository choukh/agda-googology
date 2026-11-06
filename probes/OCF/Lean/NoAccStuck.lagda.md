# NoAcc (二): 卡点, 逐点折叠的两段折法不保第一位置

> 不含记号. 入口 [NoAcc](NoAcc.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延. 只用**同底**的折叠 (第 $2$ 层折到第 $0$ 层), 不涉及世界的移动与回灌.
>
> **问题.** [NoAccFold](NoAccFold.lagda.md) 的 `Φᴾ` 是 CRw 的折叠把 ℕ-极限子句改成逐点. 逐点之后, 输出的 ℕ-极限要合法, 只能靠单调: $f\,n\lhd f\,(n+1)\Rightarrow\Phi f\,n\lhd\Phi f\,(n+1)$ (证书读输入合法, 同 Fab3Typed 的 `Ψ-mono`). Fab3Typed 只有一层一层的折叠 (折到下一层), 多层是复合. CRw 的折叠是**直接**折到目标层 $t$, 遇到在上的种类 (第 $j+1$ 层, $t\lhd j$) 走两段: 先坍缩到第 $j$ 层, 再从 $j$ 折到 $t$. 于是同一个子项, 在兄弟位置上被直接折 ($\Phi_{m\to t}$), 在在上结点的分支里被两段折 ($\Phi_{j\to t}\circ\Phi_{m\to j}$). 本篇证这两种折法在字面第一位置下不可比.
>
> **定理.**
>
> 1. **`route-mismatch`.** $N=\lim(0,1,2,\dots)$ (无 $\Omega$, 合法). $\Phi_{2\to0}\,N\not\lhd\Phi_{1\to0}(\Phi_{2\to1}\,N)$.
> 2. **`no-step`, `not-lg`, `no-cert`.** 第 $2$ 层的合法输入 $\lim(N, \Omega_2\{\_\mapsto N\}, \Omega_2\{\_\mapsto N\},\dots)$ (`Lg-inp`), 逐点折到第 $0$ 层的输出**不合法**: 第 $0$ 项不是第 $1$ 项的第一位置. 所以 `Φᴾ` 没有 "输入 `LgB` ⇒ 输出 `LgB`" 的证书 (`no-cert`), 无论证书怎么写.
> 3. **`crw-lg` (对照).** 同一输入, CRw 的累加折叠 `Φ` 的输出合法 (形状证书).
>
> **证明的想法.** $\Phi_{2\to0}N=\lim(1,\omega,\omega^2,\dots)$, 第 $0$ 项是 $1$, 第 $1$ 项是极限 (`Bad`). 不变量 `Ok`: 一棵树的每个第一位置既不是 "第 $0$ 项为 $0$ 的极限" (`Zl`), 也不是 `Bad`. 无 $\Omega$ 且没有 "第 $0$ 项为 $0$ 的极限" 的输入 (`NI`), 折到第 $0$ 层后满足 `Ok` (`Φ-ok`); $\Phi_{2\to1}N$ 与回灌链的点都是这样的输入 (`NI-Φ`, `NI-ch`). 唯一产生 "第 $0$ 项为 $1$ 的极限" 的地方是输入里第 $0$ 项为 $0$ 的极限, 而 $N$ 本身已被第一段折掉了.
>
> **前提实例.** 输入合法 `Lg-inp` (定理); 层号 $2$ 合法 (`tt`); 目标 $0\lhd2$.
>
> **只否定什么.** 只否定: CRw 的同底折叠把 ℕ-极限子句改成逐点后 (其余子句不变) 保 `LgB`. **不否定**: 别的在上写法 (例如复合式的, 只到有限层; 或在上时的链点另取); 别的合法性 (值合法 `Mo`); 只在一类 "规范" 输入上保合法的证书 (`NI` 一类的不变量是一个方向, 见入口). 跨底的世界移动另有卡点 (入口, 判断).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NoAccStuck where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (I₁)
open import OCF.Lean.CRwFold I₁
open import OCF.Lean.NoAccFold I₁
```

## §1 对一切种类结构: 无 $\Omega$, 第 $0$ 项不为 $0$

```agda
module _ {S : KS} where
  num : ℕ → HB S
  num zero = hz
  num (suc n) = hs (num n)

  Zg : HB S → Set
  Zg hz = ⊤
  Zg (hs _) = ⊥
  Zg (hl _) = ⊥
  Zg (hΩ _ _) = ⊥

  OF : HB S → Set
  OF hz = ⊤
  OF (hs z) = OF z
  OF (hl h) = ∀ n → OF (h n)
  OF (hΩ _ _) = ⊥

  -- 无 Ω, 且每个 ℕ-极限的第 0 项不是 0
  NI : HB S → Set
  NI hz = ⊤
  NI (hs z) = NI z
  NI (hl h) = ¬ Zg (h 0) × (∀ n → NI (h n))
  NI (hΩ _ _) = ⊥

  NI→OF : ∀ z → NI z → OF z
  NI→OF hz n = tt
  NI→OF (hs z) n = NI→OF z n
  NI→OF (hl h) (_ , n) = λ k → NI→OF (h k) (n k)
  NI→OF (hΩ _ _) ()

  nZg-⊞ : ∀ a b → ¬ Zg b → ¬ Zg (a ⊞ b)
  nZg-⊞ a hz zb = λ _ → zb tt
  nZg-⊞ a (hs b) zb = λ ()
  nZg-⊞ a (hl f) zb = λ ()
  nZg-⊞ a (hΩ κ g) zb = λ ()

  zg-⊞ : ∀ a y → ¬ Zg a → ¬ Zg (a ⊞ y)
  zg-⊞ a hz za = za
  zg-⊞ a (hs y) za = λ ()
  zg-⊞ a (hl f) za = λ ()
  zg-⊞ a (hΩ κ g) za = λ ()

  NI-⊞ : ∀ a b → NI a → ¬ Zg a → NI b → NI (a ⊞ b)
  NI-⊞ a hz na za nb = na
  NI-⊞ a (hs b) na za nb = NI-⊞ a b na za nb
  NI-⊞ a (hl q) na za (zq , nq) = zg-⊞ a (q 0) za , λ n → NI-⊞ a (q n) na za (nq n)
  NI-⊞ a (hΩ κ g) na za ()

  NI-mul : ∀ X → NI X → ¬ Zg X → ∀ n → NI (mul X n)
  nZg-mul : ∀ X → ¬ Zg X → ∀ n → ¬ Zg (mul X n)
  NI-mul X nx zx zero = nx
  NI-mul X nx zx (suc n) = NI-⊞ (mul X n) X (NI-mul X nx zx n) (nZg-mul X zx n) nx
  nZg-mul X zx zero = zx
  nZg-mul X zx (suc n) = nZg-⊞ (mul X n) X zx

  NI-chain : ∀ b (k : HB S → HB S) → (∀ x → NI (k x)) → (∀ x → ¬ Zg (k x)) → ∀ n → NI (chain b k n) × ¬ Zg (chain b k n)
  NI-chain b k nk zk zero = nk b , zk b
  NI-chain b k nk zk (suc n) =
    NI-⊞ (chain b k n) _ (proj₁ (NI-chain b k nk zk n)) (proj₂ (NI-chain b k nk zk n)) (nk _) ,
    nZg-⊞ (chain b k n) _ (zk _)
```

## §2 同底的逐点折叠作用在无 $\Omega$ 的输入上

`Φᴾ` 的前三个子句不看可达性证明, 所以对任意参数都归约.

```agda
module _ (m : Cd) (a : Acc b⊥ m) (lm : LgB m) (t : Cd) (pt : t ⊲ m) (b : HB (Lev b⊥ t)) where
  private
    F : HB (Lev b⊥ m) → HB (Lev b⊥ t)
    F z = Φᴾ b⊥ m a lm b⊥ t (sm pt) b z tt

  nZg-Φ : ∀ z → OF z → ¬ Zg (F z)
  nZg-Φ hz o = λ ()
  nZg-Φ (hs z) o = λ ()
  nZg-Φ (hl h) o = λ ()
  nZg-Φ (hΩ _ _) ()

  NI-Φ : ∀ z → OF z → NI (F z)
  NI-Φ hz o = tt
  NI-Φ (hs z) o = nZg-Φ z o , NI-mul (F z) (NI-Φ z o) (nZg-Φ z o)
  NI-Φ (hl h) o = nZg-Φ (h 0) (o 0) , λ n → NI-Φ (h n) (o n)
  NI-Φ (hΩ _ _) ()
```

## §3 第 $0$ 层的不变量 `Ok`

```agda
IsL : Cd → Set
IsL (hl _) = ⊤
IsL hz = ⊥
IsL (hs _) = ⊥
IsL (hΩ () _)

-- 第 0 项是 0 的极限
Zl : Cd → Set
Zl (hl q) = Zg (q 0)
Zl hz = ⊥
Zl (hs _) = ⊥
Zl (hΩ () _)

-- 第 0 项是 1, 第 1 项是极限的极限
Bad : Cd → Set
Bad (hl q) = (q 0 ≡ hs hz) × IsL (q 1)
Bad hz = ⊥
Bad (hs _) = ⊥
Bad (hΩ () _)

OkP : Cd → Set
OkP x = ¬ Zl x × ¬ Bad x

Ok : Cd → Set
Ok y = ∀ {x} → x ⊲ y → OkP x

NZ0 : Cd → Set
NZ0 hz = ⊥
NZ0 (hs _) = ⊤
NZ0 (hl _) = ⊤
NZ0 (hΩ () _)

Ok-hz : Ok hz
Ok-hz hself = (λ ()) , (λ ())

Ok-hs : ∀ {y} → Ok y → Ok (hs y)
Ok-hs oy hself = (λ ()) , (λ ())
Ok-hs oy (hsuc p) = oy p

Ok-hl : ∀ {f} → OkP (hl f) → (∀ n → Ok (f n)) → Ok (hl f)
Ok-hl op of hself = op
Ok-hl op of (hlim n p) = of n p

hs-inj : ∀ {x y : Cd} → hs x ≡ hs y → x ≡ y
hs-inj refl = refl

⊞-nz : ∀ a y → NZ0 a → a ⊞ y ≡ hz → ⊥
⊞-nz a hz na e = subst NZ0 e na
⊞-nz a (hs y) na ()
⊞-nz a (hl f) na ()
⊞-nz a (hΩ () _) na e

nz-Zg : ∀ a → NZ0 a → ¬ Zg a
nz-Zg hz () z
nz-Zg (hs a) na ()
nz-Zg (hl f) na ()
nz-Zg (hΩ () _) na z

nz-⊞ : ∀ a b → NZ0 b → NZ0 (a ⊞ b)
nz-⊞ a hz ()
nz-⊞ a (hs b) nb = tt
nz-⊞ a (hl f) nb = tt
nz-⊞ a (hΩ () _) nb

Ok-⊞ : ∀ a b → NZ0 a → Ok a → Ok b → Ok (a ⊞ b)
Ok-⊞ a hz na oa ob = oa
Ok-⊞ a (hs b) na oa ob = Ok-hs (Ok-⊞ a b na oa (λ p → ob (hsuc p)))
Ok-⊞ a (hl q) na oa ob = Ok-hl (zl (q 0) , bd) (λ n → Ok-⊞ a (q n) na oa (λ p → ob (hlim n p)))
  where
  zl : ∀ y → ¬ Zg (a ⊞ y)
  zl hz = nz-Zg a na
  zl (hs y) = λ ()
  zl (hl f) = λ ()
  zl (hΩ () _)
  bd′ : ∀ y → ¬ Zg y → a ⊞ y ≡ hs hz → ⊥
  bd′ hz zy e = zy tt
  bd′ (hs y) zy e = ⊞-nz a y na (hs-inj e)
  bd′ (hl f) zy ()
  bd′ (hΩ () _) zy e
  bd : ¬ Bad (hl (λ n → a ⊞ q n))
  bd (e , il) = bd′ (q 0) (proj₁ (ob hself)) e

nz-mul : ∀ X → NZ0 X → ∀ n → NZ0 (mul X n)
nz-mul X nx zero = nx
nz-mul X nx (suc n) = nz-⊞ (mul X n) X nx

Ok-mul : ∀ X → NZ0 X → Ok X → ∀ n → Ok (mul X n)
Ok-mul X nx ox zero = ox
Ok-mul X nx ox (suc n) = Ok-⊞ (mul X n) X (nz-mul X nx n) (Ok-mul X nx ox n) ox
```

**主引理 `Φ-ok`.** 折到第 $0$ 层, 输入 `NI`, 输出 `Ok`.

```agda
module _ (m : Cd) (a : Acc b⊥ m) (lm : LgB m) (pt : hz ⊲ m) (b : Cd) where
  private
    F : HB (Lev b⊥ m) → Cd
    F z = Φᴾ b⊥ m a lm b⊥ hz (sm pt) b z tt

  nz-Φ : ∀ z → OF z → NZ0 (F z)
  nz-Φ hz o = tt
  nz-Φ (hs z) o = tt
  nz-Φ (hl h) o = tt
  nz-Φ (hΩ _ _) ()

  one-Φ : ∀ z → OF z → F z ≡ hs hz → Zg z
  one-Φ hz o e = tt
  one-Φ (hs z) o ()
  one-Φ (hl h) o ()
  one-Φ (hΩ _ _) ()

  Φ-ok : ∀ z → NI z → Ok (F z)
  Φ-ok hz n = Ok-hs Ok-hz
  Φ-ok (hs z) n = Ok-hl (nz-Zg (F z) (nz-Φ z (NI→OF z n)) , bd)
                        (Ok-mul (F z) (nz-Φ z (NI→OF z n)) (Φ-ok z n))
    where
    bd : ¬ Bad (hl (mul (F z)))
    bd (e , il) = subst (λ Y → IsL (Y ⊞ Y)) e il
  Φ-ok (hl h) (zh , nh) = Ok-hl (nz-Zg (F (h 0)) (nz-Φ (h 0) (NI→OF (h 0) (nh 0))) , bd) (λ n → Φ-ok (h n) (nh n))
    where
    bd : ¬ Bad (hl (λ n → F (h n)))
    bd (e , il) = zh (one-Φ (h 0) (NI→OF (h 0) (nh 0)) e)
  Φ-ok (hΩ _ _) ()
```

## §4 两段折法与直接折法不可比

$N=\lim(0,1,2,\dots)$ 放在第 $2$ 层. 三个折叠: $\Phi_{2\to0}$, $\Phi_{2\to1}$, $\Phi_{1\to0}$ (界都取 $0$ 或第 $1$ 层的 $0$).

```agda
L2 : Cd
L2 = hs (hs hz)

N : HB (Lev b⊥ L2)
N = hl num

OF-num : ∀ {S : KS} n → OF {S} (num n)
OF-num zero = tt
OF-num (suc n) = OF-num n

Φ20 : HB (Lev b⊥ L2) → Cd
Φ20 z = Φᴾ b⊥ L2 (wf b⊥ L2) tt b⊥ hz (sm (z⊲ᴮ L2)) hz z tt

Φ21 : HB (Lev b⊥ L2) → HB (Lev b⊥ (hs hz))
Φ21 z = Φᴾ b⊥ L2 (wf b⊥ L2) tt b⊥ (hs hz) (sm (hsuc hself)) hz z tt

Φ10 : HB (Lev b⊥ (hs hz)) → Cd
Φ10 z = Φᴾ b⊥ (hs hz) (wf b⊥ (hs hz)) tt b⊥ hz (sm (hsuc hself)) hz z tt

Bad-N : Bad (Φ20 N)
Bad-N = refl , tt

route-mismatch : ¬ (Φ20 N ⊲ Φ10 (Φ21 N))
route-mismatch p =
  proj₂ (Φ-ok (hs hz) (wf b⊥ (hs hz)) tt (hsuc hself) hz (Φ21 N)
           (NI-Φ L2 (wf b⊥ L2) tt (hs hz) (hsuc hself) hz N OF-num) p) Bad-N
```

## §5 一个合法输入, 输出不合法

`inp` $=\lim(N, \Omega_2\{\_\mapsto N\}, \Omega_2\{\_\mapsto N\}, \dots)$. $\Omega_2$ 是第 $2$ 层的新种类 (`inj₂ tt`), 对目标 $0$ 在上: 先坍缩到第 $1$ 层 (链从地板 `top b⊥ 1` 起, 链点是 $\Phi_{2\to1}N$ 的和), 再折到第 $0$ 层.

```agda
Ωc : HB (Lev b⊥ L2)
Ωc = hΩ (inj₂ tt) (λ _ → N)

fI : ℕ → HB (Lev b⊥ L2)
fI zero = N
fI (suc n) = Ωc

inp : HB (Lev b⊥ L2)
inp = hl fI

Lg-num : ∀ {S : KS} n → LgB {S} (num n)
Lg-num zero = tt
Lg-num (suc n) = Lg-num n

Lg-N : LgB N
Lg-N = (λ n → hsuc hself) , Lg-num

Lg-inp : LgB inp
Lg-inp = st , lg
  where
  st : ∀ {w} n → fI n ⊲[ w ] fI (suc n)
  st {w} zero = hLim (botBd (Lev b⊥ L2) (inj₂ tt) w) hself
  st (suc n) = hself
  lg : ∀ n → LgB (fI n)
  lg zero = Lg-N
  lg (suc n) = (λ lw e e′ p → hself) , (λ lw e → Lg-N)

out : Cd
out = Φ20 inp

-- 在上: 链从第 1 层的地板起, 每个链点加上 Φ21 N
ch : ℕ → HB (Lev b⊥ (hs hz))
ch = chain (top b⊥ (hs hz)) (λ b′ → Φᴾ b⊥ L2 (wf b⊥ L2) tt b⊥ (hs hz) (sm (⊏⊑ hself)) b′ N tt)

NI-ch : NI (hl ch)
NI-ch = (λ ()) , λ n → proj₁ (NI-chain _ _
  (λ b′ → NI-Φ L2 (wf b⊥ L2) tt (hs hz) (⊏⊑ hself) b′ N OF-num)
  (λ b′ → nZg-Φ L2 (wf b⊥ L2) tt (hs hz) (⊏⊑ hself) b′ N OF-num) n)

-- Φ20 Ωc 字面是 Φ10′ (lim ch); Φ10′ 与 Φ10 只差可达性与层号合法的证明项
Ok-Ωc : Ok (Φ20 Ωc)
Ok-Ωc = Φ-ok (hs hz) (wf b⊥ (hs hz)) (lg↓ hself tt) (hsuc hself) hz (hl ch) NI-ch

no-step : ¬ (Φ20 (fI 0) ⊲ Φ20 (fI 1))
no-step p = proj₂ (Ok-Ωc p) Bad-N

not-lg : ¬ LgB out
not-lg (st , _) = no-step (st {tt} 0)

no-cert : ¬ (∀ h → LgB h → LgB (Φ20 h))
no-cert c = not-lg (c inp Lg-inp)
```

**对照: CRw 的累加折叠在同一输入上合法 (形状证书).**

```agda
crw-lg : LgB (Φ b⊥ L2 (wf b⊥ L2) tt b⊥ hz (sm (z⊲ᴮ L2)) hz inp tt)
crw-lg = sh→lg _ (Sh-Φ b⊥ L2 (wf b⊥ L2) tt b⊥ hz (sm (z⊲ᴮ L2)) hz inp tt)
```

## 结论 (按档)

- **[定理]** `NI-⊞`, `NI-mul`, `NI-chain`, `NI-Φ`, `nZg-Φ` (对一切种类结构与同底参数); `Ok-⊞`, `Ok-mul`, **`Φ-ok`** (折到第 $0$ 层: `NI` 输入的输出满足 `Ok`); **`route-mismatch`**: $\Phi_{2\to0}N\not\lhd\Phi_{1\to0}(\Phi_{2\to1}N)$; `Lg-inp`; **`no-step`, `not-lg`, `no-cert`**: 逐点折叠在合法输入上输出不合法, 没有读输入合法的证书; **`crw-lg`**: 累加折叠在同一输入上合法.
- **[判断]** 卡点在 "在上" 的两段折法, 不在证书的写法: 直接折法对无 $\Omega$ 的部分只作用一次 ($0\mapsto1$, $+1\mapsto\cdot\omega$), 两段折法作用两次, 而 $x\lhd\Phi x$ 对 $x=\lim(0,1,2,\dots)$ 不成立. 复合式的折叠 (Fab3Typed) 每层作用一次, 字面一致, 但只到有限层.
