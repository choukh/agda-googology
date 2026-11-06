# 第 1 层差树的值语义 (四): `nκ` 的上确界读法

> 不含记号. 入口 [L1Val](L1Val.lagda.md). **编译过的否定.** 两棵第 1 层差树, 都只有一个 `nκ` ($\sum_{c\ge W}u(c)$, 世界 $W=1$):
>
> - $x_\kappa$: 只在世界 $1$ 自身 (路径 `self`) 放 `n1`, 别处 `n0`;
> - $x'_\kappa$: 只在世界 $2$ (路径 `suc self`) 放 `n1`, 别处 `n0`.
>
> $\mathrm{toB}\,x_\kappa\preccurlyeq\mathrm{toB}\,x'_\kappa$ (`toB-le`): 左边每个世界分支 (部分和 $\sum_{1\le c'\le c}u(c')$) 都 $\preccurlyeq1$ (`K-bd`, 对一切世界与一切路径), 右边在世界 $2$ 上 $\succcurlyeq1$. 而折叠 (同 [L1ValBase](L1ValBase.lagda.md) §4 的场景, 目标第 0 层) 在 $x_\kappa$ 上输出 $\ge1$, 在 $x'_\kappa$ 上输出 $0$ (`fold-sep`).
>
> **原因是回灌只读层之下.** 目标第 0 层时 `nκ` 走回灌 (`RKy` 的 `azero`, `κc`, `κΔ`): 层取当前输出 $v_0=W+(\text{第 0 层增长})=2$, 沿字面路径走 $[W,v_0)$ 上的分支, 再把输出接到层上, 反复. $x'_\kappa$ 在 $[1,2)$ 上的分支是 `n0`, 第一格输出 $0$, 层不再长, 之后全部停滞 (`L1ValBase.κ-stall`, 对一切 `nκ`); 世界 $2$ 上的 `n1` 永远走不到. `toB` 把 `nκ` 读成一切世界上部分和的上确界, 看不见 "质量在哪个世界".
>
> **否定的是什么.** "折叠对第 1 层输入的 `toB` 值单调" 对只含 `nκ` 的输入也不成立 (`¬toB-mono-κ`). 所以 `nκ` 不能用上确界 (`κ≼`) 读; 值语义要按世界逐个比 (同一个世界、同一条路径上的部分和), 或者加一个排除停滞的判据. 这也说明 `LayerTr` §3 的 "极限世界读不回" 不是这条路线的关键: 就算读得回, 读回的东西 (上确界的值) 对折叠也不够.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.L1ValKappa where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; z⊲; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_)
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; ni; nκ; nw; tailP; drp)
import OCF.Align.SumOneClosed as F
open import OCF.Align.LayerTrBase
open import OCF.Align.LayerTrOne using (one; S; K; KR; toB)
open import OCF.Align.L1ValBase
```

## §1 两棵树

```agda
pk : ∀ {W} → Bool → D one W
pk true = n1
pk false = n0

isSelf : ∀ {c} → one ⊲ c → Bool
isSelf C.self = true
isSelf _ = false

isS1 : ∀ {c} → one ⊲ c → Bool
isS1 (C.suc C.self) = true
isS1 _ = false

uκ u′κ : ∀ {c} → one ⊲ c → Lg c → D one c
uκ r l = pk (isSelf r)
u′κ r l = pk (isS1 r)

xκ x′κ : D one one
xκ = nκ tt uκ
x′κ = nκ tt u′κ
```

## §2 $x_\kappa$ 的每个世界分支 $\preccurlyeq1$

`K uκ b p aW` 是从 $a$ 沿 $p$ 走到 $b$ 的部分和, $aW$ 是从节点的世界 $1$ 到 $a$ 的路径. 只有路径 `self` 上的分支是 `n1`, 一条路径上它至多走到一次. 不变量: 起点 $\preccurlyeq1$; 若 $aW$ 还是 `self`, 起点 $\preccurlyeq0$.

```agda
isSelf-tr : ∀ {a b c} (r : one ⊲ a) (t : a ⊲ b) (s : b ⊲ c) → isSelf (⊲-tr r (⊲-tr t s)) ≡ isSelf (⊲-tr (⊲-tr r t) s)
isSelf-tr r t C.self = refl
isSelf-tr r t (C.suc s) = refl
isSelf-tr r t (C.lim n s) = refl

one₁ : ∀ {W} → B₁ W
one₁ = bs bz

K-bd  : ∀ b {a} (p : a ⊲ b) (aW : one ⊲ a) (lb : Lg b) (x : B₁ a) → x ≼ one₁ {one} → (isSelf aW ≡ true → x ≼ bz {one}) →
        (K uκ b p aW lb x ≼ one₁ {one}) × (isSelf (⊲-tr aW p) ≡ true → K uκ b p aW lb x ≼ bz {one})
KR-bd : ∀ (f : ℕ → A) (st : ∀ n → f n ⊲ f (suc n)) (wl : ∀ n → Lg (f n)) {a n} (p : a ⊲ f n) (aW : one ⊲ a) (x : B₁ a) →
        x ≼ one₁ {one} → (isSelf aW ≡ true → x ≼ bz {one}) →
        ∀ m → (KR uκ f st wl p aW x m ≼ one₁ {one}) × (isSelf (⊲-tr aW (tailP f st p m)) ≡ true → KR uκ f st wl p aW x m ≼ bz {one})
K-bd b C.self aW lb x h₁ h₀ = h₁ , h₀
K-bd (asuc c) (C.suc p) aW lb x h₁ h₀ with isSelf (⊲-tr aW p) | K-bd c p aW lb x h₁ h₀
... | true  | (k₁ , k₀) = w≼ (s≼s (k₀ refl)) , (λ ())
... | false | (k₁ , k₀) = w≼ k₁ , (λ ())
K-bd (alim f) (C.lim n p) aW (st , wl) x h₁ h₀ =
  l≼ (λ m → w≼ (proj₁ (KR-bd f st wl p aW x h₁ h₀ m))) , (λ ())
KR-bd f st wl p aW x h₁ h₀ zero = K-bd (f _) p aW (wl _) x h₁ h₀
KR-bd f st wl {n = n} p aW x h₁ h₀ (suc m) =
  let (r₁ , r₀) = KR-bd f st wl p aW x h₁ h₀ m
      (k₁ , k₀) = K-bd (f (suc (m + n))) (st (m + n)) (⊲-tr aW (tailP f st p m)) (wl (suc (m + n))) _ r₁ r₀
  in k₁ , (λ e → k₀ (trans (sym (isSelf-tr aW (tailP f st p m) (st (m + n)))) e))

g-bd : ∀ {c} (p : one ⊲ c) (lc : Lg c) → S C.self lc (K uκ c p C.self lc bz) (uκ (⊲-tr C.self p) lc) ≼ one₁ {one}
g-bd p lc with isSelf (⊲-tr C.self p) | K-bd _ p C.self lc bz z≼ (λ _ → z≼)
... | true  | (k₁ , k₀) = s≼s (k₀ refl)
... | false | (k₁ , k₀) = k₁

toB-le : toB tt xκ ≼ toB tt x′κ
toB-le = κ≼ (λ p lc → ≼-trans (g-bd p lc) (≼κ (C.suc C.self) tt (s≼s z≼)))
```

## §3 折叠: $x_\kappa$ 给东西, $x'_\kappa$ 停滞

第一格沿 `suc self` 从世界 $1$ 走到层 $2$, 只经过世界 $1$ 的分支. $x_\kappa$ 在那里是 `n1`, 动作 `Step` 给出 $\ge1$; $x'_\kappa$ 在那里是 `n0`. 第一格由检查器归约 (`R0`), 以后由 `κ-stall`.

```agda
big : has1 (out xκ) ≡ true
big = refl

R0 : Rκ (F.accCn one) u′κ C.self tt C.self StepA₁ n0 Ys 0
R0 = (λ τ lt → _) , _

rs : ∀ n → Rκ (F.accCn one) u′κ C.self tt C.self StepA₁ n0 Ys n
rs zero = R0
rs (suc n) = κ-stall (F.accCn one) u′κ C.self tt C.self StepA₁ n0 Ys n (rs n)

small : Z (out x′κ)
small n = drp-Z _ (proj₁ (rs n) (inj₁ (z⊲ _)) tt)
```

## §4 否定

```agda
fold-sep : ¬ (val xκ ≤ val x′κ)
fold-sep = sep (out xκ) (out x′κ) big small

¬toB-mono-κ : ¬ (∀ (x x′ : D one one) → toB tt x ≼ toB tt x′ → val x ≤ val x′)
¬toB-mono-κ H = fold-sep (H xκ x′κ toB-le)
```
