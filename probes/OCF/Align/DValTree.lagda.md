# 差树上的值关系 (三): 定义, 只看差树

> 不含记号, 不提折叠. 入口 [DVal](DVal.lagda.md). 第 1 层差树 (`D one V`, 世界可以不同) 上的关系 `_⊑ᵈ_`. 构造子分三类:
>
> - **和的结构** (第 0 层的那一部分: `n0`, `n1`, `⨾`, `nl`, `nw`): 同余, 单位, 结合, 极限的部分和 (`pre⊑`) 与 "极限是部分和的上界" (`lim⊑`), 两种传递. 这些与 `CvLayerRun` 的结构律同形; 第 0 层的值比较由它们经规范形拼出 (那是 `cong0` 的证法).
> - **节点 `ni` 逐分支比**: `ni⊑`. 同一个坐标位置上比 (不是上确界), 坐标按**第 0 层的值**对齐: 左边坐标的值 $\le$ 右边的, 则分支 $\sqsubseteq^{\mathsf d}$. 没有 "左边分支都 $\le$ 右边 ⇒ 节点 $\le$ 右边" (`LayerTrBase.i≼` 那样) 的规则.
> - **判据作前提**: `ni⊑` 要两边的分支各自对坐标的值单调且与抬升路径无关 (`Mono`, 也用 $\sqsubseteq^{\mathsf d}$ 说), 结合律 (`as*`) 与极限上界 (`lim⊑`) 要被重排的那一段自比 (`Rf`). 这些前提由折叠的形状逼出: 没有它们, 规则在语义下不成立 (反例在 [DValNeg](DValNeg.lagda.md), `¬assoc`).
>
> **没有 `nκ` 的规则.** `nκ` 只能经 `n0⊑` 出现在右边. 原因与下一步要的东西见 [DValNeg](DValNeg.lagda.md) 与入口 §3.
>
> `Rf x` ($x\sqsubseteq^{\mathsf d}x$) 就是这一层的输入判据: 不是一切树都自比 (`DValNeg.xb-not-Rf`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.DValTree where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg; ss)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_)
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; ni; nκ; nw)
open import OCF.Align.BrwMidZero using (toA)
open import OCF.Align.LayerTrOne using (one)
```

## §1 记号

```agda
V0 : ∀ {V} → D azero V → A
V0 z = proj₁ (toA z)

pre₁ : ∀ {V} → (ℕ → D one V) → ℕ → D one V
pre₁ d zero = n0
pre₁ d (suc k) = pre₁ d k ⨾ d k

-- 第 1 层 ni 的分支: 更大世界上, 第 0 层差树坐标
Br : A → Set
Br V = ∀ {W′} → V ⊲ W′ → Lg W′ → D azero W′ → D one W′
```

## §2 关系

```agda
infix 4 _⊑ᵈ_
data _⊑ᵈ_ : ∀ {V V′} → D one V → D one V′ → Set where
  n0⊑ : ∀ {V V′} {x : D one V′} → n0 {W = V} ⊑ᵈ x
  n1⊑ : ∀ {V V′} → n1 {W = V} ⊑ᵈ n1 {W = V′}
  ⨾⊑  : ∀ {V V′} {x y : D one V} {x′ y′ : D one V′} → x ⊑ᵈ x′ → y ⊑ᵈ y′ → (x ⨾ y) ⊑ᵈ (x′ ⨾ y′)
  nl⊑ : ∀ {V V′} {d : ℕ → D one V} {d′ : ℕ → D one V′} → (∀ n → d n ⊑ᵈ d′ n) → nl d ⊑ᵈ nl d′
  nwˡ : ∀ {V₀ V V′} {p : V₀ ⊲ V} {x : D one V₀} {x′ : D one V′} → x ⊑ᵈ x′ → nw p x ⊑ᵈ x′
  nwʳ : ∀ {V₀ V V′} {p : V₀ ⊲ V′} {x : D one V} {x′ : D one V₀} → x ⊑ᵈ x′ → x ⊑ᵈ nw p x′
  -- 逐分支: 坐标按第 0 层的值对齐; 两边的分支各自对坐标值单调
  ni⊑ : ∀ {V V′} {u : Br V} {u′ : Br V′} →
        (∀ {W} (q q′ : V ⊲ W) (l : Lg W) (z z′ : D azero W) → V0 z ≤ V0 z′ → u q l z ⊑ᵈ u q′ l z′) →
        (∀ {W} (q q′ : V′ ⊲ W) (l : Lg W) (z z′ : D azero W) → V0 z ≤ V0 z′ → u′ q l z ⊑ᵈ u′ q′ l z′) →
        (∀ {W} (q : V ⊲ W) (q′ : V′ ⊲ W) (l : Lg W) (z z′ : D azero W) → V0 z ≤ V0 z′ → u q l z ⊑ᵈ u′ q′ l z′) →
        ni (ss C.self) u ⊑ᵈ ni (ss C.self) u′
  -- 传递: 中间的树与一边同世界
  trˡ : ∀ {V V′} {x y : D one V} {z : D one V′} → x ⊑ᵈ y → y ⊑ᵈ z → x ⊑ᵈ z
  trʳ : ∀ {V V′} {x : D one V′} {y z : D one V} → x ⊑ᵈ y → y ⊑ᵈ z → x ⊑ᵈ z
  -- 单位
  u0ˡ : ∀ {V V′} {x : D one V} {x′ : D one V′} → x ⊑ᵈ x′ → (n0 ⨾ x) ⊑ᵈ x′
  u0ʳ : ∀ {V V′} {x : D one V} {x′ : D one V′} → x ⊑ᵈ x′ → x ⊑ᵈ (n0 ⨾ x′)
  u1ˡ : ∀ {V V′} {x : D one V} {x′ : D one V′} → x ⊑ᵈ x′ → (x ⨾ n0) ⊑ᵈ x′
  u1ʳ : ∀ {V V′} {x : D one V} {x′ : D one V′} → x ⊑ᵈ x′ → x ⊑ᵈ (x′ ⨾ n0)
  -- 结合: 被重新加括号的最后一段要自比
  asˡ  : ∀ {V V′} {x y z : D one V} {t : D one V′} → z ⊑ᵈ z → (x ⨾ (y ⨾ z)) ⊑ᵈ t → ((x ⨾ y) ⨾ z) ⊑ᵈ t
  asˡ′ : ∀ {V V′} {x y z : D one V} {t : D one V′} → z ⊑ᵈ z → ((x ⨾ y) ⨾ z) ⊑ᵈ t → (x ⨾ (y ⨾ z)) ⊑ᵈ t
  asʳ  : ∀ {V V′} {x y z : D one V′} {t : D one V} → z ⊑ᵈ z → t ⊑ᵈ ((x ⨾ y) ⨾ z) → t ⊑ᵈ (x ⨾ (y ⨾ z))
  asʳ′ : ∀ {V V′} {x y z : D one V′} {t : D one V} → z ⊑ᵈ z → t ⊑ᵈ (x ⨾ (y ⨾ z)) → t ⊑ᵈ ((x ⨾ y) ⨾ z)
  -- 极限: 部分和在极限之下; 部分和都在 t 之下则极限在 t 之下 (各项要自比)
  pre⊑ : ∀ {V V′} {x : D one V} {x′ : D one V′} {d : ℕ → D one V} {d′ : ℕ → D one V′} →
         x ⊑ᵈ x′ → (∀ n → d n ⊑ᵈ d′ n) → ∀ k → (x ⨾ pre₁ d k) ⊑ᵈ (x′ ⨾ nl d′)
  lim⊑ : ∀ {V V′} {x : D one V} {d : ℕ → D one V} {t : D one V′} →
         (∀ n → d n ⊑ᵈ d n) → (∀ k → (x ⨾ pre₁ d k) ⊑ᵈ t) → (x ⨾ nl d) ⊑ᵈ t

Rf : ∀ {V} → D one V → Set
Rf x = x ⊑ᵈ x

Mono : ∀ {V} → Br V → Set
Mono {V} u = ∀ {W} (q q′ : V ⊲ W) (l : Lg W) (z z′ : D azero W) → V0 z ≤ V0 z′ → u q l z ⊑ᵈ u q′ l z′
```

## §3 简单的推论

```agda
rf-nw : ∀ {V₀ V} {p : V₀ ⊲ V} {x : D one V₀} → Rf x → Rf (nw p x)
rf-nw h = nwˡ (nwʳ h)

rf-ni : ∀ {V} {u : Br V} → Mono u → Rf (ni (ss C.self) u)
rf-ni m = ni⊑ m m m
```
