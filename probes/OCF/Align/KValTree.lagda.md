# `nκ` 的值语义 (一): 关系, 只看差树

> 不含记号, 不提折叠. 入口 [KVal](KVal.lagda.md). 在 [DValTree](DValTree.lagda.md) 的 $\sqsubseteq^{\mathsf d}$ 上做两处改动:
>
> - **两档** `lo`, `hi`. `lo` 档没有 `nκ` 的规则, 语义是**跨世界**的: 两边可以在不同的世界里折叠 (`KValSound` 的 `OutLe`). `hi` 档多一条 `κ⊑`, 语义要求上下文里记下两边回灌的层 $\ell=W+z$ 可比 (`Hℓ`).
> - **`ni⊑` 的分支跨世界比**: 左边分支在世界 $W$, 右边在 $W'$, 坐标按第 0 层的值对齐, 分支在 `lo` 档里比. 原来同一世界的 `ni⊑` 不够: `nκ` 的各格在不同的层 $v_n$, $v'_n$ 里跑, 格里的 `ni` 的链也就在不同世界里.
> - **`κ⊑`: 分支按层的值对齐.** $V'\le V$ (右边的树世界不高于左边, 回灌从更低处起步), 层 $c\le c'$ ⇒ $u(c)\sqsubseteq_{\mathsf{lo}}u'(c')$, 两边各自对层的值单调. 分支只在 `lo` 档: **不嵌套**. 嵌套的 `nκ` 不在这个关系里 (入口 §4).
>
> `Rfᵏ m x = x ⊑[ m ] x` 是输入判据.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.KValTree where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg; ss)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_)
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; ni; nκ; nw)
open import OCF.Align.DValTree using (V0; pre₁; Br) public
open import OCF.Align.LayerTrOne using (one)
```

## §1 档与分支

`Bk V`: `nκ` 在树世界 $V$ 上的分支, 每个层 $c\ge V$ 上一棵第 1 层树.

```agda
data Md : Set where
  lo hi : Md

Bk : A → Set
Bk V = ∀ {c} → V ⊲ c → Lg c → D one c
```

## §2 关系

```agda
infix 4 _⊑[_]_
data _⊑[_]_ : ∀ {V V′} → D one V → Md → D one V′ → Set where
  n0⊑ : ∀ {m V V′} {x : D one V′} → n0 {W = V} ⊑[ m ] x
  n1⊑ : ∀ {m V V′} → n1 {W = V} ⊑[ m ] n1 {W = V′}
  ⨾⊑  : ∀ {m V V′} {x y : D one V} {x′ y′ : D one V′} → x ⊑[ m ] x′ → y ⊑[ m ] y′ → (x ⨾ y) ⊑[ m ] (x′ ⨾ y′)
  nl⊑ : ∀ {m V V′} {d : ℕ → D one V} {d′ : ℕ → D one V′} → (∀ n → d n ⊑[ m ] d′ n) → nl d ⊑[ m ] nl d′
  nwˡ : ∀ {m V₀ V V′} {p : V₀ ⊲ V} {x : D one V₀} {x′ : D one V′} → x ⊑[ m ] x′ → nw p x ⊑[ m ] x′
  nwʳ : ∀ {m V₀ V V′} {p : V₀ ⊲ V′} {x : D one V} {x′ : D one V₀} → x ⊑[ m ] x′ → x ⊑[ m ] nw p x′
  -- 逐分支, 跨世界: 坐标按第 0 层的值对齐, 分支在 lo 档
  ni⊑ : ∀ {m V V′} {u : Br V} {u′ : Br V′} →
        (∀ {W W′} (q : V ⊲ W) (q′ : V ⊲ W′) (l : Lg W) (l′ : Lg W′) (z : D azero W) (z′ : D azero W′) → V0 z ≤ V0 z′ → u q l z ⊑[ lo ] u q′ l′ z′) →
        (∀ {W W′} (q : V′ ⊲ W) (q′ : V′ ⊲ W′) (l : Lg W) (l′ : Lg W′) (z : D azero W) (z′ : D azero W′) → V0 z ≤ V0 z′ → u′ q l z ⊑[ lo ] u′ q′ l′ z′) →
        (∀ {W W′} (q : V ⊲ W) (q′ : V′ ⊲ W′) (l : Lg W) (l′ : Lg W′) (z : D azero W) (z′ : D azero W′) → V0 z ≤ V0 z′ → u q l z ⊑[ lo ] u′ q′ l′ z′) →
        ni (ss C.self) u ⊑[ m ] ni (ss C.self) u′
  -- 回灌: 层按值对齐, 分支在 lo 档 (不嵌套), 右边从不高于左边的层起步
  κ⊑ : ∀ {V V′ zz zz′} {u : Bk V} {u′ : Bk V′} → V′ ≤ V →
       (∀ {c c′} (p : V ⊲ c) (p′ : V ⊲ c′) (l : Lg c) (l′ : Lg c′) → c ≤ c′ → u p l ⊑[ lo ] u p′ l′) →
       (∀ {c c′} (p : V′ ⊲ c) (p′ : V′ ⊲ c′) (l : Lg c) (l′ : Lg c′) → c ≤ c′ → u′ p l ⊑[ lo ] u′ p′ l′) →
       (∀ {c c′} (p : V ⊲ c) (p′ : V′ ⊲ c′) (l : Lg c) (l′ : Lg c′) → c ≤ c′ → u p l ⊑[ lo ] u′ p′ l′) →
       nκ zz u ⊑[ hi ] nκ zz′ u′
  trˡ : ∀ {m V V′} {x y : D one V} {z : D one V′} → x ⊑[ m ] y → y ⊑[ m ] z → x ⊑[ m ] z
  trʳ : ∀ {m V V′} {x : D one V′} {y z : D one V} → x ⊑[ m ] y → y ⊑[ m ] z → x ⊑[ m ] z
  u0ˡ : ∀ {m V V′} {x : D one V} {x′ : D one V′} → x ⊑[ m ] x′ → (n0 ⨾ x) ⊑[ m ] x′
  u0ʳ : ∀ {m V V′} {x : D one V} {x′ : D one V′} → x ⊑[ m ] x′ → x ⊑[ m ] (n0 ⨾ x′)
  u1ˡ : ∀ {m V V′} {x : D one V} {x′ : D one V′} → x ⊑[ m ] x′ → (x ⨾ n0) ⊑[ m ] x′
  u1ʳ : ∀ {m V V′} {x : D one V} {x′ : D one V′} → x ⊑[ m ] x′ → x ⊑[ m ] (x′ ⨾ n0)
  asˡ  : ∀ {m V V′} {x y z : D one V} {t : D one V′} → z ⊑[ m ] z → (x ⨾ (y ⨾ z)) ⊑[ m ] t → ((x ⨾ y) ⨾ z) ⊑[ m ] t
  asˡ′ : ∀ {m V V′} {x y z : D one V} {t : D one V′} → z ⊑[ m ] z → ((x ⨾ y) ⨾ z) ⊑[ m ] t → (x ⨾ (y ⨾ z)) ⊑[ m ] t
  asʳ  : ∀ {m V V′} {x y z : D one V′} {t : D one V} → z ⊑[ m ] z → t ⊑[ m ] ((x ⨾ y) ⨾ z) → t ⊑[ m ] (x ⨾ (y ⨾ z))
  asʳ′ : ∀ {m V V′} {x y z : D one V′} {t : D one V} → z ⊑[ m ] z → t ⊑[ m ] (x ⨾ (y ⨾ z)) → t ⊑[ m ] ((x ⨾ y) ⨾ z)
  pre⊑ : ∀ {m V V′} {x : D one V} {x′ : D one V′} {d : ℕ → D one V} {d′ : ℕ → D one V′} →
         x ⊑[ m ] x′ → (∀ n → d n ⊑[ m ] d′ n) → ∀ k → (x ⨾ pre₁ d k) ⊑[ m ] (x′ ⨾ nl d′)
  lim⊑ : ∀ {m V V′} {x : D one V} {d : ℕ → D one V} {t : D one V′} →
         (∀ n → d n ⊑[ m ] d n) → (∀ k → (x ⨾ pre₁ d k) ⊑[ m ] t) → (x ⨾ nl d) ⊑[ m ] t

Rfᵏ : Md → ∀ {V} → D one V → Set
Rfᵏ m x = x ⊑[ m ] x

-- 判据: 分支对层的值单调 (跨一切路径与合法性证明)
KMono : ∀ {V} → Bk V → Set
KMono {V} u = ∀ {c c′} (p : V ⊲ c) (p′ : V ⊲ c′) (l : Lg c) (l′ : Lg c′) → c ≤ c′ → u p l ⊑[ lo ] u p′ l′
```

## §3 简单的推论

```agda
rf-κ : ∀ {V zz} {u : Bk V} → (V≤ : V ≤ V) → KMono u → Rfᵏ hi (nκ zz u)
rf-κ V≤ m = κ⊑ V≤ m m m

-- lo 档推出 hi 档
up-hi : ∀ {V V′} {x : D one V} {x′ : D one V′} → x ⊑[ lo ] x′ → x ⊑[ hi ] x′
up-hi n0⊑ = n0⊑
up-hi n1⊑ = n1⊑
up-hi (⨾⊑ h h′) = ⨾⊑ (up-hi h) (up-hi h′)
up-hi (nl⊑ h) = nl⊑ (λ n → up-hi (h n))
up-hi (nwˡ h) = nwˡ (up-hi h)
up-hi (nwʳ h) = nwʳ (up-hi h)
up-hi (ni⊑ a b c) = ni⊑ a b c
up-hi (trˡ h h′) = trˡ (up-hi h) (up-hi h′)
up-hi (trʳ h h′) = trʳ (up-hi h) (up-hi h′)
up-hi (u0ˡ h) = u0ˡ (up-hi h)
up-hi (u0ʳ h) = u0ʳ (up-hi h)
up-hi (u1ˡ h) = u1ˡ (up-hi h)
up-hi (u1ʳ h) = u1ʳ (up-hi h)
up-hi (asˡ r h) = asˡ (up-hi r) (up-hi h)
up-hi (asˡ′ r h) = asˡ′ (up-hi r) (up-hi h)
up-hi (asʳ r h) = asʳ (up-hi r) (up-hi h)
up-hi (asʳ′ r h) = asʳ′ (up-hi r) (up-hi h)
up-hi (pre⊑ h hd k) = pre⊑ (up-hi h) (λ n → up-hi (hd n)) k
up-hi (lim⊑ hr h) = lim⊑ (λ n → up-hi (hr n)) (λ k → up-hi (h k))
```
