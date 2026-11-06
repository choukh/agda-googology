# 可数层的对角 (一): 部分和给出字面的第一位置

> 不含记号. 入口 [DiagK](DiagK.lagda.md). 给任意一族可数下标 $x_k : A$ (各级折叠的闭项), 不比较两族的值, 只靠形状造一个合法的 ℕ-极限:
>
> - `pre x k` $=x_0+x_1+\dots+x_k$ (`TLRuleSpec._⊞_`, 右边逐构造子). 相邻两项**字面地**是第一位置 (`pre-st`, 即 `⊞-fst`), 所以 `Dg x = alim (pre x)` 合法只要每个 $x_k$ 合法 (`Lg-Dg`). 这就是 BTBO 的 $\lim_n\psi^n$ 的形状: 下一项以上一项为底.
> - `itr F a`: 下一项是 $t + F(t)$, $F$ 读上一项 (回灌), 同样字面合法 (`Lg-itr`).
> - 值 (`TLRuleSpec._≤_`, 定理): $x_k\le$ `pre x k` $\le$ `Dg x`; `alim x ≤ Dg x`; 对任意加法封闭、严格高于一切 $x_k$ 的 $y$, `Dg x ≤ y` (`Dg-least`). 所以当 $\sup_k x_k$ 加法封闭且严格高于每个 $x_k$ 时, `Dg x` 与 `alim x` 互相 $\le$ (`Dg≈sup`).
> - **毛刺 (定理):** 上确界不加法封闭时部分和改了值: `x = 常值 1` 时 `Dg x` 不 $\le$ `alim x` (`glitch`). 累加的账要两边算 (记忆 `feedback-cumsum-not-natural`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.DiagKSum where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; Strict; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; ≤-suc; ≤lim⁻; irr; _⊞_; ≤⊞; ⊞-mono; z⊞; Clo; one)
import OCF.Free.Level as FL
```

## §1 加法的字面性质

`TLRuleSpec` 只有加法的值性质. 这里补字面的: 左边是和的第一位置, 右边的第一位置搬过去, 合法保持.

```agda
⊞-fst : ∀ a b → a ⊲ a ⊞ b
⊞-fst a azero = C.self
⊞-fst a (asuc b) = C.suc (⊞-fst a b)
⊞-fst a (alim f) = C.lim 0 (⊞-fst a (f 0))

⊞-⊲ : ∀ a {x y} → x ⊲ y → a ⊞ x ⊲ a ⊞ y
⊞-⊲ a C.self = C.self
⊞-⊲ a (C.suc p) = C.suc (⊞-⊲ a p)
⊞-⊲ a (C.lim n p) = C.lim n (⊞-⊲ a p)

Lg-⊞ : ∀ a b → Lg a → Lg b → Lg (a ⊞ b)
Lg-⊞ a azero la lb = la
Lg-⊞ a (asuc b) la lb = Lg-⊞ a b la lb
Lg-⊞ a (alim f) la (st , l) = (λ n → ⊞-⊲ a (st n)) , (λ n → Lg-⊞ a (f n) la (l n))

-- 值上严格: 右边至少是 1
⊞-< : ∀ a {b} → one ≤ b → asuc a ≤ a ⊞ b
⊞-< a h = ⊞-mono (≤-refl a) h

-- 字面上: 右边不是 0 就严格 (CumReadCF 的 Strict)
NZ : A → Set
NZ azero = ⊥
NZ (asuc _) = ⊤
NZ (alim _) = ⊤

⊞-strict : ∀ a b → NZ b → Strict a (a ⊞ b)
⊞-strict a (asuc b) _ = C.ss (⊞-fst a b)
⊞-strict a (alim f) _ = C.sl 0 (⊞-fst a (f 0))
```

## §2 部分和的对角

```agda
pre : (ℕ → A) → ℕ → A
pre x zero = x zero
pre x (suc k) = pre x k ⊞ x (suc k)

Dg : (ℕ → A) → A
Dg x = alim (pre x)

pre-st : ∀ x k → pre x k ⊲ pre x (suc k)
pre-st x k = ⊞-fst (pre x k) (x (suc k))

Lg-pre : ∀ x → (∀ k → Lg (x k)) → ∀ k → Lg (pre x k)
Lg-pre x l zero = l zero
Lg-pre x l (suc k) = Lg-⊞ (pre x k) (x (suc k)) (Lg-pre x l k) (l (suc k))

Lg-Dg : ∀ x → (∀ k → Lg (x k)) → Lg (Dg x)
Lg-Dg x l = pre-st x , Lg-pre x l

pre-strict : ∀ x k → NZ (x (suc k)) → Strict (pre x k) (pre x (suc k))
pre-strict x k z = ⊞-strict (pre x k) (x (suc k)) z

pre-< : ∀ x k → one ≤ x (suc k) → asuc (pre x k) ≤ pre x (suc k)
pre-< x k h = ⊞-< (pre x k) h

pre⊲Dg : ∀ x k → pre x k ⊲ Dg x
pre⊲Dg x k = C.lim k C.self
```

**回灌的形状.** 下一项是 $t+F(t)$: $F$ 读上一项 (例如 "以 $t$ 定出的高度折叠一次"). 合法由形状给出, 只要 $F$ 保合法.

```agda
itr : (A → A) → A → ℕ → A
itr F a zero = a
itr F a (suc k) = itr F a k ⊞ F (itr F a k)

Dgᶠ : (A → A) → A → A
Dgᶠ F a = alim (itr F a)

Lg-itr : ∀ F a → (∀ t → Lg t → Lg (F t)) → Lg a → ∀ k → Lg (itr F a k)
Lg-itr F a lF la zero = la
Lg-itr F a lF la (suc k) = Lg-⊞ (itr F a k) (F (itr F a k)) (Lg-itr F a lF la k) (lF _ (Lg-itr F a lF la k))

Lg-Dgᶠ : ∀ F a → (∀ t → Lg t → Lg (F t)) → Lg a → Lg (Dgᶠ F a)
Lg-Dgᶠ F a lF la = (λ k → ⊞-fst (itr F a k) (F (itr F a k))) , Lg-itr F a lF la
```

## §3 值: 部分和与上确界

```agda
x≤pre : ∀ x k → x k ≤ pre x k
x≤pre x zero = ≤-refl (x zero)
x≤pre x (suc k) = ≤-trans (z⊞ (x (suc k))) (⊞-mono z≤ (≤-refl (x (suc k))))

pre≤Dg : ∀ x k → pre x k ≤ Dg x
pre≤Dg x k = ≤l k (≤-refl (pre x k))

sup≤Dg : ∀ x → alim x ≤ Dg x
sup≤Dg x = l≤ (λ k → ≤l k (x≤pre x k))

Dg-least : ∀ x {y} → Clo y → (∀ k → asuc (x k) ≤ y) → Dg x ≤ y
Dg-least x {y} C h = l≤ (λ k → ≤-trans (≤-suc (≤-refl (pre x k))) (go k))
  where
  go : ∀ k → asuc (pre x k) ≤ y
  go zero = h zero
  go (suc k) = C (go k) (h (suc k))

Dg≈sup : ∀ x → Clo (alim x) → (∀ k → asuc (x k) ≤ alim x) → (Dg x ≤ alim x) × (alim x ≤ Dg x)
Dg≈sup x C h = Dg-least x C h , sup≤Dg x
```

**毛刺.** 上确界不加法封闭时, 部分和改了值. 常值 $1$ 的族: 上确界是 $1$, 部分和的极限是 $\omega$.

```agda
c1 : ℕ → A
c1 _ = one

glitch : ¬ (Dg c1 ≤ alim c1)
glitch p with ≤lim⁻ (≤-trans (pre≤Dg c1 1) p)
... | n , q = irr one q
```

## §4 FGH

```agda
ord : A → FL.Ordᶜ FL.zero
ord azero = FL.zero
ord (asuc a) = FL.suc (ord a)
ord (alim f) = FL.lim (λ n → ord (f n))

fghᴰ : (ℕ → A) → ℕ → ℕ
fghᴰ x = FL.FGH (ord (Dg x))
```
