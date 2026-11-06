# `Tᴰ₊` 的 View: 各项的第 0 层树

> 不含记号. 入口 [TdPlus](TdPlus.lagda.md). `Tᴰ₊ : A` 本身就是布劳威尔树 ($0$, 后继, ℕ-极限; `A` 的构造子), View 是恒等. 中间层是两种种类的差树: 每一项 $t_k$ 都是 `T⁺ h = sum azero ΨΩ`, $\Psi\Omega$ 是 `HtTowerFTree` 的第 0 层树. [MainViewTower](MainViewTower.lagda.md) 的 `Zero` 对这一层给出无条件的 View, 部分良基与 FGH 一致; 这里只是把它套在 `Tᴰ₊` 的各项上:
>
> - **`fgh-T⁺`** (定理): 对一切合法的 $h$, 经 View 算出的 FGH 与 `fghA (T⁺ h lh)` 逐点相等.
> - **`fgh-t`** (定理): 对 `Tᴰ₊` 的每一项 (第 0 项是 `t₀`, 第 $k+1$ 项是 `fold₊` 的输出).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TdPlusView where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Align.HtTowerTy using (hs; hz; LgB; Lg-⊞; ⊞-fst)
open import OCF.Align.HtTowerFTree using (Ht; D₀)
open import OCF.Align.HtTowerFClosed using (module At; W₁; T⁺; top⁺)
open import OCF.Align.MainViewTower using (module Zero)
open import OCF.Align.BrwWfZero using (fghA)
open import OCF.Align.DiagKTop using (λh; Lg-λh)
open import OCF.Align.DiagK3Zero using (pr₀; Lg-pr₀)
open import OCF.Align.TdPlusFold using (prL; Lg-prL)
open import OCF.Align.TdPlusVal using (t₊)
```

```agda
Ψ : ∀ h → LgB h → D₀ W₁
Ψ h lh = At.ΨΩ (top⁺ h) (Lg-⊞ (hs hz) h tt lh) (⊞-fst (hs hz) h)

fgh-T⁺ : ∀ h (lh : LgB h) n → Zero.fgh₀ᵀ W₁ (tt , Ψ h lh , tt) n ≡ fghA (T⁺ h lh) n
fgh-T⁺ h lh n = Zero.fgh₀≡ᵀ W₁ (Ψ h lh) n

-- 第 k 项的高度 (投影之后)
hk : ℕ → Ht
hk zero = pr₀ (λh 0)
hk (suc k) = prL (suc (suc k)) (λh (suc k))

lhk : ∀ k → LgB (hk k)
lhk zero = Lg-pr₀ (λh 0) (Lg-λh 0)
lhk (suc k) = Lg-prL (suc (suc k)) (λh (suc k)) (Lg-λh (suc k))

fgh-t : ∀ k n → Zero.fgh₀ᵀ W₁ (tt , Ψ (hk k) (lhk k) , tt) n ≡ fghA (t₊ k) n
fgh-t zero n = fgh-T⁺ (hk zero) (lhk zero) n
fgh-t (suc k) n = fgh-T⁺ (hk (suc k)) (lhk (suc k)) n
```
