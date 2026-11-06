# EboLeanDef: EBO 的定义 (第 1 层) 与沿基本列的 FGH (第 2 层)

> **记号侧验收工作**, 读记号, 不进成品. [EboLean](EboLean.lagda.md) 的第 1, 2 层. 项、序、比较、共尾度、`pred`、Ω-基本列 `fsT` 与 γ-链 `γT` 直接取自 [EBO](EBO.lagda.md) (只取用到的定义, 切片只数到达的块). 本文新写的只有两件:
>
> 1. **裸值的 ω-基本列 `fsn`** (§1). EBO 的 `fsn` 是带递减证书的 `fsn↓` 去掉证书, 证书 (`Below`, `fsT↓`, `γ↓`, `rep↓`) 与对齐引理 (`fsT↓-trm` 等) 约 100 行. 递减性在第 3 层由封闭性证明顺带给出 (`Trian` 的 `t<`), 所以定义里不必带. 子句与 `fsn↓` 一一对应, 值相同 ([EboLeanCmp](EboLeanCmp.lagda.md) 的 `fsn≡`, 定理).
> 2. **沿基本列的 FGH** (§2). EBO 的 `FGH` 沿全体项上 `_<ᵀ_` 的 `Acc` 递归, 而那个 `Acc` 只在自然数上成立 ([AccTree](AccTree.lagda.md) 的 `acc→nat`), 所以它在 ω 以上没有输入. 这里改沿 `HC` (遗传地沿 `pred`/`fsn` 良基且不碰 Ω-共尾) 递归: `HC` 就是 "这个项的基本列遗传地良基且可数", FGH 的三条方程就是记号的递归方程.
>
> `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EboLeanDef where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using (List; []; _∷_; replicate)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import OCF.Align.EBO public
  using (T; PT; ψ; 𝟏; natT; sucT; Ωt; Ωs; _<ᵀ_; _<ᴾ_; []<; hd<; tl<; lv<; ar<;
         Cmp; lt; eq; gt; cmpᵀ; cmpᴾ; Cof; c0; c1; cω; cΩ; cof; cofP; cofA; cofψ0; cofψ₊;
         pred; fsT; fsT0; fsT₊; fsTc; γT; ΩTower; EBOψ)
```

## §1 ω-基本列 (裸值)

规则同 EBO §5.3: 和取末项; $1[n]=0$; 奇异叶 $\Omega_u[n]=\Omega_{u[n]}$ ($u$ 的共尾度为 ω 时取 $u[n]$, 为 $\Omega_{\nu+1}$ 时取 $u[n]$ 的 Ω-基本列值); $\psi_u(b+1)[n]=\psi_u(b)\cdot n$; $\psi_u(b)[n]=\psi_u(b[n])$; 规则 6 走 γ-链. 正规叶 (`c1` 行) 与规则 5Ω (`lt`/`eq` 行) 是只为全函数性存在的哑值, 与 EBO 相同.

```agda
fsn  : T → ℕ → T
fsn0 : T → Cof → ℕ → T              -- 第二参数 = cof u
fsn₊ : T → T → Cof → ℕ → T          -- 第三参数 = cof b
fsnc : T → T → T → Cmp → ℕ → T      -- 第四参数 = cmpᵀ (ν+1) u

fsn []                   n = []
fsn (x ∷ xs@(_ ∷ _))     n = x ∷ fsn xs n
fsn (ψ u b@(_ ∷ _) ∷ []) n = fsn₊ u b (cof b) n
fsn (ψ u@(_ ∷ _) [] ∷ []) n = fsn0 u (cof u) n
fsn (𝟏 ∷ [])             n = []

fsn0 u c0     n = []                         -- 不可达哑值
fsn0 u c1     n = natT n                     -- 正规叶: 哑值
fsn0 u cω     n = ψ (fsn u n) [] ∷ []
fsn0 u (cΩ ν) n = ψ (fsT u (natT n)) [] ∷ []

fsn₊ u b c0     n = []                       -- 不可达哑值
fsn₊ u b c1     n = replicate n (ψ u (pred b))   -- 规则 4
fsn₊ u b cω     n = ψ u (fsn b n) ∷ []       -- 规则 5 (ω)
fsn₊ u b (cΩ ν) n = fsnc u b ν (cmpᵀ (sucT ν) u) n

fsnc u b ν gt n = ψ u (fsT b (γT b ν n)) ∷ []   -- 规则 6
fsnc u b ν lt n = ψ u (fsT b (natT n)) ∷ []     -- 规则 5Ω 的 ℕ-截断 (哑值)
fsnc u b ν eq n = ψ u (fsT b (natT n)) ∷ []
```

## §2 沿基本列的 FGH

`HC t`: $t$ 是零, 或后继且前驱 `HC`, 或共尾度 ω 且每个 $t[n]$ 都 `HC`. 没有 `cΩ` 行: 不可数共尾的项不在里面. `fgh` 对 `HC` 的推导结构递归, 方程就是 $f_0(n)=n+1$, $f_{\alpha+1}(n)=f_\alpha^n(n)$, $f_\lambda(n)=f_{\lambda[n]}(n)$.

```agda
data HC (t : T) : Set where
  h0 : cof t ≡ c0 → HC t
  h1 : cof t ≡ c1 → HC (pred t) → HC t
  hω : cof t ≡ cω → (∀ n → HC (fsn t n)) → HC t

iter : (ℕ → ℕ) → ℕ → ℕ → ℕ
iter f x zero    = x
iter f x (suc k) = f (iter f x k)

fgh : ∀ t → HC t → ℕ → ℕ
fgh t (h0 _)   n = suc n
fgh t (h1 _ h) n = iter (fgh (pred t) h) n n
fgh t (hω _ h) n = fgh (fsn t n) (h n) n
```
