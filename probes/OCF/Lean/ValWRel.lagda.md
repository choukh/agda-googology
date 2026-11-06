# ValW (二): 两个层、两个世界的模拟关系 `Mx`

> 不含记号. 入口 [ValW](ValW.lagda.md), 接口 [ValWIf](ValWIf.lagda.md). 第 4 层: 只新增关系与定理. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延.
>
> 推广 [ValNewRel](../Align/ValNewRel.lagda.md) 的 `Mo` (同层、同一世界) 到 [LeanTTree](LeanTTree.lagda.md) 的数据, 两个层 $L_1$, $L_2$, 两个世界 $W_1$, $W_2$:
>
> - **结点 `mi`**: 两边的结点层可以不同, 带字面证据 $k_1\lhd k_2$ (在 $W_2$ 里); 分支在**成对的更大世界** $W_1\le W_1'$, $W_2\le W_2'$, $W_1'\le W_2'$ 上相关 (输入按结点层递归地相关).
> - **闭包 `mc`**: 同一个种类, 分支在成对的更大世界上相关. 这就是 "闭包分支对世界单调" 写成关系的样子: 左边在小世界取分支, 右边在大世界取分支.
> - **换世界 `mw`, `mw′`**: 任一边的 `nw` 透明.
> - **右边多出一段** (`mz`, `mr`, `me`, `mlₙ`): 同 `ValNewRel`, 只是 "取极限的第 0 项" 放宽到任一项.
>
> 关系本身不带世界与层的比较 (接口 `ValWIf.SimW.Rx` 的证据 `e`, `q` 在这里不进关系); 证据只出现在构造子的前提里 (`mi` 的 $k_1\lhd k_2$, 分支的 $W_1'\le W_2'$).
>
> **定理.** `x-sum` (接口律 X1): 第 0 层上关系推出 `sum` 的值序. `Ωd-self` (接口律 X2 的同层情形, **条件**: 种类的顶对世界单调 `TopMono`, 层合法): $\Omega_t$ 在 $W_1$ 与 $W_2$ 里相关, 两边闭包分支过的层 $g(\mathrm{top}\,\kappa\,W_1')\lhd g(\mathrm{top}\,\kappa\,W_2')$ 不同, 由 `mi` 的跨层证据接住.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Lean.LeanTBase
module OCF.Lean.ValWRel (T : KS) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Lean.LeanTTree
open import OCF.Lean.NegLeanLvVal using (z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; ≤-suc) renaming (_≤_ to _≤ᵥ_)
open Tree T
```

## §1 关系

```agda
module _ {L₁ L₂ : HB L₀}
  (Lo : ∀ {W₁ k₁} → StH W₁ k₁ L₁ → ∀ {k₂ U₁ U₂} → D k₁ U₁ → D k₂ U₂ → Set) where
  data Mx : ∀ {W₁ W₂} → D L₁ W₁ → D L₂ W₂ → Set where
    m1  : ∀ {W₁ W₂} → Mx (n1 {W = W₁}) (n1 {W = W₂})
    m⨾  : ∀ {W₁ W₂} {x y : D L₁ W₁} {x′ y′ : D L₂ W₂} → Mx x x′ → Mx y y′ → Mx (x ⨾ y) (x′ ⨾ y′)
    ml  : ∀ {W₁ W₂} {d : ℕ → D L₁ W₁} {d′ : ℕ → D L₂ W₂} → (∀ n → Mx (d n) (d′ n)) → Mx (nl d) (nl d′)
    mi  : ∀ {W₁ W₂ k₁ k₂} {R₁ : StH W₁ k₁ L₁} {R₂ : StH W₂ k₂ L₂} → k₁ ⊲[ W₂ ] k₂ →
          {v₁ : ∀ {W′} → W₁ ≤ W′ → LgW L₀ W′ → Vs L₁ R₁ W′ → D L₁ W′}
          {v₂ : ∀ {W′} → W₂ ≤ W′ → LgW L₀ W′ → Vs L₂ R₂ W′ → D L₂ W′} →
          (∀ {W₁′ W₂′} (p₁ : W₁ ≤ W₁′) (p₂ : W₂ ≤ W₂′) → W₁′ ≤ W₂′ → (l₁ : LgW L₀ W₁′) (l₂ : LgW L₀ W₂′) → ∀ y₁ y₂ →
             Lo R₁ (outS R₁ y₁) (outS R₂ y₂) → Mx (v₁ p₁ l₁ y₁) (v₂ p₂ l₂ y₂)) →
          Mx (ni R₁ v₁) (ni R₂ v₂)
    mc  : ∀ {W₁ W₂ κ} {z₁ : ZK L₁ κ} {z₂ : ZK L₂ κ}
          {v₁ : ∀ {W′} → W₁ ≤ W′ → LgW L₀ W′ → D L₁ W′} {v₂ : ∀ {W′} → W₂ ≤ W′ → LgW L₀ W′ → D L₂ W′} →
          (∀ {W₁′ W₂′} (p₁ : W₁ ≤ W₁′) (p₂ : W₂ ≤ W₂′) → W₁′ ≤ W₂′ → (l₁ : LgW L₀ W₁′) (l₂ : LgW L₀ W₂′) →
             Mx (v₁ p₁ l₁) (v₂ p₂ l₂)) →
          Mx (nc κ z₁ v₁) (nc κ z₂ v₂)
    mw  : ∀ {W₀ W₁ W₂} {p : W₀ ≤ W₁} {x : D L₁ W₀} {y : D L₂ W₂} → Mx x y → Mx (nw p x) y
    mw′ : ∀ {W₀ W₁ W₂} {p : W₀ ≤ W₂} {x : D L₁ W₁} {y : D L₂ W₀} → Mx x y → Mx x (nw p y)
    mz  : ∀ {W₁ W₂} {y : D L₂ W₂} → Mx (n0 {W = W₁}) y
    mr  : ∀ {W₁ W₂} {x : D L₁ W₁} {y e : D L₂ W₂} → Mx x y → Mx x (y ⨾ e)
    me  : ∀ {W₁ W₂} {x : D L₁ W₁} {y e : D L₂ W₂} → Mx x y → Mx x (e ⨾ y)
    mlₙ : ∀ {W₁ W₂} {x : D L₁ W₁} {d : ℕ → D L₂ W₂} n → Mx x (d n) → Mx x (nl d)

RelA : ∀ {L₁} → AccY L₁ → ∀ {L₂ W₁ W₂} → D L₁ W₁ → D L₂ W₂ → Set
RelA (acc g) = Mx (λ R₁ → RelA (g R₁))
```

## §2 第 0 层: 关系推出 `sum` 的值序 (接口律 X1)

```agda
⊲→≤ : ∀ {w} {a b : HB S⊥} → a ⊲[ w ] b → a ≤ᵥ b
⊲→≤ hself = ≤-refl _
⊲→≤ (hsuc p) = ≤-suc (⊲→≤ p)
⊲→≤ (hlim n p) = ≤l n (⊲→≤ p)
⊲→≤ (hLim {κ = () , _} e p)

sum≥ : ∀ {W} b (x : D₀ W) → b ≤ᵥ sum b x
sum≥ b x = ⊲→≤ {w₀ S⊥} (sum-fst b x)

pt≥ : ∀ {W} b (d : ℕ → D₀ W) n → b ≤ᵥ pt b d n
pt≥ b d zero = ≤-refl b
pt≥ b d (suc n) = ≤-trans (pt≥ b d n) (sum≥ (pt b d n) (d n))

x-sum : ∀ (a : AccY hz) {W₁ W₂} {x : D₀ W₁} {y : D₀ W₂} → RelA a x y → ∀ {b b′} → b ≤ᵥ b′ → sum b x ≤ᵥ sum b′ y
x-pt  : ∀ (a : AccY hz) {W₁ W₂} {d : ℕ → D₀ W₁} {d′ : ℕ → D₀ W₂} → (∀ n → RelA a (d n) (d′ n)) →
        ∀ {b b′} → b ≤ᵥ b′ → ∀ n → pt b d n ≤ᵥ pt b′ d′ n
x-sum (acc g) m1 h = s≤ h
x-sum (acc g) (m⨾ p q) h = x-sum (acc g) q (x-sum (acc g) p h)
x-sum (acc g) (ml hd) h = l≤ (λ n → ≤l n (x-pt (acc g) hd h n))
x-sum (acc g) (mi {R₁ = ()} _ _) h
x-sum (acc g) (mc {κ = inj₁ _} {z₁ = ()} _) h
x-sum (acc g) (mc {κ = inj₂ _} {z₁ = ()} _) h
x-sum (acc g) (mw p) h = x-sum (acc g) p h
x-sum (acc g) (mw′ p) h = x-sum (acc g) p h
x-sum (acc g) {y = y} mz h = ≤-trans h (sum≥ _ y)
x-sum (acc g) (mr {e = e} p) h = ≤-trans (x-sum (acc g) p h) (sum≥ _ e)
x-sum (acc g) (me {e = e} p) h = x-sum (acc g) p (≤-trans h (sum≥ _ e))
x-sum (acc g) {y = nl d} (mlₙ n p) {b′ = b′} h =
  ≤l (suc n) (x-sum (acc g) p (≤-trans h (pt≥ b′ d n)))
x-pt a hd h zero = h
x-pt a hd h (suc n) = x-sum a (hd n) (x-pt a hd h n)
```

## §3 $\Omega_t$ 在两个世界里 (接口律 X2 的同层情形; 条件)

**条件 `TopMono`**: 种类的顶沿世界的序不后退: $W\le W'$ 时 $\mathrm{top}\,\kappa\,W$ 与 $\mathrm{top}\,\kappa\,W'$ 相等, 或在 $W'$ 里是第一位置. 前提可满足: 新种类的顶是世界的第二分量, $W\le W'$ 的第二分量正是这个第一位置 (`topMono-new`, 定理); 对 `step`/`sup` 搭出的结构逐种类成立是判断, 本篇不证.

```agda
TopMono : Set
TopMono = ∀ κ {W W′} → W ≤ W′ → (top L₀ κ W ≡ top L₀ κ W′) ⊎ Pr L₀ κ W′ (top L₀ κ W) (top L₀ κ W′)

topMono-new : ∀ {W W′} → W ≤ W′ → Pr L₀ (inj₂ tt) W′ (top L₀ (inj₂ tt) W) (top L₀ (inj₂ tt) W′)
topMono-new q = proj₂ q

module OmX (tm : TopMono) where
  -- 两个顶给出的层: g (top W₁′) ⊲ g (top W₂′)
  gUp : ∀ κ {g : E L₀ κ → HB L₀} → LgB (hΩ κ g) → ∀ {W₁′ W₂′} → W₁′ ≤ W₂′ → LgW L₀ W₂′ →
        g (top L₀ κ W₁′) ⊲[ W₂′ ] g (top L₀ κ W₂′)
  gUp κ {g} (mo , _) {W₁′} {W₂′} q l₂ with tm κ q
  ... | inj₁ eq = subst (λ c → g (top L₀ κ W₁′) ⊲[ W₂′ ] g c) eq hself
  ... | inj₂ pr = mo l₂ (Bd↑ L₀ q (topBd L₀ κ W₁′)) (topBd L₀ κ W₂′) pr

  Ωd-self : ∀ t → LgB t → (a : AccY t) → ∀ {W₁ W₂} → RelA a (Ωd t {W₁}) (Ωd t {W₂})
  Ωd-self hz lt (acc g) = m1
  Ωd-self (hs b) lt (acc g) = m⨾ m1 (mi hself (λ p₁ p₂ q l₁ l₂ y₁ y₂ r → m1))
  Ωd-self (hl f) lt (acc g) = m⨾ m1 (ml (λ n → mi hself (λ p₁ p₂ q l₁ l₂ y₁ y₂ r → m1)))
  Ωd-self (hΩ κ h) lt (acc g) =
    m⨾ m1 (mc (λ p₁ p₂ q l₁ l₂ → mi (gUp κ lt q l₂) (λ p₁′ p₂′ q′ l₁′ l₂′ y₁ y₂ r → m1)))
```
