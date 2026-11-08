# 扩大外层世界时保留受限树

固定界不能容纳全部原地板，并不等于已有受限树不能扩大世界。
这里对同一高度证明：可入证据随世界扩大搬运，分支坐标不变；
第一位置与合法性保持。擦除后的树逐构造子双模拟，不使用函数外延。
由双模拟导出既有值关系 `≤ᵛ` 的双向比较。
这不是折叠与搬运交换的定理，也没有给无界地板的统一构造。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.FrozenWorldLift where

open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdIf using (Tw; Pos)
open import OCF.Lean.FrozenOmegaIf
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; s≤s; l≤; ≤l; Ω≤Ω)

position-up : ∀ {U w w′} → _≤w_ U w w′ → ∀ m κ →
  Pos U w m κ → Pos U w′ m κ
position-up q hz κ p = tt
position-up q (hs m) (inj₁ κ) p = position-up q m κ p
position-up q (hs m) (inj₂ _) p = tt
position-up q (hl f) (n , κ) p = position-up q (f n) κ p
position-up {U} q (hΩ κ g) (c , j) (b , p) =
  Bd↑ U q b , position-up q (g c) j p

module Lift {U : KS} {w w′ : Wd U} (q : _≤w_ U w w′) (m : HB U) where
  lift : HB (SafeTw U w m) → HB (SafeTw U w′ m)
  lift hz = hz
  lift (hs a) = hs (lift a)
  lift (hl f) = hl (λ n → lift (f n))
  lift (hΩ (κ , p) g) = hΩ (κ , position-up q m κ p) (λ c → lift (g c))

  first : ∀ {a b v} → a ⊲[ v ] b → lift a ⊲[ v ] lift b
  first hself = hself
  first (hsuc p) = hsuc (first p)
  first (hlim n p) = hlim n (first p)
  first (hLim e p) = hLim e (first p)

  legal : ∀ a → LgB a → LgB (lift a)
  legal hz l = tt
  legal (hs a) l = legal a l
  legal (hl f) (s , l) = (λ n → first (s n)) , (λ n → legal (f n) (l n))
  legal (hΩ (κ , p) g) (s , l) =
    (λ lv e e′ r → first (s lv e e′ r)) , (λ lv e → legal (g _) (l lv e))

-- 强于有限深度测试：所有分支递归地同形。
data Same {S : KS} : HB S → HB S → Set where
  zz : Same hz hz
  ss : ∀ {a b} → Same a b → Same (hs a) (hs b)
  ll : ∀ {f g} → (∀ n → Same (f n) (g n)) → Same (hl f) (hl g)
  oo : ∀ {κ f g} → (∀ c → Same (f c) (g c)) → Same (hΩ κ f) (hΩ κ g)

erase-lift : ∀ {U w w′} (q : _≤w_ U w w′) m (a : HB (SafeTw U w m)) →
  Same (erase a) (erase (Lift.lift q m a))
erase-lift q m hz = zz
erase-lift q m (hs a) = ss (erase-lift q m a)
erase-lift q m (hl f) = ll (λ n → erase-lift q m (f n))
erase-lift q m (hΩ (κ , p) g) = oo (λ c → erase-lift q m (g c))

same-value : ∀ {S} {a b : HB S} → Same a b → a ≤ᵛ b
same-value zz = z≤
same-value (ss p) = s≤s (same-value p)
same-value (ll p) = l≤ (λ n → ≤l n (same-value (p n)))
same-value (oo p) = Ω≤Ω (λ c → same-value (p c))

same-sym : ∀ {S} {a b : HB S} → Same a b → Same b a
same-sym zz = zz
same-sym (ss p) = ss (same-sym p)
same-sym (ll p) = ll (λ n → same-sym (p n))
same-sym (oo p) = oo (λ c → same-sym (p c))

erase-lift≤ : ∀ {U w w′} (q : _≤w_ U w w′) m (a : HB (SafeTw U w m)) →
  erase a ≤ᵛ erase (Lift.lift q m a)
erase-lift≤ q m a = same-value (erase-lift q m a)

lift-erase≤ : ∀ {U w w′} (q : _≤w_ U w w′) m (a : HB (SafeTw U w m)) →
  erase (Lift.lift q m a) ≤ᵛ erase a
lift-erase≤ q m a = same-value (same-sym (erase-lift q m a))

-- 非空实例的外层世界：界从 1 扩到 2。
U = step S⊥
M : HB U
M = hΩ (inj₂ tt) up
w₁ w₂ : Wd U
w₁ = tt , hs hz
w₂ = tt , hs (hs hz)
growth : _≤w_ U w₁ w₂
growth = tt , hsuc hself
lw₁ : LgW U w₁
lw₁ = tt , tt
lw₂ : LgW U w₂
lw₂ = tt , tt

module Grow = Lift growth M
```

`growth` 的两端都是合法世界，公共高度 M 没有改变。上述一般定理
不要求判等、不比较裸坐标，不改变坐标的类型或分支函数的定义域。
实例输入可直接取 `FrozenOmegaClosed.input`，其世界就是 w₁；本模块
不导入该闭项，避免把其末层兜底折叠混入搬运定义。

翻译账：搬运由已有 `Bd↑` 逐构造子推出，没有新增记号式规则。
尚需的关键定理是折叠对这些搬运的关系；不能由本篇推断值强度。
