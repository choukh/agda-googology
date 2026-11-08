# 原事件 Int 的实际低层节点一步

继承 StrRel12Int.IntM 的“低坐标关系—内 Int—前缀—外 Int”机制。
本实验限定原第一层 Ωd 生成的节点；不是完整 Int 的迁回自然性。
关系允许高阶 ni 和 nw，并把异坐标关系放在分支前提中。
不引用函数外延，不把任意 continuation 当作相容函数。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EventReturnInt where

open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Align.CumReadCF using (A; _⊲_; Lg)
open import OCF.Align.HtTowerTy
open import OCF.Align.EvFoldTree
open import OCF.Align.EvFoldRead using (D₁)
open import OCF.Align.EventReturnCodeIf using (Code; cz; co; ca; cl; ck)

data Plain : ∀ {W W′} → D₀ W → D₀ W′ → Set where
  pz : ∀ {W W′} → Plain (n0 {W = W}) (n0 {W = W′})
  po : ∀ {W W′} → Plain (n1 {W = W}) (n1 {W = W′})
  pa : ∀ {W W′} {a b : D₀ W} {a′ b′ : D₀ W′} → Plain a a′ → Plain b b′ → Plain (a ⨾ b) (a′ ⨾ b′)
  pl : ∀ {W W′} {f : ℕ → D₀ W} {g : ℕ → D₀ W′} → (∀ n → Plain (f n) (g n)) → Plain (nl f) (nl g)
  pw : ∀ {U U′ W W′} {a : D₀ U} {b : D₀ U′} {p : U ≤ W} {q : U′ ≤ W′} → Plain a b → Plain (nw p a) (nw q b)

data R (a : A) (H H′ : Hist) : D₁ (a , H) → D₁ (a , H′) → Set where
  rz : R a H H′ n0 n0
  ro : R a H H′ n1 n1
  ra : ∀ {x y x′ y′} → R a H H′ x x′ → R a H H′ y y′ → R a H H′ (x ⨾ y) (x′ ⨾ y′)
  rl : ∀ {f g} → (∀ n → R a H H′ (f n) (g n)) → R a H H′ (nl f) (nl g)
  rw : ∀ {b J J′} {x : D₁ (b , J)} {y : D₁ (b , J′)}
       (p : b ⊲ a) (s : Suf J H) (s′ : Suf J′ H′) → R b J J′ x y →
       R a H H′ (nw (p , s) x) (nw (p , s′) y)
  rk : ∀ {u : ∀ {c} → a ⊲ c → Lg c → D₁ (c , H)}
         {v : ∀ {c} → a ⊲ c → Lg c → D₁ (c , H′)} →
       (∀ {c} (p : a ⊲ c) lc → R c H H′ (u p lc) (v p lc)) → R a H H′ (nκ tt u) (nκ tt v)
  ri : ∀ {u : ∀ {W} → (a , H) ≤ W → LgWε W → D₀ W → D₁ W}
         {v : ∀ {W} → (a , H′) ≤ W → LgWε W → D₀ W → D₁ W} →
       (∀ {b J J′} (p : a ⊲ b) (s : Suf H J) (s′ : Suf H′ J′) (lb : Lg b)
          {x : D₀ (b , J)} {y : D₀ (b , J′)} → Plain x y →
          R b J J′ (u (p , s) (lb , tt) x) (v (p , s′) (lb , tt) y)) →
       R a H H′ (ni (ss hself) u) (ni (ss hself) v)

from-code : ∀ {a H H′ x y} → Code a H H′ x y → R a H H′ x y
from-code cz = rz
from-code co = ro
from-code (ca p q) = ra (from-code p) (from-code q)
from-code (cl p) = rl (λ n → from-code (p n))
from-code (ck p) = rk (λ q lc → from-code (p q lc))

zero-acc : AccY hz
zero-acc = acc (λ ())

one-acc : AccY (hs hz)
one-acc = acc (λ { (ss hself) → zero-acc })

-- 原 Int 在第零层坐标上的实际调用；context 任意，回调是原 Ωd 的 n1。
ZMap : Set
ZMap = ∀ κ → ZE κ hz → ZE κ (hs hz)

Mk : Wε → Set
Mk W = ∀ {V j} → W ≤ V → StH V j hz → StH V j (hs hz)

lift-zero : ∀ {U W} → U ≤ W → LgWε W → ZMap → Mk W → D₀ U → D₀ W → D₁ W
lift-zero q lw ze mk z w = Int zero-acc z q lw tt ze mk (λ _ _ _ → n1) w

lift-related : ∀ {U U′ a H H′} {x : D₀ U} {y : D₀ U′} → Plain x y →
  (q : U ≤ (a , H)) (q′ : U′ ≤ (a , H′)) (la : Lg a) →
  ∀ (ze ze′ : ZMap) (mk : Mk (a , H)) (mk′ : Mk (a , H′)) w w′ →
  R a H H′ (lift-zero q (la , tt) ze mk x w) (lift-zero q′ (la , tt) ze′ mk′ y w′)
lift-related pz q q′ la ze ze′ mk mk′ w w′ = rz
lift-related po q q′ la ze ze′ mk mk′ w w′ = ro
lift-related (pa p r) q q′ la ze ze′ mk mk′ w w′ =
  ra (lift-related p q q′ la ze ze′ mk mk′ w w′) (lift-related r q q′ la ze ze′ mk mk′ _ _)
lift-related (pl p) q q′ la ze ze′ mk mk′ w w′ = rl (λ n → lift-related (p n) q q′ la ze ze′ mk mk′ _ _)
lift-related (pw {p = p} {q = p′} r) q q′ la ze ze′ mk mk′ w w′ = lift-related r (≤tr p q) (≤tr p′ q′) la ze ze′ mk mk′ w w′

node : ∀ {W} → LgWε W → D₁ W → D₁ W
node lw w = Int one-acc (ni (ss hself) (λ _ _ _ → n1)) ≤rf lw tt
  (λ _ z → z) (λ _ r → r) (λ _ _ z → z) w

node-related : ∀ {a H H′ x y} → (la : Lg a) → R a H H′ x y →
  R a H H′ (node (la , tt) x) (node (la , tt) y)
node-related la r = ri (λ p s s′ lb h →
  ra (rw p s s′ r) (lift-related h ≤rf ≤rf lb _ _ _ _ n0 n0))
```

`node-related` 是原 Int 高阶节点的完整异坐标分支证明，内层输入可以是
任意 Plain 相关的原 D₀ 数据。它不覆盖 nε/IWε 的两条历史走法。
