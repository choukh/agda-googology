# 全部原 Φ 输出都带全分支位置

对任意原底、合法世界及原 San 实填共享接口。不要求输入或种子 Full。
关键在原 nodeG：keep 的坐标转换对全部裸坐标都有旧输入证书；same
链从 k b 开始，种子 b 本身没有直接进入输出；above 再调用低高度折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.CircuitGeneratedBuild where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁)
open import OCF.Lean.CRwBase
import OCF.Lean.ThirdFold as TF
import OCF.Lean.CircuitGeneratedIf as I

module At (U : KS) (w : Wd U) (lw : LgW U w)
  (Sn : TF.San U w lw) where
  open TF U w lw
  open F Sn
  open I.At U w lw

  add : ∀ m a b → Full m a → Full m b → Full m (a ⊞ b)
  add m a hz pa pb = pa
  add m a (hs b) pa pb = add m a b pa pb
  add m a (hl f) pa pb = λ n → add m a (f n) pa (pb n)
  add m a (hΩ κ g) pa (p , pb) = p , λ e → add m a (g e) pa (pb e)

  Good : ∀ {m} → GT m → Set
  Good {m} x = Full m (proj₁ x)

  mul : ∀ {m} (x : GT m) → Good x → Good (limG (mulG x))
  mul x sx = go
    where
    go : ∀ n → Good (mulG x n)
    go zero = sx
    go (suc n) = add _ _ _ (go n) sx

  sums : ∀ {m} (f : ℕ → GT m) → (∀ n → Good (f n)) → Good (limG (ΣG f))
  sums f sf = go
    where
    go : ∀ n → Good (ΣG f n)
    go zero = sf zero
    go (suc n) = add _ _ _ (go n) (sf (suc n))

  chain : ∀ {m} (b : GT m) (k : GT m → GT m) →
    (∀ b′ → Good (k b′)) → Good (limG (chainG b k))
  chain b k sk = go
    where
    go : ∀ n → Good (chainG b k n)
    go zero = sk b
    go (suc n) = add _ _ _ (go n) (sk _)

  node : ∀ {X t A P} (d : Dg X t A P) (pt : t ⊲ᵘ X) (b : GT t) rec dn →
    (∀ t′ pt′ b′ c pc → Good (rec t′ pt′ b′ c pc)) →
    (∀ i u q x → Good (dn i u q x)) → Good (nodeG d pt b rec dn)
  node {t = t} (keep κ p fr a) pt b rec dn hr hd =
    p , λ c → hr t pt b (fr c) (a c)
  node {t = t} (same to a) pt b rec dn hr hd =
    chain b _ (λ b′ → hr t pt b′ (to (proj₁ b′)) (a _ _))
  node (above i u q to a) pt b rec dn hr hd = hd i u q _

  outputs : ∀ m a lm t pt b h nd → Good (Φ m a lm t pt b h nd)
  outputs m a lm t pt b hz nd = tt
  outputs m a lm t pt b (hs h) nd = mul _ (outputs m a lm t pt b h nd)
  outputs m a lm t pt b (hl f) nd = sums _
    (λ n → outputs m a lm t pt b (f n) (nd n))
  outputs m (acc rs) lm t pt b (hΩ κ g) (ev , pg) =
    node (dcg pt lm (cg m κ ev)) pt b _ _
      (λ t′ pt′ b′ c pc → outputs m (acc rs) lm t′ pt′ b′ (g c) (pg c pc))
      (λ i u q x → outputs i (rs i u) (lg↓ u lm) t q b (proj₁ x) _)

  actual : OutputClosure Sn
  actual = record { outputs = outputs }
```

这里证明的是原程序的全部输出，不以改写程序换取证书。Full 是关于
输出的定理，并非要求原 topT 或所有 Gd 输入也落入它。此结果本身不
给任何序数值增长或 EBO 覆盖；原 San 的损失也没有因此消失。
