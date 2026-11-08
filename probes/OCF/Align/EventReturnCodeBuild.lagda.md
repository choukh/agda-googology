# 原全 H₀ 编码的迁回与读回相容

对任意原 H₀ 输入（包括 Ω 分支），证明迁回后逐枝读回相同。
不证明数据函数的命题等式，也不把这个子语言扩读成任意 ni 的性质。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EventReturnCodeBuild where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; Lg)
open import OCF.Align.HtTowerTy
open import OCF.Align.EvFoldTree
open import OCF.Align.EvFoldRead
open import OCF.Align.HtTowerFRead using (nbA)
open import OCF.Align.EventReturnCodeIf

encoded : ∀ {a H H′} x → Code a H H′ (toD₁ x) (toD₁ x)
encoded hz = cz
encoded (hs x) = ca (encoded x) co
encoded (hl f) = cl (λ n → encoded (f n))
encoded (hΩ tt g) = ck (λ {c} p lc → encoded (g c))

migrated : ∀ {a H H′ H″ x y} → Code a H H′ x y → Code a H″ H′ (drp₁ x) y
migrated cz = cz
migrated co = co
migrated (ca p q) = ca (migrated p) (migrated q)
migrated (cl p) = cl (λ n → migrated (p n))
migrated (ck p) = ck (λ q lc → migrated (p q lc))

nb-shape : ∀ {b b′ s s′} → Shape b b′ →
           (∀ c {v v′} → Shape v v′ → Shape (s c v) (s′ c v′)) →
           ∀ d → Shape (nbA b s d) (nbA b′ s′ d)
nb-shape p q azero = p
nb-shape p q (asuc d) = q d (nb-shape p q d)
nb-shape p q (alim f) = sl (λ n → nb-shape p q (f n))

mutual
  observed : ∀ {a H H′ x y b b′} → (la : Lg a) → Code a H H′ x y → Shape b b′ →
             Shape (rd₁ (la , tt) b x) (rd₁ (la , tt) b′ y)
  observed la cz p = p
  observed la co p = ss p
  observed la (ca {x} {y} {x′} {y′} r s) p =
    observed {x = y} {y = y′} la s (observed {x = x} {y = x′} la r p)
  observed la (cl r) p = sl (λ n → partials la r p n)
  observed {a} la (ck r) p =
    so (nb-shape p (λ c q → observed (lwκ c la) (r (pwκ a c) (lwκ c la)) q))

  partials : ∀ {a H H′ f g b b′} → (la : Lg a) →
             (∀ n → Code a H H′ (f n) (g n)) → Shape b b′ →
             ∀ n → Shape (rdp₁ (la , tt) b f n) (rdp₁ (la , tt) b′ g n)
  partials la r p zero = p
  partials la r p (suc n) = observed la (r n) (partials la r p n)

actual : EncodedMigration
actual = record { encoded = encoded ; migrated = migrated ; observed = observed }

shape-self : ∀ {S} (b : HB S) → Shape b b
shape-self hz = sz
shape-self (hs b) = ss (shape-self b)
shape-self (hl f) = sl (λ n → shape-self (f n))
shape-self (hΩ κ g) = so (λ e → shape-self (g e))

-- 精确消费原 drp₁ 和原 toD₁；不是另造的编码。
encoded-readback : ∀ {a H H′} (la : Lg a) b x →
  Shape (rd₁ {a , H′} (la , tt) b (drp₁ (toD₁ {a , H} x)))
        (rd₁ {a , H′} (la , tt) b (toD₁ x))
encoded-readback la b x = observed la (migrated (encoded x)) (shape-self b)
```

这填满合同且包含全部 Ω 编码；新事件第三层仍需原高阶分支
保持此类输入关系，不能将 `encoded-readback` 当作任意函数的替换律。
