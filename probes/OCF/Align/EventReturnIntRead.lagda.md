# 含高阶节点的第一层关系：迁回与读回

本文件消费 EventReturnInt 的真实 ni 分支关系；不要求两数据字面相等。
迁回输入时同时搬低坐标，正是原 drp₁ 的逆向输入运输。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EventReturnIntRead where

open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; Lg; lg⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.EvFoldTree
open import OCF.Align.EvFoldRead
open import OCF.Align.EventReturnCodeIf using (Shape; sz; ss; sl; so)
open import OCF.Align.EventReturnCodeBuild using (nb-shape; encoded; shape-self)
open import OCF.Align.EventReturnInt

plain-self : ∀ {W} (x : D₀ W) → Plain x x
plain-self n0 = pz
plain-self n1 = po
plain-self (x ⨾ y) = pa (plain-self x) (plain-self y)
plain-self (nl f) = pl (λ n → plain-self (f n))
plain-self (ni () u)
plain-self (nκ () u)
plain-self (nε κ z u) = ⊥-elim (ze0 κ z)
plain-self (nw p x) = pw (plain-self x)

encoded-zero : ∀ {W W′} c → Plain (toD {W} c) (toD {W′} c)
encoded-zero azero = pz
encoded-zero (asuc c) = pa (encoded-zero c) po
encoded-zero (alim f) = pl (λ n → encoded-zero (f n))

plain-drop : ∀ {U U′ W W′} {x : D₀ U} {y : D₀ U′} → Plain x y →
             Plain (drp {W′ = W} x) (drp {W′ = W′} y)
plain-drop pz = pz
plain-drop po = po
plain-drop (pa p q) = pa (plain-drop p) (plain-drop q)
plain-drop (pl p) = pl (λ n → plain-drop (p n))
plain-drop (pw {a = x} {b = y} p) = plain-drop {x = x} {y = y} p

migrate : ∀ {a H H′ J J′ x y} → R a H H′ x y → R a J J′ (drp₁ x) (drp₁ y)
migrate rz = rz
migrate ro = ro
migrate (ra p q) = ra (migrate p) (migrate q)
migrate (rl p) = rl (λ n → migrate (p n))
migrate (rw p s s′ r) = rw p here here (migrate r)
migrate (rk r) = rk (λ p lc → migrate (r p lc))
migrate (ri r) = ri (λ p s s′ lc h →
  migrate (r p (tp-suf s _) (tp-suf s′ _) lc (plain-drop h)))

mutual
  observe : ∀ {a H H′ x y b b′} → (la : Lg a) → R a H H′ x y → Shape b b′ →
            Shape (rd₁ (la , tt) b x) (rd₁ (la , tt) b′ y)
  observe la rz p = p
  observe la ro p = ss p
  observe la (ra {x} {y} {x′} {y′} r s) p =
    observe {x = y} {y = y′} la s (observe {x = x} {y = x′} la r p)
  observe la (rl r) p = sl (λ n → partials la r p n)
  observe la (rw q s s′ r) p = observe (lg⊲ q la) r p
  observe {a} la (rk r) p =
    so (nb-shape p (λ c q → observe (lwκ c la) (r (pwκ a c) (lwκ c la)) q))
  observe la (ri r) p =
    so (nb-shape p (λ c q → observe la (r _ here here la (encoded-zero c)) q))

  partials : ∀ {a H H′ f g b b′} → (la : Lg a) →
             (∀ n → R a H H′ (f n) (g n)) → Shape b b′ →
             ∀ n → Shape (rdp₁ (la , tt) b f n) (rdp₁ (la , tt) b′ g n)
  partials la r p zero = p
  partials la r p (suc n) = observe la (r n) (partials la r p n)

-- 原编码输入全部实填：先执行真实 Int 节点，再迁回，再读回。
node-encoded : ∀ {a H H′} (la : Lg a) x →
  R a H H′ (node (la , tt) (toD₁ x)) (node (la , tt) (toD₁ x))
node-encoded la x = node-related la (from-code (encoded x))

whole : ∀ {W} → LgWε W → D₁ W → D₁ W
whole lw w = Int one-acc (Ωd (hs hz)) ≤rf lw tt
  (λ _ z → z) (λ _ r → r) (λ _ _ z → z) w

whole-related : ∀ {a H H′ x y} → (la : Lg a) → R a H H′ x y →
  R a H H′ (whole (la , tt) x) (whole (la , tt) y)
whole-related la r = ra r (node-related la (ra r (rw C.self here here ro)))

whole-encoded-observed : ∀ {a H H′} (la : Lg a) b x →
  Shape (rd₁ {a , H} (la , tt) b (whole (la , tt) (toD₁ x)))
        (rd₁ {a , H′} (la , tt) b (whole (la , tt) (toD₁ x)))
whole-encoded-observed la b x = observe la (whole-related la (from-code (encoded x))) (shape-self b)
```

这证明第一层 R 迁回后仍可读回相容，且 R 的实际 ni 生成者已有全 H₀
输入实例。尚未证明原 Int 对任意 R 源及任意相关外回调整体封闭；
该推广的 nκ 句必须同时处理 Cut₀/IW₀，不能由本文件的读回定理倒推。

注意 `migrate` 是两侧都迁回的保持；它不推出左侧迁回而右侧不动。
Plain 只含双侧 nw，完整单侧迁回应改用允许擦除单侧 nw 的坐标关系，
不能把本定理扩读成该字段。这里不修改已冻结的 Plain。
