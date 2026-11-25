# 零常值极限：本轮 Reg 不被结构 Ω 保持

只检查已冻结的 YiRegBase.Reg，不改树、原 Legal 或 Reg。
q=lim const0 与 x=suc q 都满足 Legal、Reg；结构 Ωx 仍满足 Legal，
但其根要求的 Below(suc q,Ωx) 不存在。本篇否定这份 Reg 的全域 Ω 保持，
不否定其它正则性定义或带额外证据的生成域。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiRegZeroLimit where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; subst)
open import OCF.Align.LevelFixCore using (LF; Raw; Cp; Lgl; Gd)
import OCF.Align.LevelFixCore as F
open F using (module G)
open import OCF.Align.LevelFixVal using (Legal)
import OCF.Align.LevelFixVal as V
import OCF.Align.YiLevelBase as Y
open import OCF.Align.YiDispBase using (Edge; Below; one; more; e-suc; e-lim; e-first; e-branch)
open import OCF.Align.YiRegBase using (Reg)

q x : LF
q = F.lim (λ _ → F.zero)
x = F.suc q

q-legal : Legal q
q-legal = (λ _ → V.self) , (λ _ → tt)

x-legal : Legal x
x-legal = q-legal

q-reg : Reg q
q-reg = λ _ → tt

x-reg : Reg x
x-reg = q-reg

q-level x-level : Y.Level
q-level = Y.level q q-legal
x-level = Y.level x x-legal

omega-x-legal : Legal (V.Ω̂ x)
omega-x-legal = V.Legal-Ω̂ x x-legal

top-guard : Gd q (V.cO q) G.top
top-guard = inj₁ refl , tt
```

q 的 top 没有真前驱。若一个合法 raw 极限的某一项包含 top，
其较晚各项由步进向上传；较早各项与 top 在同一合法项下用原 cmpC 比较。
较早项若位于 top 下，只能就是 top。因此全部列项仍包含 top。
这里没有比较两个宽位置或使用裸下标律。

```agda
cp-to-top : ∀ {a : Raw q} → Cp q a G.top → a ≡ G.top
cp-to-top (inj₁ e) = e
cp-to-top (inj₂ ())

top-back : ∀ {a b : Raw q} → Lgl q b → Cp q a b → Cp q G.top b → Cp q G.top a
top-back {b = b} lawful ab tb with F.cmpC q b tb ab lawful
... | inj₁ ta = ta
... | inj₂ at = subst (Cp q G.top) (sym (cp-to-top at)) (inj₁ refl)

top-at-zero : (f : ℕ → Raw q) →
  (∀ n → Cp q (f n) (f (suc n))) → (∀ n → Lgl q (f n)) →
  ∀ m → Cp q G.top (f m) → Cp q G.top (f zero)
top-at-zero f step lawful zero p = p
top-at-zero f step lawful (suc m) p =
  top-at-zero f step lawful m (top-back (lawful (suc m)) (step m) p)

top-forward : (f : ℕ → Raw q) →
  (∀ n → Cp q (f n) (f (suc n))) → Cp q G.top (f zero) →
  ∀ n → Cp q G.top (f n)
top-forward f step p zero = p
top-forward f step p (suc n) = F.Cp-tr q (top-forward f step p n) (step n)

data TopBuilt : Raw q → Set where
  top-built : TopBuilt G.top
  suc-built : ∀ {η} → TopBuilt η → TopBuilt (G.suc η)
  lim-built : ∀ {f} → (∀ n → TopBuilt (f n)) → TopBuilt (G.lim f)

guard-built : (η : Raw q) → Lgl q η → Cp q G.top η → TopBuilt η
guard-built G.zero lawful (inj₁ ())
guard-built G.zero lawful (inj₂ ())
guard-built (G.suc η) lawful (inj₁ ())
guard-built (G.suc η) lawful (inj₂ p) = suc-built (guard-built η lawful p)
guard-built (G.lim f) lawful (inj₁ ())
guard-built (G.lim f) (step , lawful) (inj₂ (m , p)) = lim-built
  (λ n → guard-built (f n) (lawful n)
    (top-forward f step (top-at-zero f step lawful m p) n))
guard-built (G.lc (n , ()) c t g) lawful p
guard-built (G.em n t) lawful (inj₁ ())
guard-built (G.em n t) lawful (inj₂ ())
guard-built G.top lawful p = top-built
```

由此，合法守卫坐标只由 top、后继、极限构成；其读回以 Ωq=lim const1 为底。
下面只读极限的第0支来区分 q，不比较极限函数，也不要求函数外延。

```agda
sample : LF → LF
sample F.zero = F.zero
sample (F.suc t) = F.zero
sample (F.lim f) = f zero
sample (F.lc k c t g) = F.zero

one-not-zero : F.suc F.zero ≡ F.zero → ⊥
one-not-zero ()

suc-injective : ∀ {a b} → F.suc a ≡ F.suc b → a ≡ b
suc-injective refl = refl

read-nonzero : ∀ {η} → TopBuilt η → V.up q η ≡ F.zero → ⊥
read-nonzero top-built ()
read-nonzero (suc-built p) ()
read-nonzero (lim-built p) ()

read-not-q : ∀ {η} → TopBuilt η → V.up q η ≡ q → ⊥
read-not-q top-built e = one-not-zero (cong sample e)
read-not-q (suc-built p) ()
read-not-q (lim-built p) e = read-nonzero (p zero) (cong sample e)

read-not-x : ∀ {η} → TopBuilt η → V.up q η ≡ x → ⊥
read-not-x top-built ()
read-not-x (suc-built p) e = read-not-q p (suc-injective e)
read-not-x (lim-built p) ()

below-suc : ∀ {a b} → Below a (F.suc b) → a ≡ b ⊎ Below a b
below-suc (one e-suc) = inj₁ refl
below-suc (more p e-suc) = inj₂ p

below-lim : ∀ {a f} → Below a (F.lim f) →
  Σ ℕ (λ n → a ≡ f n ⊎ Below a (f n))
below-lim (one (e-lim n)) = n , inj₁ refl
below-lim (more p (e-lim n)) = n , inj₂ p

below-node : ∀ {a k c t g} → Below a (F.lc k c t g) →
  (a ≡ t ⊎ Below a t) ⊎
  Σ (Raw k) (λ η → Σ (Gd k c η) (λ e → a ≡ g η e ⊎ Below a (g η e)))
below-node (one e-first) = inj₁ (inj₁ refl)
below-node (more p e-first) = inj₁ (inj₂ p)
below-node (one (e-branch η e)) = inj₂ (η , e , inj₁ refl)
below-node (more p (e-branch η e)) = inj₂ (η , e , inj₂ p)

no-below-zero : ∀ {a} → Below a F.zero → ⊥
no-below-zero (one ())
no-below-zero (more p ())

x-not-zero : x ≡ F.zero → ⊥
x-not-zero ()

x-not-one : x ≡ F.suc F.zero → ⊥
x-not-one ()

no-below-one : Below x (F.suc F.zero) → ⊥
no-below-one p with below-suc p
... | inj₁ e = x-not-zero e
... | inj₂ r = no-below-zero r

no-below-omega-q : Below x (V.Ω̂ q) → ⊥
no-below-omega-q p with below-lim p
... | n , inj₁ e = x-not-one e
... | n , inj₂ r = no-below-one r

no-below-read : ∀ {η} → TopBuilt η → Below x (V.up q η) → ⊥
no-below-read top-built p = no-below-omega-q p
no-below-read (suc-built b) p with below-suc p
... | inj₁ e = read-not-x b (sym e)
... | inj₂ r = no-below-read b r
no-below-read (lim-built b) p with below-lim p
... | n , inj₁ e = read-not-x (b n) (sym e)
... | n , inj₂ r = no-below-read (b n) r

x-not-omega-q : x ≡ V.Ω̂ q → ⊥
x-not-omega-q ()

no-root-bound : Below x (V.Ω̂ x) → ⊥
no-root-bound p with below-node p
... | inj₁ (inj₁ e) = x-not-omega-q e
... | inj₁ (inj₂ r) = no-below-omega-q r
... | inj₂ (η , e , inj₁ eq) =
  read-not-x (guard-built η (proj₂ e) (proj₁ e)) (sym eq)
... | inj₂ (η , e , inj₂ r) =
  no-below-read (guard-built η (proj₂ e) (proj₁ e)) r

no-reg-omega-x : Reg (V.Ω̂ x) → ⊥
no-reg-omega-x r = no-root-bound (proj₁ r)

OmegaPreservesReg : Set
OmegaPreservesReg = ∀ t → Legal t → Reg t → Reg (V.Ω̂ t)

no-omega-preservation : OmegaPreservesReg → ⊥
no-omega-preservation preserves = no-reg-omega-x (preserves x x-legal x-reg)
```

所有输入前提都有闭实例：q、x 合法且 Reg；top-guard 也表明原分支域非空。
Ωx 的合法性仍由旧定理给出，失败仅在新增 Reg 的根位置义务。
证明没有使用函数外延、UIP、记号、C 线或裸下标律。
这不是实际 EBO 运行反例，也没有说明所有正则性方案或乙路线不可能。
