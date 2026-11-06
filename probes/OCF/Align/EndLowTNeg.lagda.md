# `T-Ω` 的值验收 (二): `SumOne` 的精确对应搬不到高度树的 $\Omega_L$

> 不含记号, 不是验收文件. 入口 [EndLowT](EndLowT.lagda.md). 只导入 `CumReadCF`, `CumReadCFEq`, `TLRuleRel`, `TLRuleSum` (都是树侧).
>
> `SumOne` (和 `TLRule`) 的序数值验收走的是**精确对应** `TLRuleRel.Rel L b x y`: 旧树 (`CumReadCF` 的 $\psi$ 折叠的数据树 `O`) 从 $b$ 走差树 $x$ 到 $y$, 模结构等价 `≈`. 节点 `ni` 只有一条规则 `ri`: 分支的读数是一个连续的 $H$, 起点是 $H(\dot\Omega_k)$, $k$ 是节点的层. 每个可数层的 $\Omega_L$ 都对上 $\dot\Omega_L$ (`TLRuleRel.Ω-Rel`). 这能成立是因为 `TLRuleSum` 的 $\Omega_{a+1}$ 是 `n1 ⨾ Dif (a+1)`: 节点之前先走完 $\mathrm{Dif}$, 底已经是 $\Omega_a$.
>
> 高度树的 $\Omega_L$ (`HtFeedTree.Ωd`) 只看最外的构造子: $\Omega_{b+1}$ = `n1 ⨾ ni (ss hself) (λ _ _ _ → n1)`, **节点紧跟在 `n1` 之后**, 底是 $1$.
>
> **定理 (`no-Rel`, `no-Relˡ`).** 对一切层 $L$, 一切底 $b$, 一切终点 $y$, 一切分支 $u$: 只要节点的层 $k\ne0$ (后继或极限), 差树 `n1 ⨾ ni r u` 与任何旧树都没有 `Rel`. 原因: `n1` 之后的点的头是后继 (`n1-hd`), 而 `ri` 要求它 $\approx H(\dot\Omega_k)$, $H$ 连续 (`ContF`) 推出 $H(\dot\Omega_k)$ 的头是节点或极限 (`ni-hd`, `ni-hdˡ`); 头在 `≈` 下不变 (`≈-hd`).
>
> 所以 "照 `SumOneRel`/`Sim`/`Top` 为 `HtFeedFold` 重写" 不能逐字照写: 高度树的 $\Omega_{b+1}$ ($b\ge1$) 在那套关系里没有像. 移植必须换掉参照的读法 (例如把节点的分支从 $0$ 而不是从 $\Omega_k$ 起计, 那样参照树就不再是 $\dot\Omega$, 与 $\psi$ 折叠的比较只能在值上做). 这条否定只针对 `TLRuleRel.Rel` 这一种精确对应, 不否定值层的验收.
>
> 正对照 (`pos`): `TLRuleSum` 自己的 $\Omega_{a+2}$ 有 `Rel` (就是 `Ω-Rel`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EndLowTNeg where

open import Data.Nat using (ℕ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import OCF.Align.CumReadCF
open import OCF.Align.CumReadCFEq using (_≈_; EqL; EqLC; EqR; EqRC; Ω≈; ≈oe)
open import OCF.Align.TLRuleRel using (Rel; rz; rs; rc; rb; rr; rl; rd; ri; ContF; cn; cl; Ω-Rel; emb)
import OCF.Align.TLRuleSum as N
```

## §1 头在 `≈` 下不变

`hd` 看最外的构造子, 懒嵌入 `oe` 透明.

```agda
data Hd : Set where
  h0 hS hL hI : Hd

hd  : ∀ {a} → O a → Hd
hdS : ∀ {L a} (R : Strict a L) → Vs L R → Hd
hdC : ∀ {L a} (P : a ⊲ L) → Vc L P → Hd
hd o0 = h0
hd (os _) = hS
hd (ol _) = hL
hd (oi _ _) = hI
hd (oe R y) = hdS R y
hdS (ss P) y = hdC P y
hdS (sl n P) y = hdC P y
hdC self y = hd y
hdC (suc P) y = hdC P y
hdC (lim n P) y = hdC P y

≈-hd : ∀ {a b} (x : O a) (y : O b) → x ≈ y → hd x ≡ hd y
hdL  : ∀ {L b a} (R : Strict a L) (x : Vs L R) (y : O b) → EqL R x y → hdS R x ≡ hd y
hdLC : ∀ {L b a} (P : a ⊲ L) (x : Vc L P) (y : O b) → EqLC P x y → hdC P x ≡ hd y
hdR  : ∀ {L b a} (x : O a) (R : Strict b L) (y : Vs L R) → EqR x R y → hd x ≡ hdS R y
hdRC : ∀ {L b a} (x : O a) (P : b ⊲ L) (y : Vc L P) → EqRC x P y → hd x ≡ hdC P y

≈-hd (oe R x) y e = hdL R x y e
≈-hd o0 (oe R y) e = hdR o0 R y e
≈-hd (os x) (oe R y) e = hdR (os x) R y e
≈-hd (ol F) (oe R y) e = hdR (ol F) R y e
≈-hd (oi r h) (oe R y) e = hdR (oi r h) R y e
≈-hd o0 o0 e = refl
≈-hd (os x) (os y) e = refl
≈-hd (ol F) (ol G) e = refl
≈-hd (oi r h) (oi r′ h′) e = refl
≈-hd o0 (os y) ()
≈-hd o0 (ol G) ()
≈-hd o0 (oi r h) ()
≈-hd (os x) o0 ()
≈-hd (os x) (ol G) ()
≈-hd (os x) (oi r h) ()
≈-hd (ol F) o0 ()
≈-hd (ol F) (os y) ()
≈-hd (ol F) (oi r h) ()
≈-hd (oi r h) o0 ()
≈-hd (oi r h) (os y) ()
≈-hd (oi r h) (ol G) ()

hdL (ss P) x y e = hdLC P x y e
hdL (sl n P) x y e = hdLC P x y e
hdLC self x y e = ≈-hd x y e
hdLC (suc P) x y e = hdLC P x y e
hdLC (lim n P) x y e = hdLC P x y e

hdR x (ss P) y e = hdRC x P y e
hdR x (sl n P) y e = hdRC x P y e
hdRC x self y e = ≈-hd x y e
hdRC x (suc P) y e = hdRC x P y e
hdRC x (lim n P) y e = hdRC x P y e
```

## §2 `n1` 之后是后继; 层非零的节点之前不是

```agda
n1-hd : ∀ {L b c} → Rel L b N.n1 c → hd c ≡ hS
n1-hd (rs d p) = ≈-hd _ _ d
n1-hd (rb d p D) = n1-hd D
n1-hd (rr {y = y} {y′ = y′} D d p) = trans (sym (≈-hd y y′ d)) (n1-hd D)

-- 节点的层是后继: H 在 Ω̇ (a+1) = oi zero … 上给出节点
ni-hd : ∀ {L a b y} (r : asuc a ≪ L) (u : N.Ws L (≪S r) → N.D L) → Rel L b (N.ni r u) y → hd b ≡ hI
ni-hd {a = a} r u (ri r′ u′ p H d q e₀ C ds) =
  trans (≈-hd _ _ e₀) (≈-hd _ _ (cn C zero g (Ω≈ (asuc a)) (λ {a₁} {a₁′} e → ≈oe a₁ (ss self) a₁′ e)))
  where
  g : O a → O (asuc a)
  g z = oe (ss self) z
ni-hd r u (rb {b = b₁} d p D) = trans (≈-hd _ b₁ d) (ni-hd r u D)
ni-hd r u (rr D d p) = ni-hd r u D

-- 节点的层是极限: H 在 Ω̇ (lim f) = ol … 上给出极限
ni-hdˡ : ∀ {L f b y} (r : alim f ≪ L) (u : N.Ws L (≪S r) → N.D L) → Rel L b (N.ni r u) y → hd b ≡ hL
ni-hdˡ {f = f} r u (ri r′ u′ p H d q e₀ C ds) =
  trans (≈-hd _ _ e₀) (≈-hd _ _ (cl C (λ n → oe (sl n self) (Ω̇ (f n))) (Ω≈ (alim f))))
ni-hdˡ r u (rb {b = b₁} d p D) = trans (≈-hd _ b₁ d) (ni-hdˡ r u D)
ni-hdˡ r u (rr D d p) = ni-hdˡ r u D
```

## §3 否定

```agda
hS≢hI : hS ≡ hI → ⊥
hS≢hI ()

hS≢hL : hS ≡ hL → ⊥
hS≢hL ()

no-Rel : ∀ {L a b y} (r : asuc a ≪ L) (u : N.Ws L (≪S r) → N.D L) → ¬ Rel L b (N.n1 N.⨾ N.ni r u) y
no-Rel r u (rc D₁ D₂) = hS≢hI (trans (sym (n1-hd D₁)) (ni-hd r u D₂))
no-Rel r u (rb d p D) = no-Rel r u D
no-Rel r u (rr D d p) = no-Rel r u D

no-Relˡ : ∀ {L f b y} (r : alim f ≪ L) (u : N.Ws L (≪S r) → N.D L) → ¬ Rel L b (N.n1 N.⨾ N.ni r u) y
no-Relˡ r u (rc D₁ D₂) = hS≢hL (trans (sym (n1-hd D₁)) (ni-hdˡ r u D₂))
no-Relˡ r u (rb d p D) = no-Relˡ r u D
no-Relˡ r u (rr D d p) = no-Relˡ r u D
```

**实例: 高度树的 $\Omega_2$, $\Omega_{\omega+1}$ 搬进 `TLRuleSum` 的差树.** `HtFeedTree.Ωd (hs b)` = `n1 ⨾ ni (ss hself) (λ _ _ _ → n1)`, 节点的层是 $b$. 取 $b=1$ (层 $L=2$) 与 $b=\omega$ (层 $\omega+1$): 同形的差树没有 `Rel`. 正对照 `pos`: `TLRuleSum` 自己的 $\Omega_2$ (`n1 ⨾ Dif 2`, 节点之前有 `Dif 1`) 有 `Rel`.

```agda
two : A
two = asuc (asuc azero)

Ωht₂ : N.D two
Ωht₂ = N.n1 N.⨾ N.ni zero (λ _ → N.n1)

no-Ω₂ : ∀ {b y} → ¬ Rel two b Ωht₂ y
no-Ω₂ = no-Rel zero (λ _ → N.n1)

ωᴬ : A
ωᴬ = alim nat
  where
  nat : ℕ → A
  nat ℕ.zero = azero
  nat (ℕ.suc n) = asuc (nat n)

Ωht-ω+1 : N.D (asuc ωᴬ)
Ωht-ω+1 = N.n1 N.⨾ N.ni zero (λ _ → N.n1)

no-Ωω+1 : ∀ {b y} → ¬ Rel (asuc ωᴬ) b Ωht-ω+1 y
no-Ωω+1 = no-Relˡ zero (λ _ → N.n1)

pos : Rel two o0 (N.Ωd two self tt) (emb self (Ω̇ two))
pos = Ω-Rel two self tt
```
