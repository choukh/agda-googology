# 上折: 验收文件

> 验收文件. 判决: 接口 `YiUpIface.Iface` 由 `YiUpFold`, `YiUpLegal` 实填 (`upI`, 编译定理, 对一切带证据的层号); 旧接口 `YiPhiIface.Iface` 也实填 (`upφ`), `KAll upφ` 成立 (`kall-up`).
> 编译定理: 后继层的 Ω 树折到自身, 分支 c 是 `next (Up … β c)` (`self-Ω`), 右加 Ω 树不再是加法 (`self-add`); 上折出的结点都不在顶槽位 (`up-notTop`). 有限测试 (`refl`, `tt`): Ω₂ 下的链 `z₂` 的第 1, 2 步; E2 的结点; 与 `YiPhiFold` 的异同.
> 不陈述值 (值在 `YiUpVal`). 不否定任何路线. 入口: `YiUpFold`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiUpCheck where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; subst; sym)

open import OCF.Lean.YiFreshBlock
open import OCF.Lean.YiFreshFold using (_+_; iter; next; cum; Ωt; ι; eqℕ-refl)
open import OCF.Lean.YiPhiBlock
import OCF.Lean.YiPhiFold as P
import OCF.Lean.YiPhiIface as PI
open import OCF.Lean.YiPhiCheck using (isΩ; isLim)
open import OCF.Lean.YiPhiNegK using (InB; prE; brE; lemB; evc; Kept; kept-self; KAll)
open import OCF.Lean.YiTopDom using (IsTop)
open import OCF.Lean.YiTopE2 using (Occ; here; inS; inL; inΩ; inX; inC; Node; c₀) renaming (LN to LNᴱ)
open import OCF.Lean.YiUpBlock
open import OCF.Lean.YiUpFold
open import OCF.Lean.YiUpLegal
import OCF.Lean.YiUpIface as UI
```

## 接口的实填

嵌入一致与自身行律都是 `refl` (ℕ 极限指定孩子的一条先用 `eqℕ-refl`). `kall` 的证明与 `YiPhiNegK.child-kept` 同文, 保留判定没有改.

```agda
J2-lim : (g : ℕ → L) (ε : Ev (lim g)) (B : Base (lim g)) (n : ℕ) (j : L) (w : j ≤ g n) (β : Tr j)
  (x : Tr (lim g)) (y : Tr (g n))
  → ψs (lim g) ε B j (inl n w) β (up x n y)
  ≡ ψs (g n) (ε n) (dL g ε B n x) j w (ψs (lim g) ε B j (inl n w) β x) y
J2-lim g ε B n j w β x y rewrite eqℕ-refl n = refl

self-up : (ℓ : L) (ε : Ev ℓ) (B : Base ℓ) (β : Tr ℓ) (x : Tr ℓ) (c : Ch ℓ) (y : ChT ℓ c)
  → ψs ℓ ε B ℓ self β (up x c y) ≡ Upc ℓ c (ψs ℓ ε B ℓ self β x) y
self-up ℓ ε B β x c y = refl

child-kept : (a b : L) (ea : Ev a) (eb : EvO a b) (B : Base (a ⊕ b)) (β : Tr a)
  {t : Pos (a ⊕ b)} (G : Br (a ⊕ b) t → Tr (a ⊕ b)) (i : InB a b t) (p : Pos a) → prE i eb ≡ inj₂ p
  → Kept p (ψs (a ⊕ b) (Ev⊕ a b ea eb) B a (self ∙ lift a b) β (Ω t G))
child-kept a b ea eb B β G i p e =
  subst (Kept p)
    (sym (lemB a b ea i eb self (λ q cv → Ω q (λ z → ψs (a ⊕ b) (Ev⊕ a b ea eb) B a (self ∙ lift a b) β (G (cv z)))) _))
    (kept-self a ea (prE i eb) p e (λ q cv z → ψs (a ⊕ b) (Ev⊕ a b ea eb) B a (self ∙ lift a b) β (G (brE i eb (cv z)))) _)

upφ : PI.Iface
upφ = record
  { ψ⊥ = ψ⊥
  ; ψs = ψs
  ; J2-suc  = λ a ε B j w β x y → refl
  ; J2-lim  = J2-lim
  ; J2-limu = λ g ε B j ws β x n y → refl
  ; J2-Ωk   = λ k h ε B j w β x c y → refl
  ; J2-Ωu   = λ k h ε B j ws β x c y → refl
  ; J2⊥-suc = λ a ε B x y → refl
  ; J2⊥-lim = λ g ε B x n y → refl
  ; J2⊥-Ω   = λ k h ε B x c y → refl
  ; mono⊥ = mono⊥
  ; monos = monos
  ; pres⊥ = pres⊥
  ; press = press
  ; tw-leg = twᶜ-leg
  ; EBO-leg = EBOᶜ-leg
  ; kstep = λ n B β x p g → refl
  }

kall-up : KAll upφ
kall-up n B β x c G i p e = child-kept (tw n) (↑ (tw n) c) (Ev-tw n) (evc n c) _ _ G i p e

upI : UI.Iface
upI = record
  { ψ⊥ = ψ⊥
  ; ψs = ψs
  ; J2-suc  = λ a ε B j w β x y → refl
  ; J2-lim  = J2-lim
  ; J2-limu = λ g ε B j ws β x n y → refl
  ; J2-Ωk   = λ k h ε B j w β x c y → refl
  ; J2-Ωu   = λ k h ε B j ws β x c y → refl
  ; J2⊥-suc = λ a ε B x y → refl
  ; J2⊥-lim = λ g ε B x n y → refl
  ; J2⊥-Ω   = λ k h ε B x c y → refl
  ; mono⊥ = mono⊥
  ; monos = monos
  ; pres⊥ = pres⊥
  ; press = press
  ; tw-leg = twᶜ-leg
  ; EBO-leg = EBOᶜ-leg
  ; kstep = λ n B β x p g → refl
  ; self-up = self-up
  ; kall = kall-up
  }
```

塔第 1, 2, 3 项与 Λ 上的自身行律 (接口字段的特例, 逐字写出).

```agda
self-up-tw : (n : ℕ) (B : Base (tw (suc n))) (β x : Tr (tw (suc n))) (c : Tr (tw n)) (y : Tr (tw n ⊕ ↑ (tw n) c))
  → ψs (tw (suc n)) (Ev-tw (suc n)) B (tw (suc n)) self β (up x c y)
  ≡ Up (tw n ⊕ ↑ (tw n) c) (down stop c) (ψs (tw (suc n)) (Ev-tw (suc n)) B (tw (suc n)) self β x) y
self-up-tw n B β x c y = refl

self-up-Λ : (B : Base Λ) (β x : Tr Λ) (n : ℕ) (y : Tr (tw n))
  → ψs Λ Ev-Λ B Λ self β (up x n y) ≡ Up (tw n) (down stop n) (ψs Λ Ev-Λ B Λ self β x) y
self-up-Λ B β x n y = refl
```

## (a) 值的形状

后继层的 Ω 树折到自身: 结点保留, 分支 c 的像是 `next (Up … β c)`; 上折把零送到 β, 后继送到 `next`. 所以分支 c = n 的像是 β 上的 n+1 次 `next`. 原折叠 (`YiFreshValGap.self-Ω`) 这里是 `bs B _ self + Ωt (suc a)`.

```agda
self-Ω : (a : L) (ε : Ev (suc a)) (B : Base (suc a)) (β : Tr (suc a)) →
  ψs (suc a) ε B (suc a) self β (Ωt (suc a))
  ≡ Ω (inj₁ tt) (λ c → next (Up a (down stop tt) β c))
self-Ω a ε B β = refl

self-add : (a : L) (ε : Ev (suc a)) (B : Base (suc a)) (β x : Tr (suc a)) →
  ψs (suc a) ε B (suc a) self β (x + Ωt (suc a))
  ≡ Ω (inj₁ tt) (λ c → next (Up a (down stop tt) (ψs (suc a) ε B (suc a) self β x) c))
self-add a ε B β x = refl

Up-zero : ∀ {ℓ} (j : L) (d : Dn ℓ j) (b : Tr ℓ) → Up j d b zero ≡ b
Up-zero j d b = refl

Up-suc : ∀ {ℓ} (j : L) (d : Dn ℓ j) (b : Tr ℓ) (c : Tr j) → Up j d b (suc c) ≡ next (Up j d b c)
Up-suc j d b c = refl

Up-lim : ∀ {ℓ} (j : L) (d : Dn ℓ j) (b : Tr ℓ) (f : ℕ → Tr j) → Up j d b (lim f) ≡ lim (λ n → Up j d b (f n))
Up-lim j d b f = refl

old-self-Ω : (a : L) (ε : Ev (suc a)) (B : Base (suc a)) (β : Tr (suc a)) →
  P.ψs (suc a) ε B (suc a) self β (Ωt (suc a)) ≡ β + Ωt (suc a)
old-self-Ω a ε B β = refl
```

Ω₂ 下的链. `ψ₀(Ωt 2)` 的根结点的链在第 1 层: 每步是 "折到自身再 `next`", 底是 `Ωt 1`.

```agda
one two : L
one = suc zero
two = suc one

B₁ : Base one
B₁ = dS one tt (B₀ two) zero

d₁ : Dn one zero
d₁ = down stop tt

z₂ : ℕ → Tr one
z₂ = iter (λ c → next (ψs one tt B₁ one self (Ωt one) c)) zero

G2-form : ψ₀ two tt (Ωt two) ≡ lim (cum (λ k → next (ψ⊥ one tt B₁ (z₂ k))))
G2-form = refl

z₂-1 : z₂ 1 ≡ next (Ωt one)
z₂-1 = refl

sq : Tr one → Tr one
sq b = Ω (inj₁ tt) (λ c → next (Up zero d₁ b c))

z₂-2 : z₂ 2 ≡ next (lim (λ n → ψs one tt B₁ one self (Ωt one) (iter (Ωt one +_) (Ωt one) n)))
z₂-2 = refl

z₂-2₀ : ψs one tt B₁ one self (Ωt one) (iter (Ωt one +_) (Ωt one) 0) ≡ sq (Ωt one)
z₂-2₀ = refl

z₂-2₁ : ψs one tt B₁ one self (Ωt one) (iter (Ωt one +_) (Ωt one) 1) ≡ sq (sq (Ωt one))
z₂-2₁ = refl

z₂-2₂ : ψs one tt B₁ one self (Ωt one) (iter (Ωt one +_) (Ωt one) 2) ≡ sq (sq (sq (Ωt one)))
z₂-2₂ = refl
```

对照: 原折叠同一处是加法, 第 n 项多 n+1 个 Ω 树.

```agda
old-z₂-2₁ : P.ψs one tt (B₀ one) one self (Ωt one) (iter (Ωt one +_) (Ωt one) 1)
          ≡ Ωt one + Ωt one + Ωt one
old-z₂-2₁ = refl
```

## (b) E2 的结点

源与 `YiTopE2.occP` 相同: `suc LNᴱ` 层根结点的链第二步的源 `up zero tt (suc (η 1))`, η 1 = `next (Ωt LNᴱ)`; 结点是孩子 c₀ 那一层的 Ω 树的根. 新折叠下它在输出里是 `LNᴱ` 层的结点, 槽位是 `chP LNᴱ c₀` 搬进来的那一个 (恰是 `YiTopE2.couldP` 的槽位); 它所在的位置是结点不是 `up`, 即孩子被折了.

```agda
εN : Ev LNᴱ
εN = proj₂ (proj₂ (Ev-tw 2) (Ωt (tw 1)))

stU : Tr LNᴱ → Tr LNᴱ
stU z = ψs (suc LNᴱ) εN (B₀ _) LNᴱ (ins self) (Ωt LNᴱ) (up zero tt (suc z))

ηU : ℕ → Tr LNᴱ
ηU = iter stU zero

ηU-1 : ηU 1 ≡ next (Ωt LNᴱ)
ηU-1 = refl

occU : Node (suc LNᴱ) (up zero tt (suc (ηU 1))) (chL LNᴱ c₀) (inj₁ (inj₁ tt))
occU = _ , inC (inS (inL 0 (inΩ c₀ (inC here))))

slotU : Pos LNᴱ
slotU = inj₂ (c₀ , inj₂ (inj₁ (inj₁ tt)))

slotU-form : slotU ≡ chP LNᴱ c₀ (inj₁ (inj₁ tt))
slotU-form = refl

keptU : Node LNᴱ (ηU 2) LNᴱ slotU
keptU = _ , inL 0 (inL 0 (inΩ c₀ here))

root-kept : (B : Base LNᴱ) → ψs LNᴱ εN B LNᴱ self (Ωt LNᴱ) (Ωt LNᴱ)
  ≡ Ω (inj₁ (inj₁ tt)) (λ c → ψs LNᴱ εN B LNᴱ self (Ωt LNᴱ) (up zero c (Ωt (chL LNᴱ c))))
root-kept B = refl

isUp : ∀ {P B C D} → T P B C D → Set
isUp (up _ _ _) = ⊤
isUp _          = ⊥

spot-new : isΩ (ψs LNᴱ εN (B₀ _) LNᴱ self (Ωt LNᴱ) (up zero c₀ (Ωt (chL LNᴱ c₀))))
spot-new = tt

spot-old : isUp (P.ψs LNᴱ εN (B₀ _) LNᴱ self (Ωt LNᴱ) (up zero c₀ (Ωt (chL LNᴱ c₀))))
spot-old = tt
```

## (c) 顶槽位

上折出的结点的槽位都经 `chP` 搬进来, 都不是顶槽位 (编译定理, 任意下行链). 所以新折叠的输出离开 `YiTopDom.Top` 域; 上面的 `slotU` 是链里实际出现的一例.

```agda
chP-notTop : (j : L) (c : Ch j) (p : Pos (chL j c)) → IsTop j (chP j c p) → ⊥
chP-notTop (suc a)  _ p ()
chP-notTop (lim g)  n p ()
chP-notTop (Ωₗ k h) c p ()

mv-notTop : ∀ {ℓ j} (d : Dn ℓ j) (q : Pos j) → (IsTop j q → ⊥) → IsTop ℓ (mv d q) → ⊥
mv-notTop stop           q nq = nq
mv-notTop (down {j} d c) q nq = mv-notTop d (chP j c q) (chP-notTop j c q)

up-notTop : ∀ {ℓ j} (d : Dn ℓ j) (c : Ch j) (p : Pos (chL j c)) → IsTop ℓ (mv (down d c) p) → ⊥
up-notTop {j = j} d c p = mv-notTop d (chP j c p) (chP-notTop j c p)

slotU-notTop : IsTop LNᴱ slotU → ⊥
slotU-notTop ()
```

## (d) 与 `YiPhiFold` 的关系 (有限测试)

没有 `up` 的输入上两者相同 (样本: 后继, 自身目标; 没有嵌入的结点折到第 0 层; ℕ 极限层号). 有 `up` 而目标不是自身、孩子里也没有 `up` 的样本也相同. 自身目标上的 `up` 不同.

```agda
same-suc : ψs one tt (B₀ one) one self (Ωt one) (suc (suc zero))
         ≡ P.ψs one tt (B₀ one) one self (Ωt one) (suc (suc zero))
same-suc = refl

same-node : ψ₀ one tt (Ω (inj₁ tt) (λ c → suc zero)) ≡ P.ψ₀ one tt (Ω (inj₁ tt) (λ c → suc zero))
same-node = refl

same-2 : ψ₀ two tt (up (suc zero) tt (up zero tt (suc (suc zero))))
       ≡ P.ψ₀ two tt (up (suc zero) tt (up zero tt (suc (suc zero))))
same-2 = refl

self-differs : ψs one tt (B₀ one) one self (Ωt one) (up zero tt (suc zero))
             ≢ P.ψs one tt (B₀ one) one self (Ωt one) (up zero tt (suc zero))
self-differs e = subst isLim e tt
```
