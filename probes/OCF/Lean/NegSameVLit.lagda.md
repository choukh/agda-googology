# NegSameV (三): `floor-block` 的边界: P2 在基本列都是有限树的一对上成立

> 不含记号. 入口 [NegSameV](NegSameV.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K. 模块参数 `uipC` 是 `Cd` 上的 UIP (条件, 经 `monoX`).
>
> **问题.** `floor-block`, `P2-block` 在 $1+\omega_1\le1+\omega_2$ 这一对上挡住了层反射的关系. 本篇问挡在哪里开始: 去掉 "$1+$", 坐标是 $\omega_1\le\omega_2$ 本身时, 地板的分支是**可比的**, P2 就是 `monoX` 的直接推论.
>
> **定理.**
>
> 1. **`P2-on` (条件 UIP).** 对一切 $b_1\le b_2$ (`LeAt hz`): 若 $\mathrm{gt}(\mathrm{sh}\,b_1)\le_X\mathrm{gt}(\mathrm{sh}\,b_2)$, 则 $k_R\,b_1\le k_R\,b_2$.
> 2. **`gt-⊲` (不用 UIP).** $a\lhd b$ ⟹ $\mathrm{gt}\,a\le_X\mathrm{gt}\,b$.
> 3. **`P2-ω₁₂`, `P2-ω₂₁` (条件 UIP).** 同值不同结构的 $\omega_1,\omega_2$ 上, P2 的两个方向都成立: $k_R\,\omega_1\approx k_R\,\omega_2$.
>
> **后来的情况.** 构造一路证了 `P2` 全体 (`SameVGoal.P2-thm`, 条件 UIP). 本篇的价值只剩: 标出不用跨层关系 (`_≤X_` 就够) 的那部分.
>
> **读法 (判断).** `P2` 的难点不是 "同值不同结构" 本身, 而是**层号**上的同值不同结构: 回灌后的坐标 $c$ 的**后继**位置 $c+1$ 落在 ℕ-极限 $c$ 之上时, 种类 $(c,\Omega_{c+1})$ 的分量随 $c$ 的结构变. 坐标 $\omega_i$ 回灌后是 $\lim$ (有限树), 地板的一切种类的层都有限, 分量字面相同.
>
> **前提实例.** `P2-on` 的前提: `ω≤X` (定理). `uipC`: 同 [NegSameVKr](NegSameVKr.lagda.md).
>
> **只否定什么.** 没有否定; 这是 `floor-block` 的边界. 本篇不说 $1+\omega_1, 1+\omega_2$ 处的 P2 (那一对要跨层).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Lean.CRwBase using (Cd)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
module OCF.Lean.NegSameVLit (uipC : ∀ {x y : Cd} (e e′ : x ≡ y) → e ≡ e′) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (I₁; W₀; leg; Σ₀)
open import OCF.Lean.CRwFold I₁
open import OCF.Lean.ValCRel I₁
open import OCF.Lean.ValCBase I₁
open import OCF.Lean.ValXRel I₁
open import OCF.Lean.ValXTm using (shLaw₁)
open import OCF.Lean.ValXBase I₁ shLaw₁
open import OCF.Lean.ValXMono I₁ uipC shLaw₁ using (monoX)
open import OCF.Lean.ValXGoal using (κΩ; g₀; nd₀; kR)
open import OCF.Lean.ValXP1 uipC using (MoX-gt; MoX-U; U; U-mono; P2)
open import OCF.Lean.NegSameVSpine using (nat; ω₁; ω₂; le₁₂; le₂₁; ≤₀-rf; ≤₀-tr)

S : Cd → Cd
S b = W₀ ⊞ leg b

Wx : Cd → Cd
Wx x = nWE κΩ {W₀} tt x

lW : ∀ x → LgB (Wx x)
lW x = lgE κΩ {W₀} tt x

pW : ∀ x → hz ⊲ Wx x
pW x = ptE κΩ {W₀} tt (z⊲ᴮ W₀) x

pg₀ : PGt W₀ κΩ g₀
pg₀ = proj₂ nd₀
```

## §1 `P2-on`

```agda
P2-on : ∀ b₁ b₂ → LeAt hz b₁ b₂ → gt (S b₁) ≤X gt (S b₂) → LeAt hz (kR b₁) (kR b₂)
P2-on b₁ b₂ le r = monoX (wf bX hz) (wf bX hz) {Wx b₁} {Wx b₂} (lW b₁) (lW b₂)
  (nW-mono κΩ tt tt (L.≤-refl hz W₀) le) (pW b₁) (pW b₂)
  (moZ b₁ , moZ b₂ , Rel.z≤ , le)
  (g₀ (S b₂)) (pgE κΩ {W₀} tt pg₀ b₁) (pgE κΩ {W₀} tt pg₀ b₂)
  (MoX-U topL (gt (S b₁)) (MoX-gt (S b₁))) (MoX-U topL (gt (S b₂)) (MoX-gt (S b₂)))
  (U-mono topL r)
```

## §2 地板沿第一位置单调; 有限树

```agda
gt-⊲ : ∀ {a b : Cd} → a ⊲ b → gt a ≤X gt b
gt-⊲ {a} hself = ≤X-refl (gt a)
gt-⊲ (hsuc {b = b} p) = ≤X-trans (gt-⊲ p) (≤X⊞ (gt b) _)
gt-⊲ (hlim n p) = ≤l n (gt-⊲ p)
gt-⊲ (hLim {κ = ()} _ _)

data Fin : Cd → Set where
  fz : Fin hz
  fs : ∀ {x} → Fin x → Fin (hs x)

fin-nat : ∀ n → Fin (nat n)
fin-nat zero = fz
fin-nat (suc n) = fs (fin-nat n)

fin-⊞ : ∀ {a b} → Fin a → Fin b → Fin (a ⊞ b)
fin-⊞ fa fz = fa
fin-⊞ fa (fs fb) = fs (fin-⊞ fa fb)

fin-leg : ∀ {a} → Fin a → Fin (leg a)
fin-leg fz = fz
fin-leg (fs f) = fs (fin-leg f)

fin-Σ : ∀ (f : ℕ → Cd) → (∀ n → Fin (f n)) → ∀ n → Fin (Σ₀ f n)
fin-Σ f v zero = v 0
fin-Σ f v (suc n) = fin-⊞ (fin-Σ f v n) (v (suc n))

⊲-hs : ∀ {a b} → Fin b → a ⊲ b → hs a ⊲ hs b
⊲-hs fb hself = hself
⊲-hs (fs fb) (hsuc p) = hsuc (⊲-hs fb p)

≤→⊲fin : ∀ {a b} → Fin b → LeAt hz a b → a ⊲ b
≤→⊲fin {b = b} fb Rel.z≤ = z⊲ᴮ b
≤→⊲fin (fs fb) (Rel.s≤s p) = ⊲-hs fb (≤→⊲fin fb p)
≤→⊲fin (fs fb) (Rel.≤s p) = hsuc (≤→⊲fin fb p)
```

## §3 实例

坐标 $\omega_i$ 回灌后是有限树的 ℕ-极限; 在这两棵树的项之间取 `leg` 单调的现成结果 (`ShLaw` 的 `shM`), 再读成字面的 $\lhd$.

```agda
fS : ∀ {g : ℕ → Cd} → (∀ n → Fin (g n)) → ∀ n → Fin (W₀ ⊞ Σ₀ (λ k → leg (g k)) n)
fS {g} v n = fin-⊞ (fs fz) (fin-Σ (λ k → leg (g k)) (λ k → fin-leg (v k)) n)

gt-lim : ∀ {f g : ℕ → Cd} (σ : ℕ → ℕ) → Inc σ → (∀ n → Fin (g n)) → (∀ n → LeAt hz (f n) (g (σ n))) →
         gt (hl f) ≤X gt (hl g)
gt-lim σ i v h = l≤l σ i (λ n → gt-⊲ (≤→⊲fin (v (σ n)) (h n)))

open ShLaw shLaw₁ using (shM)

-- shM 给出回灌后的 ≤; 把它拆成项之间的比较
no-fin : ∀ {f : ℕ → Cd} {y} → Fin y → ¬ LeAt hz (hl f) y
no-fin (fs fy) (Rel.≤s p) = no-fin fy p

le-hl : ∀ {f g : ℕ → Cd} → (∀ n → Fin (g n)) → LeAt hz (hl f) (hl g) → gt (hl f) ≤X gt (hl g)
le-hl vg (Rel.l≤l σ i h) = gt-lim σ i vg h
le-hl vg (Rel.≤l n p) = ⊥-elim (no-fin (vg n) p)

ω≤X : ∀ {b₁ b₂} → (b₁ ≡ ω₁ × b₂ ≡ ω₂) ⊎ (b₁ ≡ ω₂ × b₂ ≡ ω₁) → LeAt hz b₁ b₂ → gt (S b₁) ≤X gt (S b₂)
ω≤X (inj₁ (refl , refl)) p =
  le-hl (fS (λ n → fin-nat (suc n))) (shM (L.≤-refl hz W₀) p)
ω≤X (inj₂ (refl , refl)) p =
  le-hl (fS fin-nat) (shM (L.≤-refl hz W₀) p)

P2-ω₁₂ : LeAt hz (kR ω₁) (kR ω₂)
P2-ω₁₂ = P2-on ω₁ ω₂ le₁₂ (ω≤X (inj₁ (refl , refl)) le₁₂)

P2-ω₂₁ : LeAt hz (kR ω₂) (kR ω₁)
P2-ω₂₁ = P2-on ω₂ ω₁ le₂₁ (ω≤X (inj₂ (refl , refl)) le₂₁)
```

## 结论 (按档)

- **[条件定理, 条件: `Cd` 上的 UIP]** **`P2-on`**, **`P2-ω₁₂`**, **`P2-ω₂₁`**.
- **[定理, 不用 UIP]** `gt-⊲`, `≤→⊲fin`, `ω≤X`.
- **[判断]** P2 的难点在层号上的同值不同结构 (后继落在 ℕ-极限之上).
