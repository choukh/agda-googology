# 第一路径守卫的边界: 编译过的否定

> 不含记号. 结论写在 [DomFold](DomFold.lagda.md). 这些定理**只说第一路径守卫 `Fg` 窄**, 不否定别的守卫.
>
> - `no-fg-Ω3-Ω2`: `no-WFˢ-Ω⁺` 的反例不满足新守卫. 所以旧否定不适用, 新定理 `WF-Ωᶠ` 与它不矛盾.
> - `no-fg-1-Ω₁`: $1$ 不经第一路径在 $\Omega_1$ 之下. 所以自然数目标若走路径穿过 $\Omega_2$ 的分支, 地板 $k+1$ 就把 $\Omega_1$ 与绝大多数分支排除. 这是 `tn n` (目标不走路径) 的来历.
> - `first-Ω₁`: 经第一路径在 $\Omega_1$ 之下的只有 $0$. **所以第 1 层的有界比较 `bd′` 看不到 $\Omega_1$ 的初始段**, 与 [Barrier](../Barrier.lagda.md) 的前提 ("以 `Ordᴰ` 为精确初始段, 含 $\Omega$-共尾元, 有有界三歧") 不是同一件事. 这句对照是判断.
> - `no-tn-ω⁺`: **$\Omega_{\Omega_\eta}$ 的具体卡点之一.** `tn n` 能用, 是因为节点的层与自然数目标可以结构比较 (`natCmp`). 把目标换成 $\omega+1$, 这个比较就是 WLPO (与 [ScafOmega2Family](ScafOmega2Family.lagda.md) 的 `no-read-ᴵ` 同形, 这里在 `OCF.Free.Level` 上重证, 因为那个文件的导入闭包不干净; `flag` 一组逐字取自 [LvIRNeg](LvIRNeg.lagda.md)). 所以 $\psi_{\omega+1}$ 的目标只能走路径, 而走路径就回到 `no-fg-1-Ω₁`, `no-fg-floor`.
> - `chain-stuck`: 上一条落到这棵树上. 同键的活帧在 $\Omega_1+3$ 时, $\psi_0(\Omega_{\Omega_2})$ 的闭包的下界就是 $\Omega_1+3$ (`Yₑ`), 链点 `Lv₅` 过不了这个守卫. 定理, 无条件.
> - `below-floor`, `no-fg-floor`: **第一个障碍.** $\Omega_1+3$ 在 $\gamma_1=\psi_1(\Omega_{\Omega_1})$ 之下 (带分支的路径), 但不经第一路径. 所以同键的帧在 $\Omega_1+3$ 时, 新闭包的下界 `Bd` 把链点 $\gamma_1$ 排除: 链读回成分支的证书在这里给不出. 真闭包不受影响, 分支集仍共尾 (判断). 带链的闭包 (`oĉ`, 目标低于 `ix`) 受影响.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.DomFoldNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
open import OCF.Align.GuardTightCum using (Ordᴵ; _<ᴵ_; _⊑ᴵ_; natᴵ; Ω; _+_; add; Ordᶜ; suc; zero; lim; limᵢ; s⊑; z≅; add-≅; Ω-refl)
open import OCF.Align.GuardTightLv
open Lv Dom₀ using (LG; _≈_; _≪_; _≺ᶠ_; preᶠ; _<_; Below; pre; fst; bra; Cfˢ; s≈; z≈; o≈; l≈)
import OCF.Align.GuardTightLv as GL
private module LL = Lv Dom₀
import OCF.Align.GuardTightUni as Uni
private module U = Uni Dom₀
open U using (rb₁; F; Lv₅; Cf-Lv₅)
open import OCF.Align.GuardTightRd using (module RdIter)
open import OCF.Align.GuardTightFeed using (Cf-Ωᴸ)
open import OCF.Align.DomFoldNext using (module FgOf)
open FgOf Dom₀ using (Fg)
open import Data.Maybe using (just; nothing)
open import Data.Unit using (tt)
open import OCF.Align.DomFoldDom using (DomX; X₀)
open import OCF.Align.DomFoldNext using (module Next)
import OCF.Align.DomFoldBase as DBase
import OCF.Align.DomFoldTree as DTree
open import OCF.Align.GuardTightFeed using (ofL; ofL≈⁻; pull)
open import Data.Bool using (Bool; true; false; _∨_)
open import Relation.Nullary using (¬_)
open import OCF.Free.Level using (_≅ᴵ_; _≺ᴵ_; via; z⊑; l≅; s≅; l⊑; ωᴵ; ⊑ᴵ-trans; ⊑ᴵ-refl; Sim→⊑ᴵ; ≺ᴵ-irrefl; ≺ᴵ-respʳ; <ᴵ-trans; ≅ᴵ-refl; ≅ᴵ-sym)
```

## §1 反例不满足新守卫

```agda
Ω₁L : LG
Ω₁L = rb₁ (Ω (suc zero))

Ω₁·2 : LG
Ω₁·2 = rb₁ (Ω (suc zero) + Ω (suc zero))

Ω₁+3 : LG
Ω₁+3 = LL.suc (LL.suc (LL.suc Ω₁L))

-- 经第一路径在 Ω₁ 之下的只有 0
first-Ω₁ : ∀ {a} → a ≪ Ω₁L → a ≡ LL.zero
first-Ω₁ (LL.fst LL.zero) = refl

no-fg-1-Ω₁ : Fg (LL.suc LL.zero) Ω₁L → ⊥
no-fg-1-Ω₁ (inj₁ ())
no-fg-1-Ω₁ (inj₂ (preᶠ d (LL.fst LL.zero))) with d
... | ()

no-Ω+3-lc : ∀ {a} → a ≈ Ω₁+3 → a ≪ Ω₁L → ⊥
no-Ω+3-lc d (LL.fst LL.zero) with d
... | ()

no-fg-Ω3-Ω2 : Fg Ω₁+3 Ω₁·2 → ⊥
no-fg-Ω3-Ω2 (inj₁ ())
no-fg-Ω3-Ω2 (inj₂ (preᶠ d (LL.fst LL.zero))) with d
... | ()
no-fg-Ω3-Ω2 (inj₂ (preᶠ d (LL.fst (LL.suc r)))) = no-Ω+3-lc (LL.≈-sym d) r
```

## §2 第一个障碍

$\gamma_1$ 的第一路径: 第一支是 $\lim_n\Omega_1\cdot n$, $\Omega_1\cdot(k+2)$ 的第一支是 $\Omega_1\cdot(k+1)+1$. 所以第一路径只经过 $\Omega_1\cdot m$ 与 $0$, 碰不到 $\Omega_1+3$.

```agda
open RdIter using (c; Y; Ys; eqL; eqI)

Y₀ : ℕ → Ordᶜ (suc zero)
Y₀ k = Y k zero

notSuc : ∀ k → rb₁ (Y₀ k) ≈ Ω₁+3 → ⊥
notSuc zero ()
notSuc (suc k) d with subst (λ z → rb₁ z ≈ Ω₁+3) (eqL k) d
... | ()

nofirst : ∀ k {a} → a ≈ Ω₁+3 → a ≪ rb₁ (Y₀ k) → ⊥
stepF : ∀ k {a} → a ≈ Ω₁+3 → a ≪ LL.suc (rb₁ (Y₀ k)) → ⊥
stepL : ∀ k {a} → a ≈ Ω₁+3 → a ≪ rb₁ (limᵢ zero (Y k)) → ⊥

nofirst zero d r = no-Ω+3-lc d r
nofirst (suc k) d r = stepL k d (subst (λ z → _ ≪ rb₁ z) (eqL k) r)

stepF k d LL.zero = notSuc k d
stepF k d (LL.suc r) = nofirst k d r

stepL k d (LL.fst r) = stepF k d (subst (λ z → _ ≪ rb₁ z) (Ys k zero) r)

no-fg-floor : Fg Ω₁+3 Lv₅ → ⊥
no-fg-floor (inj₁ ())
no-fg-floor (inj₂ (preᶠ d (LL.fst (LL.fst (LL.lim zero ())))))
no-fg-floor (inj₂ (preᶠ d (LL.fst (LL.fst (LL.lim (suc k) r))))) = nofirst k (LL.≈-sym d) (subst (λ z → _ ≪ rb₁ z) (eqI k) r)

-- 但它确实在 Lv₅ 之下: 路径穿过分支 4
self-3 : Ω₁+3 ≈ Ω₁+3
self-3 = s≈ (s≈ (s≈ (proj₂ Cf-Ωᴸ)))

e₄ : suc zero ⊑ᴵ natᴵ 4
e₄ = s⊑ z≅ (suc (suc (suc zero)))

below-floor : Below Ω₁+3 Lv₅
below-floor = pre self-3 (LL.fst (LL.fst (LL.lim 3 (LL.fst (LL.suc (LL.bra (natᴵ 4) e₄ LL.zero))))))
```

## §3 旧守卫推不出新守卫, 新守卫推出旧守卫

`fg→⊑ⁿ`: 新守卫强于旧守卫. 反方向的反例就是 `below-floor`, `no-fg-floor`.

```agda
fg→⊑ⁿ : ∀ {a b} → b ≈ b → Fg a b → a LL.⊑ⁿ b
fg→⊑ⁿ sf f = LL.⊴→⊑ⁿ (FgOf.fg→⊴ Dom₀ sf f)
```

## §4 不走路径的目标止于 $\omega$

`natCmp` ([DomFoldTree](DomFoldTree.lagda.md)) 对自然数目标成立, 只读层的结构. 目标 $\omega$ 也还行: 折叠只要分 "节点在目标之下" 与 "否则", 下面只有字面的自然数. **目标 $\omega+1$ 不行:** 下面还有 $\omega$ 本身, 判断 $y_s\cong\omega$ 就是 WLPO. 反例族与 [ScafOmega2Family](ScafOmega2Family.lagda.md) §1 逐字同形.

```agda
WLPO : Set
WLPO = ∀ (s : ℕ → Bool) → (∀ n → s n ≡ false) ⊎ ¬ (∀ n → s n ≡ false)

flag : (ℕ → Bool) → ℕ → Bool
flag s zero    = s zero
flag s (suc n) = flag s n ∨ s (suc n)

flag-false : ∀ s → (∀ n → s n ≡ false) → ∀ n → flag s n ≡ false
flag-false s e zero    = e zero
flag-false s e (suc n) rewrite flag-false s e n | e (suc n) = refl

∨-true : ∀ b → (b ∨ true) ≡ true
∨-true true  = refl
∨-true false = refl

flag-true : ∀ s n → s n ≡ true → flag s n ≡ true
flag-true s zero    p = p
flag-true s (suc n) p rewrite p = ∨-true (flag s n)

flag→s : ∀ s → (∀ n → flag s n ≡ false) → ∀ n → s n ≡ false
flag→s s e n with s n in sn
... | false = refl
... | true  with trans′ (sym (flag-true s n sn)) (e n) where
  trans′ : {x y z : Bool} → x ≡ y → y ≡ z → x ≡ z
  trans′ refl q = q
... | ()

plusᴵ : Ordᴵ → ℕ → Ordᴵ
plusᴵ a zero    = a
plusᴵ a (suc n) = suc (plusᴵ a n)

ωfᴵ : Ordᴵ → Ordᴵ
ωfᴵ a = lim (plusᴵ a) (λ n → Sim→⊑ᴵ suc)

stepᴵ : Bool → Bool → Ordᴵ → ℕ → Ordᴵ
stepᴵ true  _     p n       = suc p
stepᴵ false true  p n       = ωfᴵ p
stepᴵ false false p zero    = p
stepᴵ false false p (suc n) = suc p

hᴵ : (ℕ → Bool) → ℕ → Ordᴵ
hᴵ s zero    = stepᴵ false (s zero) zero zero
hᴵ s (suc n) = stepᴵ (flag s n) (s (suc n)) (hᴵ s n) (suc n)

step-⊑ : ∀ b c p n → p ⊑ᴵ stepᴵ b c p (suc n)
step-⊑ true  c     p n = Sim→⊑ᴵ suc
step-⊑ false true  p n = Sim→⊑ᴵ (lim 0)
step-⊑ false false p n = Sim→⊑ᴵ suc

yᴵ : (ℕ → Bool) → Ordᴵ
yᴵ s = lim (hᴵ s) (λ n → step-⊑ (flag s n) (s (suc n)) (hᴵ s n) n)

ω⁺ : Ordᴵ
ω⁺ = suc ωᴵ

h-false : ∀ s → (∀ n → s n ≡ false) → ∀ n → hᴵ s n ≅ᴵ natᴵ n
h-false s e zero rewrite e zero = z≅
h-false s e (suc n) rewrite flag-false s e n | e (suc n) = s≅ (h-false s e n)

y-false : ∀ s → (∀ n → s n ≡ false) → yᴵ s ≅ᴵ ωᴵ
y-false s e = l≅ (h-false s e)

h-true : ∀ s n → flag s n ≡ true → hᴵ s n ≅ᴵ natᴵ n → ⊥
h-true s zero p e with s zero
h-true s zero p () | true
h-true s (suc n) p e with flag s n in fe | s (suc n)
h-true s (suc n) p (s≅ e) | true  | c = h-true s n fe e
h-true s (suc n) p ()     | false | true

nat-sub : ∀ m {a} → a <ᴵ natᴵ m → Σ ℕ λ k → a ≡ natᴵ k
nat-sub (suc m) zero    = m , refl
nat-sub (suc m) (suc q) = nat-sub m q

lim≠nat : ∀ k {f t} → lim f t ≡ natᴵ k → ⊥
lim≠nat zero    ()
lim≠nat (suc k) ()

lim≮nat : ∀ m {f t} → lim f t <ᴵ natᴵ m → ⊥
lim≮nat m q with nat-sub m q
... | k , e = lim≠nat k e

read-yes : ∀ s → yᴵ s ≺ᴵ ω⁺ → ∀ n → flag s n ≡ false
read-yes s (via (l≅ e) zero) n with flag s n in fe
... | false = refl
... | true  = ⊥-elim (h-true s n fe (e n))
read-yes s (via (l≅ e) (suc (lim m q))) n = ⊥-elim (lim≮nat m q)

-- 不走路径的比较: 层 a 严格在目标 τ 的字面之下, 或者 τ 在 a 之下
NoPath : Ordᴵ → Set
NoPath τ = ∀ a → Below (ofL a) (ofL τ) ⊎ (τ ⊑ᴵ a)

toFrom : ∀ {a τ} → Below (ofL a) (ofL τ) → a ≺ᴵ τ
toFrom {a} {τ} (pre d r) with pull τ r
... | a′ , refl , q = via (ofL≈⁻ d) q

no-tn-ω⁺ : NoPath ω⁺ → WLPO
no-tn-ω⁺ d s with d (yᴵ s)
... | inj₁ b = inj₁ (flag→s s (read-yes s (toFrom b)))
... | inj₂ (s⊑ e q) = inj₂ (λ af → ≺ᴵ-irrefl (≺ᴵ-respʳ (via e q) (y-false s af)))
```

## §5 第一个障碍落到树上

`Yₑ`: 第 1 层的闭包 $\Omega_2$, 目标 0, 外面有一个同键的活帧, 分支值 $\Omega_1+3$ (`St` 给证据). 这是 $W$ 那种位置的最小形式. `lowB Yₑ` 是输出闭包的下界. **定理 `chain-stuck`: 链点 `Lv₅` 不满足这个下界.** 对照: `below-floor` 说旧守卫 `⊑ⁿ` 放得过它, 而 `no-WFˢ-Ω⁺` 说旧守卫没有 `WFˢ`. 所以两个守卫各败一边, 这是当前设计的边界, 不是对一切设计的否定.

```agda
private
  X₁ : DomX
  X₁ = Next.X′ X₀
  module N₀ = Next X₀
  module T₁ = DTree X₁
  module B₁ = DBase X₁

x₃ᵍ : N₀.GLv
x₃ᵍ = Ω₁+3 , proj₁ Cf-Ωᴸ , self-3

sx₃ᵍ : N₀.GLv
sx₃ᵍ = LL.suc Ω₁+3 , proj₁ Cf-Ωᴸ , s≈ self-3

e₃ : Fg Ω₁L Ω₁+3
e₃ = inj₂ (preᶠ (proj₂ Cf-Ωᴸ) (LL.suc (LL.suc LL.zero)))

E₀ : N₀.L₁.Ents
E₀ = N₀.L₁.∅ (inj₂ sx₃ᵍ)

P₀ : N₀.L₁.Cp (N₀.emb Ω₁+3) N₀.Ωᶠ
P₀ = N₀.L₁.bra (inj₂ x₃ᵍ) e₃ N₀.L₁.self

tcΩ : B₁.Tc N₀.Ωᶠ
tcΩ = B₁.Tc-id N₀.Ωᶠ

module F = T₁.Fold N₀.Ωᶠ N₀.WF-Ωᶠ N₀.self-Ωᶠ tcΩ

-- 把活帧放到闭包的环境里: 闭包的地板只读它自己环境里的帧
live : T₁.O N₀.Ωᶠ N₀.L₁.tz → T₁.O N₀.Ωᶠ (B₁.pF P₀)
live (T₁.ocl P k cv t g) =
  T₁.ocl P k (B₁.admC-wk (λ ()) P cv) (T₁.owk (λ ()) t)
         (λ η e → T₁.owk (λ { (N₀.L₁.mr m) → N₀.L₁.mr m ; (N₀.L₁.ml ()) }) (g η e))
live x = T₁.owk (λ ()) x

Yₑ : T₁.T⁰ 0
Yₑ = F.ψ E₀ (F.tn 0)
      (λ { (N₀.L₁.ml N₀.L₁.hr) → F.fs (just (F.evd N₀.L₁.self tt N₀.self-Ωᶠ (inj₂ sx₃ᵍ , refl , preᶠ self-3 LL.zero))) nothing ; (N₀.L₁.mr ()) })
      (live (T₁.Ω̇ N₀.Ωᶠ tcΩ))

lowB : ∀ {π} → T₁.O (T₁.natL 0) π → N₀.D′
lowB (T₁.oĉ c _ _ _ _) = c
lowB (T₁.oŝ c _ _) = c
lowB (T₁.owk _ x) = lowB x
lowB (T₁.ocv _ x) = lowB x
lowB _ = inj₁ zero

chain-stuck : N₀._⊑′_ (lowB Yₑ) (inj₂ (Lv₅ , Cf-Lv₅)) → ⊥
chain-stuck e = no-fg-floor e
```
