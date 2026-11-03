# 带守卫的层号: 验收 (与 EBO 比较)

> **验收节.** 记号只在本文件. 结论写在 [LvGuard](LvGuard.lagda.md). 比较器与 [UniformLvAccept](UniformLvAccept.lagda.md) 同形, 搬到层号 `LG` 上: 后继对后继, $\omega$-极限对基本列, 闭包对共尾度 $\Omega_1$ 的基本列 (`fsT`, 在字面自然数的分支上). **有限测试, 不是证明; 种类检验不看界.** 对照 `ctl₁`, `ctl₂` 说这个比较器分得开相邻的 $\theta$.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvGuardAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Align.Level using (Ordᴵ; natᴵ; ωᴵ; suc; zero; lim; _⊑ᴵ_; _<ᴵ_; s⊑; z≅)
open import OCF.Align.LvGuardBase
open Lv Dom₀
open import OCF.Align.LvGuardFeed using (Ωᴸ; Fᵍ)
import OCF.Align.LvGuardUni as Uni
private module U = Uni Dom₀
open U using (F; Lv₅)
import OCF.Align.EBO as E
open E using (T; fsn; fsT; cof; c0; c1; cω; cΩ; pred; Ωt; natT; sucT; 𝟏) renaming (ψ to ψᵗ)
open import OCF.Align.Uniform5Wall using (ψ₁)
```

## §1 比较器

`dfL d w t x`: 深度 $d$, 宽度 $w$. 闭包的第 0 个孩子是第一支 $t'$, 对 `fsT t 1`; 第 $k\ge1$ 个孩子是分支 $k+1$.

```agda
data Why : Set where
  kindBad : Why
  headBad : Why

zero<nat : ∀ k → zero <ᴵ natᴵ (suc k)
zero<nat zero    = zero
zero<nat (suc k) = suc (zero<nat k)

one⊑nat : ∀ k → suc zero ⊑ᴵ natᴵ (suc k)
one⊑nat k = s⊑ z≅ (zero<nat k)

dfL : ℕ → ℕ → T → LG → Maybe (Why × List ℕ)
dfs : ℕ → ℕ → ℕ → T → (ℕ → LG) → Maybe (Why × List ℕ)
dfb : ℕ → ℕ → ℕ → T → ((k : ℕ) → LG) → Maybe (Why × List ℕ)
dfL zero w t x = nothing
dfL (suc d) w t zero with cof t
... | c0 = nothing
... | _  = just (kindBad , [])
dfL (suc d) w t (suc x) with cof t
... | c1 = dfL d w (pred t) x
... | _  = just (kindBad , [])
dfL (suc d) w t (lim f) with cof t
... | cω = dfs w d w t f
... | _  = just (kindBad , [])
dfL (suc d) w t (lc c t′ g) with cof t
... | cΩ [] with dfL d w (fsT t (natT 1)) t′
...   | just r = just r
...   | nothing = nothing
dfL (suc d) w t (lc c t′ g) | _ = just (headBad , [])

dfs zero d w t f = nothing
dfs (suc n) d w t f with dfL d w (fsn t n) (f n)
... | just (g , p) = just (g , n ∷ p)
... | nothing = dfs n d w t f

dfb zero d w t f = nothing
dfb (suc n) d w t f with dfL d w (fsT t (natT (suc n))) (f n)
... | just (g , p) = just (g , n ∷ p)
... | nothing = dfb n d w t f

-- 分支: 字面自然数 k+1
branches : LG → ℕ → LG
branches (lc (suc zero) t′ g) k = g (natᴵ (suc k)) (one⊑nat k)
branches x k = x

dfB : ℕ → ℕ → T → LG → Maybe (Why × List ℕ)
dfB d w t x = dfb w d w t (branches x)

is-ok : Maybe (Why × List ℕ) → Bool
is-ok nothing  = true
is-ok (just _) = false
```

## §2 $F\,\theta$ 对 $\psi_1(\Omega_\theta)$

$\theta=0$ 是 $\psi_1(1)$, $\theta=1$ 是 $\psi_1(\Omega)$. 这就是任务的两个下标.

```agda
tF : ℕ → T
tF n = ψ₁ (Ωt (natT n))

Fn : ℕ → LG
Fn n = F (natᴵ n)

c-F0 : dfL 8 3 (tF 0) (Fn 0) ≡ nothing
c-F0 = refl
c-F1 : dfL 8 3 (tF 1) (Fn 1) ≡ nothing
c-F1 = refl
c-F1b : dfB 8 3 (tF 1) (Fn 1) ≡ nothing
c-F1b = refl
c-F2 : dfL 7 3 (tF 2) (Fn 2) ≡ nothing
c-F2 = refl
c-F3 : dfL 7 2 (tF 3) (Fn 3) ≡ nothing
c-F3 = refl

-- 对照: 相邻的 θ 分得开
ctl₁ : is-ok (dfL 8 3 (tF 0) (Fn 1)) ≡ false
ctl₁ = refl
ctl₂ : is-ok (dfL 8 3 (tF 1) (Fn 2)) ≡ false
ctl₂ = refl
```

## §3 第 5 站的下标 $\psi_1(\Omega_\Omega)$

```agda
tLv₅ : T
tLv₅ = ψ₁ (Ωt (Ωt (natT 1)))

c-Lv₅ : dfL 7 2 tLv₅ Lv₅ ≡ nothing
c-Lv₅ = refl
c-Lv₅b : dfB 6 2 tLv₅ Lv₅ ≡ nothing
c-Lv₅b = refl

ctl₃ : is-ok (dfL 7 2 (tF 1) Lv₅) ≡ false
ctl₃ = refl
```

## §4 树: $\psi_0(\Omega_L)$ 的种类

比较器 `dfZ` 与 [UniformLvAccept](UniformLvAccept.lagda.md) 的 `dfᵉ` 同形: 闭包只走第 0 个孩子, 所以没有近似. **种类检验不看界 (`noW`), 也走不到第 $\ge1$ 个孩子; 通过不说明有证书.**

```agda
open import OCF.Align.Prefix using (Z)
open import OCF.Align.LvGuardTree using (T₀)
open import OCF.Align.Level using (Ω; _+_; add; Ordᶜ)
open U using (rb₁; rb-≈₁₁; Good-Ω; Good-add; Good→WF₁)
open import OCF.Align.Level using (add-≅; Ω-refl)
open import OCF.Align.Stage2 using (Ωᵗ)
open import OCF.Align.Uniform5Wall using (Ω·2)
open import OCF.Align.Uniform3Base using (ψ₀ᵗ)
open import Data.List using (_++_)

dfZ  : ℕ → ℕ → T → Z → Maybe (Why × List ℕ)
dfZs : ℕ → ℕ → ℕ → T → (ℕ → Z) → Maybe (Why × List ℕ)
dfZ zero w t x = nothing
dfZ (suc d) w t Z.zero with cof t
... | c0 = nothing
... | _  = just (kindBad , [])
dfZ (suc d) w t (Z.suc x) with cof t
... | c1 = dfZ d w (pred t) x
... | _  = just (kindBad , [])
dfZ (suc d) w t (Z.lim f) with cof t
... | cω = dfZs w d w t f
... | _  = just (kindBad , [])
dfZ (suc d) w t (Z.ĉᴸ c z zg o₀ o) with cof t
... | cω = dfZ d w (fsn t 0) o₀
... | _  = just (kindBad , [])

dfZs zero d w t f = nothing
dfZs (suc n) d w t f with dfZ d w (fsn t n) (f n)
... | just (g , p) = just (g , n ∷ p)
... | nothing = dfZs n d w t f

Ω₁ᶜ : Ordᶜ (suc zero)
Ω₁ᶜ = Ω (suc zero)

xΩ₁ x2 x3 : LG
xΩ₁ = rb₁ Ω₁ᶜ
x2  = rb₁ (Ω₁ᶜ + Ω₁ᶜ)
x3  = rb₁ ((Ω₁ᶜ + Ω₁ᶜ) + Ω₁ᶜ)

e1 : Ω₁ᶜ OCF.Align.Level.≅ Ω₁ᶜ
e1 = Ω-refl (suc zero)

Cf-xΩ₁ : Cfˢ xΩ₁
Cf-xΩ₁ = Good→WF₁ (Good-Ω (suc zero)) , rb-≈₁₁ e1

e2 : (Ω₁ᶜ + Ω₁ᶜ) OCF.Align.Level.≅ (Ω₁ᶜ + Ω₁ᶜ)
e2 = add-≅ {σ = λ q → q} {σ′ = λ q → q} e1 e1

g2 : U.Good (Ω₁ᶜ + Ω₁ᶜ)
g2 = Good-add {σ = λ q → q} (Good-Ω (suc zero)) e1 (Good-Ω (suc zero))

Cf-x2 : Cfˢ x2
Cf-x2 = Good→WF₁ g2 , rb-≈₁₁ e2

Cf-x3 : Cfˢ x3
Cf-x3 = Good→WF₁ (Good-add {σ = λ q → q} g2 e2 (Good-Ω (suc zero))) , rb-≈₁₁ (add-≅ {σ = λ q → q} {σ′ = λ q → q} e2 e1)

-- 目标
tΩ1 tΩ11 tΩ2 tΩ21 tΩ3 tψ1 tψΩ tψ5 : T
tΩ1 = ψ₀ᵗ (Ωt (natT 0 ++ Ωᵗ))
tΩ11 = ψ₀ᵗ (Ωt (sucT Ωᵗ))
tΩ2 = ψ₀ᵗ (Ωt Ω·2)
tΩ21 = ψ₀ᵗ (Ωt (sucT Ω·2))
tΩ3 = ψ₀ᵗ (Ωt (Ω·2 ++ Ωᵗ))
tψ1 = ψ₀ᵗ (Ωt (tF 0))
tψΩ = ψ₀ᵗ (Ωt (tF 1))
tψ5 = ψ₀ᵗ (Ωt tLv₅)

t1 t11 t2 t21 t3 tf0 tf1 tf5 : Z
t1 = T₀ xΩ₁ Cf-xΩ₁
t11 = T₀ (suc xΩ₁) (proj₁ Cf-xΩ₁ , s≈ (proj₂ Cf-xΩ₁))
t2 = T₀ x2 Cf-x2
t21 = T₀ (suc x2) (proj₁ Cf-x2 , s≈ (proj₂ Cf-x2))
t3 = T₀ x3 Cf-x3
tf0 = T₀ (F (natᴵ 0)) (U.Cf-F (natᴵ 0))
tf1 = T₀ (F (natᴵ 1)) (U.Cf-F (natᴵ 1))
tf5 = T₀ Lv₅ U.Cf-Lv₅

c-t1 : dfZ 10 2 tΩ1 t1 ≡ nothing
c-t1 = refl
c-t11 : dfZ 12 2 tΩ11 t11 ≡ nothing
c-t11 = refl
c-t2 : dfZ 12 2 tΩ2 t2 ≡ nothing
c-t2 = refl
c-t21 : dfZ 12 2 tΩ21 t21 ≡ nothing
c-t21 = refl
c-t3 : dfZ 12 2 tΩ3 t3 ≡ nothing
c-t3 = refl
-- ψ₀(Ω_{ψ₁(1)}), ψ₀(Ω_{ψ₁(Ω)}) (第一个超出 Ordᴵ 的下标), 第 5 站
c-tf0 : dfZ 10 2 tψ1 tf0 ≡ nothing
c-tf0 = refl
c-tf1 : dfZ 10 2 tψΩ tf1 ≡ nothing
c-tf1 = refl
c-tf5 : dfZ 10 2 tψ5 tf5 ≡ nothing
c-tf5 = refl

-- 对照
ctl₄ : is-ok (dfZ 12 2 tΩ2 t21) ≡ false
ctl₄ = refl
ctl₅ : is-ok (dfZ 12 2 tψ1 tf1) ≡ false
ctl₅ = refl
ctl₆ : is-ok (dfZ 10 2 tψΩ tf5) ≡ false
ctl₆ = refl
```

## §5 界: `noW` 的两半

这是**有限测试, 看界**. `Tgt`: 顶层 $D+1$ ($D=\Omega\cdot2$), 目标 $\Omega$, 闭包 $W=\dot\Omega_D$.

- `boundB τ`: 目标的路径穿过分支 $	au$ (`bra τ`). 这是链从分支 $	au$ 里的节点上升时目标的路径. 结果 $c=	au+1$ (`c-bra2`, `c-bra3`, `c-bra5`): **`noW` 的这一半还在: 界读到的是穿过的分支, 不是目标自己的 $a$.** 这就是 `tight` 要做的事, 这里没有写.
- `boundF τ`: 目标的路径取最小的分支 1 (紧的路径), 同时活的帧 $	au$ 经 `owk` 不进 $W$. 结果 $c=2$, 对一切测过的 $	au$ (`c-tight2`, `c-tight5`): **帧不属于 $W$ 就不进界.** 这是 [LvCert](LvCert.lagda.md) 的第 3 步: 旧树的 `ι (db τ)` 把 $	au$ 加进保留的闭包; 这里闭包在目标之下立刻计值, 没有保留.

```agda
open import OCF.Align.LvGuardTree using (O; module Fold; Ω̇; ι; ds; rdZ; oŝ; owk; ol; os; o0; oĉ; oΩ; ocl)

iterS : LG → ℕ → LG
iterS x zero = x
iterS x (suc n) = suc (iterS x n)

pthS : ∀ n x → x < iterS x (suc n)
pthS zero x = zero
pthS (suc n) x = suc (pthS n x)

adm-pthS : ∀ n x E → Adm E (pthS n x)
adm-pthS zero x E = tt
adm-pthS (suc n) x E = adm-pthS n x E

toN : Ordᴵ → ℕ
toN zero = 0
toN (suc a) = suc (toN a)
toN (lim f s) = toN (f 1)

cO : ∀ {t ρ} → O t ρ → ℕ
cO (oŝ c _ _) = toN c
cO (owk _ x) = cO x
cO (ol f) = 100
cO (os f) = 101
cO o0 = 102
cO (oĉ c _ _ _ _) = 103
cO (oΩ _ _ _) = 104
cO (ocl _ _ _ _ _) = 105

module Tgt {c₁ t₁ g₁} (cf : Cfˢ (lc c₁ t₁ g₁)) (τ : Ordᴵ) (eτ : c₁ ⊑ᴵ τ) (b : LG) (r : b < g₁ τ eτ) (ar : ∀ E → Adm E r) (B : Ordᴵ) (τ<B : τ <ᴵ B) where
  c₀ : LG
  c₀ = suc (lc c₁ t₁ g₁)
  open Fold c₀ (proj₁ cf) (s≈ (proj₂ cf))
  E : Ents
  E = ∅ B
  q : b < c₀
  q = suc (bra τ eτ r)
  aq : Adm (tab E) q
  aq = (B , refl , τ<B) , ar (tab E)
  Y : O b tz
  Y = ψ E (tp q aq) (λ { (ml ()) ; (mr ()) }) (ι ds (Ω̇ (lc c₁ t₁ g₁)))
  -- 活的帧 τ′ 经 owk 不进 W
  module WithFrame (τ′ : Ordᴵ) (e′ : c₁ ⊑ᴵ τ′) (l : τ′ <ᴵ B) where
    φ₀ : Frm
    φ₀ = frm c₁ t₁ g₁ τ′ e′

    Y′ : O b tz
    Y′ = ψ E (tp q aq) (λ { (ml (ml ())) ; (ml (mr ())) ; (mr hr) → fs (just (evd (suc self) tt (proj₂ cf) (B , refl , l))) nothing })
           (owk {π = tz ∪ tz} {ρ = (tz ∪ tz) ∪ tk φ₀} ml (ι ds (Ω̇ (lc c₁ t₁ g₁))))

τₙ : ℕ → Ordᴵ
τₙ n = natᴵ (suc n)

c-bra2 : cO (Tgt.Y {_} {_} {_} Cf-x2 (τₙ 1) (one⊑nat 1) xΩ₁ (pthS 1 xΩ₁) (adm-pthS 1 xΩ₁) (suc (τₙ 1)) zero) ≡ 3
c-bra2 = refl
c-bra3 : cO (Tgt.Y {_} {_} {_} Cf-x2 (τₙ 2) (one⊑nat 2) xΩ₁ (pthS 2 xΩ₁) (adm-pthS 2 xΩ₁) (suc (τₙ 2)) zero) ≡ 4
c-bra3 = refl
c-bra5 : cO (Tgt.Y {_} {_} {_} Cf-x2 (τₙ 4) (one⊑nat 4) xΩ₁ (pthS 4 xΩ₁) (adm-pthS 4 xΩ₁) (suc (τₙ 4)) zero) ≡ 6
c-bra5 = refl

c-tight2 : cO (Tgt.WithFrame.Y′ {_} {_} {_} Cf-x2 (τₙ 0) (one⊑nat 0) xΩ₁ (pthS 0 xΩ₁) (adm-pthS 0 xΩ₁) (natᴵ 3) (suc zero) (τₙ 1) (one⊑nat 1) zero) ≡ 2
c-tight2 = refl
c-tight5 : cO (Tgt.WithFrame.Y′ {_} {_} {_} Cf-x2 (τₙ 0) (one⊑nat 0) xΩ₁ (pthS 0 xΩ₁) (adm-pthS 0 xΩ₁) (natᴵ 6) (suc (suc (suc (suc zero)))) (τₙ 4) (one⊑nat 4) zero) ≡ 2
c-tight5 = refl
```

## §6 嵌套下标: $\psi_1(\Omega_{\psi_1(\Omega)})$

`F⁺ (F 1)`: 第二层读回的定义. 有限测试. 证书没有 (`F⁺` 的 `WF` 没有写).

```agda
open import OCF.Align.LvGuardRead using (F⁺)

q₁ : suc zero < F (natᴵ 1)
q₁ = fst (lim 1 (bra (natᴵ 2) (one⊑nat 1) zero))

aq₁ : Adm (tab (∅ (natᴵ 3))) q₁
aq₁ = (natᴵ 3 , refl , zero) , tt

F²1 : LG
F²1 = F⁺ (F (natᴵ 1)) (U.Cf-F (natᴵ 1)) (∅ (natᴵ 3)) q₁ aq₁

tF²1 : T
tF²1 = ψ₁ (Ωt (tF 1))

c-F²1 : dfL 6 2 tF²1 F²1 ≡ nothing
c-F²1 = refl

ctl₇ : is-ok (dfL 6 2 tF²1 (F (natᴵ 2))) ≡ false
ctl₇ = refl
```
