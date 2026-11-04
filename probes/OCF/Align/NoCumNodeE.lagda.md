# 第 0 层是值: 计值 `E`

> 不含记号. 入口在 [NoCumNode](NoCumNode.lagda.md). **这里不给折叠加节点.** `NoCumW` 的数据树, 折叠, 加法一行不动; 改的是第 0 层: 目标 $(0,0)$ 不再是数据上的折叠, 而是对一切层的项直接计值. `E x gu m …`: $\psi_0(x)$ 有证书, `val` 是它的值, 是第 0 层的树.
>
> 与 [NoCumForce](NoCumForce.lagda.md) 的 `G`, 差三处, 都因为第 0 层的项是**值**:
>
> - `os`: $\psi_0(x+1)=\lim_n \psi_0(x)\cdot n$, 乘法是树上的加法 `_+₀_`, 不经过数据的 `add`. 所以 `W⊕` 不会碰到第 0 层的闭包, 上一轮的 `shift` 这里没有.
> - 上升到 $(0,0)$: 链是值, $z_{n+1}=\ulcorner\psi_0(h\,z_n)\urcorner$ (`rv`), `⌜_⌝` 把值读回成只有 `o0`, `os`, `ol` 的数据, 世界是 $1$. 其他层的上升仍走数据的折叠 (`rg`).
> - 第 0 层的闭包从不作输入. 它只在计值里 (`ec`).
>
> 全文 `--safe --without-K --lossy-unification`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NoCumNodeE where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.BTBO using (module Trich)
open Trich renaming (_<_ to _<ᴺ_) using (zero; suc)
import OCF.Free.Level as FL
open FL using (_≅_; z≅; s≅; l≅; lᵢ≅; upˡ; upʳ)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; Strict; ss; sl; ⊲-tr; z⊲; ≪S; ≪⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.NoCumLit
open import OCF.Align.NoCumW
open import OCF.Align.NoCumEq
open import OCF.Align.NoCumPsi using (ψQ)
open import OCF.Align.NoCumLe
open import OCF.Align.NoCumMain using (WF; ψL′; Ωfst; ΩW)
open import OCF.Align.NoCumForce using (outs; Fp; fq; fs; fl; Fp-mono; ⊴→Fp; Fp→Pj)
open import OCF.Align.Om1HnCx using (≅₀-sym; ≅₀-trans; ⊴₀-r; ⊴₀-l; ⊴₀-tr; ≅₀-refl; Fp-z)
```

## §1 第 0 层的值: 树上的加法, 读回

```agda
infixl 21 _+₀_
_+₀_ : Ord₀ → Ord₀ → Ord₀
a +₀ FL.zero = a
a +₀ FL.suc b = FL.suc (a +₀ b)
a +₀ FL.lim f = FL.lim (λ n → a +₀ f n)
a +₀ FL.limᵢ () f
a +₀ FL.up () x

rep₀ : Ord₀ → ℕ → Ord₀
rep₀ a zero = FL.zero
rep₀ a (suc n) = a +₀ rep₀ a n

+₀≅ : ∀ {a a′ b b′} → a ≅ a′ → b ≅ b′ → a +₀ b ≅ a′ +₀ b′
+₀≅ ea z≅ = ea
+₀≅ ea (s≅ e) = s≅ (+₀≅ ea e)
+₀≅ ea (l≅ h) = l≅ (λ n → +₀≅ ea (h n))
+₀≅ ea (lᵢ≅ {p = ()} e h)
+₀≅ ea (upˡ {r = ()} e)
+₀≅ ea (upʳ {r = ()} e)

rep₀≅ : ∀ {a a′} → a ≅ a′ → ∀ n → rep₀ a n ≅ rep₀ a′ n
rep₀≅ e zero = z≅
rep₀≅ e (suc n) = +₀≅ e (rep₀≅ e n)

z⊴₀ : ∀ (b : Ord₀) → FL.zero ⊴₀ b
z⊴₀ FL.zero = r0 z≅
z⊴₀ (FL.suc b) = s0 (z⊴₀ b)
z⊴₀ (FL.lim f) = l0 0 (z⊴₀ (f 0))
z⊴₀ (FL.limᵢ () f)
z⊴₀ (FL.up () x)

+₀⊴ʳ : ∀ a {b c} → b ⊴₀ c → a +₀ b ⊴₀ a +₀ c
+₀⊴ʳ a (r0 e) = r0 (+₀≅ (≅₀-refl a) e)
+₀⊴ʳ a (s0 p) = s0 (+₀⊴ʳ a p)
+₀⊴ʳ a (l0 n p) = l0 n (+₀⊴ʳ a p)

rep₀⊴ : ∀ a n → rep₀ a n ⊴₀ rep₀ a (suc n)
rep₀⊴ a zero = z⊴₀ (a +₀ FL.zero)
rep₀⊴ a (suc n) = +₀⊴ʳ a (rep₀⊴ a n)

Lit-+₀ : ∀ {a} b → Lit₀ a → Lit₀ b → Lit₀ (a +₀ b)
Lit-+₀ FL.zero la lb = la
Lit-+₀ (FL.suc b) la lb = Lit-+₀ b la lb
Lit-+₀ {a} (FL.lim f) la (st , lb) = (λ n → +₀⊴ʳ a (st n)) , (λ n → Lit-+₀ (f n) la (lb n))
Lit-+₀ (FL.limᵢ () f) la lb
Lit-+₀ (FL.up () x) la lb

Lit-rep₀ : ∀ {a} → Lit₀ a → ∀ n → Lit₀ (rep₀ a n)
Lit-rep₀ la zero = tt
Lit-rep₀ {a} la (suc n) = Lit-+₀ (rep₀ a n) la (Lit-rep₀ la n)

-- 读回: 只有 o0, os, ol, 世界是 1
⌜_⌝ : Ord₀ → 𝓞 zero azero one
⌜ FL.zero ⌝ = o0
⌜ FL.suc a ⌝ = os ⌜ a ⌝
⌜ FL.lim f ⌝ = ol (λ n → ⌜ f n ⌝)
⌜ FL.limᵢ () f ⌝
⌜ FL.up () x ⌝

⌜⌝≈ : ∀ {a b} → a ≅ b → ⌜ a ⌝ ≈ ⌜ b ⌝
⌜⌝≈ z≅ = tt
⌜⌝≈ (s≅ e) = refl , z≈ , s≈ z≈ , ⌜⌝≈ e
⌜⌝≈ (l≅ h) = λ n → ⌜⌝≈ (h n)
⌜⌝≈ (lᵢ≅ {p = ()} e h)
⌜⌝≈ (upˡ {r = ()} e)
⌜⌝≈ (upʳ {r = ()} e)

⌜⌝⊴ : ∀ {a b} → a ⊴₀ b → ⌜ a ⌝ ⊴ ⌜ b ⌝
⌜⌝⊴ (r0 e) = rf (⌜⌝≈ e)
⌜⌝⊴ (s0 p) = s (⌜⌝⊴ p)
⌜⌝⊴ (l0 n p) = l n (⌜⌝⊴ p)

⌜⌝W : ∀ a → Lit₀ a → WF ⌜ a ⌝
⌜⌝W FL.zero la = tt
⌜⌝W (FL.suc a) la = ⌜⌝W a la
⌜⌝W (FL.lim f) (st , la) = (λ n → ⌜⌝⊴ (st n)) , (λ n → ⌜⌝W (f n) (la n))
⌜⌝W (FL.limᵢ () f) la
⌜⌝W (FL.up () x) la

v₁ : Ord₀
v₁ = FL.suc FL.zero

lfv : ∀ {m} → Gw m → Ord₀ → 𝓞 zero azero m
lfv gm a = ow (pos gm) g₀ ⌜ a ⌝

Fp→⊴₁ : ∀ {y} → Fp one y → v₁ ⊴₀ y
Fp→⊴₁ {FL.suc FL.zero} (fq (s≈ z≈)) = r0 (s≅ z≅)
Fp→⊴₁ {FL.zero} (fq ())
Fp→⊴₁ {FL.suc (FL.suc y)} (fq (s≈ ()))
Fp→⊴₁ {FL.suc (FL.lim f)} (fq (s≈ ()))
Fp→⊴₁ {FL.suc (FL.limᵢ () f)} (fq (s≈ e))
Fp→⊴₁ {FL.suc (FL.up () x)} (fq (s≈ e))
Fp→⊴₁ {FL.lim f} (fq ())
Fp→⊴₁ {FL.limᵢ () f} (fq e)
Fp→⊴₁ {FL.up () x} (fq e)
Fp→⊴₁ (fs p) = s0 (Fp→⊴₁ p)
Fp→⊴₁ (fl n p) = l0 n (Fp→⊴₁ p)
```

## §2 计值

`Nz h₀ k`: $(h_0,k)\neq(0,0)$. 上升时链走数据还是走值, 只由它决定. `E` 是对项递归的函数 (同 `WF`), 不是归纳族, 这样模式匹配不用解索引.

```agda
data Nz : ℕ → A → Set where
  nzs : ∀ {h k} → Nz (suc h) k
  nza : ∀ {c} → Nz zero (asuc c)
  nzl : ∀ {f} → Nz zero (alim f)

data Is0 : ℕ → A → Set where
  is0 : Is0 zero azero

emb : ∀ {h k m} → Is0 h k → Gw m → Ord₀ → 𝓞 h k m
emb is0 gm a = lfv gm a

Mz : ∀ {u a v} → Gw u → Gw v → u ⊲ v → a ⊲ v → Mx u azero a v
Mz {v = v} gu gv uv av = mx gu gv uv (z⊲ v) av

Mi : ∀ {u a v} (gu : Gw u) (gv : Gw v) (uv : u ⊲ v) (av : a ⊲ v) → Mis (Mx.m (Mz gu gv uv av)) u azero a
Mi {v = v} gu gv uv av = mx-is gu gv uv (z⊲ v) av

-- 上升的证书: 对被积函数 f 参数化
data Rs {p a m h₀ k} (gm : Gw m) (am : a ⊲ m) (kM : k ⊲ m) (f : 𝓞 h₀ k m → 𝓞 p a m) (Ef : 𝓞 h₀ k m → Set) (vf : ∀ z → Ef z → Ord₀) : Set where
  rg : Nz h₀ k → (Es : ∀ n → Ef (chainᵒ gm (λ z → ψ h₀ k (f z) gm m gm C.self kM am) n)) → (∀ n → vf _ (Es n) ⊴₀ vf _ (Es (suc n))) → Rs gm am kM f Ef vf
  rv : (w : Is0 h₀ k) (vz : ℕ → Ord₀) (Es : ∀ n → Ef (emb w gm (outs v₁ vz n))) → (∀ n → vz n ≅ vf _ (Es n)) → (∀ n → vf _ (Es n) ⊴₀ vf _ (Es (suc n))) → Rs gm am kM f Ef vf

vRs : ∀ {p a m h₀ k} {gm : Gw m} {am : a ⊲ m} {kM : k ⊲ m} {f : 𝓞 h₀ k m → 𝓞 p a m} {Ef : 𝓞 h₀ k m → Set} {vf : ∀ z → Ef z → Ord₀} → Rs gm am kM f Ef vf → ℕ → Ord₀
vRs {vf = vf} (rg nz Es st) n = vf _ (Es n)
vRs {vf = vf} (rv w vz Es tS st) n = vf _ (Es n)

-- 闭包的证书
record Oc {m : A} (Ex : Set) (vx : Ex → Ord₀) (Eh : ∀ {v} → m ⊲ v → Gw v → Set) (vh : ∀ {v} (q : m ⊲ v) (g : Gw v) → Eh q g → Ord₀) : Set where
  constructor oc′
  field
    G₀ : Ex
    vs : ℕ → A
    gv : ∀ n → Gw (vs n)
    up : ∀ n → m ⊲ vs n
    Gh : ∀ n → Eh (up n) (gv n)
    t₀ : vs 0 ≈ᴬ rd (vx G₀)
    tS : ∀ n → vs (suc n) ≈ᴬ rd (vh (up n) (gv n) (Gh n))
    s₀ : vx G₀ ⊴₀ vh (up 0) (gv 0) (Gh 0)
    sS : ∀ n → vh (up n) (gv n) (Gh n) ⊴₀ vh (up (suc n)) (gv (suc n)) (Gh (suc n))

vOc : ∀ {m : A} {Ex : Set} {vx : Ex → Ord₀} {Eh : ∀ {v} → m ⊲ v → Gw v → Set} {vh : ∀ {v} (q : m ⊲ v) (g : Gw v) → Eh q g → Ord₀} → Oc {m} Ex vx Eh vh → Ord₀
vOc {vx = vx} {vh = vh} (oc′ G₀ vs gv up Gh t₀ tS s₀ sS) = FL.lim (outs (vx G₀) (λ n → vh (up n) (gv n) (Gh n)))

E   : ∀ {p a u} (x : 𝓞 p a u) → Gw u → ∀ m → Gw m → u ⊲ m → a ⊲ m → Set
val : ∀ {p a u} (x : 𝓞 p a u) {gu m gm um am} → E x gu m gm um am → Ord₀
EL  : ∀ {p h k u a} (j : h <ᴺ p) (x : Low p j k u) → Gw u → ∀ m → Gw m → u ⊲ m → k ⊲ m → a ⊲ m → Set
vL  : ∀ {p h k u a} (j : h <ᴺ p) (x : Low p j k u) {gu m gm um km} {am : a ⊲ m} → EL {a = a} j x gu m gm um km am → Ord₀

Ev : ∀ {p a u} (x : 𝓞 p a u) (gu : Gw u) v (gv : Gw v) (uv : u ⊲ v) (av : a ⊲ v) → Set
Ev x gu v gv uv av = E x gu (Mx.m (Mz gu gv uv av)) (Mx.gm (Mz gu gv uv av)) (Mx.um (Mz gu gv uv av)) (Mx.am (Mz gu gv uv av))

E o0 gu m gm um am = ⊤
E (os x) gu m gm um am = Ev x gu m gm um am
E (ol F) gu m gm um am = Σ (∀ n → Ev (F n) gu m gm um am) (λ Es → ∀ n → val (F n) (Es n) ⊴₀ val (F (suc n)) (Es (suc n)))
E (oi r h) gu m gm um am = Rs gm am (⊲-tr (≪⊲ r) am) (λ z → h um gm (inS (≪S r) z)) (λ z → Ev (h um gm (inS (≪S r) z)) gm m gm C.self am) (λ z d → val (h um gm (inS (≪S r) z)) d)
E (od j k r h) gu m gm um am = Rs gm am (⊲-tr (≪⊲ r) um) (λ z → h um gm (inL j z)) (λ z → Ev (h um gm (inL j z)) gm m gm C.self am) (λ z d → val (h um gm (inL j z)) d)
E (oc x h) gu m gm um am = Oc {m} (Ev x gu m gm um am) (val x) (λ {v} q g → Ev (h (⊲-tr um q) g) g v g C.self (⊲-tr am q)) (λ {v} q g d → val (h (⊲-tr um q) g) d)
E (oe es x) gu m gm um am = Ev x gu m gm um (⊲-tr (C.suc C.self) am)
E (oe (el n) x) gu m gm um am = Ev x gu m gm um (⊲-tr (C.lim n C.self) am)
E (oL j k e x) gu m gm um am = EL j x gu m gm um (⊲-tr e um) am
E (ow p₁ g x) gu m gm um am = Ev x g m gm (⊲-tr p₁ um) am

EL zero x gu m gm um km am = Ev x gu m gm um km
EL (suc j) x gu m gm um km am = EL j x gu m gm um km am

val o0 d = v₁
val (os x) d = FL.lim (rep₀ (val x d))
val (ol F) (Es , st) = FL.lim (λ n → val (F n) (Es n))
val (oi r h) R = FL.lim (vRs R)
val (od j k r h) R = FL.lim (vRs R)
val (oc x h) d = vOc d
val (oe es x) d = val x d
val (oe (el n) x) d = val x d
val {a = a} (oL j k e x) {am = am} d = vL {a = a} j x {am = am} d
val (ow p₁ g x) d = val x d

vL zero x d = val x d
vL {a = a} (suc j) x {am = am} d = vL {a = a} j x {am = am} d
```

## §3 值的字面性, 下界

```agda
Rs-st : ∀ {p a m h₀ k} {gm : Gw m} {am : a ⊲ m} {kM : k ⊲ m} {f : 𝓞 h₀ k m → 𝓞 p a m} {Ef : 𝓞 h₀ k m → Set} {vf : ∀ z → Ef z → Ord₀} (R : Rs gm am kM f Ef vf) → ∀ n → vRs R n ⊴₀ vRs R (suc n)
Rs-st (rg nz Es st) = st
Rs-st (rv w vz Es tS st) = st

Lit-Rs : ∀ {p a m h₀ k} {gm : Gw m} {am : a ⊲ m} {kM : k ⊲ m} {f : 𝓞 h₀ k m → 𝓞 p a m} {Ef : 𝓞 h₀ k m → Set} {vf : ∀ z → Ef z → Ord₀} (R : Rs gm am kM f Ef vf) → (∀ z (d : Ef z) → Lit₀ (vf z d)) → Lit₀ (FL.lim (vRs R))
Lit-Rs {vf = vf} R LL = Rs-st R , each R
  where
  each : ∀ (R₁ : Rs _ _ _ _ _ vf) n → Lit₀ (vRs R₁ n)
  each (rg nz Es st) n = LL _ (Es n)
  each (rv w vz Es tS st) n = LL _ (Es n)

Lit-val : ∀ {p a u} (x : 𝓞 p a u) {gu m gm um am} (d : E x gu m gm um am) → Lit₀ (val x d)
Lit-L : ∀ {p h k u a} (j : h <ᴺ p) (x : Low p j k u) {gu m gm um km} {am : a ⊲ m} (d : EL {a = a} j x gu m gm um km am) → Lit₀ (vL j x d)
Lit-val o0 d = tt
Lit-val (os x) d = rep₀⊴ (val x d) , Lit-rep₀ (Lit-val x d)
Lit-val (ol F) (Es , st) = st , (λ n → Lit-val (F n) (Es n))
Lit-val (oi r h) R = Lit-Rs R (λ z d → Lit-val (h _ _ (inS (≪S r) z)) d)
Lit-val (od j k r h) R = Lit-Rs R (λ z d → Lit-val (h _ _ (inL j z)) d)
Lit-val {p} {a} {u} (oc x h) {gu} {m} {gm} {um} {am} (oc′ G₀ vs gv up Gh t₀ tS s₀ sS) = step , each
  where
  yy : ℕ → Ord₀
  yy = outs (val x G₀) (λ n → val (h (⊲-tr um (up n)) (gv n)) (Gh n))
  step : ∀ n → yy n ⊴₀ yy (suc n)
  step zero = s₀
  step (suc n) = sS n
  each : ∀ n → Lit₀ (yy n)
  each zero = Lit-val x G₀
  each (suc n) = Lit-val (h (⊲-tr um (up n)) (gv n)) (Gh n)
Lit-val (oe es x) d = Lit-val x d
Lit-val (oe (el n) x) d = Lit-val x d
Lit-val {a = a} (oL j k e x) {am = am} d = Lit-L {a = a} j x {am = am} d
Lit-val (ow p₁ g x) d = Lit-val x d
Lit-L zero x d = Lit-val x d
Lit-L {a = a} (suc j) x {am = am} d = Lit-L {a = a} j x {am = am} d

HS-val : ∀ {p a u} (x : 𝓞 p a u) {gu m gm um am} (d : E x gu m gm um am) → FL.HS (val x d)
HS-val x d = HS₀ _ (Lit-val x d)

-- 每个值都以 1 为第一位置
one-Rs : ∀ {p a m h₀ k} {gm : Gw m} {am : a ⊲ m} {kM : k ⊲ m} {f : 𝓞 h₀ k m → 𝓞 p a m} {Ef : 𝓞 h₀ k m → Set} {vf : ∀ z → Ef z → Ord₀} (R : Rs gm am kM f Ef vf) → (∀ z (d : Ef z) → Fp one (vf z d)) → Fp one (FL.lim (vRs R))
one-Rs (rg nz Es st) O₁ = fl 0 (O₁ _ (Es 0))
one-Rs (rv w vz Es tS st) O₁ = fl 0 (O₁ _ (Es 0))

one-val : ∀ {p a u} (x : 𝓞 p a u) {gu m gm um am} (d : E x gu m gm um am) → Fp one (val x d)
one-L : ∀ {p h k u a} (j : h <ᴺ p) (x : Low p j k u) {gu m gm um km} {am : a ⊲ m} (d : EL {a = a} j x gu m gm um km am) → Fp one (vL j x d)
one-val o0 d = fq (s≈ z≈)
one-val (os x) d = fl 1 (one-val x d)
one-val (ol F) (Es , st) = fl 0 (one-val (F 0) (Es 0))
one-val (oi r h) R = one-Rs R (λ z d → one-val (h _ _ (inS (≪S r) z)) d)
one-val (od j k r h) R = one-Rs R (λ z d → one-val (h _ _ (inL j z)) d)
one-val (oc x h) (oc′ G₀ vs gv up Gh t₀ tS s₀ sS) = fl 0 (one-val x G₀)
one-val (oe es x) d = one-val x d
one-val (oe (el n) x) d = one-val x d
one-val {a = a} (oL j k e x) {am = am} d = one-L {a = a} j x {am = am} d
one-val (ow p₁ g x) d = one-val x d
one-L zero x d = one-val x d
one-L {a = a} (suc j) x {am = am} d = one-L {a = a} j x {am = am} d
```

## §4 证书无关, 搬运

都走 `Mis`: 闭包的链点在 $m$ 之上, 两边的 $m$ 模 $\approx^A$ 相同.

```agda
Mm≈ : ∀ {m u a m′ u′ a′} → Mis m u azero a → Mis m′ u′ azero a′ → u ⊲ m → a ⊲ m → u′ ⊲ m′ → a′ ⊲ m′ → u ≈ᴬ u′ → a ≈ᴬ a′ → m ≈ᴬ m′
Mm≈ {m} {m′ = m′} is is′ um am um′ am′ eu ea = m≈ is is′ um (z⊲ m) am um′ (z⊲ m′) am′ eu z≈ ea

NzT : ∀ {h k k′} → k ≈ᴬ k′ → Nz h k′ → Nz h k
NzT e nzs = nzs
NzT (s≈ e) nza = nza
NzT (l≈ h) nzl = nzl

noNz : ∀ {k} → Nz zero k → k ≈ᴬ azero → ⊥
noNz nza ()
noNz nzl ()

zP : ∀ {p a p′ a′ m m′ h₀ k k′} {gm : Gw m} {gm′ : Gw m′} {am : a ⊲ m} {am′ : a′ ⊲ m′} {kM : k ⊲ m} {kM′ : k′ ⊲ m′} {f : 𝓞 h₀ k m → 𝓞 p a m} {f′ : 𝓞 h₀ k′ m′ → 𝓞 p′ a′ m′} →
     k ≈ᴬ k′ → (∀ z z′ → z ≈ z′ → f z ≈ f′ z′) → ∀ i → chainᵒ gm (λ z → ψ h₀ k (f z) gm m gm C.self kM am) i ≈ chainᵒ gm′ (λ z → ψ h₀ k′ (f′ z) gm′ m′ gm′ C.self kM′ am′) i
zP {h₀ = h₀} {gm = gm} {gm′ = gm′} ek Nf zero = ≈-Ωat h₀ gm gm′ ek
zP {m = m} {m′} {gm = gm} {gm′} {am} {am′} {kM} {kM′} {f} {f′} ek Nf (suc i) = ψQ (f _) (f′ _) gm gm′ m gm C.self kM am m′ gm′ C.self kM′ am′ ek (Nf _ _ (zP {gm = gm} {gm′} {am} {am′} {kM} {kM′} {f} {f′} ek Nf i))

ez : ∀ {m m′} (gm : Gw m) (gm′ : Gw m′) {x x′ : Ord₀} → x ≅ x′ → lfv gm x ≈ lfv gm′ x′
ez gm gm′ {x} {x′} e = ≈ow ⌜ x ⌝ (pos gm′) g₀ ⌜ x′ ⌝ (⌜⌝≈ e)

vR≅ : ∀ {p a p′ a′ m m′ h₀ k k′} {gm : Gw m} {gm′ : Gw m′} {am : a ⊲ m} {am′ : a′ ⊲ m′} {kM : k ⊲ m} {kM′ : k′ ⊲ m′}
      {f : 𝓞 h₀ k m → 𝓞 p a m} {f′ : 𝓞 h₀ k′ m′ → 𝓞 p′ a′ m′} {Ef : 𝓞 h₀ k m → Set} {Ef′ : 𝓞 h₀ k′ m′ → Set} {vf : ∀ z → Ef z → Ord₀} {vf′ : ∀ z → Ef′ z → Ord₀} →
      k ≈ᴬ k′ → (∀ z z′ → z ≈ z′ → f z ≈ f′ z′) → (∀ z z′ → z ≈ z′ → (d : Ef z) (d′ : Ef′ z′) → vf z d ≅ vf′ z′ d′) →
      (R : Rs gm am kM f Ef vf) (R′ : Rs gm′ am′ kM′ f′ Ef′ vf′) → ∀ n → vRs R n ≅ vRs R′ n
vR≅ {gm = gm} {gm′} {am} {am′} {kM} {kM′} {f} {f′} ek Nf Vf (rg nz Es st) (rg nz′ Es′ st′) n = Vf _ _ (zP {gm = gm} {gm′} {am} {am′} {kM} {kM′} {f} {f′} ek Nf n) (Es n) (Es′ n)
vR≅ {gm = gm} {gm′} {vf = vf} {vf′} ek Nf Vf (rv is0 vz Es tS st) (rv is0 vz′ Es′ tS′ st′) n = EE n
  where
  vv : ∀ i → outs v₁ vz i ≅ outs v₁ vz′ i
  EE : ∀ i → vf _ (Es i) ≅ vf′ _ (Es′ i)
  vv zero = s≅ z≅
  vv (suc i) = ≅₀-trans (tS i) (≅₀-trans (EE i) (≅₀-sym (tS′ i)))
  EE i = Vf _ _ (ez gm gm′ (vv i)) (Es i) (Es′ i)
vR≅ ek Nf Vf (rg nz Es st) (rv is0 vz Es′ tS′ st′) n = ⊥-elim (noNz nz ek)
vR≅ ek Nf Vf (rv is0 vz Es tS st) (rg nz′ Es′ st′) n = ⊥-elim (noNz nz′ (≈ᴬ-sym ek))

RsT : ∀ {p a p′ a′ m m′ h₀ k k′} {gm : Gw m} {gm′ : Gw m′} {am : a ⊲ m} {am′ : a′ ⊲ m′} {kM : k ⊲ m} {kM′ : k′ ⊲ m′}
      {f : 𝓞 h₀ k m → 𝓞 p a m} {f′ : 𝓞 h₀ k′ m′ → 𝓞 p′ a′ m′} {Ef : 𝓞 h₀ k m → Set} {Ef′ : 𝓞 h₀ k′ m′ → Set} {vf : ∀ z → Ef z → Ord₀} {vf′ : ∀ z → Ef′ z → Ord₀} →
      k ≈ᴬ k′ → (∀ z z′ → z ≈ z′ → f z ≈ f′ z′) → (∀ z z′ → z ≈ z′ → Ef′ z′ → Ef z) → (∀ z z′ → z ≈ z′ → (d : Ef z) (d′ : Ef′ z′) → vf z d ≅ vf′ z′ d′) →
      Rs gm′ am′ kM′ f′ Ef′ vf′ → Rs gm am kM f Ef vf
RsT {gm = gm} {gm′} {am} {am′} {kM} {kM′} {f} {f′} ek Nf Tf Vf (rg nz′ Es′ st′) = rg (NzT ek nz′) Es (λ n → ⊴₀-l (EE n) (⊴₀-r (st′ n) (≅₀-sym (EE (suc n)))))
  where
  Pz = zP {gm = gm} {gm′} {am} {am′} {kM} {kM′} {f} {f′} ek Nf
  Es = λ n → Tf _ _ (Pz n) (Es′ n)
  EE = λ n → Vf _ _ (Pz n) (Es n) (Es′ n)
RsT {gm = gm} {gm′} ek Nf Tf Vf (rv is0 vz Es′ tS′ st′) with ek
... | z≈ = rv is0 vz Es (λ n → ≅₀-trans (tS′ n) (≅₀-sym (EE n))) (λ n → ⊴₀-l (EE n) (⊴₀-r (st′ n) (≅₀-sym (EE (suc n)))))
  where
  Es = λ n → Tf _ _ (ez gm gm′ (≅₀-refl (outs v₁ vz n))) (Es′ n)
  EE = λ n → Vf _ _ (ez gm gm′ (≅₀-refl (outs v₁ vz n))) (Es n) (Es′ n)

val≅ : ∀ {p a u p′ a′ u′} (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) {gx m gm um am gy m′ gm′ um′ am′} (A₁ : E x gx m gm um am) (B₁ : E y gy m′ gm′ um′ am′) → x ≈ y → Mis m u azero a → Mis m′ u′ azero a′ → val x A₁ ≅ val y B₁
val≅ᵉ : ∀ {p a u p′ a′ u′} (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) {gx v gv uv av gy v′ gv′ uv′ av′} (A₁ : Ev x gx v gv uv av) (B₁ : Ev y gy v′ gv′ uv′ av′) → x ≈ y → val x A₁ ≅ val y B₁
vLˡ : ∀ {p h k u a p′ a′ u′} (j : h <ᴺ p) (x : Low p j k u) (y : 𝓞 p′ a′ u′) {gx m gm um km gy m′ gm′ um′ am′} {am : a ⊲ m} (A₁ : EL {a = a} j x gx m gm um km am) (B₁ : E y gy m′ gm′ um′ am′) → outL j x ≈ y → Mis m′ u′ azero a′ → vL j x A₁ ≅ val y B₁
vLʳ : ∀ {p a u p′ h k u′ a′} (x : 𝓞 p a u) (j : h <ᴺ p′) (y : Low p′ j k u′) {gx m gm um am gy m′ gm′ um′ km′} {am′ : a′ ⊲ m′} (A₁ : E x gx m gm um am) (B₁ : EL {a = a′} j y gy m′ gm′ um′ km′ am′) → x ≈ outL j y → Mis m u azero a → val x A₁ ≅ vL j y B₁

val≅ᵉ x y {gx} {v} {gv} {uv} {av} {gy} {v′} {gv′} {uv′} {av′} A₁ B₁ e = val≅ x y A₁ B₁ e (Mi gx gv uv av) (Mi gy gv′ uv′ av′)

vLˡ zero x y {gx} {m} {gm} {um} {km} A₁ B₁ e is′ = val≅ x y A₁ B₁ e (Mi gx gm um km) is′
vLˡ {a = a} (suc j) x y {am = am} A₁ B₁ e is′ = vLˡ {a = a} j x y {am = am} A₁ B₁ e is′
vLʳ x zero y {gy = gy} {gm′ = gm′} {um′ = um′} {km′ = km′} A₁ B₁ e is = val≅ x y A₁ B₁ e is (Mi gy gm′ um′ km′)
vLʳ {a′ = a′} x (suc j) y {am′ = am′} A₁ B₁ e is = vLʳ {a′ = a′} x j y {am′ = am′} A₁ B₁ e is

val≅ (ow p₁ g x) y {gm = gm} {um} {am} A₁ B₁ e is is′ = val≅ x y A₁ B₁ e (Mi g gm (⊲-tr p₁ um) am) is′
val≅ (oe es x) y {gx} {gm = gm} {um} {am} A₁ B₁ e is is′ = val≅ x y A₁ B₁ e (Mi gx gm um (⊲-tr (C.suc C.self) am)) is′
val≅ (oe (el n) x) y {gx} {gm = gm} {um} {am} A₁ B₁ e is is′ = val≅ x y A₁ B₁ e (Mi gx gm um (⊲-tr (C.lim n C.self) am)) is′
val≅ {a = a} (oL j k e′ x) y {am = am} A₁ B₁ e is is′ = vLˡ {a = a} j x y {am = am} A₁ B₁ (Ll→ j x e) is′
val≅ x (ow p₁ g y) {gm′ = gm′} {um′} {am′} A₁ B₁ e is is′ = val≅ x y A₁ B₁ (≈ow⁻ x p₁ g y e) is (Mi g gm′ (⊲-tr p₁ um′) am′)
val≅ x (oe es y) {gy = gy} {gm′ = gm′} {um′} {am′} A₁ B₁ e is is′ = val≅ x y A₁ B₁ (≈oe⁻ {R = ss C.self} x es y e) is (Mi gy gm′ um′ (⊲-tr (C.suc C.self) am′))
val≅ x (oe (el n) y) {gy = gy} {gm′ = gm′} {um′} {am′} A₁ B₁ e is is′ = val≅ x y A₁ B₁ (≈oe⁻ {R = sl n C.self} x (el n) y e) is (Mi gy gm′ um′ (⊲-tr (C.lim n C.self) am′))
val≅ {a′ = a′} x (oL j k e′ y) {am′ = am′} A₁ B₁ e is is′ = vLʳ {a′ = a′} x j y {am′ = am′} A₁ B₁ (≈oL⁻ x j e′ y e) is
val≅ o0 o0 A₁ B₁ e is is′ = s≅ z≅
val≅ (os x) (os y) A₁ B₁ (_ , _ , _ , e) is is′ = l≅ (rep₀≅ (val≅ᵉ x y A₁ B₁ e))
val≅ (ol F) (ol H) (As , _) (Bs , _) e is is′ = l≅ (λ n → val≅ᵉ (F n) (H n) (As n) (Bs n) (e n))
val≅ (oi {k = k} r h) (oi {k = k′} r′ h′) {gm = gm} {um} {am} {gm′ = gm′} {um′} {am′} A₁ B₁ (refl , ea , eu , ek , N) is is′ =
  l≅ (vR≅ ek Nf (λ z z′ e d d′ → val≅ᵉ _ _ d d′ (Nf z z′ e)) A₁ B₁)
  where
  Nf : ∀ z z′ → z ≈ z′ → h um gm (inS (≪S r) z) ≈ h′ um′ gm′ (inS (≪S r′) z′)
  Nf z z′ e = nI {r = r} {r′} {h} {h′} N um um′ gm gm′ (Mm≈ is is′ um am um′ am′ eu ea) z z′ e
val≅ (od j k r h) (od j′ k′ r′ h′) {gm = gm} {um} {am} {gm′ = gm′} {um′} {am′} A₁ B₁ (refl , refl , ea , eu , ek , N) is is′ =
  l≅ (vR≅ ek Nf (λ z z′ e d d′ → val≅ᵉ _ _ d d′ (Nf z z′ e)) A₁ B₁)
  where
  Nf : ∀ z z′ → z ≈ z′ → h um gm (inL j z) ≈ h′ um′ gm′ (inL j′ z′)
  Nf z z′ e = nD {j = j} {j′} {h} {h′} N um um′ gm gm′ (Mm≈ is is′ um am um′ am′ eu ea) z z′ e
val≅ (oc x h) (oc x′ h′) {um = um} {um′ = um′} (oc′ G₀ vs gv up Gh t₀ tS s₀ sS) (oc′ G₀′ vs′ gv′ up′ Gh′ t₀′ tS′ s₀′ sS′) (_ , ea , eu , ex , N) is is′ = l≅ out
  where
  e₀ = val≅ᵉ x x′ G₀ G₀′ ex
  vv : ∀ n → vs n ≈ᴬ vs′ n
  Eh : ∀ n → val (h (⊲-tr um (up n)) (gv n)) (Gh n) ≅ val (h′ (⊲-tr um′ (up′ n)) (gv′ n)) (Gh′ n)
  vv zero = ≈ᴬ-trans t₀ (≈ᴬ-trans (≅→≈ e₀) (≈ᴬ-sym t₀′))
  vv (suc n) = ≈ᴬ-trans (tS n) (≈ᴬ-trans (≅→≈ (Eh n)) (≈ᴬ-sym (tS′ n)))
  Eh n = val≅ᵉ _ _ (Gh n) (Gh′ n) (N _ _ (gv n) (gv′ n) (vv n))
  out : ∀ n → outs (val x G₀) (λ k → val (h (⊲-tr um (up k)) (gv k)) (Gh k)) n ≅ outs (val x′ G₀′) (λ k → val (h′ (⊲-tr um′ (up′ k)) (gv′ k)) (Gh′ k)) n
  out zero = e₀
  out (suc n) = Eh n
val≅ o0 (os _) A₁ B₁ () is is′
val≅ o0 (ol _) A₁ B₁ () is is′
val≅ o0 (oi _ _) A₁ B₁ () is is′
val≅ o0 (od _ _ _ _) A₁ B₁ () is is′
val≅ o0 (oc _ _) A₁ B₁ () is is′
val≅ (os _) o0 A₁ B₁ () is is′
val≅ (os _) (ol _) A₁ B₁ () is is′
val≅ (os _) (oi _ _) A₁ B₁ () is is′
val≅ (os _) (od _ _ _ _) A₁ B₁ () is is′
val≅ (os _) (oc _ _) A₁ B₁ () is is′
val≅ (ol _) o0 A₁ B₁ () is is′
val≅ (ol _) (os _) A₁ B₁ () is is′
val≅ (ol _) (oi _ _) A₁ B₁ () is is′
val≅ (ol _) (od _ _ _ _) A₁ B₁ () is is′
val≅ (ol _) (oc _ _) A₁ B₁ () is is′
val≅ (oi _ _) o0 A₁ B₁ () is is′
val≅ (oi _ _) (os _) A₁ B₁ () is is′
val≅ (oi _ _) (ol _) A₁ B₁ () is is′
val≅ (oi _ _) (od _ _ _ _) A₁ B₁ () is is′
val≅ (oi _ _) (oc _ _) A₁ B₁ () is is′
val≅ (od _ _ _ _) o0 A₁ B₁ () is is′
val≅ (od _ _ _ _) (os _) A₁ B₁ () is is′
val≅ (od _ _ _ _) (ol _) A₁ B₁ () is is′
val≅ (od _ _ _ _) (oi _ _) A₁ B₁ () is is′
val≅ (od _ _ _ _) (oc _ _) A₁ B₁ () is is′
val≅ (oc _ _) o0 A₁ B₁ () is is′
val≅ (oc _ _) (os _) A₁ B₁ () is is′
val≅ (oc _ _) (ol _) A₁ B₁ () is is′
val≅ (oc _ _) (oi _ _) A₁ B₁ () is is′
val≅ (oc _ _) (od _ _ _ _) A₁ B₁ () is is′

E-tr : ∀ {p a u p′ a′ u′} (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gx : Gw u) → x ≈ y → ∀ m (gm : Gw m) (um : u ⊲ m) (am : a ⊲ m) → Mis m u azero a →
       ∀ (g′ : Gw u′) m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (am′ : a′ ⊲ m′) → Mis m′ u′ azero a′ → E y g′ m′ gm′ um′ am′ → E x gx m gm um am
E-trᵉ : ∀ {p a u p′ a′ u′} (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gx : Gw u) → x ≈ y → ∀ v (gv : Gw v) (uv : u ⊲ v) (av : a ⊲ v) →
       ∀ (g′ : Gw u′) v′ (gv′ : Gw v′) (uv′ : u′ ⊲ v′) (av′ : a′ ⊲ v′) → Ev y g′ v′ gv′ uv′ av′ → Ev x gx v gv uv av
TLˡ : ∀ {p h k u a p′ a′ u′} (j : h <ᴺ p) (x : Low p j k u) (y : 𝓞 p′ a′ u′) (gx : Gw u) → outL j x ≈ y → ∀ m (gm : Gw m) (um : u ⊲ m) (km : k ⊲ m) (am : a ⊲ m) →
      ∀ (g′ : Gw u′) m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (am′ : a′ ⊲ m′) → Mis m′ u′ azero a′ → E y g′ m′ gm′ um′ am′ → EL {a = a} j x gx m gm um km am
TLʳ : ∀ {p a u p′ h k u′ a′} (x : 𝓞 p a u) (j : h <ᴺ p′) (y : Low p′ j k u′) (gx : Gw u) → x ≈ outL j y → ∀ m (gm : Gw m) (um : u ⊲ m) (am : a ⊲ m) → Mis m u azero a →
      ∀ (g′ : Gw u′) m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (km′ : k ⊲ m′) (am′ : a′ ⊲ m′) → EL {a = a′} j y g′ m′ gm′ um′ km′ am′ → E x gx m gm um am

E-trᵉ x y gx e v gv uv av g′ v′ gv′ uv′ av′ b = E-tr x y gx e _ _ _ _ (Mi gx gv uv av) g′ _ _ _ _ (Mi g′ gv′ uv′ av′) b

TLˡ zero x y gx e m gm um km am g′ m′ gm′ um′ am′ is′ b = E-tr x y gx e _ _ _ _ (Mi gx gm um km) g′ m′ gm′ um′ am′ is′ b
TLˡ (suc j) x y gx e m gm um km am g′ m′ gm′ um′ am′ is′ b = TLˡ j x y gx e m gm um km am g′ m′ gm′ um′ am′ is′ b
TLʳ x zero y gx e m gm um am is g′ m′ gm′ um′ km′ am′ b = E-tr x y gx e m gm um am is g′ _ _ _ _ (Mi g′ gm′ um′ km′) b
TLʳ x (suc j) y gx e m gm um am is g′ m′ gm′ um′ km′ am′ b = TLʳ x j y gx e m gm um am is g′ m′ gm′ um′ km′ am′ b

E-tr (ow p₁ g x) y gx e m gm um am is g′ m′ gm′ um′ am′ is′ b = E-tr x y g e _ _ _ _ (Mi g gm (⊲-tr p₁ um) am) g′ m′ gm′ um′ am′ is′ b
E-tr (oe es x) y gx e m gm um am is g′ m′ gm′ um′ am′ is′ b = E-tr x y gx e _ _ _ _ (Mi gx gm um (⊲-tr (C.suc C.self) am)) g′ m′ gm′ um′ am′ is′ b
E-tr (oe (el n) x) y gx e m gm um am is g′ m′ gm′ um′ am′ is′ b = E-tr x y gx e _ _ _ _ (Mi gx gm um (⊲-tr (C.lim n C.self) am)) g′ m′ gm′ um′ am′ is′ b
E-tr (oL j k e′ x) y gx e m gm um am is g′ m′ gm′ um′ am′ is′ b = TLˡ j x y gx (Ll→ j x e) m gm um (⊲-tr e′ um) am g′ m′ gm′ um′ am′ is′ b
E-tr x (ow p₁ g y) gx e m gm um am is g′ m′ gm′ um′ am′ is′ b = E-tr x y gx (≈ow⁻ x p₁ g y e) m gm um am is g _ _ _ _ (Mi g gm′ (⊲-tr p₁ um′) am′) b
E-tr x (oe es y) gx e m gm um am is g′ m′ gm′ um′ am′ is′ b = E-tr x y gx (≈oe⁻ {R = ss C.self} x es y e) m gm um am is g′ _ _ _ _ (Mi g′ gm′ um′ (⊲-tr (C.suc C.self) am′)) b
E-tr x (oe (el n) y) gx e m gm um am is g′ m′ gm′ um′ am′ is′ b = E-tr x y gx (≈oe⁻ {R = sl n C.self} x (el n) y e) m gm um am is g′ _ _ _ _ (Mi g′ gm′ um′ (⊲-tr (C.lim n C.self) am′)) b
E-tr x (oL j k e′ y) gx e m gm um am is g′ m′ gm′ um′ am′ is′ b = TLʳ x j y gx (≈oL⁻ x j e′ y e) m gm um am is g′ m′ gm′ um′ (⊲-tr e′ um′) am′ b
E-tr o0 o0 gx e m gm um am is g′ m′ gm′ um′ am′ is′ b = tt
E-tr (os x) (os y) gx (_ , _ , _ , e) m gm um am is g′ m′ gm′ um′ am′ is′ b = E-trᵉ x y gx e m gm um am g′ m′ gm′ um′ am′ b
E-tr (ol F) (ol H) gx e m gm um am is g′ m′ gm′ um′ am′ is′ (Bs , st) = Es , (λ n → ⊴₀-l (EE n) (⊴₀-r (st n) (≅₀-sym (EE (suc n)))))
  where
  Es : ∀ n → Ev (F n) gx m gm um am
  Es n = E-trᵉ (F n) (H n) gx (e n) m gm um am g′ m′ gm′ um′ am′ (Bs n)
  EE : ∀ n → val (F n) (Es n) ≅ val (H n) (Bs n)
  EE n = val≅ᵉ (F n) (H n) (Es n) (Bs n) (e n)
E-tr (oi r h) (oi r′ h′) gx (refl , ea , eu , ek , N) m gm um am is g′ m′ gm′ um′ am′ is′ b =
  RsT ek Nf (λ z z′ e d′ → E-trᵉ _ _ gm (Nf z z′ e) m gm C.self am gm′ m′ gm′ C.self am′ d′) (λ z z′ e d d′ → val≅ᵉ _ _ d d′ (Nf z z′ e)) b
  where
  Nf : ∀ z z′ → z ≈ z′ → h um gm (inS (≪S r) z) ≈ h′ um′ gm′ (inS (≪S r′) z′)
  Nf z z′ e = nI {r = r} {r′} {h} {h′} N um um′ gm gm′ (Mm≈ is is′ um am um′ am′ eu ea) z z′ e
E-tr (od j k r h) (od j′ k′ r′ h′) gx (refl , refl , ea , eu , ek , N) m gm um am is g′ m′ gm′ um′ am′ is′ b =
  RsT ek Nf (λ z z′ e d′ → E-trᵉ _ _ gm (Nf z z′ e) m gm C.self am gm′ m′ gm′ C.self am′ d′) (λ z z′ e d d′ → val≅ᵉ _ _ d d′ (Nf z z′ e)) b
  where
  Nf : ∀ z z′ → z ≈ z′ → h um gm (inL j z) ≈ h′ um′ gm′ (inL j′ z′)
  Nf z z′ e = nD {j = j} {j′} {h} {h′} N um um′ gm gm′ (Mm≈ is is′ um am um′ am′ eu ea) z z′ e
E-tr (oc x h) (oc x′ h′) gx (_ , ea , eu , ex , N) m gm um am is g′ m′ gm′ um′ am′ is′ (oc′ G₀ vs gv up Gh t₀ tS s₀ sS) =
  oc′ G₀′ vs′ gv′ up′ Gh′ t₀′ tS′ (⊴₀-l E₀ (⊴₀-r s₀ (≅₀-sym (EE 0)))) (λ n → ⊴₀-l (EE n) (⊴₀-r (sS n) (≅₀-sym (EE (suc n)))))
  where
  em = Mm≈ is is′ um am um′ am′ eu ea
  G₀′ : Ev x gx m gm um am
  G₀′ = E-trᵉ x x′ gx ex m gm um am g′ m′ gm′ um′ am′ G₀
  E₀ : val x G₀′ ≅ val x′ G₀
  E₀ = val≅ᵉ x x′ G₀′ G₀ ex
  r : ∀ n → Gr (vs n) m
  r n = graftA (vs n) (up n) (lgw (gv n)) m (lgw gm) em
  vs′ : ℕ → A
  vs′ n = g (gE (r n))
  gv′ : ∀ n → Gw (vs′ n)
  gv′ n = gw (lg (gE (r n))) (⊲-tr (pos gm) (at (r n)))
  up′ : ∀ n → m ⊲ vs′ n
  up′ n = at (r n)
  en : ∀ n → h (⊲-tr um (up′ n)) (gv′ n) ≈ h′ (⊲-tr um′ (up n)) (gv n)
  en n = N _ _ (gv′ n) (gv n) (eq (gE (r n)))
  Gh′ : ∀ n → Ev (h (⊲-tr um (up′ n)) (gv′ n)) (gv′ n) (vs′ n) (gv′ n) C.self (⊲-tr am (up′ n))
  Gh′ n = E-trᵉ _ _ (gv′ n) (en n) (vs′ n) (gv′ n) C.self (⊲-tr am (up′ n)) (gv n) (vs n) (gv n) C.self (⊲-tr am′ (up n)) (Gh n)
  EE : ∀ n → val (h (⊲-tr um (up′ n)) (gv′ n)) (Gh′ n) ≅ val (h′ (⊲-tr um′ (up n)) (gv n)) (Gh n)
  EE n = val≅ᵉ _ _ (Gh′ n) (Gh n) (en n)
  t₀′ : vs′ 0 ≈ᴬ rd (val x G₀′)
  t₀′ = ≈ᴬ-trans (eq (gE (r 0))) (≈ᴬ-trans t₀ (≅→≈ (≅₀-sym E₀)))
  tS′ : ∀ n → vs′ (suc n) ≈ᴬ rd (val (h (⊲-tr um (up′ n)) (gv′ n)) (Gh′ n))
  tS′ n = ≈ᴬ-trans (eq (gE (r (suc n)))) (≈ᴬ-trans (tS n) (≅→≈ (≅₀-sym (EE n))))
E-tr o0 (os _) gx () m gm um am is g′ m′ gm′ um′ am′ is′ b
E-tr o0 (ol _) gx () m gm um am is g′ m′ gm′ um′ am′ is′ b
E-tr o0 (oi _ _) gx () m gm um am is g′ m′ gm′ um′ am′ is′ b
E-tr o0 (od _ _ _ _) gx () m gm um am is g′ m′ gm′ um′ am′ is′ b
E-tr o0 (oc _ _) gx () m gm um am is g′ m′ gm′ um′ am′ is′ b
E-tr (os _) o0 gx () m gm um am is g′ m′ gm′ um′ am′ is′ b
E-tr (os _) (ol _) gx () m gm um am is g′ m′ gm′ um′ am′ is′ b
E-tr (os _) (oi _ _) gx () m gm um am is g′ m′ gm′ um′ am′ is′ b
E-tr (os _) (od _ _ _ _) gx () m gm um am is g′ m′ gm′ um′ am′ is′ b
E-tr (os _) (oc _ _) gx () m gm um am is g′ m′ gm′ um′ am′ is′ b
E-tr (ol _) o0 gx () m gm um am is g′ m′ gm′ um′ am′ is′ b
E-tr (ol _) (os _) gx () m gm um am is g′ m′ gm′ um′ am′ is′ b
E-tr (ol _) (oi _ _) gx () m gm um am is g′ m′ gm′ um′ am′ is′ b
E-tr (ol _) (od _ _ _ _) gx () m gm um am is g′ m′ gm′ um′ am′ is′ b
E-tr (ol _) (oc _ _) gx () m gm um am is g′ m′ gm′ um′ am′ is′ b
E-tr (oi _ _) o0 gx () m gm um am is g′ m′ gm′ um′ am′ is′ b
E-tr (oi _ _) (os _) gx () m gm um am is g′ m′ gm′ um′ am′ is′ b
E-tr (oi _ _) (ol _) gx () m gm um am is g′ m′ gm′ um′ am′ is′ b
E-tr (oi _ _) (od _ _ _ _) gx () m gm um am is g′ m′ gm′ um′ am′ is′ b
E-tr (oi _ _) (oc _ _) gx () m gm um am is g′ m′ gm′ um′ am′ is′ b
E-tr (od _ _ _ _) o0 gx () m gm um am is g′ m′ gm′ um′ am′ is′ b
E-tr (od _ _ _ _) (os _) gx () m gm um am is g′ m′ gm′ um′ am′ is′ b
E-tr (od _ _ _ _) (ol _) gx () m gm um am is g′ m′ gm′ um′ am′ is′ b
E-tr (od _ _ _ _) (oi _ _) gx () m gm um am is g′ m′ gm′ um′ am′ is′ b
E-tr (od _ _ _ _) (oc _ _) gx () m gm um am is g′ m′ gm′ um′ am′ is′ b
E-tr (oc _ _) o0 gx () m gm um am is g′ m′ gm′ um′ am′ is′ b
E-tr (oc _ _) (os _) gx () m gm um am is g′ m′ gm′ um′ am′ is′ b
E-tr (oc _ _) (ol _) gx () m gm um am is g′ m′ gm′ um′ am′ is′ b
E-tr (oc _ _) (oi _ _) gx () m gm um am is g′ m′ gm′ um′ am′ is′ b
E-tr (oc _ _) (od _ _ _ _) gx () m gm um am is g′ m′ gm′ um′ am′ is′ b
```

## §5 第一位置: 值的单调, 证书往下搬

```agda
val⊴ : ∀ {p a u p′ a′ u′} {x : 𝓞 p a u} {y : 𝓞 p′ a′ u′} {gx m gm um am gy m′ gm′ um′ am′} → x ⊴ y → (A₁ : E x gx m gm um am) (B₁ : E y gy m′ gm′ um′ am′) → Mis m u azero a → Mis m′ u′ azero a′ → val x A₁ ⊴₀ val y B₁
vsLˡ : ∀ {p h k u a p′ a′ u′} (j : h <ᴺ p) (x : Low p j k u) {y : 𝓞 p′ a′ u′} {gx m gm um km gy m′ gm′ um′ am′} {am : a ⊲ m} → outL j x ⊴ y → (A₁ : EL {a = a} j x gx m gm um km am) (B₁ : E y gy m′ gm′ um′ am′) → Mis m′ u′ azero a′ → vL j x A₁ ⊴₀ val y B₁
vsLʳ : ∀ {p a u p′ h k u′ a′} {x : 𝓞 p a u} (j : h <ᴺ p′) (y : Low p′ j k u′) {gx m gm um am gy m′ gm′ um′ km′} {am′ : a′ ⊲ m′} → x ⊴ outL j y → (A₁ : E x gx m gm um am) (B₁ : EL {a = a′} j y gy m′ gm′ um′ km′ am′) → Mis m u azero a → val x A₁ ⊴₀ vL j y B₁

vsLˡ zero x {gx = gx} {gm = gm} {um = um} {km = km} d A₁ B₁ is′ = val⊴ d A₁ B₁ (Mi gx gm um km) is′
vsLˡ {a = a} (suc j) x {am = am} d A₁ B₁ is′ = vsLˡ {a = a} j x {am = am} d A₁ B₁ is′
vsLʳ zero y {gy = gy} {gm′ = gm′} {um′ = um′} {km′ = km′} d A₁ B₁ is = val⊴ d A₁ B₁ is (Mi gy gm′ um′ km′)
vsLʳ {a′ = a′} (suc j) y {am′ = am′} d A₁ B₁ is = vsLʳ {a′ = a′} j y {am′ = am′} d A₁ B₁ is

val⊴ {x = x} {y} (rf e) A₁ B₁ is is′ = r0 (val≅ x y A₁ B₁ e is is′)
val⊴ {gy = gy} {gm′ = gm′} {um′ = um′} {am′ = am′} (s d) A₁ B₁ is is′ = l0 1 (val⊴ d A₁ B₁ is (Mi gy gm′ um′ am′))
val⊴ {gy = gy} {gm′ = gm′} {um′ = um′} {am′ = am′} (l n d) A₁ (Bs , _) is is′ = l0 n (val⊴ d A₁ (Bs n) is (Mi gy gm′ um′ am′))
val⊴ {gy = gy} {gm′ = gm′} {um′ = um′} {am′ = am′} (fc d) A₁ (oc′ G₀ _ _ _ _ _ _ _ _) is is′ = l0 0 (val⊴ d A₁ G₀ is (Mi gy gm′ um′ am′))
val⊴ {m′ = m′} {gm′ = gm′} {um′ = um′} {am′ = am′} (ni d) A₁ (rg nz Es st) is is′ = l0 0 (val⊴ (d um′ gm′) A₁ (Es 0) is (Mi gm′ gm′ C.self am′))
val⊴ {m′ = m′} {gm′ = gm′} {um′ = um′} {am′ = am′} (ni d) A₁ (rv is0 vz Es tS st) is is′ = l0 0 (val⊴ (d um′ gm′) A₁ (Es 0) is (Mi gm′ gm′ C.self am′))
val⊴ {m′ = m′} {gm′ = gm′} {um′ = um′} {am′ = am′} (nd d) A₁ (rg nz Es st) is is′ = l0 0 (val⊴ (d um′ gm′) A₁ (Es 0) is (Mi gm′ gm′ C.self am′))
val⊴ {m′ = m′} {gm′ = gm′} {um′ = um′} {am′ = am′} (nd d) A₁ (rv is0 vz Es tS st) is is′ = l0 0 (val⊴ (d um′ gm′) A₁ (Es 0) is (Mi gm′ gm′ C.self am′))
val⊴ {gy = gy} {gm′ = gm′} {um′ = um′} {am′ = am′} (eR {stp = es} d) A₁ B₁ is is′ = val⊴ d A₁ B₁ is (Mi gy gm′ um′ (⊲-tr (C.suc C.self) am′))
val⊴ {gy = gy} {gm′ = gm′} {um′ = um′} {am′ = am′} (eR {stp = el n} d) A₁ B₁ is is′ = val⊴ d A₁ B₁ is (Mi gy gm′ um′ (⊲-tr (C.lim n C.self) am′))
val⊴ {gx = gx} {gm = gm} {um = um} {am = am} (eL {stp = es} d) A₁ B₁ is is′ = val⊴ d A₁ B₁ (Mi gx gm um (⊲-tr (C.suc C.self) am)) is′
val⊴ {gx = gx} {gm = gm} {um = um} {am = am} (eL {stp = el n} d) A₁ B₁ is is′ = val⊴ d A₁ B₁ (Mi gx gm um (⊲-tr (C.lim n C.self) am)) is′
val⊴ {a′ = a′} {am′ = am′} (rL {j = j} {y = y} d) A₁ B₁ is is′ = vsLʳ {a′ = a′} j y {am′ = am′} d A₁ B₁ is
val⊴ {a = a} {am = am} (lL {j = j} {x = x} d) A₁ B₁ is is′ = vsLˡ {a = a} j x {am = am} d A₁ B₁ is′
val⊴ {gm′ = gm′} {um′ = um′} {am′ = am′} (rw {w = w} {g = g} d) A₁ B₁ is is′ = val⊴ d A₁ B₁ is (Mi g gm′ (⊲-tr w um′) am′)
val⊴ {gm = gm} {um = um} {am = am} (lw₂ {w = w} {g = g} d) A₁ B₁ is is′ = val⊴ d A₁ B₁ (Mi g gm (⊲-tr w um) am) is′

val⊴ᵉ : ∀ {p a u p′ a′ u′} {x : 𝓞 p a u} {y : 𝓞 p′ a′ u′} {gx v gv uv av gy v′ gv′ uv′ av′} → x ⊴ y → (A₁ : Ev x gx v gv uv av) (B₁ : Ev y gy v′ gv′ uv′ av′) → val x A₁ ⊴₀ val y B₁
val⊴ᵉ {gx = gx} {v} {gv} {uv} {av} {gy} {v′} {gv′} {uv′} {av′} d A₁ B₁ = val⊴ d A₁ B₁ (Mi gx gv uv av) (Mi gy gv′ uv′ av′)

E-dn : ∀ {p a u p′ a′ u′} (x : 𝓞 p a u) {y : 𝓞 p′ a′ u′} {gy m′ gm′ um′ am′} → x ⊴ y → (gx : Gw u) → ∀ m (gm : Gw m) (um : u ⊲ m) (am : a ⊲ m) → Mis m u azero a →
       (B₁ : E y gy m′ gm′ um′ am′) → Mis m′ u′ azero a′ → Σ (E x gx m gm um am) (λ A₁ → val x A₁ ⊴₀ val y B₁)
dLˡ : ∀ {p h k u a p′ a′ u′} (j : h <ᴺ p) (x : Low p j k u) {y : 𝓞 p′ a′ u′} {gy m′ gm′ um′ am′} → outL j x ⊴ y → (gx : Gw u) → ∀ m (gm : Gw m) (um : u ⊲ m) (km : k ⊲ m) (am : a ⊲ m) →
      (B₁ : E y gy m′ gm′ um′ am′) → Mis m′ u′ azero a′ → Σ (EL {a = a} j x gx m gm um km am) (λ A₁ → vL j x A₁ ⊴₀ val y B₁)
dLʳ : ∀ {p a u p′ h k u′ a′} (x : 𝓞 p a u) (j : h <ᴺ p′) (y : Low p′ j k u′) {gy m′ gm′ um′ km′} {am′ : a′ ⊲ m′} → x ⊴ outL j y → (gx : Gw u) → ∀ m (gm : Gw m) (um : u ⊲ m) (am : a ⊲ m) → Mis m u azero a →
      (B₁ : EL {a = a′} j y gy m′ gm′ um′ km′ am′) → Σ (E x gx m gm um am) (λ A₁ → val x A₁ ⊴₀ vL j y B₁)
dLˡ zero x d gx m gm um km am B₁ is′ = E-dn x d gx _ _ _ _ (Mi gx gm um km) B₁ is′
dLˡ (suc j) x d gx m gm um km am B₁ is′ = dLˡ j x d gx m gm um km am B₁ is′
dLʳ x zero y {gy} {m′} {gm′} {um′} {km′} d gx m gm um am is B₁ = E-dn x d gx m gm um am is B₁ (Mi gy gm′ um′ km′)
dLʳ {a′ = a′} x (suc j) y {am′ = am′} d gx m gm um am is B₁ = dLʳ {a′ = a′} x j y {am′ = am′} d gx m gm um am is B₁

E-dn x {y} {gy} {m′} {gm′} {um′} {am′} (rf e) gx m gm um am is B₁ is′ = let A₁ = E-tr x y gx e m gm um am is gy m′ gm′ um′ am′ is′ B₁ in A₁ , r0 (val≅ x y A₁ B₁ e is is′)
E-dn x {gy = gy} {gm′ = gm′} {um′ = um′} {am′ = am′} (s d) gx m gm um am is B₁ is′ with E-dn x d gx m gm um am is B₁ (Mi gy gm′ um′ am′)
... | A₁ , f = A₁ , l0 1 f
E-dn x {gy = gy} {gm′ = gm′} {um′ = um′} {am′ = am′} (l n d) gx m gm um am is (Bs , _) is′ with E-dn x d gx m gm um am is (Bs n) (Mi gy gm′ um′ am′)
... | A₁ , f = A₁ , l0 n f
E-dn x {gy = gy} {gm′ = gm′} {um′ = um′} {am′ = am′} (fc d) gx m gm um am is (oc′ G₀ _ _ _ _ _ _ _ _) is′ with E-dn x d gx m gm um am is G₀ (Mi gy gm′ um′ am′)
... | A₁ , f = A₁ , l0 0 f
E-dn x {gm′ = gm′} {um′ = um′} {am′ = am′} (ni d) gx m gm um am is (rg nz Es st) is′ with E-dn x (d um′ gm′) gx m gm um am is (Es 0) (Mi gm′ gm′ C.self am′)
... | A₁ , f = A₁ , l0 0 f
E-dn x {gm′ = gm′} {um′ = um′} {am′ = am′} (ni d) gx m gm um am is (rv is0 vz Es tS st) is′ with E-dn x (d um′ gm′) gx m gm um am is (Es 0) (Mi gm′ gm′ C.self am′)
... | A₁ , f = A₁ , l0 0 f
E-dn x {gm′ = gm′} {um′ = um′} {am′ = am′} (nd d) gx m gm um am is (rg nz Es st) is′ with E-dn x (d um′ gm′) gx m gm um am is (Es 0) (Mi gm′ gm′ C.self am′)
... | A₁ , f = A₁ , l0 0 f
E-dn x {gm′ = gm′} {um′ = um′} {am′ = am′} (nd d) gx m gm um am is (rv is0 vz Es tS st) is′ with E-dn x (d um′ gm′) gx m gm um am is (Es 0) (Mi gm′ gm′ C.self am′)
... | A₁ , f = A₁ , l0 0 f
E-dn x {gy = gy} {gm′ = gm′} {um′ = um′} {am′ = am′} (eR {stp = es} d) gx m gm um am is B₁ is′ = E-dn x d gx m gm um am is B₁ (Mi gy gm′ um′ (⊲-tr (C.suc C.self) am′))
E-dn x {gy = gy} {gm′ = gm′} {um′ = um′} {am′ = am′} (eR {stp = el n} d) gx m gm um am is B₁ is′ = E-dn x d gx m gm um am is B₁ (Mi gy gm′ um′ (⊲-tr (C.lim n C.self) am′))
E-dn (oe es x) (eL {stp = es} d) gx m gm um am is B₁ is′ = E-dn x d gx _ _ _ _ (Mi gx gm um (⊲-tr (C.suc C.self) am)) B₁ is′
E-dn (oe (el n) x) (eL {stp = el n} d) gx m gm um am is B₁ is′ = E-dn x d gx _ _ _ _ (Mi gx gm um (⊲-tr (C.lim n C.self) am)) B₁ is′
E-dn {a′ = a′} x {am′ = am′} (rL {j = j} {y = y} d) gx m gm um am is B₁ is′ = dLʳ {a′ = a′} x j y {am′ = am′} d gx m gm um am is B₁
E-dn (oL j k e x) (lL d) gx m gm um am is B₁ is′ = dLˡ j x d gx m gm um (⊲-tr e um) am B₁ is′
E-dn x {gm′ = gm′} {um′ = um′} {am′ = am′} (rw {w = w} {g = g} d) gx m gm um am is B₁ is′ = E-dn x d gx m gm um am is B₁ (Mi g gm′ (⊲-tr w um′) am′)
E-dn (ow w g x) (lw₂ d) gx m gm um am is B₁ is′ = E-dn x d g _ _ _ _ (Mi g gm (⊲-tr w um) am) B₁ is′
```
