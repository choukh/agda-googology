# 分层的 $\approx$: 否定, 与到目标 0 的第一个障碍 (底座)

> 不含记号. 结论写在 [LvStrat](LvStrat.lagda.md). 全部对任何 `S`.
>
> §1 `both-low`, `¬low-≈`: `¬both-low` 的前提 `low-≈` 在新阶段 $T_0$ 上是假的, 两个 $\approx$ 而不字面相同的 `limᴼ` 同时低. §2 `¬CV-copy`: 代价. `CV` 是字面的穿透, 所以 $\Omega_1$ 的副本对目标 $\Omega_1+1$ 没有正确的判决. §3 `¬mono-0`, `cx-y`: **第一个障碍**: 层号上的序 $\sqsubseteq^A$ 经地板元走, 目标 0 上升时只看链, 所以序不传到目标 0. §4 `¬X∈A₀`, `self-bound`: 第 0 层的有界地板装不下目标 0 的链. §5 `no-Ω₂′`: 第 1 层分支全称仍是 WLPO. `¬Reg-floor`: 地板不是全部规整的树.

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.LvStratNeg where

open import Data.Nat using (ℕ; _<_; _≤_; z≤n; s≤s)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ; module Ord-Ord)
open import OCF.Align.InaccTreeBase using
  (Lv; zero; suc; lim; limᴼ; Ordᴸ; Pre; at; Tree; limᵢ; up; Ω; toLv; Verdict; pen; rise; iter)
open import OCF.Align.InaccFloorTree using (Sib; natL; fin; module PF)
open import OCF.Align.LevelKWorld using (Ordᴵ; _<ᴵ_; suc; lim; ωᴵ; natᴵ; em; E; flag; sel; ω₂; g; i; G; κ; tF; tT; flag-false; flag-true; at-natE)
open import OCF.Align.LvStratBase using (Fl; module Leaf; Stage)
open import OCF.Align.LvStratEq using (module Eqv)
open import OCF.Align.LvStratFin using (IsK; module Fin; at-nat)
open import OCF.Align.LvStratLvP using (module LvPs)
import OCF.Align.LvStratTower
open OCF.Align.LvStratTower using (nt; nt≡; module Next)
open import OCF.Align.LvStratOmega
```

## §1 两个 $\approx$ 的 `limᴼ` 同时低

`g₁` 与 `toLv` 在第 0 层的地板上一致 (地板元的层号字面是自然数, 不是极限), 在外面不同. [LevelKNeg](LevelKNeg.lagda.md) 的 `¬both-low` 说: 在 `low-≈` 之下这两个 `limᴼ` 不能同时低. 这里**改变的前提恰好一个: `Stage` 没有 `low-≈`**. 新的低层是 $\approx$ `new` 的全部层号, 它们同时低 (`both-low`), `low-≈` 在这个阶段上是假的 (`¬low-≈`). 新阶段不否定旧定理: 旧定理的前提在这里不成立.

```agda
g₁ : Ordᴸ zero → Lv
g₁ (Tree.lim _) = suc zero
g₁ x = toLv x

Ω₁′ : Lv
Ω₁′ = limᴼ zero g₁

Ω₁≢ : Ω₁L ≡ Ω₁′ → ⊥
Ω₁≢ e = bad (cong-g e)
  where
  x₀ : Ordᴸ zero
  x₀ = Tree.lim (λ _ → Tree.zero)
  cong-g : ∀ {u v : Ordᴸ zero → Lv} → limᴼ zero u ≡ limᴼ zero v → u x₀ ≡ v x₀
  cong-g refl = refl
  bad : toLv x₀ ≡ g₁ x₀ → ⊥
  bad ()

module Copy (S : Sib) where
  open Base S using (T₀; A0; flω; low-n; lw-nat; Stω; bl-Ω₁)
  module X₀ = Base.X₀ S
  private
    module Lω = Leaf flω
    module L₀ = Leaf (Stage.fl T₀)

  g≈ : ∀ x → Lω.Bs zero x → g₁ x Lω.≈ᴮ toLv x
  g≈ Tree.zero    b = Lω.≈ᴮ-refl _
  g≈ (Tree.suc x) b = Lω.≈ᴮ-refl _
  g≈ (Tree.lim h) b with A0 {Tree.lim h} (b (low-n 0))
  ... | ℕ.zero  , ()
  ... | ℕ.suc n , ()

  ≈Ω : Ω₁′ Lω.≈ᴮ Ω₁L
  ≈Ω = Lω.o≈ g≈

  both-low : L₀.Lw Ω₁L × L₀.Lw Ω₁′
  both-low = inj₂ (Lω.≈ᴮ-refl _) , inj₂ ≈Ω

  ¬low-≈ : (∀ {a b} → L₀.Lw a → L₀.Lw b → a L₀.≈ᴮ b → a ≡ b) → ⊥
  ¬low-≈ h = Ω₁≢ (sym (h (proj₂ both-low) (proj₁ both-low) (X₀.≈↑ ≈Ω)))
```

`copy-sim`: 新的 `≈` 真的被用到: 两个 $\Omega$, 分别在 $\Omega_1+1$ 与 $\Omega_1'+1$ 上, 相似, 层号 $\approx$. 旧的 `o≈` 写不出这个 (两侧参数层字面不同).

```agda
  private module P₀ = LvPs S T₀

  ≈₀ : suc Ω₁′ L₀.≈ᴮ suc Ω₁L
  ≈₀ = L₀.s≈ (X₀.≈↑ ≈Ω)

  copy-sim : P₀.Eq (suc Ω₁′) (Ω (suc Ω₁′)) (Ω (suc Ω₁L))
  copy-sim = P₀.Ω≃ ≈₀
    (inj₁ (proj₂ both-low) , P₀.low→lvt Ω₁′ (proj₂ both-low))
    (inj₁ (proj₁ both-low) , P₀.low→lvt Ω₁L (proj₁ both-low))
    (P₀.lvr-low Ω₁′ (proj₂ both-low))

  copy-lv : toLv (Ω (suc Ω₁′)) L₀.≈ᴮ toLv (Ω (suc Ω₁L))
  copy-lv = P₀.b≃ {suc Ω₁′} {suc Ω₁L} (bl-c Ω₁′ (proj₂ both-low)) (bl-c Ω₁L (proj₁ both-low)) copy-sim
    where
    bl-c : ∀ j → L₀.Lw j → L₀.BL (suc j)
    bl-c j l (inj₁ _) _ = l
    bl-c j l (inj₂ r) d = L₀.low-at j l r d
```

## §2 判决的代价

`CV` 的穿透是字面的 (`at i r ≡ j`). 副本 $\Omega_1'$ 对目标 $\Omega_1+1$: 字面的路径没有, 上升也不对 ($\Omega_1\approx\Omega_1'$). 所以**没有任何**判决是 `CV`. 这个否定说的是这里的规格不够宽: 丰富世界里 `S` 被问到副本时, 要 `CV` 多一个 "穿透到 $\approx$ 的路径, 带地板上的搬运" 的构造子 (判断, 没有写). 闭实例的目标里 `S` 没有被问到, 不碰这里.

```agda
  private module E₀ = Eqv S T₀

  ¬CV-copy : ∀ (v : Verdict Ω₁′ (suc Ω₁L)) → E₀.CV v → ⊥
  ¬CV-copy _ (E₀.cvr k) = k (inj₁ tt) tt (X₀.≈↑ (Lω.≈ᴮ-sym ≈Ω))
  ¬CV-copy _ (E₀.cvp (inj₁ _) e _) = Ω₁≢ e
  ¬CV-copy _ (E₀.cvp (inj₂ (inj₁ (inj₁ _))) () _)
  ¬CV-copy _ (E₀.cvp (inj₂ (inj₂ (x , r))) e (a , d))
    with A0 {x} (X₀.A⊃′ (low-n 0) (a (inj₁ (low-n 0))))
  ... | n , q with at-nat n (subst Pre q r)
  ...   | m , _ , q′ = nat≢ m (trans (sym q′) (trans (sym (at-lit q r)) e))
    where
    at-lit : ∀ {a b} (e : a ≡ b) (r : Pre a) → at a r ≡ at b (subst Pre e r)
    at-lit refl r = refl
    nat≢ : ∀ m → natL m ≡ Ω₁′ → ⊥
    nat≢ ℕ.zero ()
    nat≢ (ℕ.suc m) ()
```

## §3 第一个障碍: 层号上的序不传到目标 0

`fy`: 第 1 层的树 $y=\mathrm{limᵢ}\ (z\mapsto g_3\,z)$, 其中 $g_3$ 在 $z\ge2$ 上是 3, 其余是 0. 它的层号是好的 (`cx-y`), 只要地板含 2. 目标 $\ge1$ 时节点穿透, 分支逐点比较: 这是 `mono-lv`. 目标 0 时节点上升, 链从 $\Omega_0=1$ 走: $g_3\,1=0$, $\psi_0(0)=1$, 链不动 (`ch-stuck`), 地板元 2 永远看不到. 所以 $y'=g_3\,2$ 满足 $y'\sqsubseteq^A y$ (`lv⊑`), 而 $\psi_0(y')\not\sqsubseteq^A\psi_0(y)$ (`¬mono-0`).

这就是 `LevelKChain` 的 `¬Zt₀` 背后的数学, 不是技术限制: **`limᵢ-r₀` 与它推出的 `suc-path`, `Ω-path`, `mono-lv` 在目标 0 上是假的.** 观测前序 $\sqsubseteq^\mathsf{o}$ 要到目标 0, 右规则必须带边条件 "地板元低于链".

```agda
g₃ : Ordᴸ zero → Ordᴸ zero
g₃ (Tree.suc (Tree.suc _)) = nt 3
g₃ _ = Tree.zero

fy : Ordᴸ zero → Ordᴸ (natL 1)
fy z = up tt (g₃ z)

y y′ : Ordᴸ (natL 1)
y  = limᵢ (inj₁ tt) fy
y′ = fy (nt 2)

nt-inv : ∀ (z : Ordᴸ zero) n → toLv z ≡ natL n → z ≡ nt n
nt-inv Tree.zero    ℕ.zero    e = refl
nt-inv (Tree.suc z) (ℕ.suc n) e = cong Tree.suc (nt-inv z n (suc-inj e))
  where
  suc-inj : ∀ {a b : Lv} → Lv.suc a ≡ Lv.suc b → a ≡ b
  suc-inj refl = refl
nt-inv (Tree.lim h) ℕ.zero    ()
nt-inv (Tree.lim h) (ℕ.suc n) ()

module Mono0 (S : Sib) where
  open Base S using (A0; A0-nt; flω; Stω; low-n)
  open PF S using (ψᵖ; ψⁿ)
  open Leaf flω

  lv⊑ : toLv y′ ⊑ᴬ toLv y
  lv⊑ r d = viaᴬ (inj₂ (nt 2 , r)) (A0-nt 2 , d) (≈ᴮ-refl _)

  ch : ℕ → Ordᴸ zero
  ch = iter (λ x → ψⁿ 0 (fy x)) (Ω zero)

  ch-stuck : ∀ n → ch n ≡ nt 1
  ch-stuck ℕ.zero = refl
  ch-stuck (ℕ.suc n) = cong (λ x → ψⁿ 0 (fy x)) (ch-stuck n)

  ψy : toLv (ψⁿ 0 y) ≡ lim (λ n → toLv (ψⁿ 0 (fy (ch n))))
  ψy = refl

  at₀ : ∀ t → t ≡ nt 1 → ∀ r → at (toLv (ψⁿ 0 (fy t))) r ≡ zero
  at₀ _ refl (inj₁ _) = refl

  ¬mono-0 : toLv (ψⁿ 0 y′) ⊑ᴬ toLv (ψⁿ 0 y) → ⊥
  ¬mono-0 σ with σ (1 , 1 , 2 , inj₁ tt) tt
  ... | viaᴬ (n , r) _ e = bad (subst (λ u → suc zero ≈ᴮ u) (at₀ (ch n) (ch-stuck n) r) e)
    where
    bad : suc zero ≈ᴮ zero → ⊥
    bad ()

  -- `y` 的层号是好的: 这不是垃圾树
  cx-nat : ∀ n → Cx (natL n)
  cx-nat ℕ.zero    = tt , tt , tt
  cx-nat (ℕ.suc n) = cx-nat n

  cx-g : ∀ z → Cx (toLv (g₃ z))
  cx-g Tree.zero = tt , tt , tt
  cx-g (Tree.suc Tree.zero) = tt , tt , tt
  cx-g (Tree.suc (Tree.suc _)) = cx-nat 3
  cx-g (Tree.suc (Tree.lim _)) = tt , tt , tt
  cx-g (Tree.lim _) = tt , tt , tt

  ⊑3 : ∀ z → toLv (g₃ z) ⊑ᴬ toLv (g₃ (nt 2))
  ⊑3 Tree.zero = λ ()
  ⊑3 (Tree.suc Tree.zero) = λ ()
  ⊑3 (Tree.suc (Tree.suc _)) = ⊑ᴬ-refl
  ⊑3 (Tree.suc (Tree.lim _)) = λ ()
  ⊑3 (Tree.lim _) = λ ()

  nat≈′ : ∀ n {a} → a ≈ᴮ natL n → a ≡ natL n
  nat≈′ ℕ.zero z≈ = refl
  nat≈′ (ℕ.suc n) (s≈ e) = cong Lv.suc (nat≈′ n e)

  z≡ : ∀ {z z′} → A zero z → A zero z′ → toLv z ≈ᴮ toLv z′ → z ≡ z′
  z≡ {z} {z′} a a′ t with A0 {z′} a′
  ... | n , e =
    trans (nt-inv z n (nat≈′ n (subst (λ u → toLv z ≈ᴮ u) e t))) (sym (nt-inv z′ n e))

  mono-g : ∀ z z′ → A zero z → A zero z′ → toLv z ⊑ᴬ toLv z′ → toLv (g₃ z) ⊑ᴬ toLv (g₃ z′)
  mono-g Tree.zero z′ _ _ _ = λ ()
  mono-g (Tree.suc Tree.zero) z′ _ _ _ = λ ()
  mono-g (Tree.suc (Tree.lim _)) z′ _ _ _ = λ ()
  mono-g (Tree.lim _) z′ _ _ _ = λ ()
  mono-g (Tree.suc (Tree.suc x)) z′ a a′ σ with σ (inj₁ tt) tt
  ... | viaᴬ q d e = go z′ a′ q e
    where
    go : ∀ z″ → A zero z″ → (q : Pre (toLv z″)) → suc (toLv x) ≈ᴮ at (toLv z″) q →
         toLv (g₃ (Tree.suc (Tree.suc x))) ⊑ᴬ toLv (g₃ z″)
    go (Tree.suc Tree.zero) _ (inj₁ _) ()
    go (Tree.suc (Tree.suc _)) _ q e = ⊑ᴬ-refl
    go (Tree.suc (Tree.lim h)) ah _ _ with A0 {Tree.suc (Tree.lim h)} ah
    ... | ℕ.suc ℕ.zero , ()
    ... | ℕ.suc (ℕ.suc _) , ()
    go (Tree.lim h) ah _ _ with A0 {Tree.lim h} ah
    ... | ℕ.zero , ()
    ... | ℕ.suc _ , ()

  cx-y : Cx (toLv y)
  cx-y =
    ((λ a b _ _ → nt 2 , A0-nt 2 , ⊑3 a , ⊑3 b) ,
     (nt 2 , A0-nt 2 , viaᴬ (inj₂ (inj₂ (inj₁ tt))) tt z≈ , (λ ())) ,
     (λ z _ → proj₁ (cx-g z))) ,
    ((λ z _ → proj₁ (proj₂ (cx-g z))) ,
     (λ z z′ b b′ t → subst (λ u → toLv (g₃ z) ≈ᴮ toLv (g₃ u)) (z≡ (b (low-n 0)) (b′ (low-n 0)) t) (≈ᴮ-refl _))) ,
    ((λ z _ → proj₂ (proj₂ (cx-g z))) , mono-g)
```

## §4 第 0 层的有界地板装不下目标 0 的链

[LevelKChain](LevelKChain.lagda.md) 说还差 "链点在 `Bs` 里". 这里说明为什么单靠世界做不到. `¬X∈A₀`: 闭实例的第 0 层地板 (世界 $\omega$) 不含任何 $\psi_0(\Omega_a)$: 它们的头都是极限. `self-bound`: **一般地**, 第 0 层节点 $\mathrm{limᴼ}\ 0\ g$ 的链要是都低于 $L_0$, 那么目标 0 的输出自己就 $\sqsubseteq^A L_0$. 所以世界必须先于输出把输出框住, 而世界的 `Cx` 在 `Next` 里是前提. 阶段的次序在目标 0 上是倒的. 目标 $K\ge1$ 没有这个问题, 第 $K$ 层的节点上升时链在第 $K$ 层, 第 $K$ 层此时没有地板 (`Bs-nz`).

```agda
X-lim : ∀ (S : Sib) a → Σ (ℕ → Ordᴸ zero) λ h → PF.ψⁿ S 0 (Ω a) ≡ Tree.lim h
X-lim S zero       = _ , refl
X-lim S (suc a)    = _ , refl
X-lim S (lim f)    = _ , refl
X-lim S (limᴼ k g) = _ , refl

module Floor0 (S : Sib) where
  open Base S using (A0; flω)
  open Leaf flω

  ¬X∈A₀ : ∀ a → A zero (PF.ψⁿ S 0 (Ω a)) → ⊥
  ¬X∈A₀ a ax with X-lim S a
  ... | h , e with A0 (subst (A zero) e ax)
  ... | ℕ.zero  , ()
  ... | ℕ.suc n , ()

module SelfBound (S : Sib) (F : Fl) where
  open Leaf F
  open PF S using (ψⁿ)

  X : Lv → Ordᴸ zero
  X a = ψⁿ 0 (Ω a)

  c : (Ordᴸ zero → Lv) → ℕ → Ordᴸ zero
  c h = iter (λ t → X (h t)) (Tree.suc Tree.zero)

  self-bound : ∀ (h : Ordᴸ zero → Lv) L₀ → (∀ m → toLv (c h m) ≺ᴬ L₀) → toLv (X (limᴼ zero h)) ⊑ᴬ L₀
  self-bound h L₀ b (m , r) d = ≺→⊑ (b (ℕ.suc m)) r d
```

## §5 全称的分支与规整的树

`no-Ω₂′`: 与 [LevelKNeg](LevelKNeg.lagda.md) 逐字相同的反例族: 第 1 层的 `Bs` 含全部 `up tt (em a)`, 就是 WLPO. 分层没有动这条. `¬Reg-floor`: 地板不能同时含 $\omega_0+1$, $\omega_1+1$: `cmpA` 没有动.

```agda
WLPO : Set
WLPO = ∀ (s : ℕ → Bool) → (∀ n → s n ≡ false) ⊎ ¬ (∀ n → s n ≡ false)

module NegK (S : Sib) (St : Stage) (K : ℕ) (isK : IsK K St) where
  open Fin S St
  open IsK isK

  J : Lv
  J = E (suc ωᴵ)

  I : (ℕ → Bool) → Lv
  I s = E (suc (i s))

  natL≢ : ∀ m {f : ℕ → Lv} → natL m ≡ Lv.suc (Lv.lim f) → ⊥
  natL≢ ℕ.zero ()
  natL≢ (ℕ.suc ℕ.zero) ()
  natL≢ (ℕ.suc (ℕ.suc m)) ()

  read : ∀ s → LvT (κ s) → CV (S J (I s))
  read s w with proj₁ w (1 , inj₁ tt) tt
  ... | inj₁ l = ⊥-elim (let m , _ , e = lw⇒ _ l in natL≢ m (sym e))
  ... | inj₂ (ok , _) = proj₁ ok (0 , inj₁ tt) tt

  no-pen : ∀ s → (∀ n → s n ≡ false) → ∀ (r : Pre (I s)) → at (I s) r ≡ J → ⊥
  no-pen s h (inj₁ _) ()
  no-pen s h (inj₂ (n , r)) e = go (flag s n) (flag-false s h n) r e where
    go : ∀ b → b ≡ false → (r : Pre (E (sel b n))) → at (E (sel b n)) r ≡ J → ⊥
    go _ refl r e with at-natE n r
    ... | m , e′ = natL≢ m (trans (sym e′) e)

  yes-path : ∀ b n → b ≡ true → Σ (Pre (E (sel b n))) λ r → AdmB (E (sel b n)) r × at (E (sel b n)) r ≈ᴮ J
  yes-path _ n refl = inj₁ tt , tt , ≈ᴮ-refl J

  dec : ∀ s (v : Verdict J (I s)) → ((∀ n → s n ≡ false) → CV v) → (∀ n → s n ≡ true → CV v) →
        (∀ n → s n ≡ false) ⊎ ((∀ n → s n ≡ false) → ⊥)
  dec s (pen r b) c₁ c₂ = inj₂ λ h → absurd h (c₁ h) where
    absurd : (∀ n → s n ≡ false) → CV (pen r b) → ⊥
    absurd h (cvp _ e _) = no-pen s h r e
  dec s rise c₁ c₂ = inj₁ λ n → go n (s n) refl where
    go : ∀ n b → s n ≡ b → s n ≡ false
    go n false p = p
    go n true  p with c₂ n p
    ... | cvr k with yes-path (flag s n) n (flag-true s n p)
    ...   | r , d , e = ⊥-elim (k (inj₂ (n , r)) d e)

  no-uniform : (∀ a → LvT (E a)) → WLPO
  no-uniform H s = dec s (S J (I s))
    (λ h → read s (H (lim (G s) (tF s h))))
    (λ n p → read s (H (lim (G s) (tT s n p))))

  no-uniformG : (∀ a → LvG (E a)) → WLPO
  no-uniformG H = no-uniform (λ a → proj₂ (H (suc a)))

  no-Ω₂′ : LvG (toLv (Ω (natL 2))) → (∀ a → Bs (natL 1) (up tt (em a))) → WLPO
  no-Ω₂′ w full = no-uniformG (λ a → proj₂ (proj₂ w) (up tt (em a)) (full a))

ω₀ ω₁ : Ordᴸ zero
ω₀ = Tree.lim nt
ω₁ = Tree.lim (λ n → nt (ℕ.suc n))

at-nt : ∀ n (r : Pre (toLv (nt n))) → Σ ℕ λ m → at (toLv (nt n)) r ≡ toLv (nt m)
at-nt (ℕ.suc n) (inj₁ _) = n , refl
at-nt (ℕ.suc n) (inj₂ r) = at-nt n r

lim≉ᴮ : ∀ (F : Fl) {f} {c} m → c ≡ toLv (nt m) → Leaf._≈ᴮ_ F (Lv.suc (Lv.lim f)) c → ⊥
lim≉ᴮ F ℕ.zero refl ()
lim≉ᴮ F (ℕ.suc ℕ.zero) refl (Leaf.s≈ ())
lim≉ᴮ F (ℕ.suc (ℕ.suc m)) refl (Leaf.s≈ ())

¬Reg-floor : (St : Stage) → let open Stage St ; open Leaf fl in
             A zero (Tree.suc ω₀) → A zero (Tree.suc ω₁) → ⊥
¬Reg-floor St a a′ with Stage.cmpA St zero (Tree.suc ω₀) (Tree.suc ω₁) a a′
... | injᵃ (Leaf.viaᴬ (inj₁ _) _ ())
... | injᵃ (Leaf.viaᴬ (inj₂ (n , r)) _ e) =
  lim≉ᴮ (Stage.fl St) (proj₁ (at-nt (ℕ.suc n) r)) (proj₂ (at-nt (ℕ.suc n) r)) e
... | injᵇ (Leaf.viaᴬ (inj₁ _) _ ())
... | injᵇ (Leaf.viaᴬ (inj₂ (n , r)) _ e) =
  lim≉ᴮ (Stage.fl St) (proj₁ (at-nt n r)) (proj₂ (at-nt n r)) e
... | injᶜ (Leaf.s≈ (Leaf.l≈ h)) with h 0
...   | ()

bounded : ∀ (St : Stage) new N W j x → Next.A′ St new N W j x →
          Leaf.Lw (Stage.fl St) j ⊎ Leaf._≺ᴬ_ (Stage.fl St) (toLv x) (OCF.Align.LvStratTower.World.L W)
bounded St new N W j x (inj₁ a) = inj₁ (Leaf.A→Lw (Stage.fl St) j x a)
bounded St new N W j x (inj₂ (_ , _ , p , d , e)) = inj₂ (Leaf.viaᴬ p d e)
```
