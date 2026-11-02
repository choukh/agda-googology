# 统一折叠上的记号无关证书 (二): 深度 0 的遗传好树与闭包定理

> 接 [UniformNFBase](UniformNFBase.lagda.md). 本文是 TreeNFBase §4–§5 (`Floor β cov`) 与 Stage2Label §3–§5 (`Good-ψ0`/`Good-ψ1`/`popGood`/`Strict₁`) 在统一折叠上的合并移植. 检验与验收在 [UniformNF](UniformNF.lagda.md).
>
> 结论先说:
>
> 1. **遗传好树 `Floor.Good` (§1).** 以前缀 $P$ (及其自互模拟)、地板层 $\varphi_0$、界 $\beta$、支配假设 `S⁺ : FlΛ φ₀ y → ColC P β y` (由 Base 的 `dom-cov` 与一个覆盖得到, 或在 $\beta=0$ 时平凡) 与再生条件 `reg` ($0<^\mathsf I\ell$ 下非零目标 $\sqsupseteq\varphi_0$) 为模块参数. 非零层闭包的支配 `Occ≺ c t₀ g` $=c\sqsubseteq\beta$ 且第 0 点与各点被 $\beta$ 支配 (相对 $P$-折叠). 其余 (搬运、$\Omega$、加法、`Good→Goodᶻ`) 照 TreeNFBase 逐字.
> 2. **一条折叠定理代替两条 (§2).** `Fold.Good-fold`: 对任意前缀 $Q$ (有自互模拟与地板, 其值在到达的目标处好), 任意好且自反的尾巴, 折叠好. 它以一个目标 0 处的允许谓词族 `Ok0` 与它的遗传引理为参数: $Q=P$ 时 `Ok0` 平凡, 非零层闭包映到目标 0 的支配由输入的 `Occ≺` 在观测 `col` 处给出 (`ok-ŝ`); $Q=\emptyset^\mathsf R$ (空前缀) 时 `Ok0 = Pl` (无符号), 该情形被排除. 目标条件 `Tg` 只对**到达的**目标 (初始目标与尾巴层号的子层号) 要求, 不对整个环境 (统一形里极限层尾巴 $\Omega_{\beta_0}$ 的地板 `fk β₀` 迫使环境含 $\beta_0$ 本身, 而目标 $\beta_0$ 永不被到达).
> 3. **$\Omega_\Omega$ 闭包的好性 (§3).** `goodΩ̂∅ : (NZ i → suc i ⊑ᴵ β) → Good (Ω̂A 0 ∅ᴿ ev p)`: 地板平凡时非紧界字面是目标 (`Mx∅ : Mx (bound (fz ⊔ fk zero) ev p) ≡ i`, 由 `src` 分析), 目标 0 的支配由 `Strict₀`, 非零目标由 `S⁺` 与再生的地板. 这是 Stage2Label `popGood`/`popDom` 的统一形, 第 0 点与各点的好性由折叠定理在 $Q=\emptyset^\mathsf R$、`Ok0 = Pl` 处实例化.
> 4. **`FloorΩ̂`: 以 $P=\Omega_\Omega$ 闭包为前缀的折叠定理 (§4).** `Good-foldP : Tg i → (∀ j <ᴵ k → Tg j) → Good x → x ≅ˢ x → Good (fold 0 φ cv (Ω̂A 0 ∅ᴿ) x ev p)`, `Tg i = NZ i → suc i ⊑ᴵ β`, 无其他前提. 这是 TreeNF `Floor.Good-ψ1` 的统一形.
> 5. **严格性 `Strict₁` (§5).** 给定 $\Omega_\Omega$ 闭包在目标 0 的任一证书, 一切以它为前缀、目标 0 的折叠输出层号 $\sqsupseteq2$ (`one≺`/`onepop`/`B1`/`two⊑`).
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入已有模块, 不改任何已有文件. 定义与证明不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformNFDepth0 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Symbolic using (Mlev)
open import OCF.Align.Prefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Restrˢ; trˢ; tr⁻ˢ; resˢ; res⁻ˢ;
  Ωˢ; addˢ; _+ˢ_; Goodᶻ; force; force-HS; z<suc)
open Restrˢ
open import OCF.Align.UniformS using (kd; kd-≅; ≅ᴵ→⊑ᴵ; ⊑ᴵ-≅ˡ; ⊑ᴵ-≅ʳ; _≅ᶻ_; force-≅; Goodᶻ-tr;
  _≅ˢ_; z≅; s≅; l≅; lᵢ≅; upˡ; upʳ; ŝ≅; ĉ≅; ≅ˢ-sym; ≅ˢ-trans; ≅ˢ-reflˡ; ≅ˢ-reflʳ;
  trˢ-≅; tr⁻ˢ-≅; backˢ-≅; back⁻ˢ-≅; ≅-trˢ; ≅-tr⁻ˢ; Ωˢ-≅; Ωˢ-refl; toZ-≅; tf; addˢ-≅;
  s-invˢ; l-invˢ; i-respˢ; u-reflˢ; ŝ-refl₀; ĉ-refl₀; self-trˢ; self-tr⁻ˢ; ĉ-reflg;
  two; Lv; Lv-refl; Lv-up)
open import OCF.Align.Stage2Label using (one⁰; two⁰; two⊑; h2)
open import OCF.Align.Uniform2Base using (Flr; fz; fk; _⊔_; Ev; InF; ink; inl; inr; liftEv; Run; A; wk; limA; limᵢA; ŝA; ĉA;
  Top; top; bound; Mx; mx; src; Fc; evF; iF; FM; MF; FB; cloA; flo; cvFlo; toFlo; fold; Ω̂A; ∅ᴿ;
  _≈ᴿ_; fold-≅0; chainA; ≺0)
open import OCF.Align.UniformNFBase hiding (Occ-tr; Occ-tr⁻; Occ-add; Occ-fold; Occ-pop)
```

## §0 非零层号与目标条件

```agda
NZ : Ordᴵ → Set
NZ zero      = ⊥
NZ (suc _)   = ⊤
NZ (lim _ _) = ⊤

one⊑ : ∀ {i ℓ} → zero <ᴵ ℓ → i <ᴵ ℓ → NZ i → suc zero ⊑ᴵ i
one⊑ z p nz with <ᴵ-dec z p
... | injᵃ r          = s⊑′ r
... | injᵇ (via e ())
... | injᶜ z≅         = ⊥-elim nz

record Wrap (A : Set) : Set where
  constructor wrap
  field unwrap : A
open Wrap
```

## §1 `Floor`: 相对前缀 $P$ 的遗传好树

```agda
module Floor {fl} (P : Run fl) (rP : P ≈ᴿ P) (φ₀ β : Ordᴵ)
             (S⁺ : ∀ {k} {y : Ordˢ k} → FlΛ φ₀ y → ColC P β y)
             (reg : ∀ {i ℓ} → zero <ᴵ ℓ → i <ᴵ ℓ → NZ i → φ₀ ⊑ᴵ i) where

  Occ≺ : ∀ {k} (c : Ordᴵ) → Ordˢ k → ((η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k) → Set
  Occ≺ c t₀ g = c ⊑ᴵ β × ColC P β t₀ × (∀ η e → ColC P β (g η e))

  Dom : (ℓ c : Ordᴵ) → Ordˢ ℓ → ((η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ) → Set
  Dom zero      c t₀ g = (∀ G → c ⊑ᴵ toLevel (force (toZ t₀) G) (force-HS _ G)) ×
                         (∀ η e G → c ⊑ᴵ toLevel (force (toZ (g η e)) G) (force-HS _ G))
  Dom (suc _)   c t₀ g = Occ≺ c t₀ g
  Dom (lim _ _) c t₀ g = Occ≺ c t₀ g

  module _ (ℓ : Ordᴵ) (G< : (i : Ordᴵ) (r : i ◃ ℓ) → Uˢ i r → Set) where
    data Good₊ : Ordˢ ℓ → Set where
      bz : Good₊ Ord₊ˢ.zero
      bs : ∀ {a} → Good₊ a → Good₊ (Ord₊ˢ.suc a)
      bl : ∀ {h : ℕ → Ordˢ ℓ} → (∀ n → Good₊ (h n)) → (∀ n → h n ⊑ᵒ h (suc n)) → Good₊ (Ord₊ˢ.lim h)
      bi : ∀ {j} {p : j <ᴵ ℓ} {f : Uˢ j (<→◃ p) → Ordˢ ℓ} →
           (∀ (z : Ordˢ j) → z ≅ˢ z → G< j (<→◃ p) (intoˢ (<→◃ p) z) → Good₊ (f (intoˢ (<→◃ p) z))) →
           (∀ {z z′ : Ordˢ j} → z ⊑ᵒ z′ → f (intoˢ (<→◃ p) z) ⊑ᵒ f (intoˢ (<→◃ p) z′)) →
           Good₊ (Ord₊ˢ.limᵢ p f)
      bu : ∀ {k} {r : k ◃₁ ℓ} {x : Uˢ k (◃₁→◃ r)} → G< k (◃₁→◃ r) x → Good₊ (Ord₊ˢ.up r x)
      bŝ : ∀ {c} {t₀ : Ordˢ ℓ} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ} →
           Good₊ t₀ → (∀ η e → Good₊ (g η e)) →
           t₀ ≅ˢ t₀ → (∀ η e η′ e′ → η ≅ᴵ η′ → g η e ≅ˢ g η′ e′) →
           (∀ η e → t₀ ⊑ᵒ g η e) → (∀ η e η′ e′ → η ⊑ᴵ η′ → g η e ⊑ᵒ g η′ e′) →
           Dom ℓ c t₀ g → Good₊ (Ord₊ˢ.ŝ c t₀ g)
      bĉ : ∀ {c t₀} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z} {o₀ : Ordˢ ℓ} {o : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ}
           (G₀ : Goodᶻ t₀) (Gg : ∀ η e → Goodᶻ (g η e)) →
           c ⊑ᴵ toLevel (force t₀ G₀) (force-HS t₀ G₀) →
           (∀ η e → c ⊑ᴵ toLevel (force (g η e) (Gg η e)) (force-HS (g η e) (Gg η e))) →
           (∀ η e → force t₀ G₀ ⊑⁰ force (g η e) (Gg η e)) →
           (∀ η e η′ e′ → η ⊑ᴵ η′ → force (g η e) (Gg η e) ⊑⁰ force (g η′ e′) (Gg η′ e′)) →
           Good₊ o₀ → (∀ η e → Good₊ (o η e)) →
           (∀ η e → o₀ ⊑ᵒ o η e) → (∀ η e η′ e′ → η ⊑ᴵ η′ → o η e ⊑ᵒ o η′ e′) →
           Good₊ (Ord₊ˢ.ĉᴸ c t₀ g o₀ o)

  Gd : ∀ {ℓ} (i : Ordᴵ) (r : i ◃ ℓ) → Uˢ i r → Set
  Gd i zero         x = Good₊ i Gd x
  Gd i (suc r)      x = Gd i r x
  Gd _ (self {f} n) x = Good₊ (f n) Gd x
  Gd i (lim n r)    x = Gd i r x

  Good : ∀ {ℓ} → Ordˢ ℓ → Set
  Good {ℓ} = Good₊ ℓ Gd

  Gd→Good : ∀ {i ℓ} (r : i ◃ ℓ) {x : Ordˢ i} → Gd i r (intoˢ r x) → Good x
  Gd→Good zero      g = g
  Gd→Good (suc r)   g = Gd→Good r g
  Gd→Good (self n)  g = g
  Gd→Good (lim n r) g = Gd→Good r g

  Good→Gd : ∀ {i ℓ} (r : i ◃ ℓ) {x : Ordˢ i} → Good x → Gd i r (intoˢ r x)
  Good→Gd zero      g = g
  Good→Gd (suc r)   g = Good→Gd r g
  Good→Gd (self n)  g = g
  Good→Gd (lim n r) g = Good→Gd r g

  Gd-conv : ∀ {i ℓ ℓ′} (r : i ◃ ℓ) (r′ : i ◃ ℓ′) {x : Ordˢ i} → Gd i r (intoˢ r x) → Gd i r′ (intoˢ r′ x)
  Gd-conv r r′ g = Good→Gd r′ (Gd→Good r g)

  Good→Goodᶻ : ∀ {x : Ordˢ zero} → Good x → Goodᶻ (toZ x)
  Good→Goodᶻ bz         = Goodᶻ.gz
  Good→Goodᶻ (bs g)     = Goodᶻ.gs (Good→Goodᶻ g)
  Good→Goodᶻ (bl hg st) = Goodᶻ.gl (λ n → Good→Goodᶻ (hg n)) (λ n → st n idO (Good→Goodᶻ (hg n)) (Good→Goodᶻ (hg (suc n))))
  Good→Goodᶻ (bi {p = ()} hb hm)
  Good→Goodᶻ (bu {r = ()} g)
  Good→Goodᶻ (bŝ g₀ gg et eg m mm (d₀ , dE)) =
    Goodᶻ.gc G₀ Gg (d₀ G₀) (λ η e → dE η e (Gg η e))
             (λ η e → m η e idO G₀ (Gg η e)) (λ η e η′ e′ h → mm η e η′ e′ h idO (Gg η e) (Gg η′ e′))
             G₀ Gg (λ η e → m η e idO G₀ (Gg η e)) (λ η e η′ e′ h → mm η e η′ e′ h idO (Gg η e) (Gg η′ e′))
    where
    G₀ = Good→Goodᶻ g₀
    Gg = λ η e → Good→Goodᶻ (gg η e)
  Good→Goodᶻ (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) =
    Goodᶻ.gc G₀ Gg d₀ dE m₀ mE (Good→Goodᶻ go) (λ η e → Good→Goodᶻ (gO η e))
             (λ η e → mo η e idO (Good→Goodᶻ go) (Good→Goodᶻ (gO η e)))
             (λ η e η′ e′ h → mO η e η′ e′ h idO (Good→Goodᶻ (gO η e)) (Good→Goodᶻ (gO η′ e′)))
```

**`Occ≺` 的保持** (Base §5 的 `Occ-…` 在固定界 $\beta$ 的实例: 搬运定义性; 加法要前缀的地板; 任意前缀 $Q$ 的折叠要目标 $\sqsupseteq\varphi_0$ 与 $Q$ 的地板, 支配由 `S⁺` 重算).

```agda
  Occ-tr : ∀ {a b c} (e : a ≅ᴵ b) {t₀ : Ordˢ a} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ a} →
           Occ≺ c t₀ g → Occ≺ c (trˢ e t₀) (λ η d → trˢ e (g η d))
  Occ-tr e (cb , c₀ , cg) = cb , ColC-tr e c₀ , λ η d → ColC-tr e (cg η d)

  Occ-tr⁻ : ∀ {a b c} (e : a ≅ᴵ b) {t₀ : Ordˢ b} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ b} →
            Occ≺ c t₀ g → Occ≺ c (tr⁻ˢ e t₀) (λ η d → tr⁻ˢ e (g η d))
  Occ-tr⁻ e (cb , c₀ , cg) = cb , ColC-tr⁻ e c₀ , λ η d → ColC-tr⁻ e (cg η d)

  Occ-add : ∀ {k ℓ c} {a : Ordˢ ℓ} {σ : Simᴵ k ℓ} {t₀ : Ordˢ k} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k} →
            FlΛ φ₀ a → t₀ ≅ˢ t₀ → (∀ η e → g η e ≅ˢ g η e) → Occ≺ c t₀ g → Occ≺ c (addˢ a σ t₀) (λ η e → addˢ a σ (g η e))
  Occ-add {t₀ = t₀} {g = g} fa et eg (cb , _ , _) = cb , S⁺ (FlΛ-add t₀ fa et) , λ η e → S⁺ (FlΛ-add (g η e) fa (eg η e))

  Occ-fold : ∀ {fl′ φ k i ℓ c} {Q : Run fl′} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fl′ ⊔ φ)} {p : i <ᴵ ℓ}
             {t₀ : Ordˢ k} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k} → Q ≈ᴿ Q → FlR Q → φ₀ ⊑ᴵ i →
             Occ≺ c t₀ g → t₀ ≅ˢ t₀ → (∀ η e → g η e ≅ˢ g η e) →
             Occ≺ c (fold 0 φ cv Q t₀ ev p) (λ η e → fold 0 φ cv Q (g η e) ev p)
  Occ-fold {φ = φ} {Q = Q} {cv = cv} {ev = ev} {p = p} {t₀ = t₀} {g = g} rQ fQ h (cb , _ , _) et eg =
    cb , S⁺ (FlΛ-fold {φ = φ} {P = Q} {cv = cv} {ev = ev} {p = p} rQ fQ h t₀ et) ,
    λ η e → S⁺ (FlΛ-fold {φ = φ} {P = Q} {cv = cv} {ev = ev} {p = p} rQ fQ h (g η e) (eg η e))
```

**搬运、$\Omega$、加法** (TreeNFBase §4 逐字; `Good-add` 的非零层前缀要带地板 `FlA`).

```agda
  Dom0-≅ : ∀ {c} {t₀ t₀′ : Ordˢ zero} {g g′ : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ zero} →
           Good t₀ → (∀ η d → Good (g η d)) → t₀′ ≅ˢ t₀ → (∀ η d → g′ η d ≅ˢ g η d) →
           Dom zero c t₀ g → Dom zero c t₀′ g′
  Dom0-≅ g0 gg et eg (d₀ , dE) =
    (λ G → ⊑ᴵ-≅ʳ (d₀ (Good→Goodᶻ g0)) (toLevel-≅ (force-HS _ (Good→Goodᶻ g0)) (force-HS _ G)
              (force-≅ (toZ-≅ (≅ˢ-sym et)) (Good→Goodᶻ g0) G))) ,
    (λ η d G → ⊑ᴵ-≅ʳ (dE η d (Good→Goodᶻ (gg η d))) (toLevel-≅ (force-HS _ (Good→Goodᶻ (gg η d))) (force-HS _ G)
              (force-≅ (toZ-≅ (≅ˢ-sym (eg η d))) (Good→Goodᶻ (gg η d)) G)))

  Dom-tr : ∀ {a b c} (e : a ≅ᴵ b) {t₀ : Ordˢ a} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ a} →
           Good t₀ → (∀ η d → Good (g η d)) → t₀ ≅ˢ t₀ → (∀ η d → g η d ≅ˢ g η d) →
           Dom a c t₀ g → Dom b c (trˢ e t₀) (λ η d → trˢ e (g η d))
  Dom-tr z≅     g0 gg et eg h = Dom0-≅ g0 gg (trˢ-≅ z≅ et) (λ η d → trˢ-≅ z≅ (eg η d)) h
  Dom-tr e@(s≅ _) g0 gg et eg h = Occ-tr e h
  Dom-tr e@(l≅ _) g0 gg et eg h = Occ-tr e h

  Dom-tr⁻ : ∀ {a b c} (e : a ≅ᴵ b) {t₀ : Ordˢ b} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ b} →
            Good t₀ → (∀ η d → Good (g η d)) → t₀ ≅ˢ t₀ → (∀ η d → g η d ≅ˢ g η d) →
            Dom b c t₀ g → Dom a c (tr⁻ˢ e t₀) (λ η d → tr⁻ˢ e (g η d))
  Dom-tr⁻ z≅     g0 gg et eg h = Dom0-≅ g0 gg (tr⁻ˢ-≅ z≅ et) (λ η d → tr⁻ˢ-≅ z≅ (eg η d)) h
  Dom-tr⁻ e@(s≅ _) g0 gg et eg h = Occ-tr⁻ e h
  Dom-tr⁻ e@(l≅ _) g0 gg et eg h = Occ-tr⁻ e h

  back-mono : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {u u′ : Ordˢ (repˢ (resˢ q e))} → u ⊑ᵒ u′ → backˢ (resˢ q e) u ⊑ᵒ backˢ (resˢ q e) u′
  back-mono zero      (s≅ e) h = tr⁻-cong h
  back-mono (suc q)   (s≅ e) h = back-mono q e h
  back-mono (lim n q) (l≅ f) h = back-mono q (f n) h

  back⁻-mono : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {u u′ : Ordˢ (repˢ (res⁻ˢ q e))} → u ⊑ᵒ u′ → backˢ (res⁻ˢ q e) u ⊑ᵒ backˢ (res⁻ˢ q e) u′
  back⁻-mono zero      (s≅ e) h = tr-cong h
  back⁻-mono (suc q)   (s≅ e) h = back⁻-mono q e h
  back⁻-mono (lim n q) (l≅ f) h = back⁻-mono q (f n) h

  self-back : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (resˢ q e))} → u ≅ˢ u → backˢ (resˢ q e) u ≅ˢ backˢ (resˢ q e) u
  self-back q e d = ≅ˢ-reflˡ (backˢ-≅ q e d)

  self-back⁻ : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (res⁻ˢ q e))} → u ≅ˢ u → backˢ (res⁻ˢ q e) u ≅ˢ backˢ (res⁻ˢ q e) u
  self-back⁻ q e d = ≅ˢ-reflˡ (back⁻ˢ-≅ q e d)

  Good-tr    : ∀ {a b} (e : a ≅ᴵ b) {x : Ordˢ a} → Good x → Good (trˢ e x)
  Good-tr⁻   : ∀ {a b} (e : a ≅ᴵ b) {x : Ordˢ b} → Good x → Good (tr⁻ˢ e x)
  Good-back  : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (resˢ q e))} → Good u → Good (backˢ (resˢ q e) u)
  Good-back⁻ : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (res⁻ˢ q e))} → Good u → Good (backˢ (res⁻ˢ q e) u)

  Good-tr e bz         = bz
  Good-tr e (bs g)     = bs (Good-tr e g)
  Good-tr e (bl hg st) = bl (λ n → Good-tr e (hg n)) (λ n → tr-cong (st n))
  Good-tr e (bi {p = q} {f = f} hb hm) = bi
    (λ z ez g → subst (λ w → Good (trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) w))))) (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) z))
                      (Good-tr e (hb (backˢ (resˢ q e) z) (self-back q e ez)
                                     (Good→Gd (<→◃ q) (Good-back q e (Gd→Good (<→◃ (ltˢ (resˢ q e))) g))))))
    (λ {z} {z′} h → subst₂ (λ w w′ → trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) w))) ⊑ᵒ trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) w′))))
                           (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) z)) (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) z′))
                           (tr-cong (hm (back-mono q e h))))
  Good-tr (s≅ e) (bu {r = zero} g)   = bu (Good-tr e g)
  Good-tr (l≅ f) (bu {r = self n} g) = bu (Good-tr (f n) g)
  Good-tr e (bŝ g0 gg et eg m mm dm) =
    bŝ (Good-tr e g0) (λ η d → Good-tr e (gg η d)) (self-trˢ e et)
       (λ η d η′ d′ eη → trˢ-≅ e (≅-trˢ e (eg η d η′ d′ eη)))
       (λ η d → tr-cong (m η d)) (λ η d η′ d′ h → tr-cong (mm η d η′ d′ h))
       (Dom-tr e g0 gg et (λ η d → eg η d η d (≅ᴵ-refl η)) dm)
  Good-tr e (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) =
    bĉ G₀ Gg d₀ dE m₀ mE (Good-tr e go) (λ η d → Good-tr e (gO η d))
       (λ η d → tr-cong (mo η d)) (λ η d η′ d′ h → tr-cong (mO η d η′ d′ h))

  Good-tr⁻ e bz         = bz
  Good-tr⁻ e (bs g)     = bs (Good-tr⁻ e g)
  Good-tr⁻ e (bl hg st) = bl (λ n → Good-tr⁻ e (hg n)) (λ n → tr⁻-cong (st n))
  Good-tr⁻ e (bi {p = q} {f = f} hb hm) = bi
    (λ z ez g → subst (λ w → Good (tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) w))))) (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) z))
                      (Good-tr⁻ e (hb (backˢ (res⁻ˢ q e) z) (self-back⁻ q e ez)
                                      (Good→Gd (<→◃ q) (Good-back⁻ q e (Gd→Good (<→◃ (ltˢ (res⁻ˢ q e))) g))))))
    (λ {z} {z′} h → subst₂ (λ w w′ → tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) w))) ⊑ᵒ tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) w′))))
                           (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) z)) (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) z′))
                           (tr⁻-cong (hm (back⁻-mono q e h))))
  Good-tr⁻ (s≅ e) (bu {r = zero} g)   = bu (Good-tr⁻ e g)
  Good-tr⁻ (l≅ f) (bu {r = self n} g) = bu (Good-tr⁻ (f n) g)
  Good-tr⁻ e (bŝ g0 gg et eg m mm dm) =
    bŝ (Good-tr⁻ e g0) (λ η d → Good-tr⁻ e (gg η d)) (self-tr⁻ˢ e et)
       (λ η d η′ d′ eη → tr⁻ˢ-≅ e (≅-tr⁻ˢ e (eg η d η′ d′ eη)))
       (λ η d → tr⁻-cong (m η d)) (λ η d η′ d′ h → tr⁻-cong (mm η d η′ d′ h))
       (Dom-tr⁻ e g0 gg et (λ η d → eg η d η d (≅ᴵ-refl η)) dm)
  Good-tr⁻ e (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) =
    bĉ G₀ Gg d₀ dE m₀ mE (Good-tr⁻ e go) (λ η d → Good-tr⁻ e (gO η d))
       (λ η d → tr⁻-cong (mo η d)) (λ η d η′ d′ h → tr⁻-cong (mO η d η′ d′ h))

  Good-back zero      (s≅ e) g = Good-tr⁻ e g
  Good-back (suc q)   (s≅ e) g = Good-back q e g
  Good-back (lim n q) (l≅ f) g = Good-back q (f n) g

  Good-back⁻ zero      (s≅ e) g = Good-tr e g
  Good-back⁻ (suc q)   (s≅ e) g = Good-back⁻ q e g
  Good-back⁻ (lim n q) (l≅ f) g = Good-back⁻ q (f n) g

  Good-Ω : ∀ a → Good (Ωˢ a)
  Good-Ω zero      = bs bz
  Good-Ω (suc c)   = bi (λ z ez g → bu g) (λ {z} {z′} h → up-l {r = zero} {x = z} (up-r {r = zero} {y = z′} h))
  Good-Ω (lim g s) = bl (λ n → bu (Good-Ω (g n))) (λ n → up-l {r = self n} (up-r {r = self (suc n)} (Ω-monoᵒ (s n))))

  FlA : (ℓ : Ordᴵ) → Ordˢ ℓ → Set
  FlA zero      a = ⊤
  FlA (suc _)   a = Wrap (FlΛ φ₀ a)
  FlA (lim _ _) a = Wrap (FlΛ φ₀ a)

  Good-add : ∀ {k ℓ} {a : Ordˢ ℓ} {σ : Simᴵ k ℓ} {b : Ordˢ k} → Lv k ℓ → FlA ℓ a → Good a → a ≅ˢ a → Good b → Good (addˢ a σ b)
  Good-add lv fa ga ea bz          = ga
  Good-add lv fa ga ea (bs g)      = bs (Good-add lv fa ga ea g)
  Good-add lv fa ga ea (bl hg st)  = bl (λ n → Good-add lv fa ga ea (hg n)) (λ n → add-cong refl ea (st n))
  Good-add {a = a} {σ = σ} lv fa ga ea (bi {p = q} {f = f} hb hm) = bi
    (λ z ez g → subst (λ u → Good (addˢ a σ (f (intoˢ (<→◃ q) u)))) (sym (out-intoˢ (<→◃ (σ q)) z))
                      (Good-add lv fa ga ea (hb z ez (Gd-conv (<→◃ (σ q)) (<→◃ q) g))))
    (λ {z} {z′} h → subst₂ (λ u v → addˢ a σ (f (intoˢ (<→◃ q) u)) ⊑ᵒ addˢ a σ (f (intoˢ (<→◃ q) v)))
                           (sym (out-intoˢ (<→◃ (σ q)) z)) (sym (out-intoˢ (<→◃ (σ q)) z′)) (add-cong refl ea (hm h)))
  Good-add lv fa ga ea (bu {r = zero} g)   = Good-add (Lv-up zero lv) fa ga ea g
  Good-add lv fa ga ea (bu {r = self n} g) = Good-add (Lv-up (self n) lv) fa ga ea g
  Good-add {k = zero} lv fa ga ea (bŝ g0 gg et eg m mm dm) =
    bĉ G₀ Gg (proj₁ dm G₀) (λ η e → proj₂ dm η e (Gg η e))
       (λ η e → m η e idO G₀ (Gg η e)) (λ η e η′ e′ h → mm η e η′ e′ h idO (Gg η e) (Gg η′ e′))
       (Good-add lv fa ga ea g0) (λ η e → Good-add lv fa ga ea (gg η e))
       (λ η e → add-cong refl ea (m η e)) (λ η e η′ e′ h → add-cong refl ea (mm η e η′ e′ h))
    where
    G₀ = Good→Goodᶻ g0
    Gg = λ η e → Good→Goodᶻ (gg η e)
  Good-add {k = suc _} {ℓ = zero} lv fa ga ea (bŝ g0 gg et eg m mm dm) = ⊥-elim (tf (sym lv))
  Good-add {k = lim _ _} {ℓ = zero} lv fa ga ea (bŝ g0 gg et eg m mm dm) = ⊥-elim (tf (sym lv))
  Good-add {k = suc _} {ℓ = suc _} {a = a} {σ = σ} lv fa ga ea (bŝ g0 gg et eg m mm dm) =
    bŝ (Good-add lv fa ga ea g0) (λ η e → Good-add lv fa ga ea (gg η e)) (addˢ-≅ refl ea et)
       (λ η e η′ e′ eη → addˢ-≅ refl ea (eg η e η′ e′ eη))
       (λ η e → add-cong refl ea (m η e)) (λ η e η′ e′ h → add-cong refl ea (mm η e η′ e′ h))
       (Occ-add {a = a} {σ = σ} (unwrap fa) et (λ η e → eg η e η e (≅ᴵ-refl η)) dm)
  Good-add {k = suc _} {ℓ = lim _ _} {a = a} {σ = σ} lv fa ga ea (bŝ g0 gg et eg m mm dm) =
    bŝ (Good-add lv fa ga ea g0) (λ η e → Good-add lv fa ga ea (gg η e)) (addˢ-≅ refl ea et)
       (λ η e η′ e′ eη → addˢ-≅ refl ea (eg η e η′ e′ eη))
       (λ η e → add-cong refl ea (m η e)) (λ η e η′ e′ h → add-cong refl ea (mm η e η′ e′ h))
       (Occ-add {a = a} {σ = σ} (unwrap fa) et (λ η e → eg η e η e (≅ᴵ-refl η)) dm)
  Good-add {k = lim _ _} {ℓ = suc _} {a = a} {σ = σ} lv fa ga ea (bŝ g0 gg et eg m mm dm) =
    bŝ (Good-add lv fa ga ea g0) (λ η e → Good-add lv fa ga ea (gg η e)) (addˢ-≅ refl ea et)
       (λ η e η′ e′ eη → addˢ-≅ refl ea (eg η e η′ e′ eη))
       (λ η e → add-cong refl ea (m η e)) (λ η e η′ e′ h → add-cong refl ea (mm η e η′ e′ h))
       (Occ-add {a = a} {σ = σ} (unwrap fa) et (λ η e → eg η e η e (≅ᴵ-refl η)) dm)
  Good-add {k = lim _ _} {ℓ = lim _ _} {a = a} {σ = σ} lv fa ga ea (bŝ g0 gg et eg m mm dm) =
    bŝ (Good-add lv fa ga ea g0) (λ η e → Good-add lv fa ga ea (gg η e)) (addˢ-≅ refl ea et)
       (λ η e η′ e′ eη → addˢ-≅ refl ea (eg η e η′ e′ eη))
       (λ η e → add-cong refl ea (m η e)) (λ η e η′ e′ h → add-cong refl ea (mm η e η′ e′ h))
       (Occ-add {a = a} {σ = σ} (unwrap fa) et (λ η e → eg η e η e (≅ᴵ-refl η)) dm)
  Good-add lv fa ga ea (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) =
    bĉ G₀ Gg d₀ dE m₀ mE (Good-add lv fa ga ea go) (λ η e → Good-add lv fa ga ea (gO η e))
       (λ η e → add-cong refl ea (mo η e)) (λ η e η′ e′ h → add-cong refl ea (mO η e η′ e′ h))

  Good-iter : ∀ {ℓ} {c : Ordˢ ℓ} → Good c → c ≅ˢ c → FlA ℓ c → ∀ n → Good (iter (c +ˢ_) Ord₊ˢ.zero n)
  Good-iter {ℓ} gc ec fc zero    = bz
  Good-iter {ℓ} gc ec fc (suc n) = Good-add (Lv-refl ℓ) fc gc ec (Good-iter gc ec fc n)

  mkĉ : ∀ {ℓ c} {t₀ : Ordˢ zero} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ zero} {o₀ : Ordˢ ℓ} {o : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ} →
        Good t₀ → (∀ η e → Good (g η e)) → (∀ η e → t₀ ⊑ᵒ g η e) → (∀ η e η′ e′ → η ⊑ᴵ η′ → g η e ⊑ᵒ g η′ e′) →
        Dom zero c t₀ g → Good o₀ → (∀ η e → Good (o η e)) →
        (∀ η e → o₀ ⊑ᵒ o η e) → (∀ η e η′ e′ → η ⊑ᴵ η′ → o η e ⊑ᵒ o η′ e′) →
        Good (Ord₊ˢ.ĉᴸ c (toZ t₀) (λ η e → toZ (g η e)) o₀ o)
  mkĉ g0 gg m mm (d₀ , dE) go gO mo mO =
    bĉ G₀ Gg (d₀ G₀) (λ η e → dE η e (Gg η e))
       (λ η e → m η e idO G₀ (Gg η e)) (λ η e η′ e′ h → mm η e η′ e′ h idO (Gg η e) (Gg η′ e′))
       go gO mo mO
    where
    G₀ = Good→Goodᶻ g0
    Gg = λ η e → Good→Goodᶻ (gg η e)
```

## §2 折叠定理 (对前缀 $Q$ 与允许谓词族参数化)

**参数.** 前缀 $Q$ 自互模拟、有地板, 其在到达目标处的值好 (`gQ`, 以目标条件 `Tg` 为前提). 目标 0 的允许谓词 `Ok0` 与遗传引理: 后继、极限、`up`、折叠链点 (`ok-col`, 对 $Q$ 的链点), 以及两条关于闭包的: 非零层 `ŝ` 映到目标 0 的支配 (`ok-ŝ`: 由输入的 `Occ≺` 与 `Ok0` 给出输出链的 `Dom zero`), 与 `ŝ`/`ĉᴸ` 组成部分的允许 (`ok-ŝc`/`ok-ĉc`). 目标非零处无条件 (`Ok`). 环境层号 $\ell$ 与帧证据 `z₀` 固定 (折叠不改变环境).

**目标条件.** `ti : Tg i` (初始目标) 与 `tk : ∀ j <ᴵ k → Tg j` (尾巴层号 $k$ 的一切子层号); 沿 `up`/`limᵢ` 下降时 `tk` 经 `<ᴵ-trans`/`suc`/`lim n` 传递. 这比 "对一切 $i<^\mathsf I\ell$" 弱, 是统一形所需 (§结论).

```agda
  module Fold {fl′} (Q : Run fl′) (rQ : Q ≈ᴿ Q) (fQ : FlR Q) (Tg : Ordᴵ → Set)
              (Ok0 : ∀ {k} → Ordˢ k → Set)
              (ok-suc : ∀ {k} {a : Ordˢ k} → Ok0 (Ord₊ˢ.suc a) → Ok0 a)
              (ok-lim : ∀ {k} {f : ℕ → Ordˢ k} → Ok0 (Ord₊ˢ.lim f) → ∀ n → Ok0 (f n))
              (ok-up  : ∀ {k k′} (r : k′ ◃₁ k) {x : Uˢ k′ (◃₁→◃ r)} → Ok0 (Ord₊ˢ.up r x) → Ok0 (outˢ (◃₁→◃ r) x))
              (ok-col : ∀ {φ k j ℓ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fl′ ⊔ φ)} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
                        Ok0 (Ord₊ˢ.limᵢ q f) → ∀ n →
                        Ok0 (f (intoˢ (<→◃ q) (chainA (λ ev′ → cv (proj₂ ev′) q) (λ x → fold 0 φ cv Q (f (intoˢ (<→◃ q) x))) ev n))))
              (ok-ŝc : ∀ {k c} {t₀ : Ordˢ k} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k} → Ok0 (Ord₊ˢ.ŝ c t₀ g) → Ok0 t₀ × (∀ η e → Ok0 (g η e)))
              (ok-ĉc : ∀ {k c t₀} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z} {o₀ : Ordˢ k} {o : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k} →
                       Ok0 (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) → Ok0 o₀ × (∀ η e → Ok0 (o η e)))
              (ok-ŝ : ∀ {φ k c ℓ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fl′ ⊔ φ)} {z : zero <ᴵ ℓ}
                      {t₀ : Ordˢ k} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k} → NZ k → Ok0 (Ord₊ˢ.ŝ c t₀ g) → Occ≺ c t₀ g →
                      Dom zero c (fold 0 φ cv Q t₀ ev z) (λ η e → fold 0 φ cv Q (g η e) ev z))
              where

    Ok : (i : Ordᴵ) → ∀ {k} → Ordˢ k → Set
    Ok zero      x = Ok0 x
    Ok (suc _)   x = ⊤
    Ok (lim _ _) x = ⊤

    Ok-pen : ∀ {i j k} {x : Ordˢ k} → j <ᴵ i → Ok i x
    Ok-pen {i = suc _}   r = tt
    Ok-pen {i = lim _ _} r = tt

    Ok-nz : ∀ {i k} {x : Ordˢ k} → NZ i → Ok i x
    Ok-nz {i = suc _}   _ = tt
    Ok-nz {i = lim _ _} _ = tt

    Ok-suc : ∀ i {k} {a : Ordˢ k} → Ok i (Ord₊ˢ.suc a) → Ok i a
    Ok-suc zero      h = ok-suc h
    Ok-suc (suc _)   _ = tt
    Ok-suc (lim _ _) _ = tt

    Ok-lim : ∀ i {k} {f : ℕ → Ordˢ k} → Ok i (Ord₊ˢ.lim f) → ∀ n → Ok i (f n)
    Ok-lim zero      h n = ok-lim h n
    Ok-lim (suc _)   _ n = tt
    Ok-lim (lim _ _) _ n = tt

    Ok-up : ∀ i {k k′} (r : k′ ◃₁ k) {x : Uˢ k′ (◃₁→◃ r)} → Ok i (Ord₊ˢ.up r x) → Ok i (outˢ (◃₁→◃ r) x)
    Ok-up zero      r h = ok-up r h
    Ok-up (suc _)   r _ = tt
    Ok-up (lim _ _) r _ = tt

    Ok-ŝc : ∀ i {k c} {t₀ : Ordˢ k} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k} → Ok i (Ord₊ˢ.ŝ c t₀ g) → Ok i t₀ × (∀ η e → Ok i (g η e))
    Ok-ŝc zero      h = ok-ŝc h
    Ok-ŝc (suc _)   _ = tt , λ η e → tt
    Ok-ŝc (lim _ _) _ = tt , λ η e → tt

    Ok-ĉc : ∀ i {k c t₀} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z} {o₀ : Ordˢ k} {o : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k} →
            Ok i (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) → Ok i o₀ × (∀ η e → Ok i (o η e))
    Ok-ĉc zero      h = ok-ĉc h
    Ok-ĉc (suc _)   _ = tt , λ η e → tt
    Ok-ĉc (lim _ _) _ = tt , λ η e → tt

    -- 折叠分支 (目标 i ≺ 节点 j 或 j ≅ i) 下链点处的允许: 目标 i 与节点 j 两处
    Ok-col : ∀ i {φ k j ℓ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fl′ ⊔ φ)} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
             (i ≺ᴵ j) ⊎ (j ≅ᴵ i) → Ok i (Ord₊ˢ.limᵢ q f) → ∀ n →
             Ok j (f (intoˢ (<→◃ q) (chainA (λ ev′ → cv (proj₂ ev′) q) (λ x → fold 0 φ cv Q (f (intoˢ (<→◃ q) x))) ev n))) ×
             Ok i (f (intoˢ (<→◃ q) (chainA (λ ev′ → cv (proj₂ ev′) q) (λ x → fold 0 φ cv Q (f (intoˢ (<→◃ q) x))) ev n)))
    Ok-col zero {j = zero} {cv = cv} {ev = ev} c h n = ok-col {cv = cv} {ev = ev} h n , ok-col {cv = cv} {ev = ev} h n
    Ok-col zero {j = suc _} {cv = cv} {ev = ev} c h n = tt , ok-col {cv = cv} {ev = ev} h n
    Ok-col zero {j = lim _ _} {cv = cv} {ev = ev} c h n = tt , ok-col {cv = cv} {ev = ev} h n
    Ok-col (suc _) {j = zero} (inj₁ (via e ())) h n
    Ok-col (suc _) {j = zero} (inj₂ ()) h n
    Ok-col (suc _) {j = suc _} c h n = tt , tt
    Ok-col (suc _) {j = lim _ _} c h n = tt , tt
    Ok-col (lim _ _) {j = zero} (inj₁ (via e ())) h n
    Ok-col (lim _ _) {j = zero} (inj₂ ()) h n
    Ok-col (lim _ _) {j = suc _} c h n = tt , tt
    Ok-col (lim _ _) {j = lim _ _} c h n = tt , tt

    module _ {ℓ : Ordᴵ} (z₀ : zero <ᴵ ℓ) (gQ : ∀ {i} (ev : Ev ℓ fl′) (p : i <ᴵ ℓ) → Tg i → Good (Q ev p)) where

      FlA-fold : ∀ {φ k} i {cv : ∀ {L} → Ev L φ → Simᴵ k L} (ev : Ev ℓ (fl′ ⊔ φ)) (p : i <ᴵ ℓ) (a : Ordˢ k) → a ≅ˢ a →
                 FlA i (fold 0 φ cv Q a ev p)
      FlA-fold zero      ev p a ea = tt
      FlA-fold {φ = φ} (suc _)   {cv = cv} ev p a ea = wrap (FlΛ-fold {φ = φ} {P = Q} {cv = cv} {ev = ev} {p = p} rQ fQ (reg z₀ p tt) a ea)
      FlA-fold {φ = φ} (lim _ _) {cv = cv} ev p a ea = wrap (FlΛ-fold {φ = φ} {P = Q} {cv = cv} {ev = ev} {p = p} rQ fQ (reg z₀ p tt) a ea)

      -- 非零层闭包在非零目标处的支配 (再生地板)
      domNZ : ∀ {φ k} i {c} {cv : ∀ {L} → Ev L φ → Simᴵ k L} (ev : Ev ℓ (fl′ ⊔ φ)) (p : i <ᴵ ℓ) → NZ i →
              {t₀ : Ordˢ k} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k} → Occ≺ c t₀ g → t₀ ≅ˢ t₀ → (∀ η e → g η e ≅ˢ g η e) →
              Dom i c (fold 0 φ cv Q t₀ ev p) (λ η e → fold 0 φ cv Q (g η e) ev p)
      domNZ {φ = φ} (suc _)   {cv = cv} ev p nz dm et eg = Occ-fold {φ = φ} {Q = Q} {cv = cv} {ev = ev} {p = p} rQ fQ (reg z₀ p nz) dm et eg
      domNZ {φ = φ} (lim _ _) {cv = cv} ev p nz dm et eg = Occ-fold {φ = φ} {Q = Q} {cv = cv} {ev = ev} {p = p} rQ fQ (reg z₀ p nz) dm et eg

      -- 非零层闭包映到任意目标: 目标 0 用 ok-ŝ, 非零用 domNZ
      domŝ : ∀ {φ k} i {c} {cv : ∀ {L} → Ev L φ → Simᴵ k L} (ev : Ev ℓ (fl′ ⊔ φ)) (p : i <ᴵ ℓ) → NZ k →
             {t₀ : Ordˢ k} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k} → Ok i (Ord₊ˢ.ŝ c t₀ g) → Occ≺ c t₀ g → t₀ ≅ˢ t₀ → (∀ η e → g η e ≅ˢ g η e) →
             Dom i c (fold 0 φ cv Q t₀ ev p) (λ η e → fold 0 φ cv Q (g η e) ev p)
      domŝ {φ = φ} zero {cv = cv} ev p nk ok dm et eg = ok-ŝ {φ = φ} {cv = cv} {ev = ev} {z = p} nk ok dm
      domŝ (suc _)   ev p nk ok dm et eg = domNZ (suc _) ev p tt dm et eg
      domŝ (lim _ _) ev p nk ok dm et eg = domNZ (lim _ _) ev p tt dm et eg

      Good-fold : ∀ {φ k i} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fl′ ⊔ φ)} {p : i <ᴵ ℓ} {x : Ordˢ k} →
                  Tg i → (∀ {j} → j <ᴵ k → Tg j) → Good x → x ≅ˢ x → Ok i x → Good (fold 0 φ cv Q x ev p)
      chain-good : ∀ {φ k j} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fl′ ⊔ φ)} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
                   Tg j → (∀ {j′} → j′ <ᴵ k → Tg j′) →
                   (∀ (z : Ordˢ j) → z ≅ˢ z → Gd j (<→◃ q) (intoˢ (<→◃ q) z) → Good (f (intoˢ (<→◃ q) z))) →
                   Ord₊ˢ.limᵢ q f ≅ˢ Ord₊ˢ.limᵢ q f →
                   (∀ n → Ok j (f (intoˢ (<→◃ q) (chainA (λ ev′ → cv (proj₂ ev′) q) (λ x → fold 0 φ cv Q (f (intoˢ (<→◃ q) x))) ev n)))) →
                   ∀ n → Good (chainA (λ ev′ → cv (proj₂ ev′) q) (λ x → fold 0 φ cv Q (f (intoˢ (<→◃ q) x))) ev n)
      chain-sim : ∀ {φ k j} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fl′ ⊔ φ)} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
                  Ord₊ˢ.limᵢ q f ≅ˢ Ord₊ˢ.limᵢ q f →
                  ∀ n → chainA (λ ev′ → cv (proj₂ ev′) q) (λ x → fold 0 φ cv Q (f (intoˢ (<→◃ q) x))) ev n ≅ˢ
                        chainA (λ ev′ → cv (proj₂ ev′) q) (λ x → fold 0 φ cv Q (f (intoˢ (<→◃ q) x))) ev n
      chain-step : ∀ {φ k j} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fl′ ⊔ φ)} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
                   Ord₊ˢ.limᵢ q f ≅ˢ Ord₊ˢ.limᵢ q f →
                   (∀ {z z′ : Ordˢ j} → z ⊑ᵒ z′ → f (intoˢ (<→◃ q) z) ⊑ᵒ f (intoˢ (<→◃ q) z′)) →
                   ∀ n → chainA (λ ev′ → cv (proj₂ ev′) q) (λ x → fold 0 φ cv Q (f (intoˢ (<→◃ q) x))) ev n ⊑ᵒ
                         chainA (λ ev′ → cv (proj₂ ev′) q) (λ x → fold 0 φ cv Q (f (intoˢ (<→◃ q) x))) ev (suc n)

      chain-sim {j = j} e zero = Ωˢ-refl j
      chain-sim {φ = φ} {cv = cv} {ev = ev} {q = q} e (suc n) =
        fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = Q} {P′ = Q} rQ (i-respˢ e (chain-sim {φ = φ} {cv = cv} {ev = ev} e n)) ev _ ev _ (≅ᴵ-refl _)

      chain-step {φ = φ} {j = j} {cv = cv} {ev = ev} {q = q} {f = f} e hm zero =
        B1 {φ = φ} {P = Q} {cv = cv} {ev = ev} {p = cv (proj₂ ev) q} {x = Ωˢ j} rQ (fQ (proj₁ ev) (cv (proj₂ ev) q) ⊑ᴵ-refl)
           (f (intoˢ (<→◃ q) (Ωˢ j))) (i-respˢ e (Ωˢ-refl j))
      chain-step {φ = φ} {cv = cv} {ev = ev} e hm (suc n) = fold-cong rQ (hm (chain-step {φ = φ} {cv = cv} {ev = ev} e hm n))

      chain-good {j = j} tj tk hb e ok zero = Good-Ω j
      chain-good {φ = φ} {cv = cv} {ev = ev} {q = q} tj tk hb e ok (suc n) =
        Good-fold {φ = φ} {cv = cv} {ev = ev} {p = cv (proj₂ ev) q} tj tk
                  (hb _ (chain-sim {φ = φ} {cv = cv} {ev = ev} e n) (Good→Gd (<→◃ q) (chain-good {φ = φ} {cv = cv} {ev = ev} tj tk hb e ok n)))
                  (i-respˢ e (chain-sim {φ = φ} {cv = cv} {ev = ev} e n)) (ok n)

      Good-fold {ev = ev} {p = p} ti tk bz ex ok = gQ (proj₁ ev) p ti
      Good-fold {φ = φ} {i = i} {cv = cv} {ev = ev} {p = p} ti tk (bs g) ex ok =
        bl (Good-iter (Good-fold {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk g ea (Ok-suc i ok)) eψ (FlA-fold i ev p _ ea)) (rule4ᵒ eψ)
        where ea = s-invˢ ex
              eψ = fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = Q} {P′ = Q} rQ ea ev p ev p (≅ᴵ-refl i)
      Good-fold {φ = φ} {i = i} {cv = cv} {ev = ev} {p = p} ti tk (bl hg st) ex ok =
        bl (λ n → Good-fold {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk (hg n) (l-invˢ ex n) (Ok-lim i ok n)) (λ n → fold-cong rQ (st n))
      Good-fold {φ = φ} {i = i} {cv = cv} {ev = ev} {p = p} ti tk (bi {j = j} {p = q} {f = f} hb hm) ex ok with <ᴵ-dec (cv (proj₂ ev) q) p
      ... | injᵃ (via e r) = bi
        (λ z ez g → subst (λ u → Good (fold 0 φ cv Q (f (intoˢ (<→◃ q) (tr⁻ˢ e u))) ev p)) (sym (out-intoˢ (<→◃ r) z))
                          (Good-fold {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk
                                     (hb (tr⁻ˢ e z) (self-tr⁻ˢ e ez) (Good→Gd (<→◃ q) (Good-tr⁻ e (Gd→Good (<→◃ r) g))))
                                     (i-respˢ ex (self-tr⁻ˢ e ez)) (Ok-pen r)))
        (λ {z} {z′} h → subst₂ (λ u v → fold 0 φ cv Q (f (intoˢ (<→◃ q) (tr⁻ˢ e u))) ev p ⊑ᵒ fold 0 φ cv Q (f (intoˢ (<→◃ q) (tr⁻ˢ e v))) ev p)
                               (sym (out-intoˢ (<→◃ r) z)) (sym (out-intoˢ (<→◃ r) z′)) (fold-cong rQ (hm (tr⁻-cong h))))
      ... | injᵇ c = bl (λ n → Good-fold {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk
                                 (hb _ (chain-sim {φ = φ} {cv = cv} {ev = ev} ex n)
                                     (Good→Gd (<→◃ q) (chain-good {φ = φ} {cv = cv} {ev = ev} (tk q) tk hb ex (λ m → proj₁ (Ok-col i {cv = cv} {ev = ev} (inj₁ c) ok m)) n)))
                                 (i-respˢ ex (chain-sim {φ = φ} {cv = cv} {ev = ev} ex n)) (proj₂ (Ok-col i {cv = cv} {ev = ev} (inj₁ c) ok n)))
                        (λ n → fold-cong rQ (hm (chain-step {φ = φ} {cv = cv} {ev = ev} ex hm n)))
      ... | injᶜ c = bl (λ n → Good-fold {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk
                                 (hb _ (chain-sim {φ = φ} {cv = cv} {ev = ev} ex n)
                                     (Good→Gd (<→◃ q) (chain-good {φ = φ} {cv = cv} {ev = ev} (tk q) tk hb ex (λ m → proj₁ (Ok-col i {cv = cv} {ev = ev} (inj₂ c) ok m)) n)))
                                 (i-respˢ ex (chain-sim {φ = φ} {cv = cv} {ev = ev} ex n)) (proj₂ (Ok-col i {cv = cv} {ev = ev} (inj₂ c) ok n)))
                        (λ n → fold-cong rQ (hm (chain-step {φ = φ} {cv = cv} {ev = ev} ex hm n)))
      Good-fold {k = suc k′} {i = i} {cv = cv} {ev = ev} {p = p} ti tk (bu {r = zero} g) ex ok =
        Good-fold {φ = flo k′} {cv = cvFlo k′} {ev = proj₁ ev , toFlo k′ (cv (proj₂ ev))} {p = p} ti (λ j< → tk (suc j<)) g (u-reflˢ zero ex) (Ok-up i zero ok)
      Good-fold {φ = φ} {i = i} {cv = cv} {ev = ev} {p = p} ti tk (bu {r = self n} g) ex ok =
        Good-fold {φ = φ} {cv = λ e q → cv e (lim n q)} {ev = ev} {p = p} ti (λ j< → tk (lim n j<)) g (u-reflˢ (self n) ex) (Ok-up i (self n) ok)
      Good-fold {φ = φ} {k = zero} {i = i} {cv = cv} {ev = ev} {p = p} ti tk (bŝ g0 gg et eg m mm dm) ex ok =
        mkĉ g0 gg m mm dm (Good-fold {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk g0 et (proj₁ (Ok-ŝc i ok)))
            (λ η e → Good-fold {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk (gg η e) (eg η e η e (≅ᴵ-refl η)) (proj₂ (Ok-ŝc i ok) η e))
            (λ η e → fold-cong rQ (m η e)) (λ η e η′ e′ hh → fold-cong rQ (mm η e η′ e′ hh))
      Good-fold {φ = φ} {k = suc _} {i = i} {cv = cv} {ev = ev} {p = p} ti tk (bŝ g0 gg et eg m mm dm) ex ok =
        bŝ (Good-fold {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk g0 et (proj₁ (Ok-ŝc i ok)))
           (λ η e → Good-fold {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk (gg η e) (eg η e η e (≅ᴵ-refl η)) (proj₂ (Ok-ŝc i ok) η e))
           (fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = Q} {P′ = Q} rQ et ev p ev p (≅ᴵ-refl i))
           (λ η e η′ e′ eη → fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = Q} {P′ = Q} rQ (eg η e η′ e′ eη) ev p ev p (≅ᴵ-refl i))
           (λ η e → fold-cong rQ (m η e)) (λ η e η′ e′ hh → fold-cong rQ (mm η e η′ e′ hh))
           (domŝ i ev p tt ok dm et (λ η e → eg η e η e (≅ᴵ-refl η)))
      Good-fold {φ = φ} {k = lim _ _} {i = i} {cv = cv} {ev = ev} {p = p} ti tk (bŝ g0 gg et eg m mm dm) ex ok =
        bŝ (Good-fold {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk g0 et (proj₁ (Ok-ŝc i ok)))
           (λ η e → Good-fold {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk (gg η e) (eg η e η e (≅ᴵ-refl η)) (proj₂ (Ok-ŝc i ok) η e))
           (fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = Q} {P′ = Q} rQ et ev p ev p (≅ᴵ-refl i))
           (λ η e η′ e′ eη → fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = Q} {P′ = Q} rQ (eg η e η′ e′ eη) ev p ev p (≅ᴵ-refl i))
           (λ η e → fold-cong rQ (m η e)) (λ η e η′ e′ hh → fold-cong rQ (mm η e η′ e′ hh))
           (domŝ i ev p tt ok dm et (λ η e → eg η e η e (≅ᴵ-refl η)))
      Good-fold {φ = φ} {i = i} {cv = cv} {ev = ev} {p = p} ti tk (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) ex ok =
        bĉ G₀ Gg d₀ dE m₀ mE (Good-fold {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk go (ĉ-refl₀ ex) (proj₁ (Ok-ĉc i ok)))
           (λ η e → Good-fold {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk (gO η e) (ĉ-reflg ex η e) (proj₂ (Ok-ĉc i ok) η e))
           (λ η e → fold-cong rQ (mo η e)) (λ η e η′ e′ hh → fold-cong rQ (mO η e η′ e′ hh))
```

**读法.** 停机: 对 `Good` 推导递归, `chain-good` 只把 `hb` (推导的字段) 用在链点上; 与 Stage2Label/TreeNFBase 同. 与它们相比多的是: (i) 前缀 $Q$ 的值在 `bz` 处 (`gQ`); (ii) `up zero` 换地板与证据 (`flo k′`/`cvFlo k′`/`toFlo`); (iii) 后继子句的和的地板 `FlA-fold` 由 $Q$ 的地板再生; (iv) 非零层闭包映到目标 0 的支配经参数 `ok-ŝ`.

## §3 $\Omega_\Omega$ 闭包的好性: 空前缀实例与弹栈

**空前缀实例.** `Fold ∅ᴿ`: 目标条件平凡, 值 $\Omega_i$ 好, `Ok0 = Pl` (Base §7): 后继/极限/`up` 由 `Pl` 的反演, 链点由 `Pl-fold∅` (空前缀的折叠保持无符号), 闭包情形空 (`Pl` 没有 `ŝ`/`ĉᴸ` 构造子).

```agda
  Pl-suc : ∀ {k} {a : Ordˢ k} → Pl (Ord₊ˢ.suc a) → Pl a
  Pl-suc (ps h) = h

  Pl-lim : ∀ {k} {f : ℕ → Ordˢ k} → Pl (Ord₊ˢ.lim f) → ∀ n → Pl (f n)
  Pl-lim (pl h) = h

  Pl-up : ∀ {k k′} (r : k′ ◃₁ k) {x : Uˢ k′ (◃₁→◃ r)} → Pl (Ord₊ˢ.up r x) → Pl (outˢ (◃₁→◃ r) x)
  Pl-up zero     (pu h) = h
  Pl-up (self n) (pu h) = h

  Pl-ŝ : ∀ {k c} {t₀ : Ordˢ k} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k} → Pl (Ord₊ˢ.ŝ c t₀ g) → ⊥
  Pl-ŝ ()

  Pl-ĉ : ∀ {k c t₀} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z} {o₀ : Ordˢ k} {o : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k} → Pl (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) → ⊥
  Pl-ĉ ()

  Pl-col : ∀ {φ k j ℓ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fz ⊔ φ)} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
           Pl (Ord₊ˢ.limᵢ q f) → ∀ n →
           Pl (f (intoˢ (<→◃ q) (chainA (λ ev′ → cv (proj₂ ev′) q) (λ x → fold 0 φ cv ∅ᴿ (f (intoˢ (<→◃ q) x))) ev n)))
  Pl-col {φ = φ} {j = j} {cv = cv} {ev = ev} {q = q} {f = f} (pi h) = λ n → h _ (Pl→Pd (<→◃ q) (ch n))
    where
    ch : ∀ n → Pl (chainA (λ ev′ → cv (proj₂ ev′) q) (λ x → fold 0 φ cv ∅ᴿ (f (intoˢ (<→◃ q) x))) ev n)
    ch zero    = Pl-Ω j
    ch (suc n) = Pl-fold∅ {φ = φ} {cv = cv} {ev = ev} {p = cv (proj₂ ev) q} (h _ (Pl→Pd (<→◃ q) (ch n)))

  module F∅ = Fold ∅ᴿ r∅ FlR-∅ (λ _ → ⊤) Pl Pl-suc Pl-lim Pl-up Pl-col
                   (λ h → ⊥-elim (Pl-ŝ h)) (λ h → ⊥-elim (Pl-ĉ h)) (λ nk h → ⊥-elim (Pl-ŝ h))

  OkPl : ∀ i {k} {x : Ordˢ k} → Pl x → F∅.Ok i x
  OkPl zero      h = h
  OkPl (suc _)   h = tt
  OkPl (lim _ _) h = tt

  good∅ : ∀ {φ k i ℓ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} (ev : Ev ℓ (fz ⊔ φ)) (z₀ : zero <ᴵ ℓ) (p : i <ᴵ ℓ) (x : Ordˢ k) →
          Good x → x ≅ˢ x → Pl x → Good (fold 0 φ cv ∅ᴿ x ev p)
  good∅ {φ = φ} {i = i} {cv = cv} ev z₀ p x g ex px =
    F∅.Good-fold z₀ (λ ev′ p′ _ → Good-Ω _) {φ = φ} {cv = cv} {ev = ev} {p = p} tt (λ _ → tt) g ex (OkPl i px)
```

**弹栈.** `Ω̂A 0 ∅ᴿ ev p = cloA 0 t g ev p`, 字面是 `ŝ (suc (Mx B)) (t ev p) (λ η e → g η … )`, $t=\psi_\cdot(\Omega_1)$, $g\,\eta=\psi_\cdot(\Omega_\eta)$ 都是空前缀的折叠. **界字面是目标**: 地板 `fz ⊔ fk zero` 的项只有 $0$, `src` 说最大者是目标或某个地板项且目标 $\prec$ 它; 后者给出 $i\prec0$, 不可能 (`Mx∅`). 支配: 目标 0 用 `Strict₀` (空前缀有地板); 非零目标用 `S⁺` 与再生的地板 (`reg`).

```agda
  K∅ : ∀ {K} → InF K (fz ⊔ fk zero) → K ≅ᴵ zero
  K∅ (inl ())
  K∅ (inr ink) = z≅

  Mx∅ : ∀ {i ℓ} (ev : Ev ℓ (fz ⊔ fk zero)) (p : i <ᴵ ℓ) → Mx (bound (fz ⊔ fk zero) ev p) ≡ i
  Mx∅ ev p with src (bound (fz ⊔ fk zero) ev p)
  ... | inj₁ e = e
  ... | inj₂ (s , K , k , e) = ⊥-elim (≺0 (subst (λ M → _ ≺ᴵ M) e s) (K∅ k))

  -- Mlev 的三个字面证据 (与 cloA 里的 `lim 0 q`/`lim 1 q` 定义性相同; 单独命名以免合一器反演 lim)
  zM : ∀ {c η} (e : c ⊑ᴵ η) → zero <ᴵ c → zero <ᴵ Mlev c η e
  zM e q = lim 0 q

  iM : ∀ {c η i} (e : c ⊑ᴵ η) → i <ᴵ c → i <ᴵ Mlev c η e
  iM e q = lim 0 q

  σM₀ : ∀ {c η} (e : c ⊑ᴵ η) → Simᴵ c (Mlev c η e)
  σM₀ e q = lim 0 q

  σM₁ : ∀ {c η} (e : c ⊑ᴵ η) → Simᴵ η (Mlev c η e)
  σM₁ e q = lim 1 q

  module Pop {ℓ} (ev : Ev ℓ (fz ⊔ fk zero)) where
    z₀ : zero <ᴵ ℓ
    z₀ = proj₂ ev zero

    T₀ : ∀ {i} → i <ᴵ ℓ → Ordˢ i
    T₀ p = fold 0 (fk zero) (λ e → e) ∅ᴿ (Ωˢ (suc zero)) ev p

    B : ∀ {i} → i <ᴵ ℓ → Top i ℓ (fz ⊔ fk zero)
    B p = bound (fz ⊔ fk zero) ev p

    Lη : ∀ {i} (p : i <ᴵ ℓ) η → suc (Mx (B p)) ⊑ᴵ η → Ordᴵ
    Lη p η e = Mlev (Fc (B p)) (suc η) (FB (B p) e)

    evη : ∀ {i} (p : i <ᴵ ℓ) η (e : suc (Mx (B p)) ⊑ᴵ η) → Ev (Lη p η e) (fz ⊔ fk η)
    evη p η e = liftEv fz (σM₀ (FB (B p) e)) (proj₁ (evF (B p))) , σM₁ (FB (B p) e)

    Gη : ∀ {i} (p : i <ᴵ ℓ) η (e : suc (Mx (B p)) ⊑ᴵ η) → Ordˢ i
    Gη p η e = fold 0 (fk η) (λ e′ q → e′ (suc q)) ∅ᴿ (Ωˢ η) {ℓ = Lη p η e} (evη p η e) (iM (FB (B p) e) (iF (B p)))

    zη : ∀ {i} (p : i <ᴵ ℓ) η (e : suc (Mx (B p)) ⊑ᴵ η) → zero <ᴵ Lη p η e
    zη p η e = zM (FB (B p) e) (proj₂ (evF (B p)) zero)

    one⊑η : ∀ {i} (p : i <ᴵ ℓ) η (e : suc (Mx (B p)) ⊑ᴵ η) → suc zero ⊑ᴵ η
    one⊑η p η e = ⊑ᴵ-trans (s⊑ z≅ (z<suc z₀ (mx (B p)))) e

    lv : ∀ {x : Ordˢ zero} (G : Goodᶻ (toZ x)) → Ordᴵ
    lv G = toLevel (force _ G) (force-HS _ G)

    popDom : ∀ {i} (p : i <ᴵ ℓ) → (NZ i → suc i ⊑ᴵ β) → Dom i (suc (Mx (B p))) (T₀ p) (Gη p)
    popDom {i = zero} p ti =
      (λ G → subst (λ M → suc M ⊑ᴵ lv G) (sym (Mx∅ ev p)) (Strict₀ {φ = fk zero} {P = ∅ᴿ} {cv = λ e → e} {ev = ev} {z = p} r∅ FlR-∅ (Ωˢ (suc zero)) (Ωˢ-refl (suc zero)) G)) ,
      (λ η e G → subst (λ M → suc M ⊑ᴵ lv G) (sym (Mx∅ ev p))
                   (Strict₀ {φ = fk η} {ℓ = Lη p η e} {P = ∅ᴿ} {cv = λ e′ q → e′ (suc q)} {ev = evη p η e} {z = iM (FB (B p) e) (iF (B p))} r∅ FlR-∅ (Ωˢ η) (Ωˢ-refl η) G))
    popDom {i = suc _} p ti =
      subst (λ M → suc M ⊑ᴵ β) (sym (Mx∅ ev p)) (ti tt) ,
      S⁺ (FlΛ-fold {φ = fk zero} {P = ∅ᴿ} {cv = λ e → e} {ev = ev} {p = p} r∅ FlR-∅ (reg z₀ p tt) (Ωˢ (suc zero)) (Ωˢ-refl (suc zero))) ,
      λ η e → S⁺ (FlΛ-fold {φ = fk η} {ℓ = Lη p η e} {P = ∅ᴿ} {cv = λ e′ q → e′ (suc q)} {ev = evη p η e} {p = iM (FB (B p) e) (iF (B p))} r∅ FlR-∅
                            (reg (zη p η e) (iM (FB (B p) e) (iF (B p))) tt) (Ωˢ η) (Ωˢ-refl η))
    popDom {i = lim _ _} p ti =
      subst (λ M → suc M ⊑ᴵ β) (sym (Mx∅ ev p)) (ti tt) ,
      S⁺ (FlΛ-fold {φ = fk zero} {P = ∅ᴿ} {cv = λ e → e} {ev = ev} {p = p} r∅ FlR-∅ (reg z₀ p tt) (Ωˢ (suc zero)) (Ωˢ-refl (suc zero))) ,
      λ η e → S⁺ (FlΛ-fold {φ = fk η} {ℓ = Lη p η e} {P = ∅ᴿ} {cv = λ e′ q → e′ (suc q)} {ev = evη p η e} {p = iM (FB (B p) e) (iF (B p))} r∅ FlR-∅
                            (reg (zη p η e) (iM (FB (B p) e) (iF (B p))) tt) (Ωˢ η) (Ωˢ-refl η))

    goodΩ̂∅ : ∀ {i} (p : i <ᴵ ℓ) → (NZ i → suc i ⊑ᴵ β) → Good (Ω̂A 0 ∅ᴿ ev p)
    goodΩ̂∅ {i} p ti =
      bŝ (good∅ {φ = fk zero} {cv = λ e → e} ev z₀ p (Ωˢ (suc zero)) (Good-Ω (suc zero)) (Ωˢ-refl (suc zero)) (Pl-Ω (suc zero)))
         (λ η e → good∅ {φ = fk η} {ℓ = Lη p η e} {cv = λ e′ q → e′ (suc q)} (evη p η e) (zη p η e) (iM (FB (B p) e) (iF (B p))) (Ωˢ η) (Good-Ω η) (Ωˢ-refl η) (Pl-Ω η))
         (fold-≅0 {φ = fk zero} {φ′ = fk zero} {cv = λ e → e} {cv′ = λ e → e} {P = ∅ᴿ} {P′ = ∅ᴿ} r∅ (Ωˢ-refl (suc zero)) ev p ev p (≅ᴵ-refl i))
         (λ η e η′ e′ eη → fold-≅0 {φ = fk η} {φ′ = fk η′} {cv = λ e″ q → e″ (suc q)} {cv′ = λ e″ q → e″ (suc q)} {P = ∅ᴿ} {P′ = ∅ᴿ} r∅ (Ωˢ-≅ eη)
                                   {ℓ = Lη p η e} {ℓ′ = Lη p η′ e′} (evη p η e) (iM (FB (B p) e) (iF (B p))) (evη p η′ e′) (iM (FB (B p) e′) (iF (B p))) (≅ᴵ-refl i))
         (λ η e → fold-cong {φ = fk zero} {φ′ = fk η} {ℓ′ = Lη p η e} {cv = λ e′ → e′} {cv′ = λ e′ q → e′ (suc q)} {ev = ev} {ev′ = evη p η e} {p = p} {p′ = iM (FB (B p) e) (iF (B p))}
                            r∅ (Ω-monoᵒ (one⊑η p η e)))
         (λ η e η′ e′ h → fold-cong {φ = fk η} {φ′ = fk η′} {ℓ = Lη p η e} {ℓ′ = Lη p η′ e′} {cv = λ e″ q → e″ (suc q)} {cv′ = λ e″ q → e″ (suc q)} {ev = evη p η e} {ev′ = evη p η′ e′}
                                    {p = iM (FB (B p) e) (iF (B p))} {p′ = lim 0 (iF (B p))} r∅ (Ω-monoᵒ h))
         (popDom p ti)
```

## §4 `FloorΩ̂`: 以 $\Omega_\Omega$ 闭包为前缀的折叠定理

`Floor` 在 $P=$ `Ω̂A 0 ∅ᴿ` 处的实例, 加 `Fold` 在 $Q=P$ 处的实例: `Ok0` 平凡; 非零层闭包映到目标 0 的支配由输入的 `Occ≺` 在观测 `col` 处给出 (Base 的 `Dom-of-Occ` 的固定界版本: $c\sqsubseteq\beta\sqsubseteq$ 层号; 这一步要求折叠的前缀**字面**就是 `IsCol` 里的前缀, 所以 `Floor` 在抽象 $P$ 上写不出它, 只能在实例处写); 前缀的值由 §3 的 `goodΩ̂∅`. 这就是 TreeNF `Floor.Good-ψ1` 的统一形: 唯一前提是目标条件 `Tgβ i = NZ i → suc i ⊑ᴵ β` 在初始目标与尾巴层号的子层号处成立.

```agda
module FloorΩ̂ (φ₀ β : Ordᴵ)
              (S⁺ : ∀ {k} {y : Ordˢ k} → FlΛ φ₀ y → ColC (Ω̂A 0 ∅ᴿ) β y)
              (reg : ∀ {i ℓ} → zero <ᴵ ℓ → i <ᴵ ℓ → NZ i → φ₀ ⊑ᴵ i) where

  P̂ : Run (fz ⊔ fk zero)
  P̂ = Ω̂A 0 ∅ᴿ

  rP̂ : P̂ ≈ᴿ P̂
  rP̂ = rΩ̂ r∅

  fP̂ : FlR P̂
  fP̂ = FlR-Ω̂ r∅ FlR-∅

  open Floor P̂ rP̂ φ₀ β S⁺ reg public

  Tgβ : Ordᴵ → Set
  Tgβ i = NZ i → suc i ⊑ᴵ β

  okŝP : ∀ {φ k c ℓ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ ((fz ⊔ fk zero) ⊔ φ)} {z : zero <ᴵ ℓ}
         {t₀ : Ordˢ k} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k} → NZ k → ⊤ → Occ≺ c t₀ g →
         Dom zero c (fold 0 φ cv P̂ t₀ ev z) (λ η e → fold 0 φ cv P̂ (g η e) ev z)
  okŝP nk _ (cb , c₀ , cg) = (λ G → ⊑ᴵ-trans cb (c₀ col G)) , (λ η e G → ⊑ᴵ-trans cb (cg η e col G))

  module FP = Fold P̂ rP̂ fP̂ Tgβ (λ _ → ⊤) (λ _ → tt) (λ _ _ → tt) (λ _ _ → tt) (λ _ _ → tt)
                   (λ _ → tt , λ _ _ → tt) (λ _ → tt , λ _ _ → tt) okŝP

  okTriv : ∀ i {k} {x : Ordˢ k} → FP.Ok i x
  okTriv zero      = tt
  okTriv (suc _)   = tt
  okTriv (lim _ _) = tt

  Good-foldP : ∀ {φ k i ℓ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} (ev : Ev ℓ ((fz ⊔ fk zero) ⊔ φ)) (p : i <ᴵ ℓ) {x : Ordˢ k} →
               Tgβ i → (∀ {j} → j <ᴵ k → Tgβ j) → Good x → x ≅ˢ x → Good (fold 0 φ cv P̂ x ev p)
  Good-foldP {φ = φ} {i = i} {cv = cv} ev p ti tk g ex =
    FP.Good-fold (proj₂ (proj₁ ev) zero) (λ ev′ p′ ti′ → Pop.goodΩ̂∅ ev′ p′ ti′) {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk g ex (okTriv i)
```

**读法.** 帧证据 `zero <ᴵ ℓ` 从前缀的地板证据 `proj₂ (proj₁ ev) zero` (`Simᴵ 1 ℓ`) 读出, 所以 `Good-foldP` 不需要单独的帧参数; 这是统一形 "地板证据即帧证据" 的一处体现.

## §5 严格性 `Strict₁`

$\Omega_\Omega$ 闭包之上、目标 0 的一切折叠输出层号 $\sqsupseteq2$ (Stage2Label `Strict₁` 的统一形). 步骤: `one≺ω` (空前缀对 `up zero 1` 的折叠字面是 $\lim(0,1,2,\ldots)$, 第 2 项是 `suc (suc zero)`); `one≺` (经 `up zero 1 ⊑ᵒ Ω₁` 与 `fold-cong`, 空前缀对 $\Omega_1$ 的折叠 $\succ1$); `onepop` (闭包的计值是 $\lim$ `outs`, 第 0 项是上面的树); `B1` 推到任意尾巴, `two⊑` 把 $1\prec X$ 变成 $2\sqsubseteq X$. 闭包的证书 `G₀` 作参数 (以免在类型里展开别名).

```agda
one≺ω : (G : Goodᶻ (toZ (Ord₊ˢ.lim (iter (Ord₊ˢ.suc Ord₊ˢ.zero +ˢ_) Ord₊ˢ.zero)))) → one⁰ ≺ force _ G
one≺ω (Goodᶻ.gl Gs st) = ≺l 2 (h2 (Gs 2))

u1 : Ordˢ (suc zero)
u1 = Ord₊ˢ.up zero (Ord₊ˢ.suc Ord₊ˢ.zero)

u1⊑Ω₁ : u1 ⊑ᵒ Ωˢ (suc zero)
u1⊑Ω₁ = limᵢ-r (λ z d → up-l {r = zero} (up-r {r = zero} {y = z} (≅→⊑ᵒ (≅ˢ-sym d))))

module _ {ℓ} (ev : Ev ℓ (fz ⊔ fk zero)) (z : zero <ᴵ ℓ) where
  Gω : Goodᶻ (toZ (fold 0 (fk zero) (λ e → e) ∅ᴿ u1 ev z))
  Gω = F.Good→Goodᶻ (F.bl (F.Good-iter (F.Good-Ω zero) (Ωˢ-refl zero) tt) (rule4ᵒ (Ωˢ-refl zero)))
    where module F = Floor ∅ᴿ r∅ zero zero (λ _ _ _ → z⊑) (λ _ _ _ → z⊑)

  one≺ : (G : Goodᶻ (toZ (fold 0 (fk zero) (λ e → e) ∅ᴿ (Ωˢ (suc zero)) ev z))) → one⁰ ≺ force _ G
  one≺ G = fold-cong {φ = fk zero} {φ′ = fk zero} {cv = λ e → e} {cv′ = λ e → e} {ev = ev} {ev′ = ev} {p = z} {p′ = z} r∅ u1⊑Ω₁ idO Gω G (one≺ω Gω)

  onepop : (G₀ : Goodᶻ (toZ (Ω̂A 0 ∅ᴿ ev z))) → one⁰ ≺ force _ G₀
  onepop (Goodᶻ.gc G₀ Gg d₀ dE m₀ mE Go₀ Go mo₀ mo) = ≺l 0 (one≺ Go₀)

  Strict₁ : ∀ {φ k} {cv : ∀ {L} → Ev L φ → Simᴵ k L} (ev′ : Ev ℓ ((fz ⊔ fk zero) ⊔ φ)) → proj₁ ev′ ≡ ev →
            (G₀ : Goodᶻ (toZ (Ω̂A 0 ∅ᴿ ev z))) (y : Ordˢ k) → y ≅ˢ y →
            (G : Goodᶻ (toZ (fold 0 φ cv (Ω̂A 0 ∅ᴿ) y ev′ z))) → two ⊑ᴵ toLevel (force _ G) (force-HS _ G)
  Strict₁ {φ = φ} {cv = cv} ev′ refl G₀ y ey G =
    toLevel-⊑ (hs (hs hz)) (force-HS _ G)
              (two⊑ (B1 {φ = φ} {P = Ω̂A 0 ∅ᴿ} {cv = cv} {ev = ev′} {p = z} {x = Ω̂A 0 ∅ᴿ ev z} (rΩ̂ r∅) (≅→⊑ᵒ (rΩ̂ r∅ ev z ev z (≅ᴵ-refl zero)))
                        y ey idO G₀ G (onepop G₀)))
```

## §6 结论与边界

**已证 (编译).** `Floor P rP φ₀ β S⁺ reg`: `Occ≺`/`Dom`/`Good₊`/`Gd`/`Good`/`Good→Goodᶻ`、`Occ-tr`/`Occ-add`/`Occ-fold`、`Dom0-≅`/`Dom-tr`、`Good-tr` 四重、`Good-Ω`、`FlA`/`Good-add`/`Good-iter`、`mkĉ`; **参数化折叠定理 `Fold.Good-fold`** (任意前缀 $Q$, 允许谓词族 `Ok0`); 空前缀实例 `F∅`/`good∅` (`Ok0 = Pl`); 弹栈: `Mx∅` (平凡地板下界字面是目标), `Pop.popDom`, **`Pop.goodΩ̂∅`**; `FloorΩ̂`: **`Good-foldP`** ($P=$ `Ω̂A 0 ∅ᴿ`, 无其他前提); 严格性 `one≺ω`/`one≺`/`onepop`/**`Strict₁`**.

**与 Prefix 族的差别.** (1) 两条闭包定理 (`Good-ψ0`/`Good-ψ1`) 变成一条参数化的 `Good-fold`, 栈被前缀 $Q$ 吸收; 空栈的 "无符号" 限制变成 `Ok0 = Pl` 实例, 单 $\hat\Omega$ 栈变成 $Q=P$ 实例. (2) `popGood`/`popDom` 的界是 `suc (Mx B)`, 要先证 `Mx B ≡ i` (`src` 分析), 支配经 `subst`. (3) 目标条件只对到达的目标: 极限层尾巴 $\Omega_{\beta_0}$ 的地板 `fk β₀` 迫使环境 $\ell\ni\beta_0$, 而 TreeNF 的 `ℓ ⊑ᴵ β` 在那里不成立 (目标 $\beta_0$ 的弹栈界 $\beta_0+1\not\sqsubseteq\beta_0$); 由于目标 $\beta_0$ 永不被到达, 条件 `Tg` 只需在初始目标与尾巴层号的子层号处 (`ti`/`tk`). (4) 帧证据从地板证据读出. (5) 深度 $\ge1$ 未做 (Base §1 读法).

**边界.** `Floor` 的支配是单覆盖 ($\varphi_0$ 固定, 界 $\beta$ 固定), 与 TreeNFBase 的 `Floor` 同; 一般 `Occ≺ᴳ` 的分层覆盖 (TreeNF §3–§4 的 $\gamma'_3$ 停点) 不在本文. 只导入已有模块, 不改任何已有文件.
