# 统一折叠上的三层遗传好树 (四): $P=\Omega_\Omega$ 闭包的实例, 记号无关的 $\psi_0(\Omega_\Omega\cdot2)$

> 接 [UniformPendingGoodBase](UniformPendingGoodBase.lagda.md)、[UniformPendingGoodZ](UniformPendingGoodZ.lagda.md)、[UniformPendingGoodF](UniformPendingGoodF.lagda.md). 这是决定性检验在统一形上的结果.
>
> 结论先说:
>
> 1. **`TopM.Gᴺ₂ᵁ ev z : Goodᴺ (toZ (Ω̂A 0 P̂ ev z))`, 对一切环境与证据, 构造不读记号.** 这是 $\psi_0(\Omega_\Omega\cdot2)$ 的统一树. 验收在 [UniformPendingGoodAccept](UniformPendingGoodAccept.lagda.md) (`A₂.label`, `A₂.tree : forceᴺ _ G ≅ T2ᴸ`), 记号只在那里.
> 2. **折叠定理 `PFold` 对任意前缀 $P$ 参数化**, 外部数据是 $P$ 的自互模拟、地板与值的三个好性; `PopCov` (逐点形式 `Tg`) 只进 $P̂$ 的值 `Val.vP`/`vV`. 统一形比 Pending 多一个参数 `Tg`/`tk`: 地板证据 `Simᴵ (suc η) ℓ` 迫使环境含 $\eta$, 所以只对到达的目标要求覆盖.
> 3. **增长不经 Growth.** `grow-g` 用 UniformPendingBase 的 `Ω-strict`, 因此这条证书的增长部分也不再是条件式的: 证书在这里造出.
> 4. **范围.** 只到 $k=2$. 地板读取: `cov-of` 经 `toFlo`/`cvFlo`, 分支 `gpt` 字面照抄 `cloA` 的 `fk η` 子句.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入已有模块, 不改任何已有文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformPendingGood where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Align.Level
open import OCF.Align.Symbolic using (Mlev)
open import OCF.Align.Prefix using (Z; ĉᴸ; Ord₊ˢ; Ordˢ; toZ; Ωˢ; Goodᶻ; force; force-HS)
open import OCF.Align.UniformS using (two; ≅ᴵ→⊑ᴵ; ⊑ᴵ-≅ˡ; ⊑ᴵ-≅ʳ; _≅ᶻ_; ≅ᶻ-sym; force-≅; Goodᶻ-tr; _≅ˢ_; Ωˢ-≅; Ωˢ-refl; toZ-≅)
open import OCF.Align.Stage2Label using (two⁰)
open import OCF.Align.Uniform2Base using (Flr; fz; fk; _⊔_; Ev; InF; inl; inr; ink; liftEv; Run; Top; bound; Mx; mx; src; Fc; evF; iF; FB;
  flo; cvFlo; toFlo; fold; Ω̂A; ∅ᴿ; _≈ᴿ_; fold-≅0; ≺0)
open import OCF.Align.UniformNFBase using (_⊑ᵒ_; idO; fo; col; fold-cong; Ω-monoᵒ; FlΛ-fold; FlR; FlR-∅; FlR-Ω̂; r∅; rΩ̂; CovΛ; dom-cov; χ̂; Strict₀; run-≅)
open import OCF.Align.UniformNFDepth0 using (NZ; one⊑; module FloorΩ̂; Strict₁)
open import OCF.Align.NotFree using (Goodᴺ; forceᴺ; forceᴺ-HS; forceᴺ-≅; ofZ; ofZ-≅; gc)
open import OCF.Align.UniformPendingGoodBase
open import OCF.Align.UniformPendingGoodZ using (<→⊑; NZ-≺; NZ-≅; module ZFold)
open import OCF.Align.UniformPendingGoodF using (module PFold)
open import OCF.Align.UniformPendingBase using (Ω-strict; Ω<ᴱ; pfl∅; pfl-Ω̂; PFl)
```

## §1 前缀的值

$P̂$ `= Ω̂A 0 ∅ᴿ`. 目标条件 `Tg i`: 非零目标 $i$ 的弹栈闭包有覆盖 $\varphi\sqsubseteq i$ (`PopCov` 的逐点形式). `vP`/`vV`/`v0` 是 `PFold` 要的三个值; 目标 0 的值由 Depth0 的 `goodΩ̂∅` 经 `conv0` 转来 (第 0 层两种好性的数据相同), 所以不移植 PendingBase 的 `Z-ψ0`.

```agda
Fl₁ : Flr
Fl₁ = fz ⊔ fk zero

P̂ : Run Fl₁
P̂ = Ω̂A 0 ∅ᴿ

rP̂ : P̂ ≈ᴿ P̂
rP̂ = rΩ̂ r∅

fP̂ : FlR P̂
fP̂ = FlR-Ω̂ r∅ FlR-∅

open GoodP P̂ rP̂
open ZFold P̂ rP̂

module F0 = FloorΩ̂ zero zero (λ _ _ _ → z⊑) (λ _ _ _ → z⊑)

conv0 : ∀ (K′ : Ordᴵ) {x : Ordˢ zero} → F0.Good x → Good mV K′ x
conv0 K′ F0.bz          = bz
conv0 K′ (F0.bs g)      = bs (conv0 K′ g)
conv0 K′ (F0.bl hg st)  = bl (λ n → conv0 K′ (hg n)) st
conv0 K′ (F0.bi {p = ()} hb hm)
conv0 K′ (F0.bu {r = ()} g)
conv0 K′ (F0.bŝ g0 gg et eg m mm dm) = bŝ (conv0 K′ g0) (λ η e → conv0 K′ (gg η e)) et eg m mm dm
conv0 K′ (F0.bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) = bĉ G₀ Gg d₀ dE m₀ mE (conv0 K′ go) (λ η e → conv0 K′ (gO η e)) mo mO

Tg : Ordᴵ → Set
Tg i = NZ i → Cvd i (suc i)

module Val {ℓ} (ev : Ev ℓ Fl₁) where
  open F0.Pop ev using (T₀; B; Lη; evη; Gη; zη; one⊑η)

  mkPop : ∀ {m K i} (p : i <ᴵ ℓ) → Good m K (T₀ p) → (∀ η e → Good m K (Gη p η e)) → Dom m K i (suc (Mx (B p))) (T₀ p) (Gη p) → Good m K (P̂ ev p)
  mkPop {i = i} p g0 gg dm =
    bŝ g0 gg
       (fold-≅0 {φ = fk zero} {φ′ = fk zero} {cv = λ e → e} {cv′ = λ e → e} {P = ∅ᴿ} {P′ = ∅ᴿ} r∅ (Ωˢ-refl (suc zero)) ev p ev p (≅ᴵ-refl i))
       (λ η e η′ e′ eη → fold-≅0 {φ = fk η} {φ′ = fk η′} {cv = λ e″ q → e″ (suc q)} {cv′ = λ e″ q → e″ (suc q)} {P = ∅ᴿ} {P′ = ∅ᴿ} r∅ (Ωˢ-≅ eη)
                                 {ℓ = Lη p η e} {ℓ′ = Lη p η′ e′} (evη p η e) (F0.iM (FB (B p) e) (iF (B p))) (evη p η′ e′) (F0.iM (FB (B p) e′) (iF (B p))) (≅ᴵ-refl i))
       (λ η e → fold-cong {φ = fk zero} {φ′ = fk η} {ℓ′ = Lη p η e} {cv = λ e′ → e′} {cv′ = λ e′ q → e′ (suc q)} {ev = ev} {ev′ = evη p η e} {p = p} {p′ = F0.iM (FB (B p) e) (iF (B p))}
                          r∅ (Ω-monoᵒ (one⊑η p η e)))
       (λ η e η′ e′ h → fold-cong {φ = fk η} {φ′ = fk η′} {ℓ = Lη p η e} {ℓ′ = Lη p η′ e′} {cv = λ e″ q → e″ (suc q)} {cv′ = λ e″ q → e″ (suc q)} {ev = evη p η e} {ev′ = evη p η′ e′}
                                  {p = F0.iM (FB (B p) e) (iF (B p))} {p′ = lim 0 (iF (B p))} r∅ (Ω-monoᵒ h))
       dm

  P-T₀ : ∀ {K i} (p : i <ᴵ ℓ) → NZ i → i ⊑ᴵ K → Good mP K (T₀ p)
  P-T₀ {K} p nz ik = P-f {φ = fk zero} {cv = λ e → e} {ev = ev} {p = p} nz ik (Good-Ωᶜ (suc zero) K) (Ωˢ-refl (suc zero))

  P-Gη : ∀ {K i} (p : i <ᴵ ℓ) → NZ i → i ⊑ᴵ K → ∀ η e → Good mP K (Gη p η e)
  P-Gη {K} p nz ik η e = P-f {φ = fk η} {cv = λ e′ q → e′ (suc q)} {ev = evη p η e} {p = F0.iM (FB (B p) e) (iF (B p))} nz ik (Good-Ωᶜ η K) (Ωˢ-refl η)

  V-T₀ : ∀ {i} (p : i <ᴵ ℓ) → NZ i → Good mV i (T₀ p)
  V-T₀ {i} p nz = V-f {φ = fk zero} {cv = λ e → e} {ev = ev} {p = p} nz ⊑ᴵ-refl (Good-Ωᶜ (suc zero) i) (Ωˢ-refl (suc zero))

  V-Gη : ∀ {i} (p : i <ᴵ ℓ) → NZ i → ∀ η e → Good mV i (Gη p η e)
  V-Gη {i} p nz η e = V-f {φ = fk η} {cv = λ e′ q → e′ (suc q)} {ev = evη p η e} {p = F0.iM (FB (B p) e) (iF (B p))} nz ⊑ᴵ-refl (Good-Ωᶜ η i) (Ωˢ-refl η)

  cvdP : ∀ {K i} (p : i <ᴵ ℓ) → Cvd i (suc i) → i ⊑ᴵ K → Cvd K (suc (Mx (B p)))
  cvdP {K} {i} p (φ , cv , φi) ik = subst (λ M → Cvd K (suc M)) (sym (F0.Mx∅ ev p)) (φ , cv , ⊑ᴵ-trans φi ik)

  vP : ∀ {K i} (p : i <ᴵ ℓ) → Tg i → NZ i → i ⊑ᴵ K → Good mP K (P̂ ev p)
  vP {i = suc _}   p ti nz ik = mkPop p (P-T₀ p nz ik) (P-Gη p nz ik) (cvdP p (ti nz) ik , tt)
  vP {i = lim _ _} p ti nz ik = mkPop p (P-T₀ p nz ik) (P-Gη p nz ik) (cvdP p (ti nz) ik , tt)

  colV : ∀ {i} (p : i <ᴵ ℓ) (cd : Cvd i (suc (Mx (B p)))) → VisD mV (suc (Mx (B p))) (T₀ p) (Gη p)
  colV p (φ , cv , φi) =
    dom-cov rP̂ (FlΛ-fold {φ = fk zero} {P = ∅ᴿ} {cv = λ e → e} {ev = ev} {p = p} r∅ FlR-∅ φi (Ωˢ (suc zero)) (Ωˢ-refl (suc zero))) cv ,
    λ η e → dom-cov rP̂ (FlΛ-fold {φ = fk η} {ℓ = Lη p η e} {P = ∅ᴿ} {cv = λ e′ q → e′ (suc q)} {ev = evη p η e} {p = F0.iM (FB (B p) e) (iF (B p))} r∅ FlR-∅ φi (Ωˢ η) (Ωˢ-refl η)) cv

  vV : ∀ {a} (p : a <ᴵ ℓ) → Tg a → NZ a → Good mV a (P̂ ev p)
  vV {a = suc _}   p ti nz = mkPop p (V-T₀ p nz) (V-Gη p nz) (cvdP p (ti nz) ⊑ᴵ-refl , colV p (cvdP p (ti nz) ⊑ᴵ-refl))
  vV {a = lim _ _} p ti nz = mkPop p (V-T₀ p nz) (V-Gη p nz) (cvdP p (ti nz) ⊑ᴵ-refl , colV p (cvdP p (ti nz) ⊑ᴵ-refl))

  v0 : ∀ (K′ : Ordᴵ) (p : zero <ᴵ ℓ) → Good mV K′ (P̂ ev p)
  v0 K′ p = conv0 K′ (F0.Pop.goodΩ̂∅ ev p (λ ()))

cert : ∀ {φ k ℓ K} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (Fl₁ ⊔ φ)} {p : zero <ᴵ ℓ} {x : Ordˢ k} →
       (∀ {j} → j <ᴵ k → Tg j) → Good mV K x → x ≅ˢ x → Goodᶻ (toZ (fold 0 φ cv P̂ x ev p))
cert {φ = φ} {k = k} {ℓ = ℓ} {cv = cv} {ev = ev} {p = p} tk g ex =
  Good→Goodᶻ {m = mV} {K = zero} (PFold.F₀ P̂ rP̂ fP̂ Tg {ℓ} (λ ev₀ p₀ ti nz ik → Val.vP ev₀ p₀ ti nz ik) (λ ev₀ p₀ ti nz → Val.vV ev₀ p₀ ti nz) (λ K′ ev₀ p₀ → Val.v0 ev₀ K′ p₀)
                                      zero {φ = φ} {cv = cv} {ev = ev} {p = p} tk g ex)
```

## §2 外层闭包的链

`Top ev z`: $\psi_0(\Omega_\Omega\cdot2)$ `= Ω̂A 0 P̂ ev z`. 界字面是 1 (`Mx₂`). `gpt η e` 是闭包的分支, 字面就是 `cloA` 写的那棵树. `PC η`、`PC-step`、`Link` 与 Pending §1–§3 同形; 增长 `grow-g` 由 UniformPendingBase 的 `Ω-strict`, 不用 Growth.

```agda
K₂ : ∀ {K} → InF K (Fl₁ ⊔ fk zero) → K ≅ᴵ zero
K₂ (inl (inl ()))
K₂ (inl (inr ink)) = z≅
K₂ (inr ink)       = z≅

trans< : ∀ {x a b} → x <ᴵ a → a <ᴵ b → x <ᴵ b
trans< x zero      = suc x
trans< x (suc q)   = suc (trans< x q)
trans< x (lim n q) = lim n (trans< x q)

τ : ∀ {a b} → a <ᴵ b → Simᴵ (suc a) b
τ q zero    = q
τ q (suc x) = trans< x q

≺→⊑ : ∀ {a b} → a ≺ᴵ b → a ⊑ᴵ b
≺→⊑ h = ⊑ᴵ-trans (Sim→⊑ᴵ (λ q → suc q)) (s⊑′ h)

zlt : ∀ {b} → suc zero ⊑ᴵ b → zero <ᴵ b
zlt (s⊑ z≅ q) = q

lv : ∀ {x : Z} (G : Goodᶻ x) → Ordᴵ
lv G = toLevel (force _ G) (force-HS _ G)

PC : Ordᴵ → Set
PC η = ∀ {i L} → zero <ᴵ L → i <ᴵ L → NZ i → i ≺ᴵ η → Cvd i (suc i)

PC-≅ : ∀ {η η′} → η ≅ᴵ η′ → PC η → PC η′
PC-≅ e pc z p nz r = pc z p nz (≺ᴵ-respʳ r (≅ᴵ-sym e))

pickP : ∀ {η η′ i b b′} → PC η → η ≅ᴵ b → i ≅ᴵ b′ → (∀ {c} → c ⊑ᴵ η′ → CovΛ P̂ η c) → i ≺ᴵ η′ →
        ∀ {L} → zero <ᴵ L → i <ᴵ L → NZ i → (b′ ≺ᴵ b ⊎ b ≺ᴵ b′ ⊎ b′ ≅ᴵ b) → Cvd i (suc i)
pickP pc eb ei cov r z p nz (injᵃ s) = pc z p nz (≺ᴵ-respˡ ei (≺ᴵ-respʳ s (≅ᴵ-sym eb)))
pickP {η} pc eb ei cov r z p nz (injᵇ s) = η , cov (s⊑′ r) , ≺→⊑ (≺ᴵ-respˡ eb (≺ᴵ-respʳ s (≅ᴵ-sym ei)))
pickP {η} pc eb ei cov r z p nz (injᶜ c) = η , cov (s⊑′ r) , ≅ᴵ→⊑ᴵ (≅ᴵ-trans eb (≅ᴵ-trans (≅ᴵ-sym c) (≅ᴵ-sym ei)))

PC-step : ∀ {η η′} → η ≺ᴵ η′ → (∀ {c} → c ⊑ᴵ η′ → CovΛ P̂ η c) → PC η → PC η′
PC-step (via eb q) cov pc z p nz r@(via ei q′) = pickP pc eb ei cov r z p nz (<ᴵ-dec q′ q)

module TopM {ℓ} (ev : Ev ℓ (Fl₁ ⊔ fk zero)) (z : zero <ᴵ ℓ) where
  B : Top zero ℓ (Fl₁ ⊔ fk zero)
  B = bound (Fl₁ ⊔ fk zero) ev z

  Mx₂ : Mx B ≡ zero
  Mx₂ with src B
  ... | inj₁ e = e
  ... | inj₂ (s , K , k , e) = ⊥-elim (≺0 (subst (λ M → _ ≺ᴵ M) e s) (K₂ k))

  c : Ordᴵ
  c = suc (Mx B)

  one-of : ∀ {η} → c ⊑ᴵ η → suc zero ⊑ᴵ η
  one-of {η} e = subst (λ M → suc M ⊑ᴵ η) Mx₂ e

  of-one : ∀ {η} → suc zero ⊑ᴵ η → c ⊑ᴵ η
  of-one {η} e = subst (λ M → suc M ⊑ᴵ η) (sym Mx₂) e

  Lh : ∀ η → c ⊑ᴵ η → Ordᴵ
  Lh η e = Mlev (Fc B) (suc η) (FB B e)

  evh : ∀ η (e : c ⊑ᴵ η) → Ev (Lh η e) (Fl₁ ⊔ fk η)
  evh η e = liftEv Fl₁ (λ q → lim 0 q) (proj₁ (evF B)) , (λ q → lim 1 q)

  zt : ∀ η (e : c ⊑ᴵ η) → zero <ᴵ Lh η e
  zt η e = lim 0 (iF B)

  cvη : ∀ η {L} → Ev L (fk η) → Simᴵ η L
  cvη η e q = e (suc q)

  gpt : ∀ η (e : c ⊑ᴵ η) → Ordˢ zero
  gpt η e = fold 0 (fk η) (cvη η) P̂ (Ωˢ η) (evh η e) (zt η e)

  t₀ : Ordˢ zero
  t₀ = fold 0 (fk zero) (λ e → e) P̂ (Ωˢ (suc zero)) ev z

  cert-PC : ∀ η (e : c ⊑ᴵ η) → PC η → Goodᶻ (toZ (gpt η e))
  cert-PC η e pc = cert {φ = fk η} {K = η} {cv = cvη η} {ev = evh η e} {p = zt η e}
                        (λ q nz → pc (zlt (one-of e)) q nz (via (≅ᴵ-refl _) q)) (Good-Ωⱽ η ⊑ᴵ-refl) (Ωˢ-refl η)

  cov-of : ∀ η e (G : Goodᶻ (toZ (gpt η e))) {c′} → c′ ⊑ᴵ lv G → CovΛ P̂ η c′
  cov-of η e G {c′} h = Lh η e , ev′ , zt η e , Goodᶻ-tr d G , ⊑ᴵ-trans h (≅ᴵ→⊑ᴵ (toLevel-≅ (force-HS _ G) (force-HS _ (Goodᶻ-tr d G)) (force-≅ d G (Goodᶻ-tr d G))))
    where
    ev′ : Ev (Lh η e) (Fl₁ ⊔ flo η)
    ev′ = proj₁ (evh η e) , toFlo η (proj₂ (evh η e))
    d : toZ (gpt η e) ≅ᶻ toZ (χ̂ P̂ η ev′ (zt η e))
    d = toZ-≅ (fold-≅0 {φ = fk η} {φ′ = flo η} {cv = cvη η} {cv′ = cvFlo η} {P = P̂} {P′ = P̂} rP̂ (Ωˢ-refl η) (evh η e) (zt η e) ev′ (zt η e) (≅ᴵ-refl zero))

  ctx₁ : PFl P̂ × ⊤
  ctx₁ = pfl-Ω̂ pfl∅ , tt

  grow-a : ∀ {η a η′} (e : c ⊑ᴵ η) (e′ : c ⊑ᴵ η′) → η ≅ᴵ a → a <ᴵ η′ → (G : Goodᶻ (toZ (gpt η e))) (G′ : Goodᶻ (toZ (gpt η′ e′))) → lv G ≺ᴵ lv G′
  grow-a {η} {a} {η′} e e′ eη q G G′ =
    ≺ᴵ-respˡ (toLevel-≅ (force-HS _ G) (force-HS _ (proj₁ S)) e₃) (toLevel-≺ (force-HS _ (proj₁ S)) (force-HS _ G′) (proj₂ L (proj₂ S)))
    where
    Os = fo (fk η′) idO P̂ (λ e″ x → cvη η′ e″ (τ q x)) (evh η′ e′) (zt η′ e′)
    Oa = fo (fk η′) idO P̂ (λ e″ x → cvη η′ e″ (τ q (suc x))) (evh η′ e′) (zt η′ e′)
    L = Ω<ᴱ (≅ᴵ-refl a) q {O = Os} {O′ = fo (fk η′) idO P̂ (cvη η′) (evh η′ e′) (zt η′ e′)} (fo idO rP̂) G′
    S = Ω-strict a {O = Oa} {O′ = Os} (fo idO rP̂) ctx₁ (proj₁ L)
    e₃ = force-≅ (toZ-≅ (run-≅ {O = fo (fk η) idO P̂ (cvη η) (evh η e) (zt η e)} {O′ = Oa} (fo idO rP̂) (Ωˢ-≅ eη))) G (proj₁ S)

  grow-g : ∀ {η η′} (e : c ⊑ᴵ η) (e′ : c ⊑ᴵ η′) → η ≺ᴵ η′ → (G : Goodᶻ (toZ (gpt η e))) (G′ : Goodᶻ (toZ (gpt η′ e′))) → lv G ≺ᴵ lv G′
  grow-g e e′ (via eη q) = grow-a e e′ eη q

  record Link (Y : Ordᶜ zero) : Set where
    field
      η₋ : Ordᴵ
      e₋ : c ⊑ᴵ η₋
      G₋ : Goodᶻ (toZ (gpt η₋ e₋))
      eY : Y ≅ force _ G₋
      g₋ : suc η₋ ⊑ᴵ lv G₋
      pc : PC (lv G₋)

  module StepM (Y : Ordᶜ zero) (hY : HS Y) (e : c ⊑ᴵ toLevel Y hY) (l : Link Y) (G : Goodᶻ (toZ (gpt (toLevel Y hY) e))) where
    open Link l
    η : Ordᴵ
    η = toLevel Y hY

    eη : lv G₋ ≅ᴵ η
    eη = toLevel-≅ (force-HS _ G₋) hY (≅-sym eY)

    hη₋ : suc η₋ ⊑ᴵ η
    hη₋ = ⊑ᴵ-≅ʳ g₋ eη

    grow : η ≺ᴵ lv G
    grow = ≺ᴵ-respˡ (≅ᴵ-sym eη) (grow-g e₋ e (sim hη₋ zero) G₋ G)

    pcN : PC (lv G)
    pcN = PC-step grow (λ h → cov-of η e G h) (PC-≅ eη pc)

    new : Link (force _ G)
    new = record { η₋ = η ; e₋ = e ; G₋ = G ; eY = ≅-refl⁰ _ ; g₋ = s⊑′ grow ; pc = pcN }

    next-e : c ⊑ᴵ lv G
    next-e = ⊑ᴵ-trans e (≺→⊑ grow)

    mono : force _ G₋ ⊑ force _ G
    mono = fold-cong {φ = fk η₋} {φ′ = fk η} {cv = cvη η₋} {cv′ = cvη η} {ev = evh η₋ e₋} {ev′ = evh η e} {p = zt η₋ e₋} {p′ = zt η e} rP̂
                     (Ω-monoᵒ (⊑ᴵ-trans (Sim→⊑ᴵ (λ q → suc q)) hη₋)) idO G₋ G

    rise : Y ⊑⁰ force _ G
    rise = ⊑-trans (≅→⊑ eY) mono

  step-G : ∀ Y (hY : HS Y) (e : c ⊑ᴵ toLevel Y hY) → Link Y → Goodᶻ (toZ (gpt (toLevel Y hY) e))
  step-G Y hY e l = cert-PC (toLevel Y hY) e (PC-≅ (toLevel-≅ (force-HS _ (Link.G₋ l)) hY (≅-sym (Link.eY l))) (Link.pc l))

  record Pt : Set where
    constructor pt
    field
      Yp : Ordᶜ zero
      hp : HS Yp
      dp : c ⊑ᴵ toLevel Yp hp
      lp : Link Yp
  open Pt

  module Chain (G₁ : Goodᶻ (toZ t₀)) (l₀ : Link (force _ G₁)) (d₀ : c ⊑ᴵ lv G₁) where
    pk : ℕ → Pt
    Gk : ∀ k → Goodᶻ (toZ (gpt (toLevel (Yp (pk k)) (hp (pk k))) (dp (pk k))))
    pk zero    = pt (force _ G₁) (force-HS _ G₁) d₀ l₀
    pk (suc k) = pt (force _ (Gk k)) (force-HS _ (Gk k))
                    (StepM.next-e (Yp (pk k)) (hp (pk k)) (dp (pk k)) (lp (pk k)) (Gk k))
                    (StepM.new (Yp (pk k)) (hp (pk k)) (dp (pk k)) (lp (pk k)) (Gk k))
    Gk k = step-G (Yp (pk k)) (hp (pk k)) (dp (pk k)) (lp (pk k))

    mk : ∀ k → Yp (pk k) ⊑⁰ force _ (Gk k)
    mk k = StepM.rise (Yp (pk k)) (hp (pk k)) (dp (pk k)) (lp (pk k)) (Gk k)

    tr⁰ : ∀ {a a′ b b′ : Ordᶜ zero} → a′ ≅ a → b ≅ b′ → a ⊑⁰ b → a′ ⊑⁰ b′
    tr⁰ ea eb h = ⊑-trans (≅→⊑ ea) (⊑-trans h (≅→⊑ eb))

    Gᴺ : Goodᴺ (toZ (Ω̂A 0 P̂ ev z))
    Gᴺ = gc (λ k → Yp (pk k)) (λ k → hp (pk k)) (λ k → dp (pk k))
            (ofZ G₁) (ofZ-≅ G₁) (λ k → ofZ (Gk k)) (λ k → ofZ-≅ (Gk k))
            (ofZ G₁) (λ k → ofZ (Gk k))
            (tr⁰ (ofZ-≅ G₁) (≅-sym (ofZ-≅ (Gk 0))) (mk 0))
            (λ k → tr⁰ (ofZ-≅ (Gk k)) (≅-sym (ofZ-≅ (Gk (suc k)))) (mk (suc k)))
```

## §3 决定性检验: 第 0 点与实例

`e₁ = of-one ⊑ᴵ-refl`: 第一个链点的层号上界. `pc₁`: 层号 1 之下没有非零目标. `base`: 由第 0 点的证书造 `Link`; 覆盖 $\varphi=1$, $2\sqsubseteq$ 由 `Strict₁`. 模块参数是证书 (工程注记同 TreeNF).

```agda
  e₁ : c ⊑ᴵ suc zero
  e₁ = of-one ⊑ᴵ-refl

  pc₁ : PC (suc zero)
  pc₁ z p nz (via e zero) = ⊥-elim (NZ-≅ nz (≅ᴵ-sym e))
  pc₁ z p nz (via e (suc ()))

  G₀ᵀ : Goodᶻ (toZ t₀)
  G₀ᵀ = cert {φ = fk zero} {K = suc zero} {cv = λ e → e} {ev = ev} {p = z} tk₁ (Good-Ωⱽ (suc zero) ⊑ᴵ-refl) (Ωˢ-refl (suc zero))
    where
    tk₁ : ∀ {j} → j <ᴵ suc zero → Tg j
    tk₁ zero    = λ ()
    tk₁ (suc ())

  module Base (G₁ : Goodᶻ (toZ t₀)) (Gg : Goodᶻ (toZ (gpt (suc zero) e₁))) (Gb : Goodᶻ (toZ (P̂ (proj₁ (evh (suc zero) e₁)) (zt (suc zero) e₁)))) where
    e01 : force _ G₁ ≅ force _ Gg
    e01 = force-≅ (toZ-≅ (fold-≅0 {φ = fk zero} {φ′ = fk (suc zero)} {cv = λ e → e} {cv′ = cvη (suc zero)} {P = P̂} {P′ = P̂} rP̂ (Ωˢ-refl (suc zero)) ev z (evh (suc zero) e₁) (zt (suc zero) e₁) (≅ᴵ-refl zero))) G₁ Gg

    eL : lv Gg ≅ᴵ lv G₁
    eL = toLevel-≅ (force-HS _ Gg) (force-HS _ G₁) (≅-sym e01)

    two-g : two ⊑ᴵ lv Gg
    two-g = Strict₁ (proj₁ (evh (suc zero) e₁)) (zt (suc zero) e₁) {φ = fk (suc zero)} {cv = cvη (suc zero)} (evh (suc zero) e₁) refl Gb (Ωˢ (suc zero)) (Ωˢ-refl (suc zero)) Gg

    pcg : PC (lv Gg)
    pcg z′ p nz r = suc zero , cov-of (suc zero) e₁ Gg (s⊑′ r) , one⊑ z′ p nz

    l₀ : Link (force _ G₁)
    l₀ = record { η₋ = suc zero ; e₋ = e₁ ; G₋ = Gg ; eY = e01 ; g₋ = two-g ; pc = pcg }

    d₀ : c ⊑ᴵ lv G₁
    d₀ = ⊑ᴵ-trans e₁ (⊑ᴵ-trans (Sim→⊑ᴵ (λ q → suc q)) (⊑ᴵ-≅ʳ two-g eL))

  G-g1 : Goodᶻ (toZ (gpt (suc zero) e₁))
  G-g1 = cert-PC (suc zero) e₁ pc₁

  G-b : Goodᶻ (toZ (P̂ (proj₁ (evh (suc zero) e₁)) (zt (suc zero) e₁)))
  G-b = F0.Good→Goodᶻ (F0.Pop.goodΩ̂∅ (proj₁ (evh (suc zero) e₁)) (zt (suc zero) e₁) (λ ()))

  module B₀ = Base G₀ᵀ G-g1 G-b
  module C₂ = Chain G₀ᵀ B₀.l₀ B₀.d₀

  Gᴺ₂ᵁ : Goodᴺ (toZ (Ω̂A 0 P̂ ev z))
  Gᴺ₂ᵁ = C₂.Gᴺ
```
