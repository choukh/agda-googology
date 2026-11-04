# 高度抽象: 闭包与节点的右规则, 地板

> **判决: HOLDS** (编译过, 无条件). 结论写在 [LadderInf](LadderInf.lagda.md). 对高度结构 `HtS` 参数化, 由 `Survey/scripts/laddernf/mk_inf.py` 从 [LadderNFRules2](LadderNFRules2.lagda.md) 生成, 下面的说明是原文件的. 接 [LadderNFRules](LadderNFRules.lagda.md). `clo-go`: 旧的写法要 `wkC` 的合成律, 在 `pD` 行不是定义性的 (`upd-sub` 对 $n$ 递归), 所以这里带一个相似 `C′ ≈ᶜ Cʷ`, 不用合成律. 不读记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderInfBase
module OCF.Align.LadderInfRules2 (𝕊 : HtS) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Restrˢ; trˢ; tr⁻ˢ; resˢ; res⁻ˢ; Ωˢ; addˢ; _+ˢ_; 𝟎ˢ)
open import OCF.Free.Eq using (≅ᴵ→⊑ᴵ; ⊑ᴵ-≅ˡ; ⊑ᴵ-≅ʳ; _≅ᶻ_; ≅ᶻ-sym; _≅ˢ_; z≅; s≅; l≅; upˡ; upʳ; ≅ˢ-sym; ≅ˢ-trans; ≅ˢ-reflˡ; ≅ˢ-reflʳ; trˢ-≅; tr⁻ˢ-≅; ≅-trˢ; ≅-tr⁻ˢ; Ωˢ-≅; Ωˢ-refl; toZ-≅; addˢ-≅; s-invˢ; l-invˢ; i-respˢ; u-reflˢ; ŝ-refl₀; ĉ-refl₀; self-trˢ; self-tr⁻ˢ)
open import OCF.Free.Floor using (_∼ᶠ_; ∼ᶠ-refl; fz∼; ⊔∼; Flr; fz; fk; Ev; Run; flo; cvFlo; toFlo; ∅ᴿ; _⊔_; bound)
open import OCF.Free.Force using (Goodᴺ; gz; gs; gl; gc; forceᴺ; forceᴺ-HS; forceᴺ-≅; Goodᴺ-tr)
open import OCF.Free.Tree using (Fl; asl; asr; swp; dupr2; <◃)
open import OCF.Align.LadderInfTree 𝕊
open import OCF.Align.LadderInfRel 𝕊
open import OCF.Align.LadderInfCx 𝕊
open import OCF.Align.LadderInfRules 𝕊
open Ord-Ord using (iter)
open Restrˢ
open RestrQ
```

## §0 相似的对称与传递

```agda
≈ᶜ-sym : ∀ {m c φ χ ψ ρ} {C : Cx m c φ χ} {C′ : Cx m c ψ ρ} → C ≈ᶜ C′ → C′ ≈ᶜ C
≈ᵒ-sym′ : ∀ {k k′} {O : Obs k} {O′ : Obs k′} → O ≈ᵒ O′ → O′ ≈ᵒ O
≈ᵒ-sym′ idO = idO
≈ᵒ-sym′ (tlo o) = tlo (≈ᶜ-sym o)
≈ᵒ-sym′ (addo o k e) = addo (≈ᵒ-sym′ o) (≅ᴵ-sym k) (≅ˢ-sym e)
≈ᵒ-sym′ (tro o) = tro (≈ᵒ-sym′ o)
≈ᵒ-sym′ (tr⁻o o) = tr⁻o (≈ᵒ-sym′ o)
≈ᶜ-sym (top o) = top (≈ᵒ-sym′ o)
≈ᶜ-sym (pa r o) = pa r (≈ᶜ-sym o)
≈ᶜ-sym (pψ o) = pψ (≈ᶜ-sym o)
≈ᶜ-sym (pΨ o) = pΨ (≈ᶜ-sym o)
≈ᶜ-sym (pι o) = pι (≈ᶜ-sym o)
≈ᶜ-sym (pD o) = pD (≈ᶜ-sym o)
≈ᶜ-sym (ptr o) = ptr (≈ᶜ-sym o)
≈ᶜ-sym (ptr⁻ o) = ptr⁻ (≈ᶜ-sym o)

≈ᶜ-trans : ∀ {m c φ χ ψ ρ φ₂ χ₂} {C : Cx m c φ χ} {C′ : Cx m c ψ ρ} {C″ : Cx m c φ₂ χ₂} → C ≈ᶜ C′ → C′ ≈ᶜ C″ → C ≈ᶜ C″
≈ᵒ-trans′ : ∀ {k k′ k″} {O : Obs k} {O′ : Obs k′} {O″ : Obs k″} → O ≈ᵒ O′ → O′ ≈ᵒ O″ → O ≈ᵒ O″
≈ᵒ-trans′ idO idO = idO
≈ᵒ-trans′ (tlo o) (tlo o′) = tlo (≈ᶜ-trans o o′)
≈ᵒ-trans′ (addo o k e) (addo o′ k′ e′) = addo (≈ᵒ-trans′ o o′) (≅ᴵ-trans k k′) (≅ˢ-trans e e′)
≈ᵒ-trans′ (tro o) (tro o′) = tro (≈ᵒ-trans′ o o′)
≈ᵒ-trans′ (tr⁻o o) (tr⁻o o′) = tr⁻o (≈ᵒ-trans′ o o′)
≈ᶜ-trans (top o) (top o′) = top (≈ᵒ-trans′ o o′)
≈ᶜ-trans (pa r o) (pa _ o′) = pa r (≈ᶜ-trans o o′)
≈ᶜ-trans (pψ o) (pψ o′) = pψ (≈ᶜ-trans o o′)
≈ᶜ-trans (pΨ o) (pΨ o′) = pΨ (≈ᶜ-trans o o′)
≈ᶜ-trans (pι o) (pι o′) = pι (≈ᶜ-trans o o′)
≈ᶜ-trans (pD o) (pD o′) = pD (≈ᶜ-trans o o′)
≈ᶜ-trans (ptr o) (ptr o′) = ptr (≈ᶜ-trans o o′)
≈ᶜ-trans (ptr⁻ o) (ptr⁻ o′) = ptr⁻ (≈ᶜ-trans o o′)

wk≈ : ∀ {m c φ χ ψ ρ φ₁ χ₁ ψ₁ ρ₁} {C : Cx m c φ χ} {C′ : Cx m c ψ ρ} (le : ∀ {L} → Ev L φ → Ev L φ₁) (lc : Sub m χ χ₁) (le′ : ∀ {L} → Ev L ψ → Ev L ψ₁) (lc′ : Sub m ρ ρ₁) → C ≈ᶜ C′ → wkC le lc C ≈ᶜ wkC le′ lc′ C′
wk≈ le lc le′ lc′ o = ≈ᶜ-wkˡ le lc (≈ᶜ-wkʳ le′ lc′ o)

Sim∼-refl : ∀ {m} (χ : Fv) → Sim∼ m χ χ
Sim∼-refl χ i q = ∼ᶠ-refl (χ i)
```

## §1 闭包

```agda
clo-go : ∀ {m c φ₀ χ₀ φ₁ χ₁ φ χ} {x : Q m c φ₀ χ₀} {C : Cx m c φ₀ χ₀} {C′ : Cx m c φ₁ χ₁} {Cʷ : Cx m c (φ ⊔ fk zero) χ} → C ≈ᶜ C′ → C′ ≈ᶜ Cʷ →
         {t : Q m c (φ ⊔ fk zero) χ} {g : (η : Ordᴵ) → Q m c (φ ⊔ fk η) χ} → x ⊑ᵀ t →
         (G′ : Goodᴺ (toZ (runᶜ Cʷ (qclo t g)))) → Σ (Goodᴺ (toZ (runᶜ C x))) λ G → forceᴺ _ G ⊑ forceᴺ _ G′
clo-go {x = x} {Cʷ = top {ℓ = ℓʷ} Oʷ evʷ pʷ okʷ eʷ} (top {ev = ev} {p = p} {ok = ok} {e = e} o) (top o′) {t} {g} h G′ =
  ŝ-rᴱ {x = ψ̄ᵠ ok e x ev p} {t₀ = ψ̄ᵠ okʷ eʷ t evʷ pʷ} (ψ̄-cong h) (≈ᵒ-trans′ o o′) G′
clo-go {φ = φ} {χ = χ} {x = x} {Cʷ = pa W C₁ʷ} (pa r o) (pa _ o′) {t} {g} h G′ =
  proj₁ K , ⊑-trans (proj₂ K) (proj₂ J)
  where
  Y = qclo (qwk asr sub-id (W ⊞ t)) (λ η → qwk asr sub-id (W ⊞ g η))
  J = pull≡ (run-wkC asl sub-id C₁ʷ Y) G′
  K = clo-go {x = W ⊞ x} o (≈ᶜ-wkʳ asl sub-id o′) {qwk asr sub-id (W ⊞ t)} {λ η → qwk asr sub-id (W ⊞ g η)} (wk-rᵀ (⊞-cong r h)) (proj₁ J)
clo-go {φ = φ} {χ = χ} {x = x} {Cʷ = pψ q C₁ʷ} (pψ o) (pψ o′) {t} {g} h G′ =
  proj₁ K , ⊑-trans (proj₂ K) (proj₂ J)
  where
  Y = qclo (qwk asr sub-id (ψᵠ q t)) (λ η → qwk asr sub-id (ψᵠ q (g η)))
  J = pull≡ (run-wkC asl sub-id C₁ʷ Y) G′
  K = clo-go {x = ψᵠ q x} o (≈ᶜ-wkʳ asl sub-id o′) {qwk asr sub-id (ψᵠ q t)} {λ η → qwk asr sub-id (ψᵠ q (g η))} (wk-rᵀ (ψ-cong {q = q} h)) (proj₁ J)
clo-go {x = x} {C = pΨ qH₀ ok₀ e₀ p₀ C₁} {Cʷ = pΨ qH ok e p C₁ʷ} (pΨ o) (pΨ o′) {t} {g} h G′ =
  proj₁ K , ⊑-trans (proj₂ K) (proj₂ J)
  where
  Y = qclo (qwk asr sub-id (Ψ qH ok e p t)) (λ η → qwk asr sub-id (Ψ qH ok e p (g η)))
  J = pull≡ (run-wkC asl sub-id C₁ʷ Y) G′
  K = clo-go {x = Ψ qH₀ ok₀ e₀ p₀ x} o (≈ᶜ-wkʳ asl sub-id o′) {qwk asr sub-id (Ψ qH ok e p t)} {λ η → qwk asr sub-id (Ψ qH ok e p (g η))} (wk-rᵀ (Ψ-cong h)) (proj₁ J)
clo-go {x = x} {Cʷ = pι q C₁ʷ} (pι o) (pι o′) {t} {g} h G′ =
  clo-go {x = ι q x} o o′ {ι q t} {λ η → ι q (g η)} (ι-cong {q = q} h) G′
clo-go {x = x} {Cʷ = pD C₁ʷ} (pD {q = qd} o) (pD o′) {t} {g} h G′ =
  clo-go {x = ι↓ {α = zero} qd x} o o′ {ι↓ {α = zero} qd t} {λ η → ι↓ {α = zero} qd (g η)} (ιD-cong h) G′
clo-go {x = x} {C = ptr e₀ _} {Cʷ = ptr e C₁ʷ} (ptr o) (ptr o′) {t} {g} h G′ =
  clo-go {x = trQ e₀ x} o o′ {trQ e t} {λ η → trQ e (g η)} (trᵀ-cong {e = e₀} {e′ = e} h) G′
clo-go {x = x} {C = ptr⁻ e₀ _} {Cʷ = ptr⁻ e C₁ʷ} (ptr⁻ o) (ptr⁻ o′) {t} {g} h G′ =
  clo-go {x = tr⁻Q e₀ x} o o′ {tr⁻Q e t} {λ η → tr⁻Q e (g η)} (tr⁻ᵀ-cong {e = e₀} {e′ = e} h) G′

clo-rᵀ : ∀ {m c φ₀ χ₀ φ χ} {x : Q m c φ₀ χ₀} {t : Q m c (φ ⊔ fk zero) χ} {g : (η : Ordᴵ) → Q m c (φ ⊔ fk η) χ} → x ⊑ᵀ t → x ⊑ᵀ qclo t g
clo-rᵀ h o G′ = clo-go o (≈ᶜ-reflʳ o) h G′

cl-rᵀ : ∀ {m c φ₀ χ₀ φ χ n} {x : Q m c φ₀ χ₀} {q : n <ᴸ m} {ψ : Flr} {s : ∀ {ℓ} → Ev ℓ (χ n) → Ev ℓ (ψ ⊔ fk zero)} {t : Q m c φ χ} {g : (η : Ordᴵ) → Q m c φ (upd χ n (ψ ⊔ fk η))} → x ⊑ᵀ t → x ⊑ᵀ qcl q ψ s t g
cl-rᵀ {x = x} {t = t} p₁ (top {ev = ev} {ev′ = ev′} {p = p₀} {p′ = pt} {ok = ok} {ok′ = ok′} {e = e} {e′ = e′} o) = ŝ-rᴱ {x = ψ̄ᵠ ok e x ev p₀} {t₀ = ψ̄ᵠ ok′ e′ t ev′ pt} (ψ̄-cong p₁) o
cl-rᵀ {t = t} p₁ (pa {W = W} r o) = cl-rᵀ {t = W ⊞ t} (⊞-cong r p₁) o
cl-rᵀ {t = t} p₁ (pψ {q = q} o) = cl-rᵀ {t = ψᵠ q t} (ψ-cong {q = q} p₁) o
cl-rᵀ {n = n} {t = t} p₁ (pΨ {H = H} {qH = qH} {ok′ = ok} {e′ = e} {p′ = pt} o) with tri n H
... | tlt l = cl-rᵀ {t = Ψ qH ok e pt t} (Ψ-cong p₁) o
... | teq refl = ŝ-rᵀ {t = Ψ qH ok e pt t} (Ψ-cong p₁) o
... | tgt l = ŝ-rᵀ {t = Ψ qH ok e pt t} (Ψ-cong p₁) o
cl-rᵀ {t = t} p₁ (pι {q = q} o) = cl-rᵀ {t = ι q t} (ι-cong {q = q} p₁) o
cl-rᵀ {t = t} p₁ (pD {q = qd} o) = cl-rᵀ {t = ι↓ {α = zero} qd t} (ιD-cong p₁) o
cl-rᵀ {t = t} p₁ (ptr {e = e₀} {e′ = ε} o) = cl-rᵀ {t = trQ ε t} (trᵀ-cong {e = e₀} {e′ = ε} p₁) o
cl-rᵀ {t = t} p₁ (ptr⁻ {e = e₀} {e′ = ε} o) = cl-rᵀ {t = tr⁻Q ε t} (tr⁻ᵀ-cong {e = e₀} {e′ = ε} p₁) o

FlΩ̇ : ∀ m k {ξ ζ} → Q m k ξ ζ → Set
FlΩ̇ m k z = ∀ {φ χ} {x : Q m k φ χ} → Rq m k k x x → x ⊑ᵀ Ω̇ m k → x ⊑ᵀ z
```

## §2 地板沿层号搬运

```agda
⊑ᵀ-Rˡ : ∀ {m c φ χ ψ ρ} {x y : Q m c φ χ} {w : Q m c ψ ρ} → Rq m c c x y → y ⊑ᵀ w → x ⊑ᵀ w
⊑ᵀ-Rˡ e i o G′ = proj₁ K , ⊑-trans (proj₂ K) (proj₂ J)
  where
  J = i o G′
  K = R→⊑ᵀ e (≈ᶜ-reflˡ o) (proj₁ J)

FlΩ̇-tr⁻ : ∀ {m a b ξ ζ} (e : a ≅ᴵ b) {z : Q m b ξ ζ} → FlΩ̇ m b z → FlΩ̇ m a (tr⁻Q e z)
FlΩ̇-tr⁻ {m} e {z} f rx h =
  ⊑ᵀ-Rˡ (R-tr⁻ʳ e (R-trʳ e rx))
    (tr⁻ᵀ-cong {e = e} {e′ = e} (f (R-trˡ e (R-trʳ e rx)) (⊑ᵀ-Rʳ (trᵀ-cong {e = e} {e′ = e} h) (R-trˡ e (RΩ̇ m e)))))

FlΩ̇-tr : ∀ {m a b ξ ζ} (e : a ≅ᴵ b) {z : Q m a ξ ζ} → FlΩ̇ m a z → FlΩ̇ m b (trQ e z)
FlΩ̇-tr {m} e {z} f rx h =
  ⊑ᵀ-Rˡ (R-trʳ e (R-tr⁻ʳ e rx))
    (trᵀ-cong {e = e} {e′ = e} (f (R-tr⁻ˡ e (R-tr⁻ʳ e rx)) (⊑ᵀ-Rʳ (tr⁻ᵀ-cong {e = e} {e′ = e} h) (R-tr⁻ˡ e (RΩ̇ m (≅ᴵ-sym e))))))

R-back : ∀ {m j a b ξ ζ ξ′ ζ′} (q : j <ᴵ a) (e : a ≅ᴵ b) {z : Q m (repQ (resQ q e)) ξ ζ} {z′ : Q m (repQ (resQ q e)) ξ′ ζ′} → Rq m _ _ z z′ → Rq m j j (backQ (resQ q e) z) (backQ (resQ q e) z′)
R-back q e r = R-resˡ q e (R-resʳ q e r)

R-back⁻ : ∀ {m j a b ξ ζ ξ′ ζ′} (q : j <ᴵ a) (e : b ≅ᴵ a) {z : Q m (repQ (res⁻Q q e)) ξ ζ} {z′ : Q m (repQ (res⁻Q q e)) ξ′ ζ′} → Rq m _ _ z z′ → Rq m j j (backQ (res⁻Q q e) z) (backQ (res⁻Q q e) z′)
R-back⁻ q e r = R-res⁻ˡ q e (R-res⁻ʳ q e r)

Fl-back : ∀ {m j a b ξ ζ} (q : j <ᴵ a) (e : a ≅ᴵ b) {z : Q m (repQ (resQ q e)) ξ ζ} → FlΩ̇ m _ z → FlΩ̇ m j (backQ (resQ q e) z)
Fl-back zero      (s≅ e) f = FlΩ̇-tr⁻ e f
Fl-back (suc q)   (s≅ e) f = Fl-back q e f
Fl-back (lim n q) (l≅ h) f = Fl-back q (h n) f

Fl-back⁻ : ∀ {m j a b ξ ζ} (q : j <ᴵ a) (e : b ≅ᴵ a) {z : Q m (repQ (res⁻Q q e)) ξ ζ} → FlΩ̇ m _ z → FlΩ̇ m j (backQ (res⁻Q q e) z)
Fl-back⁻ zero      (s≅ e) f = FlΩ̇-tr e f
Fl-back⁻ (suc q)   (s≅ e) f = Fl-back⁻ q e f
Fl-back⁻ (lim n q) (l≅ h) f = Fl-back⁻ q (h n) f
```

## §3 节点的右规则

输入 $z$ 的地板 `FlΩ̇`: 第 0 个链点是 $\dot\Omega_k$. 两个节点互相调用: `ι↓` 把字面节点变成高度 $n$ 的节点, 目标在同高度时高度 $n$ 的节点穿透成字面节点.

```agda
Ω-rᵀ : ∀ {m c φ₀ χ₀ φ χ k} {x : Q m c φ₀ χ₀} {fe : ∀ {L} → Ev L φ → Ev L Fl} {r : k <ᴵ c} {h : ∀ ξ ζ → Us m k (<→◃ r) ξ ζ → Q m c (ξ ⊔ φ) (lo m ζ ∪ χ)} →
       (∀ ξ ζ (z : Q m k ξ ζ) → Rq m k k z z → FlΩ̇ m k z → x ⊑ᵀ h ξ ζ (intoU (<→◃ r) z)) → x ⊑ᵀ qΩ fe r h
Ω↓-rᵀ : ∀ {m c φ₀ χ₀ φ χ n k} {x : Q m c φ₀ χ₀} {q : n <ᴸ m} {fe : ∀ {L} → Ev L φ → Ev L Fl} {ac : ∀ {L} → Ev L (χ n) → k <ᴵ L} {h : ∀ ξ ζ → Vs m q k ξ ζ → Q m c (ξ ⊔ φ) (lo n ζ ∪ χ)} →
       (∀ ξ ζ (z : Q n k ξ ζ) → Rq n k k z z → FlΩ̇ n k z → x ⊑ᵀ h ξ ζ (intoV q z)) → x ⊑ᵀ qΩ↓ q fe ac h

Ω-rᵀ {m} {φ = φ} {χ = χ} {k = k} {x = x} {fe = fe} {r = r} {h = h} H (top {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} {ok = ok} {ok′ = ok′} {e = e} {e′ = e′} o) =
  lim-rᴱ {x = ψ̄ᵠ ok e x ev p} {h = λ i → ψ̄ᵠ ok′ (e⁺ m ok′ e′) (h φ (Z* χ) (intoU (<→◃ r) (chainᵠ fe fc* (λ z → qwk (λ v → fe v , (v , v)) (⇑ (cv* m)) (ψᵠ r (h φ (Z* χ) (intoU (<→◃ r) z)))) i))) (ev′ , ev′) p′} 0
    (ψ̄-cong (H φ (Z* χ) (qwk fe fc* (Ω̇ m k)) (rwk (RΩ̇ m (≅ᴵ-refl k))) (λ _ h₁ → wk-rᵀ h₁))) o
Ω-rᵀ {x = x} {fe = fe} {r = r} {h = h} H (pa {W = W} rW o) =
  Ω-rᵀ {x = W ⊞ x} {fe = λ e → fe (proj₂ e)} {r = r} {h = λ ξ ζ z → qwk swp (λ i q → swp) (W ⊞ h ξ ζ z)} (λ ξ ζ z rz f → wk-rᵀ (⊞-cong rW (H ξ ζ z rz f))) o
Ω-rᵀ {m} {c = c} {φ = φ} {χ = χ} {k = k} {x = x} {fe = fe} {r = r} {h = h} H (pψ {t = t} {q = q} o) with <ᴵ-dec r q
... | injᵃ (via e s) = Ω-rᵀ {x = ψᵠ q x} {fe = proj₁} {r = s} {h = λ ξ ζ z → qwk swp (λ i r′ → swp) (ψᵠ q (h ξ ζ (intoU (<→◃ r) (tr⁻Q e (outU (<→◃ s) z)))))}
    (λ ξ ζ z rz f → wk-rᵀ (ψ-cong {q = q} (subst (λ w → x ⊑ᵀ h ξ ζ (intoU (<→◃ r) (tr⁻Q e w))) (sym (out-intoU (<→◃ s) z)) (H ξ ζ (tr⁻Q e z) (R-tr⁻ˡ e (R-tr⁻ʳ e rz)) (FlΩ̇-tr⁻ e f))))) o
... | injᵇ _ = lim-rᵀ {x = ψᵠ q x} {F = λ n → qwk dupr2 (⇑ (cv* m)) (ψᵠ q (h (Fl ⊔ φ) (Z* χ) (intoU (<→◃ r) (chainᵠ proj₁ fc* (λ z → qwk dupr2 (⇑ (cv* m)) (ψᵠ r (h (Fl ⊔ φ) (Z* χ) (intoU (<→◃ r) z)))) n))))} 0
    (wk-rᵀ (ψ-cong {q = q} (H (Fl ⊔ φ) (Z* χ) (qwk proj₁ fc* (Ω̇ m k)) (rwk (RΩ̇ m (≅ᴵ-refl k))) (λ _ h₁ → wk-rᵀ h₁)))) o
... | injᶜ _ = lim-rᵀ {x = ψᵠ q x} {F = λ n → qwk dupr2 (⇑ (cv* m)) (ψᵠ q (h (Fl ⊔ φ) (Z* χ) (intoU (<→◃ r) (chainᵠ proj₁ fc* (λ z → qwk dupr2 (⇑ (cv* m)) (ψᵠ r (h (Fl ⊔ φ) (Z* χ) (intoU (<→◃ r) z)))) n))))} 0
    (wk-rᵀ (ψ-cong {q = q} (H (Fl ⊔ φ) (Z* χ) (qwk proj₁ fc* (Ω̇ m k)) (rwk (RΩ̇ m (≅ᴵ-refl k))) (λ _ h₁ → wk-rᵀ h₁)))) o
Ω-rᵀ {m} {φ = φ} {χ = χ} {k = k} {x = x} {fe = fe} {r = r} {h = h} H (pΨ {qH = qH} {ok = ok₀} {ok′ = ok} {e = e₀} {e′ = e} {p = p₀} {p′ = pt} o) =
  lim-rᵀ {x = Ψ qH ok₀ e₀ p₀ x} {F = λ i → qwk dupr2 (⇑ (cv* m)) (Ψ qH ok (e⁺ m ok e) pt (h (Fl ⊔ φ) (Z* χ) (intoU (<→◃ r) (chainᵠ proj₁ fc* (λ z → qwk dupr2 (⇑ (cv* m)) (ψᵠ r (h (Fl ⊔ φ) (Z* χ) (intoU (<→◃ r) z)))) i))))} 0
    (wk-rᵀ (Ψ-cong (H (Fl ⊔ φ) (Z* χ) (qwk proj₁ fc* (Ω̇ m k)) (rwk (RΩ̇ m (≅ᴵ-refl k))) (λ _ h₁ → wk-rᵀ h₁)))) o
Ω-rᵀ {x = x} {fe = fe} {r = r} {h = h} H (pι {q = q} o) =
  Ω-rᵀ {x = ι q x} {fe = fe} {r = <◃ r q} {h = λ ξ ζ z → ι q (h ξ ζ (intoU (<→◃ r) (outU (<→◃ (<◃ r q)) z)))}
    (λ ξ ζ z rz f → ι-cong {q = q} (subst (λ w → x ⊑ᵀ h ξ ζ (intoU (<→◃ r) w)) (sym (out-intoU (<→◃ (<◃ r q)) z)) (H ξ ζ z rz f))) o
Ω-rᵀ {m} {c = c} {χ = χ} {k = k} {x = x} {fe = fe} {r = r} {h = h} H (pD {q = qd} o) =
  Ω↓-rᵀ {x = ι↓ {α = zero} qd x} {q = qd} {fe = fe} {ac = λ e → cvFlo c (subst (Ev _) (cap-self χ m _) e) r} {h = λ ξ ζ z → qwk (λ e → e) (⇑ (c-∪ {lo m ζ} {χ} _)) (ι↓ qd (h ξ ζ (intoU (<→◃ r) (outV qd z))))}
    (λ ξ ζ z rz f → wk-rᵀ (ιD-cong (subst (λ w → x ⊑ᵀ h ξ ζ (intoU (<→◃ r) w)) (sym (out-intoV qd z)) (H ξ ζ z rz f)))) o
Ω-rᵀ {x = x} {fe = fe} {r = r} {h = h} H (ptr {e = e₀} {e′ = e} o) =
  Ω-rᵀ {x = trQ e₀ x} {fe = fe} {r = ltQ (resQ r e)} {h = λ ξ ζ z → trQ e (h ξ ζ (intoU (<→◃ r) (backQ (resQ r e) (outU (<→◃ (ltQ (resQ r e))) z))))}
    (λ ξ ζ z rz f → trᵀ-cong {e = e₀} {e′ = e} (subst (λ w → x ⊑ᵀ h ξ ζ (intoU (<→◃ r) (backQ (resQ r e) w))) (sym (out-intoU (<→◃ (ltQ (resQ r e))) z))
       (H ξ ζ _ (R-back r e rz) (Fl-back r e f)))) o
Ω-rᵀ {x = x} {fe = fe} {r = r} {h = h} H (ptr⁻ {e = e₀} {e′ = e} o) =
  Ω-rᵀ {x = tr⁻Q e₀ x} {fe = fe} {r = ltQ (res⁻Q r e)} {h = λ ξ ζ z → tr⁻Q e (h ξ ζ (intoU (<→◃ r) (backQ (res⁻Q r e) (outU (<→◃ (ltQ (res⁻Q r e))) z))))}
    (λ ξ ζ z rz f → tr⁻ᵀ-cong {e = e₀} {e′ = e} (subst (λ w → x ⊑ᵀ h ξ ζ (intoU (<→◃ r) (backQ (res⁻Q r e) w))) (sym (out-intoU (<→◃ (ltQ (res⁻Q r e))) z))
       (H ξ ζ _ (R-back⁻ r e rz) (Fl-back⁻ r e f)))) o

Ω↓-rᵀ {φ = φ} {χ = χ} {n = n} {k = k} {x = x} {q = q} {fe = fe} {ac = ac} {h = h} H (top {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} {ok = ok} {ok′ = ok′} {e = e} {e′ = e′} o) =
  lim-rᴱ {x = ψ̄ᵠ ok e x ev p} {h = λ i → ψ̄ᵠ ok′ (e⁺ n ok′ e′) (h φ (Z* χ) (intoV q (chainᵠ fe fc* (λ z → qwk (λ v → fe v , (v , v)) (⇑ (cv* n)) (Ψ q ok′ (e⁺ n ok′ (e↓ e′)) (ac (e↓ e′ n (inj₁ refl) q)) (h φ (Z* χ) (intoV q z)))) i))) (ev′ , ev′) p′} 0
    (ψ̄-cong (H φ (Z* χ) (qwk fe fc* (Ω̇ n k)) (rwk (RΩ̇ n (≅ᴵ-refl k))) (λ _ h₁ → wk-rᵀ h₁))) o
Ω↓-rᵀ {x = x} {q = q} {fe = fe} {ac = ac} {h = h} H (pa {W = W} rW o) =
  Ω↓-rᵀ {x = W ⊞ x} {q = q} {fe = λ e → fe (proj₂ e)} {ac = λ e → ac (proj₂ e)} {h = λ ξ ζ z → qwk swp (λ i q₁ → swp) (W ⊞ h ξ ζ z)} (λ ξ ζ z rz f → wk-rᵀ (⊞-cong rW (H ξ ζ z rz f))) o
Ω↓-rᵀ {x = x} {q = q} {fe = fe} {ac = ac} {h = h} H (pψ {q = q₁} o) =
  Ω↓-rᵀ {x = ψᵠ q₁ x} {q = q} {fe = proj₁} {ac = λ e → ac (proj₂ e)} {h = λ ξ ζ z → qwk swp (λ i r′ → swp) (ψᵠ q₁ (h ξ ζ z))} (λ ξ ζ z rz f → wk-rᵀ (ψ-cong {q = q₁} (H ξ ζ z rz f))) o
Ω↓-rᵀ {φ = φ} {χ = χ} {n = n} {k = k} {x = x} {q = q} {fe = fe} {ac = ac} {h = h} H (pΨ {H = H₀} {qH = qH} {ok = ok₀} {ok′ = ok} {e = e₀} {e′ = e} {p = p₀} {p′ = pt} o) with tri n H₀
... | tlt l = Ω↓-rᵀ {x = Ψ qH ok₀ e₀ p₀ x} {q = l} {fe = proj₁} {ac = λ u → ac (proj₂ u)} {h = λ ξ ζ z → qwk swp (λ i r → swp) (Ψ qH ok (e-lo ζ (inj₂ l) e) pt (h ξ ζ (intoV q (outV l z))))}
    (λ ξ ζ z rz f → wk-rᵀ (Ψ-cong (subst (λ w → x ⊑ᵀ h ξ ζ (intoV q w)) (sym (out-intoV l z)) (H ξ ζ z rz f)))) o
... | teq refl with <ᴵ-dec (ac (e n (inj₁ refl) q)) pt
...   | injᵃ (via d s) = Ω-rᵀ {x = Ψ qH ok₀ e₀ p₀ x} {fe = proj₁} {r = s} {h = λ ξ ζ y → qwk swp (λ i r → swp) (Ψ qH ok (e-lo ζ (inj₁ refl) e) pt (h ξ ζ (intoV q (tr⁻Q d (outU (<→◃ s) y)))))}
    (λ ξ ζ z rz f → wk-rᵀ (Ψ-cong (subst (λ w → x ⊑ᵀ h ξ ζ (intoV q (tr⁻Q d w))) (sym (out-intoU (<→◃ s) z)) (H ξ ζ (tr⁻Q d z) (R-tr⁻ˡ d (R-tr⁻ʳ d rz)) (FlΩ̇-tr⁻ d f))))) o
...   | injᵇ _ = lim-rᵀ {x = Ψ qH ok₀ e₀ p₀ x} {F = λ i → qwk dupr2 (⇑ (cv* n)) (Ψ qH ok (e⁺ n ok e) pt (h (Fl ⊔ φ) (Z* χ) (intoV q (chainᵠ proj₁ fc* (λ z → qwk dupr2 (⇑ (cv* n)) (Ψ q ok (e⁺ n ok e) (ac (e n (inj₁ refl) q)) (h (Fl ⊔ φ) (Z* χ) (intoV q z)))) i))))} 0
    (wk-rᵀ (Ψ-cong (H (Fl ⊔ φ) (Z* χ) (qwk proj₁ fc* (Ω̇ n k)) (rwk (RΩ̇ n (≅ᴵ-refl k))) (λ _ h₁ → wk-rᵀ h₁)))) o
...   | injᶜ _ = lim-rᵀ {x = Ψ qH ok₀ e₀ p₀ x} {F = λ i → qwk dupr2 (⇑ (cv* n)) (Ψ qH ok (e⁺ n ok e) pt (h (Fl ⊔ φ) (Z* χ) (intoV q (chainᵠ proj₁ fc* (λ z → qwk dupr2 (⇑ (cv* n)) (Ψ q ok (e⁺ n ok e) (ac (e n (inj₁ refl) q)) (h (Fl ⊔ φ) (Z* χ) (intoV q z)))) i))))} 0
    (wk-rᵀ (Ψ-cong (H (Fl ⊔ φ) (Z* χ) (qwk proj₁ fc* (Ω̇ n k)) (rwk (RΩ̇ n (≅ᴵ-refl k))) (λ _ h₁ → wk-rᵀ h₁)))) o
Ω↓-rᵀ {φ = φ} {χ = χ} {n = n} {k = k} {x = x} {q = q} {fe = fe} {ac = ac} {h = h} H (pΨ {H = H₀} {qH = qH} {ok = ok₀} {ok′ = ok} {e = e₀} {e′ = e} {p = p₀} {p′ = pt} o) | tgt l =
  lim-rᵀ {x = Ψ qH ok₀ e₀ p₀ x} {F = λ i → qwk dupr2 (⇑ (cv* n)) (Ψ qH ok (e⁺ n ok e) pt (h (Fl ⊔ φ) (Z* χ) (intoV q (chainᵠ proj₁ fc* (λ z → qwk dupr2 (⇑ (cv* n)) (Ψ q ok (e⁺ n ok (e↑ l e)) (ac (e↑ l e n (inj₁ refl) q)) (h (Fl ⊔ φ) (Z* χ) (intoV q z)))) i))))} 0
    (wk-rᵀ (Ψ-cong (H (Fl ⊔ φ) (Z* χ) (qwk proj₁ fc* (Ω̇ n k)) (rwk (RΩ̇ n (≅ᴵ-refl k))) (λ _ h₁ → wk-rᵀ h₁)))) o
Ω↓-rᵀ {x = x} {q = q} {fe = fe} {ac = ac} {h = h} H (pι {q = q₁} o) =
  Ω↓-rᵀ {x = ι q₁ x} {q = q} {fe = fe} {ac = ac} {h = λ ξ ζ z → ι q₁ (h ξ ζ z)} (λ ξ ζ z rz f → ι-cong {q = q₁} (H ξ ζ z rz f)) o
Ω↓-rᵀ {χ = χ} {n = j} {x = x} {q = q} {fe = fe} {ac = ac} {h = h} H (pD {q = qd} o) =
  Ω↓-rᵀ {x = ι↓ {α = zero} qd x} {q = tr< q qd} {fe = fe} {ac = λ e → ac (subst (Ev _) (cap-lt χ _ q) e)} {h = λ ξ ζ z → qwk (λ e → e) (⇑ (c-∪ {lo j ζ} {χ} _)) (ι↓ qd (h ξ ζ (intoV q (outV (tr< q qd) z))))} (λ ξ ζ z rz f → wk-rᵀ (ιD-cong (subst (λ w → x ⊑ᵀ h ξ ζ (intoV q w)) (sym (out-intoV (tr< q qd) z)) (H ξ ζ z rz f)))) o
Ω↓-rᵀ {x = x} {q = q} {fe = fe} {ac = ac} {h = h} H (ptr {e = e₀} {e′ = e} o) =
  Ω↓-rᵀ {x = trQ e₀ x} {q = q} {fe = fe} {ac = ac} {h = λ ξ ζ z → trQ e (h ξ ζ z)} (λ ξ ζ z rz f → trᵀ-cong {e = e₀} {e′ = e} (H ξ ζ z rz f)) o
Ω↓-rᵀ {x = x} {q = q} {fe = fe} {ac = ac} {h = h} H (ptr⁻ {e = e₀} {e′ = e} o) =
  Ω↓-rᵀ {x = tr⁻Q e₀ x} {q = q} {fe = fe} {ac = ac} {h = λ ξ ζ z → tr⁻Q e (h ξ ζ z)} (λ ξ ζ z rz f → tr⁻ᵀ-cong {e = e₀} {e′ = e} (H ξ ζ z rz f)) o
```
