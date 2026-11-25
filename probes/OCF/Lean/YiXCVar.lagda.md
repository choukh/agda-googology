# 第 0 层把出口条件放进向下封闭: 变体关系, 消去 mc, 两条局部否定

> 验收文件 (读记号). 判决: 编译定理, 无前提. mc 带 NF、Ctbl 的第 0 层变体 `Mᴺ` 与 "推导连同 `Exᴴ`" 一一对应 (`toᴴ`, `exᴺ`, `ofᴴ`), 出口无条件 (`exitᴺ`); 带 `Exᴴ` 的推导消去 mc, 成为同一下标、同一棵树上 `YiKVRel.M⁰` 的推导 (`elim`); 参照对是标准形时第 0 层不带 mc 的关系向下封闭 (`down⁰`).
> 否定 (局部数据不够): 核心证明里两步不能照搬到变体上: `m-add` 的前缀步 (`¬push-local`), 向下封闭步 `closeᴿ (app≤ν …)` (`¬close-local`: ψ₀(K+s) 与 s, t 都是标准形, t 可数, s ≤ t, ψ₀(K+t) 仍可以不是标准形).
> 不否定什么: 不说规范推导上出口条件不成立; 后继步改走不带 mc 的关系后不再要前缀步的标准形 (见 [YiXCEnd](YiXCEnd.lagda.md)).
> 来源: `inv-suc`, `sem→M⁰` 照 `YiKCSem`; 出口用 `YiHCRel.exitᴴ`, `YiKVRel.lower⁰`, `YiCFMono.mono≤ⁿ`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXCVar where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiRWBlock
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiKVRel as K
open K using (readRW; _⊴_; ⊴r; ⊴◃; ⊴-◃)
import OCF.Align.EboLeanDef as E
open E using (HC; h0; h1; hω; cof; c1; cω; pred; fsn; ψ; 𝟏; []<; hd<; tl<; lv<; ar<)
open import OCF.Align.EboLeanBase using (_≤ᵀ_; NF; NFP; n[]; n∷; nψ; Ctbl; c[]; c∷; HdLe; GB; GB[]; gp; gtl; gh; gw; gc;
  nf-hd; nfp-g; nf-Ω; <ᵀ-asym)
open import OCF.Align.EboLeanTree using (hc)
open import OCF.Align.Value using (_≼_; s≼s; ≼l; ≼-refl; ≼-trans)
import OCF.Align.Level as O
open import OCF.Lean.YiRefTw2 using (Rt)
open import OCF.Lean.YiCFMono using (mono≤ⁿ)
open import OCF.Align.Correspond using (cof-ne)
```

## 变体与一一对应

```agda
data Mᴺ : E.T → Tr zero → Set where
  nz : ∀ {x} → Mᴺ [] x
  n1 : ∀ {t x} → cof t ≡ c1 → Mᴺ (pred t) x → Mᴺ t (suc x)
  nL : ∀ {t x} → cof t ≡ cω → (∀ n → Mᴺ (fsn t n) x) → Mᴺ t x
  nw : ∀ {t x x′} → Mᴺ t x → zero ⊢ x ◃ x′ → Mᴺ t x′
  nc : ∀ {s t x} → NF s → NF t → Ctbl t → s ≤ᵀ t → Mᴺ t x → Mᴺ s x

toᴴ : ∀ {s x} → Mᴺ s x → H.M⁰ s x
toᴴ nz = H.mz
toᴴ (n1 e r) = H.m1 e (toᴴ r)
toᴴ (nL e h) = H.mL e (λ n → toᴴ (h n))
toᴴ (nw m d) = H.mw (toᴴ m) d
toᴴ (nc _ _ _ le m) = H.mc le (toᴴ m)

exᴺ : ∀ {s x} (m : Mᴺ s x) → H.Exᴴ (toᴴ m)
exᴺ nz = tt
exᴺ (n1 e r) = exᴺ r
exᴺ (nL e h) = λ n → exᴺ (h n)
exᴺ (nw m d) = exᴺ m
exᴺ (nc ns nt ct le m) = ns , nt , ct , exᴺ m

ofᴴ : ∀ {s x} (m : H.M⁰ s x) → H.Exᴴ m → Mᴺ s x
ofᴴ H.mz ex = nz
ofᴴ (H.m1 e r) ex = n1 e (ofᴴ r ex)
ofᴴ (H.mL e h) ex = nL e (λ n → ofᴴ (h n) (ex n))
ofᴴ (H.mΩ {p = ()} _ _ _) ex
ofᴴ (H.mU {c = ()} _ _) ex
ofᴴ (H.mw m d) ex = nw (ofᴴ m ex) d
ofᴴ (H.mc le m) (ns , nt , ct , ex) = nc ns nt ct le (ofᴴ m ex)

exitᴺ : ∀ {s x} → Mᴺ s x → (h : HC s) → Rt h ≼ readRW x
exitᴺ m = H.exitᴴ (toᴴ m) (exᴺ m)
```

## 消去 mc

mc 结点上 s 也可数 (`ctbl≤`), 于是 s 有 `HC`; 值由出口与 `mono≤ⁿ` 给出, 再由值造不带 mc 的推导.

```agda
ctbl-hd : ∀ {a xs} → NF xs → HdLe (ψ [] a) xs → Ctbl xs
ctbl-hd {xs = []} n h = c[]
ctbl-hd {xs = ψ u b ∷ xs} (n∷ p hl n) (inj₁ (lv< ()))
ctbl-hd {xs = ψ .[] b ∷ xs} (n∷ p hl n) (inj₁ (ar< _)) = c∷ (ctbl-hd n hl)
ctbl-hd {xs = .(ψ [] _) ∷ xs} (n∷ p hl n) (inj₂ refl) = c∷ (ctbl-hd n hl)

ctbl≤ : ∀ {s t} → NF s → Ctbl t → s ≤ᵀ t → Ctbl s
ctbl≤ ns ct (inj₂ refl) = ct
ctbl≤ ns ct (inj₁ []<) = c[]
ctbl≤ (n∷ p hl n) (c∷ ct) (inj₁ (hd< (lv< ())))
ctbl≤ (n∷ p hl n) (c∷ ct) (inj₁ (hd< (ar< _))) = c∷ (ctbl-hd n hl)
ctbl≤ (n∷ p hl n) (c∷ ct) (inj₁ (tl< q)) = c∷ (ctbl≤ n ct (inj₁ q))

inv-suc : (x : Tr zero) {a : O.Ordᶜ O.zero} → O.suc a ≼ readRW x → Σ (Tr zero) λ x′ → (suc x′ ⊴ x) × (a ≼ readRW x′)
inv-suc zero      ()
inv-suc (suc x)   (s≼s p) = x , ⊴r , p
inv-suc (lim f a) (≼l n p) with inv-suc (f n) p
... | x′ , le , q = x′ , ⊴◃ (⊴-◃ le (◃l n)) , q

sem→M⁰ : ∀ {t} (h : HC t) (x : Tr zero) → Rt h ≼ readRW x → K.M⁰ t x
sem→M⁰ {t = []}     (h0 e)    x q = K.mz
sem→M⁰ {t = y ∷ ys} (h0 e)    x q = ⊥-elim (cof-ne y ys e)
sem→M⁰              (h1 e hp) x q with inv-suc x q
... | x′ , le , q′ = K.G⁰.m⊴ (K.m1 e (sem→M⁰ hp x′ q′)) le
sem→M⁰              (hω e hs) x q = K.mL e (λ n → sem→M⁰ (hs n) x (≼-trans (≼l n (≼-refl (Rt (hs n)))) q))

down⁰ : ∀ {s t} {v : Tr zero} → NF s → NF t → Ctbl t → s ≤ᵀ t → K.M⁰ t v → K.M⁰ s v
down⁰ {v = v} ns nt ct le m = sem→M⁰ hs v (≼-trans (mono≤ⁿ ns nt ct hs (hc nt ct) le) (K.lower⁰ m (hc nt ct)))
  where hs = hc ns (ctbl≤ ns ct le)

elim : ∀ {s x} → Mᴺ s x → K.M⁰ s x
elim nz = K.mz
elim (n1 e r) = K.m1 e (elim r)
elim (nL e h) = K.mL e (λ n → elim (h n))
elim (nw m d) = K.mw (elim m) d
elim (nc ns nt ct le m) = down⁰ ns nt ct le (elim m)

elimᴴ : ∀ {s x} (m : H.M⁰ s x) → H.Exᴴ m → K.M⁰ s x
elimᴴ m ex = elim (ofᴴ m ex)
```

## 两条局部否定

`¬push-local`: 前缀 1 加在 ω 前面. `¬close-local`: K = 0, s = 0, t = ψ₀(Ω₁); G₀(t) 含 Ω₁ 而 Ω₁ 高于 t, 所以 ψ₀(t) 不是标准形.

```agda
ω₀ Ω₁ t₀ : E.T
ω₀ = ψ [] (𝟏 ∷ []) ∷ []
Ω₁ = ψ (𝟏 ∷ []) [] ∷ []
t₀ = ψ [] Ω₁ ∷ []

nf1 : NF (𝟏 ∷ [])
nf1 = n∷ (nψ n[] n[] GB[]) tt n[]

gb1 : GB [] (𝟏 ∷ []) (𝟏 ∷ [])
gb1 (gp (gh _)) = []<
gb1 (gp (gw _ ()))
gb1 (gp (gc _ ()))
gb1 (gtl ())

nfω : NF ω₀
nfω = n∷ (nψ n[] nf1 gb1) tt n[]

¬1ω : HdLe 𝟏 ω₀ → ⊥
¬1ω (inj₁ (lv< ()))
¬1ω (inj₁ (ar< ()))

¬push-local : (∀ {p s t} → NFP p → NF s → NF t → Ctbl t → s ≤ᵀ t → NF (p ∷ t)) → ⊥
¬push-local f with f {𝟏} {ω₀} {ω₀} (nψ n[] n[] GB[]) nfω nfω (c∷ c[]) (inj₂ refl)
... | n∷ _ hl _ = ¬1ω hl

gbΩ : GB [] Ω₁ Ω₁
gbΩ (gp (gh _)) = []<
gbΩ (gp (gw _ g)) with g
... | gp (gh _) = []<
... | gp (gw _ ())
... | gp (gc _ ())
... | gtl ()
gbΩ (gp (gc _ ()))
gbΩ (gtl ())

nft₀ : NF t₀
nft₀ = n∷ (nψ n[] (nf-Ω nf1) gbΩ) tt n[]

bad-ψ : NF (ψ [] t₀ ∷ []) → ⊥
bad-ψ n = <ᵀ-asym (nfp-g (nf-hd n) (gp (gh (inj₂ refl)))) (hd< (lv< []<))

¬close-local : (∀ {K s t} → NF (ψ [] (K ++ s) ∷ []) → NF s → NF t → Ctbl t → s ≤ᵀ t → NF (ψ [] (K ++ t) ∷ [])) → ⊥
¬close-local f = bad-ψ (f {[]} {[]} {t₀} nf1 n[] nft₀ (c∷ c[]) (inj₁ []<))
```
