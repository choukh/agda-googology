# 链的第一步: $u_1=\psi_1(\Omega_\Omega)$ 的读回与 `Lv₅` 同形 (模界), 无条件 (判决: HOLDS, 只到 $u_1$, 只是层号合法)

> 不含记号. 结论写在 [FeedGood](FeedGood.lagda.md).
>
> - `R-ψ`: $\Omega_1$ 上的折叠 (目标任意) 与 `Ordᶜ` 上的 `ψ p σ` 同形, 比较只读语义. 是 [GuardTightCert](GuardTightCert.lagda.md) 同名定理的 `Ordᶜ` 版.
> - `ψ≅ψ¹`: 目标 1 的 `ψ p σ` 与 [GuardTightUni](GuardTightUni.lagda.md) 的 `ψ¹` 互模拟.
> - `rb-rel`: 关系推出读回 $\approx$.
> - **`first≈`, `body≈`: `feedL u₀` 的第一支 $\approx$ `F 1`, 分支 $\eta$ $\approx$ `F η`. `Cf-u₁ : Cfˢ (feedL u₀)`, 无条件.** `feedL u₀` 与 `Lv₅` 只差界 (2 对 1), `no-≈₁` ([FeedGoodNeg](FeedGoodNeg.lagda.md)) 说这个差别是真的.
> - 这是**层号合法**, 不是 ψ₀ 输出的 `HS`/`Goodᴺ`: 下面没有任何关于 `T₀ (feedL u₀)` 的 `Goodᴺ`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.FeedGoodFirst where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.GuardTightCum hiding (ψ)
import OCF.Align.GuardTightCum as C
open Restr
open import OCF.Free.Aux using (Mlev; Fs)
open import OCF.Free.Prefix using (Z)
open import OCF.Align.GuardTightLv
open Lv Dom₀ hiding (zero; suc; lim)
open import OCF.Align.GuardTightBase
open import OCF.Align.GuardTightTree
open import OCF.Align.GuardTightCertRel using (⌜_⌝; ⌜≈⌝; cb-sem; cu-sem; clash; Emp; out-intoU; lk≈)
open import OCF.Align.FeedGoodRel
open import OCF.Align.GuardTightCert using (c₁; wf₁; sf₁; tc₁; Full; lower-full; full-ξ; full-body; full-chain; trim-emp; toTab-just; module NJM; Fr-c₁; Sf; sf)
import OCF.Align.GuardTightUni as Uni
private module U = Uni Dom₀
open U using (rb₀; rb₁; rb-≈₁₁; em; em-≅; ψ¹; F; F-≈; F-mono; WF-F; self-F; i-resp; s-inv; l-inv; u-inv; em-self)

open Fold c₁ wf₁ sf₁ tc₁
```

## §1 折叠与 `ψ p σ`

```agda
data Tgt {E : Ents} : ∀ {t} → Tg E t → Ordᴵ → Set where
  tg0 : Tgt t0 zero
  tgp : ∀ {t i} {q : t < c₁} {aq : Adm (tab E) q} → t ≈ ⌜ i ⌝ → Tgt (tp q aq) i

teq : ∀ {E t i} {T : Tg E t} → Tgt T i → t ≈ ⌜ i ⌝
teq tg0 = Lv.z≈
teq (tgp e) = e

rep-rel : ∀ {i A π} {y : O A π} {Y : Ordᶜ i} → Rs i y Y → ∀ n → Rs i (repᵒ y n) (iter (Y +_) zero n)
rep-rel r zero = rz
rep-rel r (suc m) = rwk (R-⊕ r (rep-rel r m))

R-ψ : ∀ {k₀ π ρ t i} (E : Ents) (T : Tg E t) (tg : Tgt T i) (st : St E ρ π) (full : Full st) {x : O c₁ π} {ŷ : Ordᶜ k₀} → Rs k₀ x ŷ →
      ∀ {ℓ} (σ : Simᴵ k₀ ℓ) (p : i <ᴵ ℓ) → Rs i (ψ E T st x) (C.ψ p σ ŷ)

module RiseM {k₀ π ρ t i k j} (E : Ents) (T : Tg E t) (tg : Tgt T i) (st : St E ρ π) (full : Full st)
             (r : k < c₁) (cv′ : Adm (cov π) r) (q : j <ᴵ k₀) {h : ∀ ξ → Us c₁ r ξ → O c₁ (ξ ∪ π)} {f : U j (<→◃ q) → Ordᶜ k₀}
             (dk : k ≈ ⌜ j ⌝)
             (prem : ∀ ξ → Emp ξ → (z : O k ξ) (ẑ : Ordᶜ j) → LRs k₀ (<→◃ q) z ẑ → Rs k₀ (h ξ (intoU r z)) (f (into (<→◃ q) ẑ)))
             {ℓ} (σ : Simᴵ k₀ ℓ) (p : i <ᴵ ℓ) where
  rise-rel : Rs i (riseΩ E T st r cv′ h) (lim (λ m → C.ψ p σ (f (into (<→◃ q) (iter (λ x → C.ψ q (λ r₁ → r₁) (f (into (<→◃ q) x))) (Ω j) m)))))
  rise-rel with Vis.toTab st r cv′ | toTab-just st full r cv′
  ... | just a | a , refl with nfT c₁ tc₁ r | trim π st {r} a | trim-emp π st {r} a full
  ...   | nft d r′ tb | mkTr ξ w bk | em′ = rl (λ n → R-ψ E T tg (stBody ξ w st) (full-body ξ w st full) (prem ξ em′ _ _ (intoR (<→◃ q) (ch n))) σ p)
    where
    ch : ∀ n → Rs j (chainᵒ (Tc-at r tc₁) (λ z → trL⁻ d (ψ E (tp r′ (tb E a)) (stChain ξ bk w st) (h ξ (intoU r z)))) n) (iter (λ x → C.ψ q (λ r₁ → r₁) (f (into (<→◃ q) x))) (Ω j) n)
    ch zero = rwk (RΩ̇ j dk (Tc-at r tc₁))
    ch (suc n) = R-trL⁻ d (R-ψ E (tp r′ (tb E a)) (tgp (lk≈ d dk)) (stChain ξ bk w st) (full-chain ξ bk w st full) (prem ξ em′ _ _ (intoR (<→◃ q) (ch n))) (λ r₁ → r₁) q)

R-ψ {t = t} {i = i} E T tg st full rz σ p = rwk (RΩ̇ i (teq tg) (tcT T))
R-ψ E T tg st full (rs r) σ p = rl (rep-rel (R-ψ E T tg st full r σ p))
R-ψ E T tg st full (rl h) σ p = rl (λ n → R-ψ E T tg st full (h n) σ p)
R-ψ E T tg st full (rwk {w = w} r) σ p = R-ψ E T tg (λ m → st (w m)) (λ m → full (w m)) r σ p
R-ψ E T tg st full (rcv {π = π′} {w = w} r) σ p with lowerSt π′ w st | lower-full π′ w st full
... | σ′ , st′ , c′ | h = rcv (R-ψ E T tg st′ h r σ p)
R-ψ E T tg st full (rmk r l x) σ p = R-ψ E T tg st full x σ p
R-ψ {k₀ = suc k′} E T tg st full (rup zero l) σ p = R-ψ E T tg st full l (λ q → σ (suc q)) p
R-ψ {k₀ = lim g s} E T tg st full (rup (self n) l) σ p = R-ψ E T tg st full l (λ q → σ (lim n q)) p
R-ψ E t0 tg0 st full (rΩ r cv′ q {h = h₁} {f = f} dk prem) σ p with <ᴵ-dec (σ q) p
... | injᵃ (via e ())
... | injᵇ _ = RiseM.rise-rel E t0 tg0 st full r cv′ q {h = h₁} {f = f} dk prem σ p
... | injᶜ _ = RiseM.rise-rel E t0 tg0 st full r cv′ q {h = h₁} {f = f} dk prem σ p
R-ψ {i = i} E (tp q₁ aq₁) (tgp et) st full (rΩ {k = k} {j = j} r cv′ q {h = h₁} {f = f} dk prem) σ p
  with Vis.cmpN st wf₁ sf₁ r q₁ cv′ aq₁ | NJM.cmpNJ st full wf₁ sf₁ Fr-c₁ r q₁ cv′ aq₁ | <ᴵ-dec (σ q) p
... | Vis.cb d s a | _ | injᵃ (via e r₂) =
  rΩ s a r₂ (≈-trans (≈-sym d) (≈-trans dk (⌜≈⌝ e)))
     (λ ξ em′ z ẑ l → subst₂ (λ u v → Rs i (ψ E (tp q₁ aq₁) (stξ ξ st) (h₁ ξ (intoU r (tr⁻O d u)))) (C.ψ p σ (f (into (<→◃ q) (tr⁻ e v)))))
                              (sym (out-intoU s z)) (sym (out-into (<→◃ r₂) ẑ))
                              (R-ψ E (tp q₁ aq₁) (tgp et) (stξ ξ st) (full-ξ ξ em′ st full)
                                   (prem ξ em′ _ _ (intoR (<→◃ q) (R-tr⁻ e (R-tr⁻O d (outR (<→◃ r₂) l))))) σ p))
... | Vis.cb d s a | _ | injᵇ w = ⊥-elim (clash (cb-sem et dk d s) (inj₁ w))
... | Vis.cb d s a | _ | injᶜ c′ = ⊥-elim (clash (cb-sem et dk d s) (inj₂ (≅ᴵ-sym c′)))
... | Vis.cu x | _ | injᵃ w = ⊥-elim (clash w (cu-sem et dk x))
... | Vis.cu x | _ | injᵇ _ = RiseM.rise-rel E (tp q₁ aq₁) (tgp et) st full r cv′ q {h = h₁} {f = f} dk prem σ p
... | Vis.cu x | _ | injᶜ _ = RiseM.rise-rel E (tp q₁ aq₁) (tgp et) st full r cv′ q {h = h₁} {f = f} dk prem σ p
```

## §2 目标 1 的 `ψ p σ` 就是 `ψ¹`

对 $\cong$ 的推导递归, 与 `ψ-≅` 同一个骨架. `<ᴵ-dec` 的答案只有与对面 $j'$ 一致的那一种: 其余的由 $\prec$ 的非自反排除.

```agda
private
  below1 : ∀ {j} → j ≺ᴵ suc zero → j ≅ᴵ zero
  below1 (via e zero) = e

  not0₁ : ∀ {j} → suc zero ≺ᴵ j → j ≅ᴵ zero → ⊥
  not0₁ (via e ()) z≅

  not0₂ : ∀ {j} → suc zero ≅ᴵ j → j ≅ᴵ zero → ⊥
  not0₂ () z≅

ψ≅ψ¹ : ∀ {k k′ ℓ} (p : suc zero <ᴵ ℓ) (σ : Simᴵ k ℓ) {a : Ordᶜ k} {b : Ordᶜ k′} → a ≅ b → C.ψ p σ a ≅ ψ¹ b
ψ≅ψ¹ p σ z≅ = Ω-≅ (s≅ z≅)
ψ≅ψ¹ p σ (s≅ e) = l≅ (iter-R _≅_ (λ e′ → add-≅ (ψ≅ψ¹ p σ e) e′) z≅)
ψ≅ψ¹ p σ (l≅ h) = l≅ (λ n → ψ≅ψ¹ p σ (h n))
ψ≅ψ¹ p σ (upˡ {r = zero} e) = ψ≅ψ¹ p (λ q → σ (suc q)) e
ψ≅ψ¹ p σ (upˡ {r = self n} e) = ψ≅ψ¹ p (λ q → σ (lim n q)) e
ψ≅ψ¹ p σ (upʳ {r = zero} e) = ψ≅ψ¹ p σ e
ψ≅ψ¹ p σ (upʳ {r = self n} e) = ψ≅ψ¹ p σ e
ψ≅ψ¹ p σ (lᵢ≅ {j = j} {j′ = j′} {p = q} {q = q′} {f = f} {g = g} e h) with <ᴵ-dec (σ q) p
ψ≅ψ¹ p σ (lᵢ≅ {j = j} {j′ = zero} {p = q} {q = q′} {f = f} {g = g} e h) | injᵃ (via e₁ r₁) with r₁ | e₁
... | zero | e₂ = lᵢ≅ z≅ λ x y d →
  subst (λ u → C.ψ p σ (f (into (<→◃ q) (tr⁻ e₂ u))) ≅ ψ¹ (g (into (<→◃ q′) y))) (sym (out-into zero x))
        (ψ≅ψ¹ p σ (h _ _ (≅→R (<→◃ q) (tr⁻-≅ e₂ (R→≅ zero d)))))
ψ≅ψ¹ p σ (lᵢ≅ {j = j} {j′ = suc a} {p = q} {q = q′} {f = f} {g = g} e h) | injᵃ w with below1 w
ψ≅ψ¹ p σ (lᵢ≅ {j = j} {j′ = suc a} e h) | injᵃ w | d with ≅ᴵ-trans (≅ᴵ-sym d) e
... | ()
ψ≅ψ¹ p σ (lᵢ≅ {j = j} {j′ = lim g′ s′} {p = q} {q = q′} {f = f} {g = g} e h) | injᵃ w with below1 w
ψ≅ψ¹ p σ (lᵢ≅ {j = j} {j′ = lim g′ s′} e h) | injᵃ w | d with ≅ᴵ-trans (≅ᴵ-sym d) e
... | ()
ψ≅ψ¹ p σ (lᵢ≅ {j = j} {j′ = zero} {p = q} {q = q′} e h) | injᵇ w = ⊥-elim (not0₁ w e)
ψ≅ψ¹ p σ (lᵢ≅ {j = j} {j′ = zero} {p = q} {q = q′} e h) | injᶜ c = ⊥-elim (not0₂ (≅ᴵ-sym c) e)
ψ≅ψ¹ p σ (lᵢ≅ {j = j} {j′ = suc a} {p = q} {q = q′} {f = f} {g = g} e h) | injᵇ _ = l≅ (λ n → ψ≅ψ¹ p σ (h _ _ (≅→R (<→◃ q) (chain n))))
  where chain = iter-R _≅_ (λ d → ψ-≅ e (h _ _ (≅→R (<→◃ q) d))) (Ω-≅ e)
ψ≅ψ¹ p σ (lᵢ≅ {j = j} {j′ = suc a} {p = q} {q = q′} {f = f} {g = g} e h) | injᶜ _ = l≅ (λ n → ψ≅ψ¹ p σ (h _ _ (≅→R (<→◃ q) (chain n))))
  where chain = iter-R _≅_ (λ d → ψ-≅ e (h _ _ (≅→R (<→◃ q) d))) (Ω-≅ e)
ψ≅ψ¹ p σ (lᵢ≅ {j = j} {j′ = lim g′ s′} {p = q} {q = q′} {f = f} {g = g} e h) | injᵇ _ = l≅ (λ n → ψ≅ψ¹ p σ (h _ _ (≅→R (<→◃ q) (chain n))))
  where chain = iter-R _≅_ (λ d → ψ-≅ e (h _ _ (≅→R (<→◃ q) d))) (Ω-≅ e)
ψ≅ψ¹ p σ (lᵢ≅ {j = j} {j′ = lim g′ s′} {p = q} {q = q′} {f = f} {g = g} e h) | injᶜ _ = l≅ (λ n → ψ≅ψ¹ p σ (h _ _ (≅→R (<→◃ q) (chain n))))
  where chain = iter-R _≅_ (λ d → ψ-≅ e (h _ _ (≅→R (<→◃ q) d))) (Ω-≅ e)
```

## §3 关系推出读回 $\approx$

```agda
open import OCF.Align.GuardTightUp using (rbO; emO; feedL; u₀; GL; gl; lvl; cfG; tcG; entG; pthG; admG)

R-em : ∀ a → Rs zero (emO a) (em a)
R-em zero = rz
R-em (suc a) = rs (R-em a)
R-em (lim f s) = rl (λ n → R-em (f n))

rb₀-rel : ∀ {π} {x : O (Lv.suc Lv.zero) π} {y : Ordᶜ zero} → Rs zero x y → rbO x ≈ rb₀ y
rb₀-rel rz = Lv.z≈
rb₀-rel (rs r) = Lv.s≈ (rb₀-rel r)
rb₀-rel (rl h) = Lv.l≈ (λ n → rb₀-rel (h n))
rb₀-rel (rwk {π = π′} {x = x} r) = rb₀-rel {π′} {x} r
rb₀-rel (rcv {π = π′} {x = x} r) = rb₀-rel {π′} {x} r
rb₀-rel (rmk () l r)
rb₀-rel (rup () l)
rb₀-rel (rΩ r cv () d h)

rb₁-rel : ∀ {π} {x : O (Lv.suc Lv.zero) π} {y : Ordᶜ (suc zero)} → Rs (suc zero) x y → y ≅ y → rbO x ≈ rb₁ y
rb₁-rel rz ey = Lv.z≈
rb₁-rel (rs r) ey = Lv.s≈ (rb₁-rel r (s-inv ey))
rb₁-rel (rl h) ey = Lv.l≈ (λ n → rb₁-rel (h n) (l-inv ey n))
rb₁-rel (rwk {π = π′} {x = x} r) ey = rb₁-rel {π′} {x} r ey
rb₁-rel (rcv {π = π′} {x = x} r) ey = rb₁-rel {π′} {x} r ey
rb₁-rel {π} (rmk {x = x} zero l r) ey = rb₁-rel {π} {x} r ey
rb₁-rel (rup zero l) ey = rb₀-rel l
rb₁-rel (rΩ Lv.zero cv zero {h = h′} {f = f} d h) ey =
  Lv.o≈ (s≅ z≅)
        (rb₁-rel (h Lv.tz (λ ()) (emO (suc zero)) (suc zero) (rs rz)) (i-resp ey (s≅ z≅)))
        (λ η e η′ e′ k → ≈-trans (rb₁-rel (h Lv.tz (λ ()) (emO η) (em η) (R-em η)) (i-resp ey (em-self η)))
                                 (rb-≈₁₁ (i-resp ey (em-≅ k))))
rb₁-rel (rΩ (Lv.suc ()) cv zero d h) ey
rb₁-rel (rΩ r cv (suc ()) d h) ey
```

## §4 层号的搬运

```agda
WF≈ : ∀ {a b} → a ≈ b → WFˢ a → WFˢ b
WF≈ Lv.z≈ w = tt
WF≈ (Lv.s≈ e) w = WF≈ e w
WF≈ (Lv.l≈ h) (st , w) =
  (λ n → ⊴-trans (≈→⊴ (≈-sym (h n))) (⊴-trans (st n) (≈→⊴ (h (suc n))))) , (λ n → WF≈ (h n) (w n))
WF≈ (Lv.o≈ {c} {c′} {t} {t′} {g} {g′} d e h) (tg , dir , wt , wg) =
  (λ η e′ → ⊴-trans (≈→⊴ (≈-sym e)) (⊴-trans (tg η (bk e′)) (≈→⊴ (at′ η e′)))) ,
  (λ η e′ η′ e″ k → ⊴-trans (≈→⊴ (≈-sym (at′ η e′))) (⊴-trans (dir η (bk e′) η′ (bk e″) k) (≈→⊴ (at′ η′ e″)))) ,
  WF≈ e wt ,
  (λ η e′ → WF≈ (at′ η e′) (wg η (bk e′)))
  where
  bk : ∀ {η} → c′ ⊑ᴵ η → c ⊑ᴵ η
  bk e′ = conv (≅ᴵ-sym d) e′
  at′ : ∀ η (e′ : c′ ⊑ᴵ η) → g η (bk e′) ≈ g′ η e′
  at′ η e′ = h η (bk e′) η e′ (≅ᴵ-refl η)

Cf≈ : ∀ {a b} → a ≈ b → Cfˢ a → Cfˢ b
Cf≈ e (w , _) = WF≈ e w , ≈-reflʳ e

-- 与 Fᵞ 同形 (模界) 的闭包是好层号
lc-good : ∀ {c t g} → (∀ η → c ⊑ᴵ η → suc zero ⊑ᴵ η) → t ≈ F (suc zero) → (∀ η e → g η e ≈ F η) → Cfˢ (Lv.lc c t g)
lc-good {c} gd t≈ g≈ =
  ((λ η e → ⊴-trans (≈→⊴ t≈) (⊴-trans (F-mono (gd η e)) (≈→⊴ (≈-sym (g≈ η e))))) ,
   (λ η e η′ e′ d → ⊴-trans (≈→⊴ (g≈ η e)) (⊴-trans (F-mono d) (≈→⊴ (≈-sym (g≈ η′ e′))))) ,
   WF≈ (≈-sym t≈) (WF-F (suc zero)) ,
   (λ η e → WF≈ (≈-sym (g≈ η e)) (WF-F η))) ,
  Lv.o≈ (≅ᴵ-refl c) (≈-trans t≈ (≈-sym t≈)) (λ η e η′ e′ k → ≈-trans (g≈ η e) (≈-trans (F-≈ k) (≈-sym (g≈ η′ e′))))
```

## §5 `feedL u₀`

```agda
-- 折叠一棵与 Ω η 同形的树, 目标 1: 读回就是 F η
body-rel : ∀ {π ρ} (E : Ents) {q : Lv.suc Lv.zero < c₁} {aq : Adm (tab E) q} (st : St E ρ π) (full : Full st) {x : O c₁ π} (η : Ordᴵ)
           {ℓ} (σ : Simᴵ η ℓ) (p : suc zero <ᴵ ℓ) → Rs η x (Ω η) → rbO (ψ E (tp q aq) st x) ≈ F η
body-rel E st full η σ p rel =
  ≈-trans (rb₁-rel (R-ψ E (tp _ _) (tgp (Lv.s≈ Lv.z≈)) st full rel σ p) (ψ-≅ (≅ᴵ-refl (suc zero)) (Ω-refl η)))
          (rb-≈₁₁ (ψ≅ψ¹ p σ (Ω-refl η)))

self≈ : ∀ a → ⌜ a ⌝ ≈ ⌜ a ⌝
self≈ a = ⌜≈⌝ (≅ᴵ-refl a)

rel₁ : Rs (suc zero) (Emb.ι c₁ tc₁ ⌜ suc zero ⌝ (Lv.fst Lv.self) (inj₂ refl) (Ω̇ ⌜ suc zero ⌝ (proj₁ (proj₂ tc₁)))) (Ω (suc zero))
rel₁ = EmbRᶜ.R-ι c₁ tc₁ (Lv.fst Lv.self) (inj₂ refl) (RΩ̇ (suc zero) (self≈ (suc zero)) (proj₁ (proj₂ tc₁)))

relη : ∀ η {e : suc zero ⊑ᴵ η} →
       Rs η (Emb.ι c₁ tc₁ ⌜ η ⌝ (Lv.bra η e Lv.self) (inj₂ refl) (Ω̇ ⌜ η ⌝ (proj₂ (proj₂ tc₁) η e))) (Ω η)
relη η {e} = EmbRᶜ.R-ι c₁ tc₁ (Lv.bra η e Lv.self) (inj₂ refl) (RΩ̇ η (self≈ η) (proj₂ (proj₂ tc₁) η e))

two : Ordᴵ
two = suc (suc zero)

Cf-u₁ : Cfˢ (feedL u₀)
Cf-u₁ = lc-good (λ η e → ⊑ᴵ-trans (s⊑ z≅ (suc zero)) e)
  (body-rel _ {q = pthG u₀} _ (λ { (Lv.ml ()) ; (Lv.mr ()) }) (suc zero) {ℓ = two} (λ q → suc q) zero rel₁)
  (λ η e → body-rel _ {q = pthG u₀} _ (λ { (Lv.ml ()) ; (Lv.mr (Lv.ml Lv.hr)) → sf ; (Lv.mr (Lv.mr ())) }) η
             {ℓ = Mlev two (suc η) (⊑-up e)} (λ q → lim 1 (suc q)) (lim 0 zero) (relη η))
```

**`feed≈`.** `feedL u₀` 的精确形状: 界 2, 第一支 `F 1`, 分支 `F η`. 与 `Lv₅` 只差界 (`no-≈₁`).

```agda
Lv₅² : LG
Lv₅² = Lv.lc two (F (suc zero)) (λ η e → F η)

feed≈ : feedL u₀ ≈ Lv₅²
feed≈ = Lv.o≈ (≅ᴵ-refl two)
  (body-rel _ {q = pthG u₀} _ (λ { (Lv.ml ()) ; (Lv.mr ()) }) (suc zero) {ℓ = two} (λ q → suc q) zero rel₁)
  (λ η e η′ e′ k → ≈-trans (body-rel _ {q = pthG u₀} _ (λ { (Lv.ml ()) ; (Lv.mr (Lv.ml Lv.hr)) → sf ; (Lv.mr (Lv.mr ())) }) η
                                      {ℓ = Mlev two (suc η) (⊑-up e)} (λ q → lim 1 (suc q)) (lim 0 zero) (relη η))
                           (F-≈ k))
```

## §6 第二项: 无条件的 `GL`

路径与表由 `feed≈` 搬来. **`tcU₁` 用恒等读法: 这棵树的界不紧, 见 [FeedGoodNeg](FeedGoodNeg.lagda.md) 的 `⊴-cross` 与验收. 所以 `T₁` 是闭项, 正确性没有保证.**

```agda
q₁ : Lv.suc Lv.zero < F (suc zero)
q₁ = Lv.fst (Lv.lim 1 (Lv.bra two (s⊑ z≅ (suc zero)) Lv.zero))

aq₁ : Adm (tab (∅ two)) q₁
aq₁ = (two , refl , zero) , tt

path-from : ∀ {x} → x ≈ F (suc zero) → Σ (Lv.suc Lv.zero < x) λ s → Adm (tab (∅ two)) s
path-from e with ≈-move (≈-sym e) q₁
... | viaᴸ (Lv.s≈ Lv.z≈) p t = p , t (tab (∅ two)) aq₁

first-of : ∀ {c t g c′ t′ g′} → Lv.lc c t g ≈ Lv.lc c′ t′ g′ → t ≈ t′
first-of (Lv.o≈ _ e _) = e

u₁ : GL
u₁ = gl (feedL u₀) Cf-u₁ (Tc-id _) (∅ two)
        (Lv.fst (proj₁ (path-from (first-of feed≈))))
        (proj₂ (path-from (first-of feed≈)))

-- ψ₀(Ω_{u₁}): 闭项, 无模块参数. 树上没有 Goodᴺ. 下面的判断说它的界不紧
T₁ : Z
T₁ = T₀ (lvl u₁) (cfG u₁) (tcG u₁)
```

## §7 改过的形状: 只沿链

`FeedChain`: 不要求对**一切** `GL` 输出是好层号 (`no-GoodFeed` 说这是假的), 只要求一条链. `FeedChain` 是**条件**, 没有证. 前两项无条件: `prefix₀`, `prefix₁`. `TΩ₂ᶜ` 对 $n$ 不分情况.

```agda
record FeedChain : Set where
  field
    us   : ℕ → GL
    us-0 : us 0 ≡ u₀
    us-s : ∀ n → lvl (us (suc n)) ≡ feedL (us n)
open FeedChain public

TΩ₂ᶜ : FeedChain → Z
TΩ₂ᶜ C = Z.lim (λ n → T₀ (lvl (us C n)) (cfG (us C n)) (tcG (us C n)))

prefix₀ : GL
prefix₀ = u₀

prefix₁ : lvl u₁ ≡ feedL prefix₀
prefix₁ = refl
```
