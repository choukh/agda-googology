> **机械克隆, 验收用.** 由 `LadderMonoRel` 经脚本复制, 只改导入 (规则同 `Survey/scripts/laddernf/mk_w.py`), 把证书搬到标签阶梯的世界. 见 [LadderMonoAccept](LadderMonoAccept.lagda.md).

# 跨高度单调 (一): 不碰顶层的跨塔互模拟

> 结论写在 [LadderMono](LadderMono.lagda.md). **`Dn m a b x y`: $x$ 在塔 $m$, $y$ 在塔 $m+1$, 两边的节点全在高度 $<m$, 一一对应.** 所以没有 `top` 对 `pD top`, 没有 `pψ` 对 `pΨ zero`, 也没有 `omk` 的不变量: 这个关系根本不含 `qΩ` 和 `omk` 两个构造子. 行与 [LadderNFRel](LadderNFRel.lagda.md) §5, §6 一一对应, 只把 $q$ 换成 `suc q`. 不读记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderMonoWRel where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Align.Level
open import OCF.Align.LadderNFWPrefix using (Z; Ord₊ˢ; Ordˢ; Ωˢ; toZ; intoˢ)
open import OCF.Align.LadderNFWAux using (tf)
open import OCF.Align.LadderNFWEq using (_≅ᶻ_; _≅ˢ_; Eq₊ˢ; z≅; s≅; l≅; lᵢ≅; upˡ; upʳ; ŝ≅; ĉ≅; ≅→Rˢ; Ωˢ-≅; toZ-≅; _≈ᴿ_; limR; sucR; limᵢR; ŝR; ĉR; cloR; wkR)
open import OCF.Align.LadderNFWFloor using (Flr; fz; fk; fb; _⊔_; Ev; Run; flo; cvFlo; toFlo; wk; limA; ∅ᴿ; _∼ᶠ_; fz∼; fk∼; fb∼; ⊔∼; ∼ᶠ-refl; bound; bound-≅; evF)
open import OCF.Align.LadderNFWFT using (Fl; asl; asr; swp; dupr2; <◃)
open import OCF.Align.LadderNFWBase using (clash; r∅)
open import OCF.Align.LadderNFWTree
open import OCF.Align.LadderNFWRel
open RestrQ
```

## §1 关系

```agda
module _ (m : ℕ) (a b : Ordᴵ) where
  data Dn : ∀ {φ χ ψ ρ} → Q m a φ χ → Q (suc m) b ψ ρ → Set where
    dz : ∀ {φ χ ψ ρ} → Dn {φ} {χ} {ψ} {ρ} q0 q0
    ds : ∀ {φ χ ψ ρ} {p : Q m a φ χ} {p′ : Q (suc m) b ψ ρ} → φ ∼ᶠ ψ → Sim∼ m χ ρ → Dn p p′ → Dn (qs p) (qs p′)
    dl : ∀ {φ χ ψ ρ} {F : ℕ → Q m a φ χ} {F′ : ℕ → Q (suc m) b ψ ρ} → (∀ n → Dn (F n) (F′ n)) → Dn (ql F) (ql F′)
    di : ∀ {φ χ ψ ρ j j′} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {ac′ : ∀ {L} → Ev L ψ → j′ <ᴵ L} {f : Ordˢ j → Q m a φ χ} {f′ : Ordˢ j′ → Q (suc m) b ψ ρ} →
         j ≅ᴵ j′ → (∀ x y → x ≅ˢ y → Dn (f x) (f′ y)) → Dn (qi ac f) (qi ac′ f′)
    dŝ : ∀ {φ χ ψ ρ c₁ c₂} {t : Q m a φ χ} {t′ : Q (suc m) b ψ ρ} {g : (η : Ordᴵ) → c₁ ⊑ᴵ η → Q m a φ χ} {g′ : (η : Ordᴵ) → c₂ ⊑ᴵ η → Q (suc m) b ψ ρ} →
         c₁ ≅ᴵ c₂ → Dn t t′ → (∀ η e η′ e′ → η ≅ᴵ η′ → Dn (g η e) (g′ η′ e′)) → Dn (qŝ c₁ t g) (qŝ c₂ t′ g′)
    dĉ : ∀ {φ χ ψ ρ c₁ c₂ z z′} {zg : (η : Ordᴵ) → c₁ ⊑ᴵ η → Z} {zg′ : (η : Ordᴵ) → c₂ ⊑ᴵ η → Z}
         {o₀ : Q m a φ χ} {o₀′ : Q (suc m) b ψ ρ} {o : (η : Ordᴵ) → c₁ ⊑ᴵ η → Q m a φ χ} {o′ : (η : Ordᴵ) → c₂ ⊑ᴵ η → Q (suc m) b ψ ρ} →
         c₁ ≅ᴵ c₂ → z ≅ᶻ z′ → (∀ η e η′ e′ → η ≅ᴵ η′ → zg η e ≅ᶻ zg′ η′ e′) → Dn o₀ o₀′ →
         (∀ η e η′ e′ → η ≅ᴵ η′ → Dn (o η e) (o′ η′ e′)) → Dn (qĉ c₁ z zg o₀ o) (qĉ c₂ z′ zg′ o₀′ o′)
    dclo : ∀ {φ χ ψ ρ} {t : Q m a (φ ⊔ fk zero) χ} {t′ : Q (suc m) b (ψ ⊔ fk zero) ρ} {g : (η : Ordᴵ) → Q m a (φ ⊔ fk η) χ} {g′ : (η : Ordᴵ) → Q (suc m) b (ψ ⊔ fk η) ρ} →
         φ ∼ᶠ ψ → Dn t t′ → (∀ η η′ → η ≅ᴵ η′ → Dn (g η) (g′ η′)) → Dn (qclo t g) (qclo t′ g′)
    dcl : ∀ {φ χ ψ ρ n κ₁ κ₂} {q : n <ᴸ m} {s : ∀ {ℓ} → Ev ℓ (χ n) → Ev ℓ (κ₁ ⊔ fk zero)} {s′ : ∀ {ℓ} → Ev ℓ (ρ n) → Ev ℓ (κ₂ ⊔ fk zero)}
         {t : Q m a φ χ} {t′ : Q (suc m) b ψ ρ} {g : (η : Ordᴵ) → Q m a φ (upd χ n (κ₁ ⊔ fk η))} {g′ : (η : Ordᴵ) → Q (suc m) b ψ (upd ρ n (κ₂ ⊔ fk η))} →
         κ₁ ∼ᶠ κ₂ → Dn t t′ → (∀ η η′ → η ≅ᴵ η′ → Dn (g η) (g′ η′)) → Dn (qcl q κ₁ s t g) (qcl (suc q) κ₂ s′ t′ g′)
    dwkˡ : ∀ {φ φ′ χ χ′ ψ ρ} {le : ∀ {L} → Ev L φ′ → Ev L φ} {lc : Sub m χ′ χ} {x : Q m a φ χ} {x′ : Q (suc m) b ψ ρ} → Dn x x′ → Dn (qwk le lc x) x′
    dwkʳ : ∀ {φ χ ψ ψ′ ρ ρ′} {le′ : ∀ {L} → Ev L ψ′ → Ev L ψ} {lc′ : Sub (suc m) ρ′ ρ} {x : Q m a φ χ} {x′ : Q (suc m) b ψ ρ} → Dn x x′ → Dn x (qwk le′ lc′ x′)
    dΩ↓ : ∀ {φ χ ψ ρ n k k′} {q : n <ᴸ m} {fe : ∀ {L} → Ev L φ → Ev L Fl} {fe′ : ∀ {L} → Ev L ψ → Ev L Fl} {ac : ∀ {L} → Ev L (χ n) → k <ᴵ L} {ac′ : ∀ {L} → Ev L (ρ n) → k′ <ᴵ L}
          {h : ∀ ξ ζ → Vs m q k ξ ζ → Q m a (ξ ⊔ φ) (lo n ζ ∪ χ)} {h′ : ∀ ξ ζ → Vs (suc m) (suc q) k′ ξ ζ → Q (suc m) b (ξ ⊔ ψ) (lo n ζ ∪ ρ)} → k ≅ᴵ k′ → φ ∼ᶠ ψ → Sim∼ m χ ρ →
          (∀ ξ ξ′ ζ ζ′ → ξ ∼ᶠ ξ′ → Sim∼ n ζ ζ′ → (z : Q n k ξ ζ) (z′ : Q n k′ ξ′ ζ′) → Rq n k k′ z z′ → Dn (h ξ ζ (intoV q z)) (h′ ξ′ ζ′ (intoV q z′))) → Dn (qΩ↓ q fe ac h) (qΩ↓ (suc q) fe′ ac′ h′)
```

## §2 目标在高度 $H<m$

右边的 `Ψ` 走的路与左边相同: `tri n H` 字面相同, 三个分支一一对应. 输出在同一个 `Q H t` 里, 所以结论是普通的 `Rq`.

```agda
D-Ψ : ∀ {H m a b t t′ φ χ ψ ρ w w′} (qH : H <ᴸ m) (ok : Ok w) (e : Eh H m w χ) (p : t <ᴵ w H) (ok′ : Ok w′) (e′ : Eh H (suc m) w′ ρ) (p′ : t′ <ᴵ w′ H) → t ≅ᴵ t′ → {x : Q m a φ χ} {x′ : Q (suc m) b ψ ρ} → Dn m a b x x′ → Rq H t t′ (Ψ qH ok e p x) (Ψ (suc qH) ok′ e′ p′ x′)
chD : ∀ {m a b n k k′ φ χ ψ ρ ξ ξ′ w w′} (q : n <ᴸ m) (ok : Ok w) (e* : Eh n m w (lo n (Z* χ) ∪ χ)) (p₁ : k <ᴵ w n) (ok′ : Ok w′) (e′* : Eh n (suc m) w′ (lo n (Z* ρ) ∪ ρ)) (p₂ : k′ <ᴵ w′ n)
       {fe : ∀ {L} → Ev L ξ → Ev L Fl} {fe′ : ∀ {L} → Ev L ξ′ → Ev L Fl} {a₁ : ∀ {L} → Ev L ξ → Ev L (Fl ⊔ (ξ ⊔ φ))} {a₂ : ∀ {L} → Ev L ξ′ → Ev L (Fl ⊔ (ξ′ ⊔ ψ))}
       {h : ∀ ξ ζ → Vs m q k ξ ζ → Q m a (ξ ⊔ φ) (lo n ζ ∪ χ)} {h′ : ∀ ξ ζ → Vs (suc m) (suc q) k′ ξ ζ → Q (suc m) b (ξ ⊔ ψ) (lo n ζ ∪ ρ)} → k ≅ᴵ k′ → ξ ∼ᶠ ξ′ → Sim∼ m χ ρ →
       (∀ ξ ξ′ ζ ζ′ → ξ ∼ᶠ ξ′ → Sim∼ n ζ ζ′ → (z : Q n k ξ ζ) (z′ : Q n k′ ξ′ ζ′) → Rq n k k′ z z′ → Dn m a b (h ξ ζ (intoV q z)) (h′ ξ′ ζ′ (intoV q z′))) →
       ∀ i → Rq n k k′ (chainᵠ fe fc* (λ z → qwk a₁ (⇑ (cv* n)) (Ψ q ok e* p₁ (h ξ (Z* χ) (intoV q z)))) i) (chainᵠ fe′ fc* (λ z → qwk a₂ (⇑ (cv* n)) (Ψ (suc q) ok′ e′* p₂ (h′ ξ′ (Z* ρ) (intoV q z)))) i)

D-Ψ {H} qH ok e p ok′ e′ p′ et dz = rwk (RΩ̇ H et)
D-Ψ qH ok e p ok′ e′ p′ et (ds sa sb r) = rl (R-repᵠ (⊔∼ (∼ᶠ-refl Fl) sa) (Z∼ (λ i q → sb i (tr< q qH))) (D-Ψ qH ok e p ok′ e′ p′ et r))
D-Ψ qH ok e p ok′ e′ p′ et (dl h) = rl (λ n → D-Ψ qH ok e p ok′ e′ p′ et (h n))
D-Ψ qH ok e p ok′ e′ p′ et (di d h) = ri d (λ x y dd → D-Ψ qH ok e p ok′ e′ p′ et (h x y dd))
D-Ψ qH ok e p ok′ e′ p′ et (dŝ d r h) = rŝ d (D-Ψ qH ok e p ok′ e′ p′ et r) (λ η ee η′ e₁ dd → D-Ψ qH ok e p ok′ e′ p′ et (h η ee η′ e₁ dd))
D-Ψ qH ok e p ok′ e′ p′ et (dĉ d dz′ dg r h) = rĉ d dz′ dg (D-Ψ qH ok e p ok′ e′ p′ et r) (λ η ee η′ e₁ dd → D-Ψ qH ok e p ok′ e′ p′ et (h η ee η′ e₁ dd))
D-Ψ qH ok e p ok′ e′ p′ et (dclo s r h) = rwk (rclo (⊔∼ (∼ᶠ-refl Fl) s) (rwk (D-Ψ qH ok e p ok′ e′ p′ et r)) (λ η η′ d → rwk (D-Ψ qH ok e p ok′ e′ p′ et (h η η′ d))))
D-Ψ qH ok e p ok′ e′ p′ et (dwkˡ {lc = lc} r) = rwkˡ (D-Ψ qH ok (λ i h r₁ → lc i r₁ (e i h r₁)) p ok′ e′ p′ et r)
D-Ψ qH ok e p ok′ e′ p′ et (dwkʳ {lc′ = lc′} r) = rwkʳ (D-Ψ qH ok e p ok′ (λ i h r₁ → lc′ i r₁ (e′ i h r₁)) p′ et r)
D-Ψ {H} qH ok e p ok′ e′ p′ et (dcl {n = n} s r h) with tri n H
... | tlt l = rcl {q = l} {q′ = l} same (⊔∼ (∼ᶠ-refl Fl) s) (D-Ψ qH ok e p ok′ e′ p′ et r) (λ η η′ d → rwk (D-Ψ qH ok _ p ok′ _ p′ et (h η η′ d)))
... | teq refl = rŝ (bound-≅ (⊔∼ s (fk∼ z≅)) _ p _ p′ et) (D-Ψ qH ok e p ok′ e′ p′ et r) (λ η d η′ d′ eη → rwk (D-Ψ qH _ _ _ _ _ _ et (h η η′ eη)))
... | tgt l = rŝ (bound-≅ (⊔∼ s (fk∼ z≅)) _ (zr ok n) _ (zr ok′ n) z≅) (D-Ψ qH ok e p ok′ e′ p′ et r) (λ η d η′ d′ eη → rwk (D-Ψ qH _ _ _ _ _ _ et (h η η′ eη)))
D-Ψ {H} {t = t} {t′} qH ok e p ok′ e′ p′ et (dΩ↓ {φ = φ} {χ} {ψ} {ρ} {n} {k = k} {k′} {q} {ac = ac} {ac′ = ac′} {h} {h′} ek s c f) with tri n H
... | tlt l = rΩ↓ {q = l} {q′ = l} same ek (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ (λ i r → c i (tr< r qH)))
      (λ ξ ξ′ ζ ζ′ d dc dc′ z z′ lz → rwk (subst₂ (λ u v → Rq H t t′ (Ψ qH ok (e-lo ζ (inj₂ l) e) p (h ξ ζ (intoV q u))) (Ψ (suc qH) ok′ (e-lo ζ′ (inj₂ l) e′) p′ (h′ ξ′ ζ′ (intoV q v)))) (sym (out-intoV l z)) (sym (out-intoV l z′))
         (D-Ψ qH ok (e-lo ζ (inj₂ l) e) p ok′ (e-lo ζ′ (inj₂ l) e′) p′ et (f ξ ξ′ ζ ζ′ d dc z z′ (outVq l lz)))))
... | teq refl with <ᴵ-dec (ac (e n (inj₁ refl) q)) p | <ᴵ-dec (ac′ (e′ n (inj₁ refl) (suc q))) p′
...   | injᵃ (via d₁ s₁) | injᵃ (via d₂ s₂) =
  rΩ {r = s₁} {r′ = s₂} (≅ᴵ-trans (≅ᴵ-sym d₁) (≅ᴵ-trans ek d₂)) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ (λ i r → c i (tr< r qH)))
     (λ ξ ξ′ ζ ζ′ d dc z z′ l → rwk (subst₂ (λ u v → Rq H t t′ (Ψ qH ok (e-lo ζ (inj₁ refl) e) p (h ξ ζ (intoV q (tr⁻Q d₁ u)))) (Ψ (suc qH) ok′ (e-lo ζ′ (inj₁ refl) e′) p′ (h′ ξ′ ζ′ (intoV q (tr⁻Q d₂ v))))) (sym (out-intoU (<→◃ s₁) z)) (sym (out-intoU (<→◃ s₂) z′))
        (D-Ψ qH ok (e-lo ζ (inj₁ refl) e) p ok′ (e-lo ζ′ (inj₁ refl) e′) p′ et (f ξ ξ′ ζ ζ′ d dc _ _ (R-tr⁻ˡ d₁ (R-tr⁻ʳ d₂ (outRq (<→◃ s₁) l)))))))
...   | injᵃ a | injᵇ b = ⊥-elim (clash a (inj₁ (≺ᴵ-respʳ (≺ᴵ-respˡ et b) (≅ᴵ-sym ek))))
...   | injᵃ a | injᶜ c₁ = ⊥-elim (clash a (inj₂ (≅ᴵ-trans et (≅ᴵ-trans (≅ᴵ-sym c₁) (≅ᴵ-sym ek)))))
...   | injᵇ b | injᵃ a = ⊥-elim (clash a (inj₁ (≺ᴵ-respʳ (≺ᴵ-respˡ (≅ᴵ-sym et) b) ek)))
...   | injᶜ c₁ | injᵃ a = ⊥-elim (clash a (inj₂ (≅ᴵ-trans (≅ᴵ-sym et) (≅ᴵ-trans (≅ᴵ-sym c₁) ek))))
...   | injᵇ _ | injᵇ _ = rl (λ i → rwk (D-Ψ qH ok (e⁺ H ok e) p ok′ (e⁺ H ok′ e′) p′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (Z* χ) (Z* ρ) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ (λ j r → c j (tr< r q))) _ _ (chD q ok (e⁺ n ok e) (ac (e n (inj₁ refl) q)) ok′ (e⁺ n ok′ e′) (ac′ (e′ n (inj₁ refl) (suc q))) {fe = proj₁} {fe′ = proj₁} {a₁ = dupr2} {a₂ = dupr2} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) c f i))))
...   | injᵇ _ | injᶜ _ = rl (λ i → rwk (D-Ψ qH ok (e⁺ H ok e) p ok′ (e⁺ H ok′ e′) p′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (Z* χ) (Z* ρ) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ (λ j r → c j (tr< r q))) _ _ (chD q ok (e⁺ n ok e) (ac (e n (inj₁ refl) q)) ok′ (e⁺ n ok′ e′) (ac′ (e′ n (inj₁ refl) (suc q))) {fe = proj₁} {fe′ = proj₁} {a₁ = dupr2} {a₂ = dupr2} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) c f i))))
...   | injᶜ _ | injᵇ _ = rl (λ i → rwk (D-Ψ qH ok (e⁺ H ok e) p ok′ (e⁺ H ok′ e′) p′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (Z* χ) (Z* ρ) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ (λ j r → c j (tr< r q))) _ _ (chD q ok (e⁺ n ok e) (ac (e n (inj₁ refl) q)) ok′ (e⁺ n ok′ e′) (ac′ (e′ n (inj₁ refl) (suc q))) {fe = proj₁} {fe′ = proj₁} {a₁ = dupr2} {a₂ = dupr2} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) c f i))))
...   | injᶜ _ | injᶜ _ = rl (λ i → rwk (D-Ψ qH ok (e⁺ H ok e) p ok′ (e⁺ H ok′ e′) p′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (Z* χ) (Z* ρ) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ (λ j r → c j (tr< r q))) _ _ (chD q ok (e⁺ n ok e) (ac (e n (inj₁ refl) q)) ok′ (e⁺ n ok′ e′) (ac′ (e′ n (inj₁ refl) (suc q))) {fe = proj₁} {fe′ = proj₁} {a₁ = dupr2} {a₂ = dupr2} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) c f i))))
D-Ψ {H} {t = t} {t′} qH ok e p ok′ e′ p′ et (dΩ↓ {φ = φ} {χ} {ψ} {ρ} {n} {k = k} {k′} {q} {ac = ac} {ac′ = ac′} {h} {h′} ek s c f) | tgt l =
  rl (λ i → rwk (D-Ψ qH ok (e⁺ n ok e) p ok′ (e⁺ n ok′ e′) p′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (Z* χ) (Z* ρ) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ (λ j r → c j (tr< r q))) _ _ (chD q ok (e⁺ n ok (e↑ l e)) (ac ((e↑ l e) n (inj₁ refl) q)) ok′ (e⁺ n ok′ (e↑ l e′)) (ac′ ((e↑ l e′) n (inj₁ refl) (suc q))) {fe = proj₁} {fe′ = proj₁} {a₁ = dupr2} {a₂ = dupr2} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) c f i))))

chD {n = n} q ok e* p₁ ok′ e′* p₂ ek sξ c f zero = rwk (RΩ̇ n ek)
chD {χ = χ} {ρ = ρ} {ξ = ξ} {ξ′} q ok e* p₁ ok′ e′* p₂ {fe = fe} {fe′} {a₁} {a₂} {h} {h′} ek sξ c f (suc i) =
  rwk (D-Ψ q ok e* p₁ ok′ e′* p₂ ek (f ξ ξ′ (Z* χ) (Z* ρ) sξ (Z∼ (λ j r → c j (tr< r q))) _ _ (chD q ok e* p₁ ok′ e′* p₂ {fe = fe} {fe′ = fe′} {a₁ = a₁} {a₂ = a₂} {h = h} {h′ = h′} ek sξ c f i)))
```

## §3 求值

```agda
D→≈ᵠ : ∀ {m a b φ χ ψ ρ w w′} {x : Q m a φ χ} {x′ : Q (suc m) b ψ ρ} → Dn m a b x x′ → (ok : Ok w) (e : Eh zero m w χ) (ok′ : Ok w′) (e′ : Eh zero (suc m) w′ ρ) → ψ̄ᵠ ok e x ≈ᴿ ψ̄ᵠ ok′ e′ x′
D→≈ᵠ dz ok e ok′ e′ = wkR _ _ r∅
D→≈ᵠ (ds s c r) ok e ok′ e′ = sucR (D→≈ᵠ r ok e ok′ e′)
D→≈ᵠ (dl h) ok e ok′ e′ = limR (λ n → D→≈ᵠ (h n) ok e ok′ e′)
D→≈ᵠ (di {ac = ac} {ac′ = ac′} {f = f} {f′ = f′} d h) ok e ok′ e′ = limᵢR {ac = ac} {ac′ = ac′} {H = λ x → ψ̄ᵠ ok e (f x)} {H′ = λ x → ψ̄ᵠ ok′ e′ (f′ x)} d (λ x y dd → D→≈ᵠ (h x y dd) ok e ok′ e′)
D→≈ᵠ (dŝ d r h) ok e ok′ e′ = ŝR d (D→≈ᵠ r ok e ok′ e′) (λ η ee η′ e₁ dd → D→≈ᵠ (h η ee η′ e₁ dd) ok e ok′ e′)
D→≈ᵠ (dĉ d dz′ dg r h) ok e ok′ e′ = ĉR d dz′ dg (D→≈ᵠ r ok e ok′ e′) (λ η ee η′ e₁ dd → D→≈ᵠ (h η ee η′ e₁ dd) ok e ok′ e′)
D→≈ᵠ (dclo {t = t} {t′} {g} {g′} s r h) ok e ok′ e′ = cloR {t = ψ̄ᵠ ok e t} {g = λ η → ψ̄ᵠ ok e (g η)} {t′ = ψ̄ᵠ ok′ e′ t′} {g′ = λ η → ψ̄ᵠ ok′ e′ (g′ η)} s (D→≈ᵠ r ok e ok′ e′) (λ η η′ d → D→≈ᵠ (h η η′ d) ok e ok′ e′)
D→≈ᵠ {χ = χ} {ρ = ρ} {w = w} {w′ = w′} (dcl {n = n} {κ₁ = κ₁} {κ₂ = κ₂} {q = q} {s = s₁} {s′ = s₂} s r h) ok e ok′ e′ =
  ŝR (bound-≅ (⊔∼ s (fk∼ z≅)) _ (zr ok n) _ (zr ok′ n) z≅) (D→≈ᵠ r ok e ok′ e′)
      (λ η d η′ d′ eη → D→≈ᵠ (h η η′ eη)
         (upd-ok n w ok (tt , λ x → lim 0 (proj₂ (evF B₁) x))) (λ i k r₁ → upd-ev n i w χ (evη κ₁ B₁ η d) (e i k r₁))
         (upd-ok n w′ ok′ (tt , λ x → lim 0 (proj₂ (evF B₂) x))) (λ i k r₁ → upd-ev n i w′ ρ (evη κ₂ B₂ η′ d′) (e′ i k r₁)))
  where
  B₁ = bound (κ₁ ⊔ fk zero) (s₁ (e n (Hi-0 n) q)) (zr ok n)
  B₂ = bound (κ₂ ⊔ fk zero) (s₂ (e′ n (Hi-0 n) (suc q))) (zr ok′ n)
D→≈ᵠ (dwkˡ {le = le} {lc = lc} r) ok e ok′ e′ = wkR le (λ v → v) (D→≈ᵠ r ok (λ i h r₁ → lc i r₁ (e i h r₁)) ok′ e′)
D→≈ᵠ (dwkʳ {le′ = le′} {lc′ = lc′} r) ok e ok′ e′ = wkR (λ v → v) le′ (D→≈ᵠ r ok e ok′ (λ i h r₁ → lc′ i r₁ (e′ i h r₁)))
D→≈ᵠ (dΩ↓ {φ = φ} {χ} {ψ} {ρ} {n} {q = q} {fe = fe} {fe′} {ac} {ac′} {h} {h′} ek s c f) ok e ok′ e′ =
  limR (λ i → wkR _ _ (D→≈ᵠ (f φ ψ (Z* χ) (Z* ρ) s (Z∼ (λ j r → c j (tr< r q))) _ _ (chD q ok (e⁺ n ok (e↓ e)) (ac (e↓ e n (inj₁ refl) q)) ok′ (e⁺ n ok′ (e↓ e′)) (ac′ (e↓ e′ n (inj₁ refl) (suc q))) {fe = fe} {fe′ = fe′} {a₁ = λ v → fe v , (v , v)} {a₂ = λ v → fe′ v , (v , v)} {h = h} {h′ = h′} ek s c f i)) ok (e⁺ n ok e) ok′ (e⁺ n ok′ e′)))
```
