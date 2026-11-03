# 新树没有证书: $\psi_0(\Omega_{\Omega\cdot2+1})$ 处的同层界 (否定)

> 底座 [LvCertRel](LvCertRel.lagda.md). 不含记号. 结论写在 [LvCert](LvCert.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvCertNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
import OCF.Align.Level as Level
open import OCF.Align.Prefix using (Z; ĉᴸ; Ord₊ˢ; Ordˢ; toZ; Ωˢ)
open import OCF.Align.NotFree using (Goodᴺ; gz; gs; gl; gc; forceᴺ; forceᴺ-HS; forceᴺ-≅)
open import OCF.Align.UniformNF3NBase using (Goodᴺ-tr)
open import OCF.Align.UniformNF3Eq using (≅ᴵ→⊑ᴵ; ⊑ᴵ-≅ʳ; ⊑ᴵ-≅ˡ; _≅ᶻ_; ≅ᶻ-sym; _≅ˢ_; z≅; s≅; l≅; toZ-≅)
open import OCF.Align.Uniform3Base using (Flr; fz; fk; fb; _⊔_; Ev; Top; Bd; sb; nz; bound; accT; top₀; sup₁-up; sup₁-K; sup-up; mapTop; Fc; evF; FM; ∼ᶠ-refl; fz∼)
open import OCF.Align.UniformLvBase renaming (_⊑_ to _⊑ᴸ_)
open import OCF.Align.UniformLvTree hiding (T)
open import OCF.Align.LvCertRel
```

## §1 从 `Goodᴺ` 反演

```agda
lvG : ∀ {x : Z} → Goodᴺ x → Ordᴵ
lvG G = toLevel (forceᴺ _ G) (forceᴺ-HS _ G)

≤lv : ∀ {x y} (G : Goodᴺ x) (G′ : Goodᴺ y) → forceᴺ _ G ⊑ forceᴺ _ G′ → lvG G ⊑ᴵ lvG G′
≤lv G G′ h = toLevel-⊑ (forceᴺ-HS _ G) (forceᴺ-HS _ G′) h

≅lv : ∀ {x y} → x ≅ᶻ y → (G : Goodᴺ x) (G′ : Goodᴺ y) → lvG G ≅ᴵ lvG G′
≅lv d G G′ = toLevel-≅ (forceᴺ-HS _ G) (forceᴺ-HS _ G′) (forceᴺ-≅ d G G′)

gl-at : ∀ {f : ℕ → Z} (n : ℕ) (G : Goodᴺ (Z.lim f)) → Σ (Goodᴺ (f n)) λ G′ → forceᴺ _ G′ ⊑ forceᴺ _ G
gl-at n (gl G st) = G n , ⊑-lim n (λ h → h)

-- 闭包: 输出的第 0 点不高于整棵; 链的第 0 点不低于界. 两者是不同的证书, 因为 `Goodᴺ` 不要 `t₀` 的自相关
gc-o : ∀ {c t₀ o₀} {g o : (η : Ordᴵ) → c ⊑ᴵ η → Z} (G : Goodᴺ (ĉᴸ c t₀ g o₀ o)) → Σ (Goodᴺ o₀) λ G′ → forceᴺ _ G′ ⊑ forceᴺ _ G
gc-o (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) = Go₀ , ⊑-lim 0 (λ h → h)

gc-t : ∀ {c t₀ o₀} {g o : (η : Ordᴵ) → c ⊑ᴵ η → Z} (G : Goodᴺ (ĉᴸ c t₀ g o₀ o)) → Σ (Goodᴺ t₀) λ G′ → c ⊑ᴵ lvG G′
gc-t (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) = G₀ , ⊑ᴵ-trans (dy 0) (≅ᴵ→⊑ᴵ (toLevel-≅ (hy 0) (forceᴺ-HS _ G₀) (≅-sym l₀)))

-- 闭包: 第 0 个分支 (在第 0 个链点的层号处)
gc-br : ∀ {c t₀ o₀} {g o : (η : Ordᴵ) → c ⊑ᴵ η → Z} (G : Goodᴺ (ĉᴸ c t₀ g o₀ o)) →
        Σ (Goodᴺ t₀) λ G₀ → Σ Ordᴵ λ τ → Σ (c ⊑ᴵ τ) λ e → (τ ≅ᴵ lvG G₀) × Goodᴺ (o τ e)
gc-br (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) =
  G₀ , toLevel (ys 0) (hy 0) , dy 0 , toLevel-≅ (hy 0) (forceᴺ-HS _ G₀) (≅-sym l₀) , Go 0

-- `limᵢ` 在目标 0 与节点 0 上: 比较只有 ≅ 一种可能
gi-at : ∀ {φ w} {ac : ∀ {w} → Evt w φ → zero <ᴵ w 0} {h : Ordˢ zero → Runᵗ φ} {ok : Wok w} {ev : Evt w φ} {p : zero <ᴵ w 0}
        (G : Goodᴺ (toZ (limᵢᵗ ac h ok ev p))) → Σ (Goodᴺ (toZ (h (Ωˢ zero) ok ev p))) λ G′ → forceᴺ _ G′ ⊑ forceᴺ _ G
gi-at {ac = ac} {ev = ev} {p = p} G with <ᴵ-dec (ac ev) p
... | injᵃ (via e ())
... | injᵇ _ = gl-at 0 G
... | injᶜ _ = gl-at 0 G
```

## §2 界里有地板

```agda
data Kin (K : Ordᴵ) : Flr → Set where
  kz : Kin K (fk K)
  kl : ∀ {a b} → Kin K a → Kin K (a ⊔ b)
  kr : ∀ {a b} → Kin K b → Kin K (a ⊔ b)

acc-up : ∀ {i ℓ φ₁} (t : Top i ℓ φ₁) (φ : Flr) (ev : Ev ℓ φ) → Bd t ⊑ᴵ Bd (accT t φ ev)
acc-up t fz ev = ⊑ᴵ-refl
acc-up t (fk K) ev = sup₁-up (Bd t) K (sb t) ev
acc-up t (fb K) ev = OCF.Align.Uniform3Base.sup-up (Bd t) K (sb t) ev
acc-up t (a ⊔ b) (x , y) = ⊑ᴵ-trans (acc-up t a x) (acc-up (accT t a x) b y)

acc-K : ∀ {K i ℓ φ₁} (t : Top i ℓ φ₁) {φ : Flr} → Kin K φ → (ev : Ev ℓ φ) → suc K ⊑ᴵ Bd (accT t φ ev)
acc-K t kz ev = sup₁-K (Bd t) _ (sb t) ev
acc-K t (kl k) (x , y) = ⊑ᴵ-trans (acc-K t k x) (acc-up (accT t _ x) _ y)
acc-K t (kr k) (x , y) = acc-K (accT t _ x) k y

Bd-in : ∀ {K i ℓ} {φ : Flr} → Kin K φ → (ev : Ev ℓ φ) (p : i <ᴵ ℓ) → suc K ⊑ᴵ Bd (bound φ ev p)
Bd-in k ev p = acc-K (top₀ p) k ev
```

## §3 带字面路径的嵌入

`Emb a σ`: 把第 $a$ 层嵌入第 $D=\Omega\cdot2$ 层, 地板加 $\sigma$. 它是 `ι` 的复合的通用形, 对路径抽象, 所以 `ιG` 在树的构造子上可算, 不要知道栈的形状.

```agda
D : LI
D = Ω· 2

c₀ : LI
c₀ = suc D

cfD : Cf c₀
cfD = WFΩ 2 , s≈ (selfΩ 2)

record Emb (a : LI) (σ : Fᵗ) : Set where
  constructor emb
  field
    pS : ∀ {k} → k <ᴸ a → k <ᴸ D
    aS : ∀ {k} (r : k <ᴸ a) {w} → Evt w σ → Adm w r → Adm w (pS r)
open Emb public

ιG : ∀ {a σ π} → Emb a σ → O a π → O D (π ∪ σ)
ιG E o0 = o0
ιG E (os a) = os (ιG E a)
ιG E (ol F) = ol (λ n → ιG E (F n))
ιG E (oi ac f) = oi (λ e → ac (proj₁ e)) (λ x → ιG E (f x))
ιG E (oŝ c₀ t g) = oŝ c₀ (ιG E t) (λ η e → ιG E (g η e))
ιG E (oĉ c₀ z zg o₁ o) = oĉ c₀ z zg (ιG E o₁) (λ η e → ιG E (o η e))
ιG E (ocl h t g) = ocl h (ιG E t) (λ η → owk sw₃ (ιG E (g η)))
ιG E (owk le t) = owk (λ e → le (proj₁ e) , proj₂ e) (ιG E t)
ιG E (oΩ fe r ac h) = oΩ (λ e → fe (proj₁ e)) (pS E r) (λ e → aS E r (proj₂ e) (ac (proj₁ e))) (λ ξ z → owk asl (ιG E (h ξ (intoU r (outU (pS E r) z)))))
ιG E (oev f) = oev (λ ok e → ιG E (f ok (proj₁ e)))

_⨾_ : ∀ {a b σ} → Emb b σ → (d : Dn a b) → Emb a (dnF d ∪ σ)
E ⨾ d = emb (λ r → pS E (pl d r)) (λ r e x → aS E (pl d r) (proj₂ e) (admD d r (proj₁ e) x))

E-br : (τ : Ordᴵ) → Emb (base ⊞ τ) (tk 1 τ)
E-br τ = emb (bra τ) (λ r e x → e zero , x)

E-fst : Emb (suc base) tz
E-fst = emb fst (λ r e x → x)
```

## §4 全互模拟下的搬运

```agda
module F = Rel (λ _ → ⊤)
open F using (Rᵒ; rz; rs; rl; ri; rŝ; rĉ; rcl; rwkˡ; rwkʳ; rΩ; rev; rwk; frefl; ∪∼; intoR; outR; R-⊕; R-ι; R-ιˡ; RΩ̇; tk∼)

hgT : ∀ L → F.Hg L
hgT zero      = tt
hgT base      = tt
hgT (suc k)   = hgT k
hgT (lim f)   = λ n → hgT (f n)
hgT (lcl h g) = tt , λ η → hgT (g η)

assoc∼ : ∀ {a a′ b c} → a F.∼ₛ a′ → ((a ∪ b) ∪ c) F.∼ₛ (a′ ∪ (b ∪ c))
assoc∼ {b = b} {c = c} s h t T T′ ((u , v) , w) (u′ , (v′ , w′)) e =
  frefl c h t (accT T (_ ⊔ _) (u , v)) (accT (accT T′ _ u′) _ v′) w w′ (frefl b h t (accT T _ u) (accT T′ _ u′) v v′ (s h t T T′ u u′ e))

cv-out : ∀ {a b} (d : Dn a b) {k} (r : k <ᴸ a) {ξ} (z : O k ξ) → outU (pl d r) (intoU (pl d r) z) ≡ z
cv-out d r z = out-intoU (pl d r) z

-- 第一层嵌入就是 `ιG`
E-of : ∀ {a} (d : Dn a D) → Emb a (dnF d)
E-of d = emb (pl d) (λ r e x → admD d r e x)

R-of : ∀ {a φ ψ} (d : Dn a D) {x : O a φ} {x′ : O a ψ} → Rᵒ a a x x′ → Rᵒ D D (ι d x) (ιG (E-of d) x′)
R-of d rz = rz
R-of d (rs sa r) = rs (∪∼ sa (frefl _)) (R-of d r)
R-of d (rl h) = rl (λ n → R-of d (h n))
R-of d (ri e h) = ri e (λ x y dd → R-of d (h x y dd))
R-of d (rŝ e r h) = rŝ e (R-of d r) (λ η ee η′ e′ dd → R-of d (h η ee η′ e′ dd))
R-of d (rĉ e dz dg r h) = rĉ e dz dg (R-of d r) (λ η ee η′ e′ dd → R-of d (h η ee η′ e′ dd))
R-of d (rcl sh s r h) = rcl sh (∪∼ s (frefl _)) (R-of d r) (λ η η′ dd → rwk (R-of d (h η η′ dd)))
R-of d (rwkˡ r) = rwkˡ (R-of d r)
R-of d (rwkʳ r) = rwkʳ (R-of d r)
R-of {a} d (rΩ {r = r} {r′ = r′} {h = h} {h′ = h′} ek hg s f) =
  rΩ {r = pl d r} {r′ = pl d r′} ek hg (∪∼ s (frefl _))
     (λ ξ ξ′ dd z z′ l → rwk (subst₂ (λ u v → Rᵒ D D (ι d (h ξ u)) (ιG (E-of d) (h′ ξ′ (intoU r′ v)))) (sym (cv-into d r z)) (sym (cv-out d r′ z′))
        (R-of d (f ξ ξ′ dd z z′ (intoR r (outR (pl d r) l))))))
R-of d (rev h) = rev (λ ok e ok′ e′ → R-of d (h ok (proj₁ e) ok′ (proj₁ e′)))

-- ιG 对 ι 的吸收: 栈多一层
R-stk : ∀ {a b σ φ ψ} (E : Emb b σ) (d : Dn a b) {x : O a φ} {x′ : O a ψ} → Rᵒ a a x x′ → Rᵒ D D (ιG E (ι d x)) (ιG (E ⨾ d) x′)
R-stk E d rz = rz
R-stk E d (rs sa r) = rs (assoc∼ sa) (R-stk E d r)
R-stk E d (rl h) = rl (λ n → R-stk E d (h n))
R-stk E d (ri e h) = ri e (λ x y dd → R-stk E d (h x y dd))
R-stk E d (rŝ e r h) = rŝ e (R-stk E d r) (λ η ee η′ e′ dd → R-stk E d (h η ee η′ e′ dd))
R-stk E d (rĉ e dz dg r h) = rĉ e dz dg (R-stk E d r) (λ η ee η′ e′ dd → R-stk E d (h η ee η′ e′ dd))
R-stk E d (rcl sh s r h) = rcl sh (assoc∼ s) (R-stk E d r) (λ η η′ dd → rwk (rwkˡ (R-stk E d (h η η′ dd))))
R-stk E d (rwkˡ r) = rwkˡ (R-stk E d r)
R-stk E d (rwkʳ r) = rwkʳ (R-stk E d r)
R-stk E d (rΩ {r = r} {r′ = r′} {h = h} {h′ = h′} ek hg s f) =
  rΩ {r = pS E (pl d r)} {r′ = pS E (pl d r′)} ek hg (assoc∼ s)
     (λ ξ ξ′ dd z z′ l → rwk (rwkˡ (subst₂ (λ u v → Rᵒ D D (ιG E (ι d (h ξ (cvU d r (intoU (pl d r) u))))) (ιG (E ⨾ d) (h′ ξ′ (intoU r′ v))))
          (sym (out-intoU (pS E (pl d r)) z)) (sym (out-intoU (pS E (pl d r′)) z′))
          (subst (λ u → Rᵒ D D (ιG E (ι d (h ξ u))) (ιG (E ⨾ d) (h′ ξ′ (intoU r′ z′)))) (sym (cv-into d r z))
             (R-stk E d (f ξ ξ′ dd z z′ (intoR r (outR (pS E (pl d r)) l))))))))
R-stk E d (rev h) = rev (λ ok e ok′ e′ → R-stk E d (h ok (proj₁ (proj₁ e)) ok′ (proj₁ e′)))
```

## §5 $W\oplus$ 与行走

```agda
module Top₀ {φW : Fᵗ} (wl : ∀ {w} → Evt w φW → Evt w Fl₀) where
  open Fold cfD using (ψᵒ; ψ̄)

  W : O D φW
  W = owk wl (Ω̇ D)

  RW : Rᵒ D D W W
  RW = rwk (RΩ̇ (selfΩ 2) (hgT D))

  K : ∀ {a σ π} (E : Emb a σ) → O a π → O c₀ ((φW ∪ (π ∪ σ)) ∪ tz)
  K E y = ι ds (W ⊕ ιG E y)

  Kstep : ∀ {a b σ φ ψ} (E : Emb b σ) (d : Dn a b) {x : O a φ} {x′ : O a ψ} → Rᵒ a a x x′ → Rᵒ c₀ c₀ (K E (ι d x)) (K (E ⨾ d) x′)
  Kstep E d r = R-ι ds ds (frefl tz) (R-⊕ (frefl φW) RW (R-stk E d r))

  Kof : ∀ {a φ ψ} (d : Dn a D) {x : O a φ} {x′ : O a ψ} → Rᵒ a a x x′ → Rᵒ c₀ c₀ (ι ds (W ⊕ ι d x)) (K (E-of d) x′)
  Kof d r = R-ι ds ds (frefl tz) (R-⊕ (frefl φW) RW (R-of d r))

  tr-good : ∀ {φ ψ w w′} {x : O c₀ φ} {y : O c₀ ψ} {ok : Wok w} {ok′ : Wok w′} {ev : Evt w φ} {ev′ : Evt w′ ψ} {p : zero <ᴵ w 0} {p′ : zero <ᴵ w′ 0} → Rᵒ c₀ c₀ x y →
            Goodᴺ (toZ (ψ̄ x ok ev p)) → Goodᴺ (toZ (ψ̄ y ok′ ev′ p′))
  tr-good {ok = ok} {ok′} {ev} {ev′} {p} {p′} r G = Goodᴺ-tr (toZ-≅ (F.R→≈ cfD cfD r ok ev p ok′ ev′ p′ z≅)) G

  -- 行走的不变量: τ 在第 1 层的地板里, 别的层平凡
  Ne1 : ℕ → Set
  Ne1 (suc zero) = ⊥
  Ne1 _          = ⊤

  Pσ : Ordᴵ → Fᵗ → Set
  Pσ τ σ = Kin τ (prj 1 σ) × (∀ h → Ne1 h → prj h σ ∼ᶜ fz)

  Pup : ∀ {τ σ} → Pσ τ σ → Pσ τ (tz ∪ σ)
  Pup (k , t) = kr k , λ h n T T′ ev ev′ e → t h n (accT T fz (proj₁ ev)) T′ (proj₂ ev) ev′ e

  Walk : ∀ {a τ σ} (q : zero <ᴵ a) (E : Emb (base ⊞ a) σ) → Pσ τ σ → ∀ {w} (ok : Wok w) (ev : Evt w ((φW ∪ (Fl₀ ∪ σ)) ∪ tz)) (p : zero <ᴵ w 0) →
         Goodᴺ (toZ (ψ̄ (K E (Ω̇ (base ⊞ a))) ok ev p)) →
         Σ Fᵗ λ σ′ → Σ (Emb (suc base) σ′) λ E′ → Pσ τ σ′ × Σ (Evt w ((φW ∪ (Fl₀ ∪ σ′)) ∪ tz)) λ ev′ → Goodᴺ (toZ (ψ̄ (K E′ (Ω̇ (suc base))) ok ev′ p))
  Walk {a = suc zero} {σ = σ} zero E P ok ev p G = σ , E , P , ev , G
  Walk {a = suc b} {σ = σ} (suc q) E P ok ((eW , (e₀ , eσ)) , tt) p G =
    Walk q (E ⨾ ds) (Pup P) ok ((eW , (e₀ , (tt , eσ))) , tt) p
      (tr-good (Kstep E ds (RΩ̇ (self⊞ b≈ b) (hgT _))) G₂)
    where
    z₀ : O (base ⊞ b) ((φW ∪ (Fl₀ ∪ σ)) ∪ tz)
    z₀ = owk (λ e → proj₁ (proj₂ (proj₁ e))) (Ω̇ (base ⊞ b))
    G₂ = subst (λ u → Goodᴺ (toZ (ψ̄ (K E (ι ds u)) ok _ p))) (out-intoU (pS E zero) z₀) (proj₁ (gl-at 0 G))
  Walk {a = lim f s} {σ = σ} (lim n q) E P ok ((eW , (e₀ , eσ)) , tt) p G =
    Walk q (E ⨾ dl {f = λ m → base ⊞ f m} n) (Pup P) ok ((eW , (e₀ , (tt , eσ))) , tt) p
      (tr-good (Kstep E (dl {f = λ m → base ⊞ f m} n) (RΩ̇ (self⊞ b≈ (f n)) (hgT _))) (proj₁ (gl-at n G)))

  -- 节点: 走到第 1 个链点里的那份 `W`, 它的闭包带着 σ 的地板
  module NodeM {σ : Fᵗ} (E : Emb (suc base) σ) where
    πn : Fᵗ
    πn = (φW ∪ (Fl₀ ∪ σ)) ∪ tz

    Rn : base <ᴸ c₀
    Rn = suc (pS E zero)

    fen : ∀ {w} → Evt w πn → Evt w Fl₀
    fen e = proj₁ (proj₂ (proj₁ e))

    acn : ∀ {w} → Evt w πn → Adm w Rn
    acn e = aS E zero (proj₂ (proj₂ (proj₁ e))) tt

    z₀ : O base πn
    z₀ = owk fen (Ω̇ base)

    hE : O base πn → O c₀ (πn ∪ πn)
    hE u = owk asl (ι ds (owk swp (W ⊕ owk asl (ιG E (owk (λ e → proj₁ e , tt) (ι ds u))))))

    z₁ : O base πn → O base πn
    z₁ u = owk (λ v → v , (v , v)) (ψᵒ Rn fen acn (hE u))

    X₁ : O c₀ ((Fl₀ ∪ tz) ∪ tz)
    X₁ = ι ds (ι (df {h = 1} {g = base ⊞_}) (Ω̇ (suc base)))

    y₁ : O base (πn ∪ ((Fl₀ ∪ tz) ∪ tz))
    y₁ = ψᵒ Rn fen acn X₁

    Hd : ∀ {w} (ok : Wok w) (ev : Evt w ((φW ∪ (((πn ∪ ((Fl₀ ∪ tz) ∪ tz)) ∪ tz) ∪ σ)) ∪ tz)) (p : zero <ᴵ w 0) → Ordˢ zero
    Hd ok ev p = ψ̄ (K E (ι ds y₁)) ok ev p

    node : ∀ {w} (ok : Wok w) (ev : Evt w πn) (p : zero <ᴵ w 0) (G : Goodᴺ (toZ (ψ̄ (K E (Ω̇ (suc base))) ok ev p))) →
           Σ (Evt w ((φW ∪ (((πn ∪ ((Fl₀ ∪ tz) ∪ tz)) ∪ tz) ∪ σ)) ∪ tz)) λ ev* → Σ (Goodᴺ (toZ (Hd ok ev* p))) λ Gᵒ → Σ (Goodᴺ (toZ (Hd ok ev* p))) λ Gᵗ →
           (forceᴺ _ Gᵒ ⊑ forceᴺ _ G) × (∀ τ → Kin τ (prj 1 σ) → suc τ ⊑ᴵ lvG Gᵗ)
    node ok ev p G = _ , proj₁ G₇ , proj₁ G₈ ,
        ⊑-trans (proj₂ G₇) (⊑-trans (proj₂ G₆) (⊑-trans (proj₂ G₅) (⊑-trans (proj₂ G₄) (proj₂ G₃)))) ,
        λ τ k → ⊑ᴵ-trans (Bd-in {φ = prj 1 ((φW ∪ (((πn ∪ (Fl₀ ∪ tz)) ∪ tz) ∪ σ)) ∪ tz) ⊔ fk zero} (kl (kl (kr (kr k)))) _ _) (proj₂ G₈)
      where
      G₁ = gl-at 1 G
      G₂ = subst (λ u → Σ (Goodᴺ (toZ (ψ̄ (K E (ι ds u)) ok _ p))) λ H → forceᴺ _ H ⊑ forceᴺ _ G) (out-intoU (pS E zero) (z₁ (outU (pS E zero) (intoU (pS E zero) z₀)))) G₁
      G₃ = subst (λ u → Σ (Goodᴺ (toZ (ψ̄ (K E (ι ds (z₁ u))) ok _ p))) λ H → forceᴺ _ H ⊑ forceᴺ _ G) (out-intoU (pS E zero) z₀) G₂
      G₄ = gc-o (proj₁ G₃)
      G₅ = gi-at (proj₁ G₄)
      G₆ = gl-at 1 (proj₁ G₅)
      G₇ = gc-o (proj₁ G₆)
      G₈ = gc-t (proj₁ G₆)
```

## §6 头与层号无关

`⊕≈`: 第 0 层的树在掩码 $h\ne1$ 下相关, 则 $K_E$ 的计值相关, $W$ 不用参与掩码. 第 0 层没有路径, 所以 `rΩ` 行是空的: 这正是这个引理成立的原因, 否则 $W$ 的闭包会被目标的地板 $\tau$ 抬高.

```agda
  module M = Rel Ne1

  zΩ : ∀ {k} → k <ᴸ base → ⊥
  zΩ ()

  ⊕≈ : ∀ {σ σ′ φ ψ} (E : Emb (suc base) σ) (E′ : Emb (suc base) σ′) → σ M.∼ₛ σ′ → {y : O base φ} {y′ : O base ψ} → M.Rᵒ base base y y′ → ψ̄ (K E (ι ds y)) ≈ᵗ ψ̄ (K E′ (ι ds y′))
  ⊕≈ E E′ sσ M.rz ok ev p ok′ ev′ p′ ei = F.R→≈ cfD cfD (R-ι ds ds (frefl tz) RW) ok (proj₁ (proj₁ ev) , tt) p ok′ (proj₁ (proj₁ ev′) , tt) p′ ei
  ⊕≈ E E′ sσ (M.rs s r) = sucT (⊕≈ E E′ sσ r)
  ⊕≈ E E′ sσ (M.rl h) = limT (λ n → ⊕≈ E E′ sσ (h n))
  ⊕≈ E E′ sσ (M.ri e h) = limᵢT e (λ x y d → ⊕≈ E E′ sσ (h x y d))
  ⊕≈ E E′ sσ (M.rŝ e r h) = ŝT e (⊕≈ E E′ sσ r) (λ η ee η′ e′ d → ⊕≈ E E′ sσ (h η ee η′ e′ d))
  ⊕≈ E E′ sσ (M.rĉ e dz dg r h) = ĉT e dz dg (⊕≈ E E′ sσ r) (λ η ee η′ e′ d → ⊕≈ E E′ sσ (h η ee η′ e′ d))
  ⊕≈ {σ = σ} {σ′ = σ′} {φ = φ} {ψ = ψ} E E′ sσ (M.rcl {h = h} sh s r f) =
    cloT h (⊔∼ᶜ (⊔∼ᶜ (ᶠ→ᶜ (∼ᶠ-refl (prj h φW))) (⊔∼ᶜ (⊔∼ᶜ (s h sh) (ᶠ→ᶜ (∼ᶠ-refl fz))) (sσ h sh))) (ᶠ→ᶜ (∼ᶠ-refl fz)))
      (⊕≈ E E′ sσ r) (λ η η′ d ok ev p ok′ ev′ p′ ei → ⊕≈ E E′ sσ (f η η′ d) ok _ p ok′ _ p′ ei)
  ⊕≈ E E′ sσ (M.rwkˡ {le = le} r) ok ev p ok′ ev′ p′ ei = ⊕≈ E E′ sσ r ok _ p ok′ ev′ p′ ei
  ⊕≈ E E′ sσ (M.rwkʳ {le′ = le′} r) ok ev p ok′ ev′ p′ ei = ⊕≈ E E′ sσ r ok ev p ok′ _ p′ ei
  ⊕≈ E E′ sσ (M.rΩ {r = ()} ek hg s f)
  ⊕≈ E E′ sσ (M.rev h) ok ev p ok′ ev′ p′ ei = ⊕≈ E E′ sσ (h ok _ ok′ _) ok ev p ok′ ev′ p′ ei
```

## §7 否定: $W\oplus\dot\Omega_D$ 没有证书

$\tau$ 是外层闭包的第 0 个链点. 第 $\tau$ 个分支里走到节点 $\Omega$, 第 1 个链点把 $W$ 放到目标之下, $W$ 的闭包的界 $\ge\tau+1$. 但那个闭包的第 0 点与 $\tau$ 无关: 同一个点在 $\tau$ 自己的展开里出现过 (`E-of df` 那一支), 所以它的层号 $\sqsubseteq\tau$.

```agda
  gD : Ordᴵ → LI
  gD η = base ⊞ η

  R₁ : M.Rᵒ c₀ c₀ (ι ds (ι (df {h = 1} {g = gD}) (Ω̇ (suc base)))) (ι ds (ι (df {h = 1} {g = gD}) (Ω̇ (suc base))))
  R₁ = M.R-ι ds ds (M.frefl tz) (M.R-ι df df (M.frefl tz) (M.RΩ̇ (s≈ b≈) tt))

  z<of : ∀ {τ} → suc zero ⊑ᴵ τ → zero <ᴵ τ
  z<of (s⊑ Level.z≅ q) = q

  suc⊑self : ∀ {τ} → suc τ ⊑ᴵ τ → ⊥
  suc⊑self (s⊑ e q) = ≺ᴵ-irrefl (via e q)

  P₀ : ∀ τ → Pσ τ (tk 1 τ)
  P₀ τ = kz , triv
    where
    triv : ∀ h → Ne1 h → prj h (tk 1 τ) ∼ᶜ fz
    triv zero n = ᶠ→ᶜ fz∼
    triv (suc (suc m)) n = ᶠ→ᶜ fz∼

  tr-same : ∀ {φ w} {x y : O c₀ φ} {ok : Wok w} {ev : Evt w φ} {p : zero <ᴵ w 0} → Rᵒ c₀ c₀ x y → Goodᴺ (toZ (ψ̄ x ok ev p)) → Goodᴺ (toZ (ψ̄ y ok ev p))
  tr-same {ok = ok} {ev} {p} r G = Goodᴺ-tr (toZ-≅ (F.R→≈ cfD cfD r ok ev p ok ev p z≅)) G

  noW : ∀ {w} (ok : Wok w) (ev : Evt w ((φW ∪ Fl₀) ∪ tz)) (p : zero <ᴵ w 0) → Goodᴺ (toZ (ψ̄ (ι ds (W ⊕ Ω̇ D)) ok ev p)) → ⊥
  noW {w} ok ((eW , e₀) , tt) p G = suc⊑self bad
    where
    Br = gc-br G
    G₀ = proj₁ Br
    τ : Ordᴵ
    τ = proj₁ (proj₂ Br)
    e = proj₁ (proj₂ (proj₂ Br))
    τ≅ : τ ≅ᴵ lvG G₀
    τ≅ = proj₁ (proj₂ (proj₂ (proj₂ Br)))
    Gb = proj₂ (proj₂ (proj₂ (proj₂ Br)))
    q : zero <ᴵ τ
    q = z<of (⊑ᴵ-trans (Bd-in {φ = prj 1 ((φW ∪ Fl₀) ∪ tz) ⊔ fk zero} (kr kz) _ _) e)
    r₀ = RΩ̇ (s≈ b≈) tt
    evA = ((eW , (e₀ , tt)) , tt)
    d₀ = toZ-≅ (F.R→≈ cfD cfD (Kof (df {h = 1} {g = gD}) r₀) ok _ p ok evA p z≅)
    G₀′ : Goodᴺ (toZ (ψ̄ (K (E-of df) (Ω̇ (suc base))) ok evA p))
    G₀′ = Goodᴺ-tr d₀ G₀
    Gb′ = tr-same (Kof (db {h = 1} {g = gD} τ) (RΩ̇ (self⊞ b≈ τ) (hgT _))) Gb
    Wk = Walk {τ = τ} q (E-of (db {h = 1} {g = gD} τ)) (P₀ τ) _ _ _ Gb′
    σ′ : Fᵗ
    σ′ = proj₁ Wk
    E′ : Emb (suc base) σ′
    E′ = proj₁ (proj₂ Wk)
    P′ = proj₁ (proj₂ (proj₂ Wk))
    Gn = proj₂ (proj₂ (proj₂ (proj₂ Wk)))
    Nτ = NodeM.node E′ _ _ _ Gn
    N₁ = NodeM.node (E-of (df {h = 1} {g = gD})) ok evA p G₀′
    sσ : σ′ M.∼ₛ tz
    sσ = proj₂ P′
    Gᵗ = proj₁ (proj₂ (proj₂ Nτ))
    Gᵒ = proj₁ (proj₂ N₁)
    hd≅ = toZ-≅ (⊕≈ E′ (E-of (df {h = 1} {g = gD})) sσ
            (M.R-ψ cfD cfD (NodeM.Rn E′) (NodeM.Rn (E-of (df {h = 1} {g = gD}))) b≈ tt
               (M.∪∼ (M.∪∼ (M.frefl φW) (M.∪∼ (M.frefl Fl₀) sσ)) (M.frefl tz)) R₁)
            _ _ _ _ _ _ z≅)
    bad : suc τ ⊑ᴵ τ
    bad = ⊑ᴵ-trans (proj₂ (proj₂ (proj₂ (proj₂ Nτ))) τ (proj₁ P′))
           (⊑ᴵ-trans (≅ᴵ→⊑ᴵ (≅lv hd≅ Gᵗ Gᵒ))
             (⊑ᴵ-trans (≤lv Gᵒ G₀′ (proj₁ (proj₂ (proj₂ (proj₂ N₁)))))
               (≅ᴵ→⊑ᴵ (≅ᴵ-sym (≅ᴵ-trans τ≅ (≅lv d₀ G₀ G₀′))))))
```

## §8 从根走到 $W\oplus\dot\Omega_D$

$\psi_0(\Omega_{\Omega\cdot2+1})$ 的第 1 个链点是 $\psi_{\Omega\cdot2}(\Omega_{\Omega\cdot2})$; 走它的头 $\Omega_{\Omega+1}$, 第 0 个链点 $\Omega$ 的头 `limᵢ` 取 $x=1$, 就得到 $\psi_{\Omega\cdot2}(1)=\lim\mathrm{rep}\,\Omega_{\Omega\cdot2}$, 第 2 份是 $\Omega_{\Omega\cdot2}+\Omega_{\Omega\cdot2}$. 这一路都不用比较世界: 目标是 `zero`, 节点的路径是字面的.

```agda
module Root where
  open Fold cfD using (ψᵒ; ψ̄)

  noCert : Goodᴺ (toZ (T₀ c₀ cfD)) → ⊥
  noCert G = Top₀.noW {φW = _} (λ e → idF (proj₁ e)) _ _ _ (proj₁ G₆)
    where
    G₁ = gl-at 1 G
    G₂ = gc-o (proj₁ G₁)
    G₃ = gl-at 0 (proj₁ G₂)
    G₄ = gc-o (proj₁ G₃)
    G₅ = gl-at 0 (proj₁ G₄)
    G₆ = gl-at 2 (proj₁ G₅)

-- 与证书的选择无关
noCert₂ : ∀ (cf : Cf c₀) → Goodᴺ (toZ (T₀ c₀ cf)) → ⊥
noCert₂ cf G = Root.noCert (Goodᴺ-tr (toZ-≅ (F.R→≈ cf cfD (RΩ̇ (s≈ (selfΩ 2)) (hgT _)) ok₀ ev₀ zero ok₀ ev₀ zero z≅)) G)
```

## §9 往上全都没有证书

更高的层号在第一支里字面含有 $\Omega\cdot m+1$ 的树: `ι df` 平凡, 所以跨层互模拟 `R-ιˡ` 把它们连起来. **这里对 $m$ 的归纳是否定结果的归纳, 不是定义的.**

```agda
Lv₊ : ℕ → LI
Lv₊ m = suc (Ω· suc (suc m))

selfL : ∀ m → Lv₊ m ≈ Lv₊ m
selfL m = s≈ (selfΩ (suc (suc m)))

cfL : ∀ m → Cf (Lv₊ m)
cfL m = WFΩ (suc (suc m)) , selfL m

trivDf : ∀ {h} {g : Ordᴵ → LI} → F.Triv (df {h} {g})
trivDf h _ = ᶠ→ᶜ fz∼

trivDs : ∀ {k} → F.Triv (ds {k})
trivDs h _ = ᶠ→ᶜ fz∼

-- 第 1 层嵌入之后的头与裸的 Ω̇ (suc L) 相关
toA : ∀ {c m φ} (cf : Cf c) {x : O c φ} → Rᵒ c (Lv₊ m) x (Ω̇ (Lv₊ m)) → ∀ {w} {ok : Wok w} {ev : Evt w φ} {p : zero <ᴵ w 0} →
      Goodᴺ (toZ (Fold.ψ̄ cf x ok ev p)) → Goodᴺ (toZ (Fold.ψ̄ (cfL m) (Ω̇ (Lv₊ m)) ok₀ ev₀ zero))
toA {m = m} cf r {ok = ok} {ev} {p} G = Goodᴺ-tr (toZ-≅ (F.R→≈ cf (cfL m) r ok ev p ok₀ ev₀ zero z≅)) G

noLv₊ : ∀ m → Goodᴺ (toZ (Fold.ψ̄ (cfL m) (Ω̇ (Lv₊ m)) ok₀ ev₀ zero)) → ⊥
noLv₊ zero G = noCert₂ (cfL zero) G
noLv₊ (suc m) G = noLv₊ m (toA (cfL (suc m)) (R-ιˡ ds trivDs (R-ιˡ df trivDf (RΩ̇ (selfL m) (hgT _)))) (proj₁ G₂))
  where
  G₁ = gl-at 0 G
  G₂ = gc-o (proj₁ G₁)

noΩ· : ∀ m (cf : Cf (Ω· suc (suc (suc m)))) → Goodᴺ (toZ (T₀ (Ω· suc (suc (suc m))) cf)) → ⊥
noΩ· m cf G = noLv₊ m (toA cf (R-ιˡ df trivDf (RΩ̇ (selfL m) (hgT _))) (proj₁ (gc-o G)))

noΩ·ω : ∀ (cf : Cf Ω·ω) → Goodᴺ (toZ (T₀ Ω·ω cf)) → ⊥
noΩ·ω cf G = noLv₊ 0 (toA cf (R-ιˡ (dl 3) (λ h _ → ᶠ→ᶜ fz∼) (R-ιˡ df trivDf (RΩ̇ (selfL 0) (hgT _)))) (proj₁ (gc-o (proj₁ (gl-at 3 G)))))
```
