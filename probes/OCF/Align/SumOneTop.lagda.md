# 和形式过 $\Omega_{\Omega+1}$ (六): $\psi_0(\Omega_\Omega)$ 这一站对上旧折叠

> 不含记号. 入口 [SumOne](SumOne.lagda.md). `CI`: `nκ` 回灌的每一格, 状态对上 $\psi(\Omega_a)$, 层对上 $\psi_0(\Omega_a)$. 只到 $\psi_0(\Omega_\Omega)$: 没有用到带 `nκ` 的项.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.SumOneTop where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF hiding (_⊕_; rkT; keep; rise; Rk)
import OCF.Align.CumReadCF as C
open import OCF.Align.CumReadCFEq
open import OCF.Align.CumReadCFThm using (_⊴_; ψL; z⊴; Ω⊴)
open import OCF.Align.TLRuleRel using (ContF; emb; emb≈; emb≈ˡ; emb≈ʳ; emb⊴ˡ; emb⊴ʳ; ≈-rp′; ≈-os′; idH; idH≈ˡ; idH≈ʳ; idH-ContF; ContF-κ)
open import OCF.Align.TLRuleMain using (Co; cz; cs; cl′; cd; ce; ce′)
import OCF.Align.SumOneTree as N
open N using (D; Dl; D̂; Ly; cnt; top; K; V; n0; n1; _⨾_; nl; ni; nw; nκ; sum; pt; sum-fst; Lg-sum; Cut; tailP; D₊; Ω̂₀)
open import OCF.Align.SumOneClosed
open import OCF.Align.SumOneRel
open import OCF.Align.SumOneSim
```

## §1 顶层

```agda
id-ContF : ∀ {k} → ContF {k} {k} (λ r → r) (λ z → z)
id-ContF = record { cq = λ e → e ; cl = λ g e → e ; cn = λ s₁ g e q → e ; cm = λ d → d }

i₁ : ∀ {M W} (Y : St W) (z₀ z₁ : O M) → z₀ ≈ z₀ → z₁ ≈ os z₀ → z₁ ≈ z₁ → Inv Y z₀ → Diff (Step Y) z₀ z₁
i₁ Y z₀ z₁ pz e p v {t} τ lt T l T′ l′ =
  rd (rep c) (ψQ z₁ (os z₀) T′ l′ T′ l′ e) (ψQ z₁ z₁ T′ l′ T′ l′ p) (rep≈ cc) (z⊴ _)
    (rl (λ m → rep c (suc m)) (λ n → rep≈ cc (suc n)) (λ n → rep≈ cc (suc n)) (λ n → rep≈ cc (suc n))
        (ψQ z₀ z₀ T l T′ l′ pz)
        (λ m → add-Rel (rep c (suc m)) (rep≈ cc (suc m)) (rc (Ω-Rel t C.self lt) (un v τ lt T′ l′))))
  where
  c = ψ t T′ l′ z₀
  cc : c ≈ c
  cc = ψQ z₀ z₀ T′ l′ T′ l′ pz

I₁ : ∀ {M W} → Itg {top} {M} {M} {W} (λ r → r) A₁ (λ z → z) (λ _ z → z ≈ z)
I₁ = record
  { ict = id-ContF
  ; i1 = λ p lW′ w z₀ z₁ Y pz d p₂ v → i₁ Y z₀ z₁ pz d p₂ v
  ; icw = λ _ D → relR D
  ; icn = λ _ p → p
  ; icr = λ _ _ p → p
  }
```

## §2 走一段层

```agda
ũ : ∀ {W₀ c} → W₀ ⊲ c → Lg c → D̂ c
ũ {c = c} _ _ = ni {k = c} C.self (λ _ _ _ → n1)

seg-T : ∀ {c M} (q : asuc c ⊲ M) → Rl top M {c} (emb (⊲-tr (suc self) q) (Ω̇ c)) (ni {k = c} C.self (λ _ _ _ → n1)) (emb q (Ω̇ (asuc c)))
seg-T {c} q =
  ri C.self (λ _ _ _ → n1) r′ (idH r′)
     (emb≈ˡ q (≈-rp′ (Ω̇ (asuc c)) {r = zero} {r″ = r′} (Ω≈ (asuc c))
        (λ x₀ z d → idH≈ʳ r′ (oe≈ x₀ (ss self) z d))))
     (emb≈ q q (Ω≈ (asuc c)))
     (emb≈ˡ (⊲-tr (suc self) q) (idH≈ʳ r′ (Ω≈ c)))
     (idH-ContF r′)
     (λ _ _ w₁ z₀ z₁ h d p → rs (idH≈ˡ r′ (≈-os′ z₁ d (λ x₀ e → idH≈ʳ r′ e))) (idH≈ˡ r′ (idH≈ʳ r′ p)))
  where
  r′ = ≪∘ zero q

Wk-Rel : ∀ b {a W₀ V₁} {A₀ : Ig top V₁} (I : Itg {top} {V₁} {V₁} {V₁} (λ r → r) A₀ (λ z → z) (λ _ z → z ≈ z)) (p : a ⊲ b) (ap : W₀ ⊲ a) (lb : Lg b) (bV : b ⊲ V₁) (q : a ⊲ V₁) (lV : Lg V₁) (co : D̂ V₁) (Y : St V₁) →
         Inv Y (emb q (Ω̇ a)) → Diff (Walk accTop ũ b p ap lb bV lV tt A₀ co Y) (emb q (Ω̇ a)) (emb bV (Ω̇ b))
WRp-Rel : ∀ {a W₀ V₁ n} {A₀ : Ig top V₁} (I : Itg {top} {V₁} {V₁} {V₁} (λ r → r) A₀ (λ z → z) (λ _ z → z ≈ z)) (f : ℕ → A) (stp : ∀ n → f n ⊲ f (suc n)) (wl : ∀ n → Lg (f n)) (p : a ⊲ f n) (ap : W₀ ⊲ a) (fV : ∀ m → f m ⊲ V₁) (lV : Lg V₁) (co : D̂ V₁) (Y : St V₁) →
          Inv Y (emb (fV n) (Ω̇ (f n))) → ∀ m → Inv (proj₂ (WRp accTop ũ f stp wl p ap fV lV tt A₀ co Y m)) (emb (fV (m + n)) (Ω̇ (f (m + n))))

Wk-Rel b I C.self ap lb bV q lV co Y v τ lt T l T′ l′ =
  rz (ψQ _ _ T l T′ l′ (emb≈ q bV (Ω≈ b))) (ψQ _ _ T′ l′ T′ l′ (emb≈ bV bV (Ω≈ b)))
Wk-Rel (asuc c) I (C.suc p) ap lb bV q lV co Y v τ lt T l T′ l′ =
  rc (Wk-Rel c I p ap lb cV q lV co Y v τ lt T l T′ l′)
     (RS accTop cV lV tt I (emb≈ cV cV (Ω≈ c)) (seg-T bV) _ (inv+ v (Wk-Rel c I p ap lb cV q lV co Y v)) τ lt T′ l′ T′ l′)
  where
  cV = ⊲-tr (suc self) bV
Wk-Rel (alim f) {a} {V₁ = V₁} I (C.lim n p) ap (stp , wl) bV q lV co Y v {t} τ lt T l T′ l′ =
  rc (Wk-Rel (f n) I p ap (wl n) (fV n) q lV co Y v τ lt T l T′ l′)
     (drpn n Gt
        (ψQ _ (ol (λ m → emb (fV m) (Ω̇ (f m)))) T′ l′ T′ l′ (emb≈ˡ bV (λ m → emb≈ʳ (fV m) (Ω≈ (f m)))))
        (ψQ _ _ T′ l′ T′ l′ (emb≈ bV bV (Ω≈ (alim f))))
        (λ i → ψQ _ _ T′ l′ T′ l′ (emb≈ (fV i) (fV i) (Ω≈ (f i))))
        (λ i → ψL T′ l′ T′ l′ (emb⊴ˡ (fV i) (emb⊴ʳ (fV (suc i)) (Ω⊴ (stp i)))))
        (ψQ _ _ T′ l′ T′ l′ (emb≈ (fV n) (fV n) (Ω≈ (f n))))
        (λ m → Wk-Rel (f (suc (m + n))) I (stp (m + n)) (⊲-tr ap (tailP f stp p m)) (wl (suc (m + n))) (fV (suc (m + n))) (fV (m + n)) lV _ _
                  (WRp-Rel I f stp wl p ap fV lV _ _ (inv+ v (Wk-Rel (f n) I p ap (wl n) (fV n) q lV co Y v)) m) τ lt T′ l′ T′ l′))
  where
  fV : ∀ m → f m ⊲ V₁
  fV m = ⊲-tr (C.lim m C.self) bV
  Gt : ℕ → O t
  Gt m = ψ t T′ l′ (emb (fV m) (Ω̇ (f m)))

WRp-Rel I f stp wl p ap fV lV co Y v zero = v
WRp-Rel {n = n} I f stp wl p ap fV lV co Y v (suc m) =
  inv+ (WRp-Rel I f stp wl p ap fV lV co Y v m)
       (Wk-Rel (f (suc (m + n))) I (stp (m + n)) (⊲-tr ap (tailP f stp p m)) (wl (suc (m + n))) (fV (suc (m + n))) (fV (m + n)) lV _ _ (WRp-Rel I f stp wl p ap fV lV co Y v m))
```

## §3 第 0 层的对应

`Co`: 同 [TLRuleMain](TLRuleMain.lagda.md), 新树的和.

```agda
Co-Rel : ∀ {W a b x y} → Rel azero {W} b x y → Co a b → Co (sum a x) y
Co-pt  : ∀ {W a b} {d : ℕ → D azero W} (g : ℕ → O azero) → Co a b → b ≈ g 0 → (∀ m → Rel azero (g m) (d m) (g (suc m))) → ∀ n → Co (pt a d n) (g n)
Co-Rel (rz e p) c = ce c e
Co-Rel (rs e p) c = ce′ (cs c) e
Co-Rel {a = a} (rc {x = x} D₁ D₂) c = Co-Rel {a = sum a x} D₂ (Co-Rel D₁ c)
Co-Rel (rb e p D) c = Co-Rel D (ce c e)
Co-Rel (rr D e p) c = ce (Co-Rel D c) e
Co-Rel (rw {W₀ = W₀} {x = x′} D) c = Co-Rel {W = W₀} {x = x′} D c
Co-Rel (rl g e p q e₀ st′) c = ce′ (cl′ (Co-pt g c e₀ st′)) e
Co-Rel (rd g e p q f D) c = ce′ (cd g (Co-Rel D c)) e
Co-Rel (ri () u p H e pz e₀ C ds) c
Co-pt g c e st′ zero = ce c e
Co-pt {a = a} {d = d} g c e st′ (suc n) = Co-Rel {a = pt a d n} (st′ n) (Co-pt g c e st′ n)
```

## §4 `nκ` 的每一格

世界 `one`, 被积函数 `A₁`, 已走了第一个 `n1`. `Cℓ n`: 第 $n$ 格.

```agda
Y′ : St one
Y′ = Y₀ ⊕ Step Y₀

w′ : D̂ one
w′ = n0 ⨾ nw (z⊲ one) n1

zero-Inv : ∀ {M W} (Y : St W) → (∀ {t} (τ : Tg t W) (lt : Lg t) → yc (d Y) τ lt ≡ n0) → Inv {M} Y o0
zero-Inv Y h = mkI (λ {t} τ lt T l → subst′ (h τ lt) (rz (Ω≈ t) (Ω≈ t)))
  where
  subst′ : ∀ {t W′} {x y : D t W′} → x ≡ y → Rel t (Ω̇ t) y (Ω̇ t) → Rel t (Ω̇ t) x (Ω̇ t)
  subst′ refl d = d

z₁ : ∀ M → O M
z₁ M = emb (z⊲ M) (Ω̇ azero)

z₁≈ : ∀ M → z₁ M ≈ z₁ M
z₁≈ M = emb≈ (z⊲ M) (z⊲ M) tt

z₁≈os : ∀ M → z₁ M ≈ os (o0 {M} {Vs M})
z₁≈os M = emb≈ˡ (z⊲ M) tt

Inv-Y′ : ∀ M → Inv {M} Y′ (z₁ M)
Inv-Y′ M = inv+ (zero-Inv Y₀ (λ τ lt → refl)) (i₁ Y₀ o0 (z₁ M) tt (z₁≈os M) (z₁≈ M) (zero-Inv Y₀ (λ τ lt → refl)))

Cℓ : ℕ → Cl one azero top
Cℓ = κc accTop ũ (z⊲ one) tt tt A₁ w′ Y′

Δℓ : ∀ n → Df (v (Cℓ n))
Δℓ n = κΔ accTop ũ tt A₁ (Cℓ n)

record CI (c : Cl one azero top) : Set where
  field
    inv : Inv {v c} (Sv c) (emb (av c) (Ω̇ (a c)))
    coᶜ : ∀ (la : Lg (a c)) → Co (v c) (ψ azero (inj₁ (z⊲ (a c))) la (Ω̇ (a c)))
open CI public

cv-Inv′ : ∀ {W W′} {Y : St W} {b : O W} (q : W ⊲ W′) (lW : Lg W) (lW′ : Lg W′) → b ≈ b → Inv {W} {W} Y b → Inv {W′} {W′} (cv q lW′ Y) (emb q b)
cv-Inv′ {W} {W′} {Y} {b} q lW lW′ pb v = mkI go
  where
  E : ∀ {t} (T₀ : Tg t W) (T : Tg t W′) (l : Lg W′) → ψ t T₀ lW b ≈ ψ t T l (emb q b)
  E T₀ T l = ψQ b (emb q b) T₀ lW T l (emb≈ʳ q pb)
  P : ∀ {t} (T : Tg t W′) (l : Lg W′) → ψ t T l (emb q b) ≈ ψ t T l (emb q b)
  P T l = ψQ _ _ T l T l (emb≈ q q pb)
  go : ∀ {t} (τ : Tg t W′) (lt : Lg t) (T : Tg t W′) (l : Lg W′) → Rel t (Ω̇ t) (yc (d (cv q lW′ Y)) τ lt) (ψ t T l (emb q b))
  go (inj₁ τ₁) lt T l with cmpF q τ₁ lW′
  ... | inj₁ t⊲W = rw (rr (un v (inj₁ t⊲W) lt (inj₁ t⊲W) lW) (E (inj₁ t⊲W) T l) (P T l))
  ... | inj₂ W⊲t = rw (rr (un v (inj₂ W⊲t) lt (inj₂ W⊲t) lW) (E (inj₂ W⊲t) T l) (P T l))
  go (inj₂ τ₂) lt T l = rr (un v (inj₂ (⊲-tr q τ₂)) lt (inj₂ (⊲-tr q τ₂)) lW) (E (inj₂ (⊲-tr q τ₂)) T l) (P T l)

Co-v₀ : ∀ (la : Lg azero) → Co (v (Cℓ 0)) (ψ azero (inj₁ self) la (Ω̇ azero))
Co-v₀ la = Co-Rel {a = one} (rc (rz tt tt) (i₁ Y₀ (o0 {azero} {Vs azero}) (os o0) tt tt tt (zero-Inv Y₀ (λ τ lt → refl)) (inj₁ (z⊲ one)) tt (inj₁ self) tt (inj₁ self) la)) (cs cz)

CIs : ∀ n → CI (Cℓ n)
CIs zero = record
  { inv = inv≈ (cv-Inv′ q tt lv₀ (z₁≈ one) (Inv-Y′ one)) (emb≈ q (⊲-tr (z⊲ one) q) {x = z₁ one} {y = Ω̇ azero} (emb≈ˡ (z⊲ one) {x = Ω̇ azero} {y = Ω̇ azero} tt)) (emb≈ (⊲-tr (z⊲ one) q) (⊲-tr (z⊲ one) q) {x = Ω̇ azero} {y = Ω̇ azero} tt)
  ; coᶜ = Co-v₀
  }
  where
  q = wv (Cℓ 0)
  lv₀ = lv (Cℓ 0)
CIs (suc n) = record
  { inv = cv-Inv′ q (lv c) (lv (Cℓ (suc n))) (Ω≈ (v c)) (inv+ (inv I) Δd)
  ; coᶜ = λ la → ce (Co-Rel {a = v c} (Δd (inj₁ (z⊲ (v c))) tt Tz (lv c) Tz (lv c))
                      (ce (coᶜ I (lg⊲ (av c) (lv c))) (ψQ (Ω̇ (a c)) (emb (av c) (Ω̇ (a c))) (inj₁ (z⊲ (a c))) (lg⊲ (av c) (lv c)) Tz (lv c) (emb≈ʳ (av c) (Ω≈ (a c))))))
                   (ψQ (Ω̇ (v c)) (Ω̇ (v c)) Tz (lv c) Tz la (Ω≈ (v c)))
  }
  where
  c = Cℓ n
  I = CIs n
  q = sum-fst (v c) (yc (Δℓ n) (inj₁ (z⊲ (v c))) tt)
  Tz : Tg azero (v c)
  Tz = inj₁ (z⊲ (v c))
  Δd : Diff (Δℓ n) (emb (av c) (Ω̇ (a c))) (Ω̇ (v c))
  Δd = Wk-Rel (v c) (Itg↾ (wv c) I₁) (av c) (ap c) (lv c) C.self (av c) (lv c) (co c) (Sv c) (inv I)
```
