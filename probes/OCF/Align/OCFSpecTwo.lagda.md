# 折叠的外部规格: 第一个不平凡的托架, $\psi_0(\Omega+\Omega)$ (底座)

> 底座, 不含记号. 结论写在 [OCFSpec](OCFSpec.lagda.md). 这是第一个托架不是平凡的节点: $C_0(\Omega+\Omega)$ 的成员 $<\Omega+\Omega$ 要落在 $\Omega+\eta_n$ 以下, 而归纳假设只说可数的成员 $<t$. 本文用手写的不变量证明它, 量一下每个节点要花多少.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.OCFSpecTwo where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst; subst₂; trans)

open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.OCFSpecBase
open import OCF.Align.OCFSpecRule
open import OCF.Align.OCFSpecAnchor
open import OCF.Align.OCFSpecOne
```

## §1 相对于前缀的标准形

`T w`: $w\in C_0(\Omega+w+1)$. $\varepsilon_0$ 不满足 `Sel`, 但满足 `T`: 前缀 $\Omega$ 让 $\psi_0(\Omega)$ 进了闭包. `RR` 是 `Reg` 的相对版本. 这一节是 Anchor §3–§5 带前缀重走一遍, 结构一样.

```agda
T : Ordᶜ zero → Set
T w = C zero (suc (Ω+ w)) w

NR : Ordᶜ zero → Set
NR w = C zero (Ω+ w) w

Ω+-≼ : ∀ {x y : Ordᶜ zero} → x ≼ y → Ω+ x ≼ Ω+ y
Ω+-≼ e = add-mono (≼-refl Ω₁) e

Ω+-≺ : ∀ {x y : Ordᶜ zero} → x ≺ᵛ y → Ω+ x ≺ᵛ Ω+ y
Ω+-≺ e = add-mono {σ = λ q → suc q} {σ′ = λ q → suc q} (≼-refl Ω₁) e

T→Sel : ∀ {w} → T w → Sel (Ω+ w)
T→Sel {w} t = plus (λ q → suc q) (Ω∈ (suc (Ω+ w)) (s≼s z≼)) t

T-+ : ∀ {x y} → T x → T y → T (x + y)
T-+ {x} {y} tx ty = plus (λ q → q) (C-a (s≼s (Ω+-≼ (+-≽ˡ x y))) tx) (C-a (s≼s (Ω+-≼ (+-≽ʳ x y))) ty)

data RR : Ordᶜ zero → Set where
  rz : RR zero
  rs : ∀ {b} → RR b → T b → RR (suc b)
  rl : ∀ {f : ℕ → Ordᶜ zero} → (∀ n → RR (f n)) → (∀ n → T (f n)) → (∀ n → f n ≺ᵛ f (suc n)) → RR (lim f)

rr→reg : ∀ {y} → RR y → Reg SdΩ (Ω+ y)
rr→reg rz = rσ sΩ
rr→reg (rs r t) = rs (rr→reg r) (T→Sel t)
rr→reg (rl r t st) = rl (λ n → rr→reg (r n)) (λ n → T→Sel (t n)) (λ n → Ω+-≺ (st n))

ψ⁺ : Ordᶜ zero → Ordᶜ zero
ψ⁺ y = ψ⁰ (Ω+ y)

correct⁺ : ∀ {y} → RR y → IsPsi zero (Ω+ y) (ψ⁺ y)
correct⁺ r = correct cs-Ω (rr→reg r)

1≼ψ⁺ : ∀ {ℓ₀} y → 𝟏 {ℓ₀} ≼ ψ⁺ y
1≼ψ⁺ y = 1≼ψ⁰ (Ω+ y)

psi⁺-≽ : ∀ {y} → RR y → y ≼ ψ⁺ y
psi⁺-≽ rz = z≼
psi⁺-≽ {suc b} (rs r t) = suc≼M (1≼ψ⁺ b) b (psi⁺-≽ r)
psi⁺-≽ (rl r t st) = l≼ (λ n → ≼l n (psi⁺-≽ (r n)))

Ω+∈ : ∀ {k} {a : Ordᶜ k} {y} → 𝟎 {zero} ≺ᵛ a → C zero a y → C zero a (Ω+ y)
Ω+∈ {a = a} q c = plus (λ q → suc q) (Ω∈ a q) c

T-ψ⁺ : ∀ {y} → RR y → T y → T (ψ⁺ y)
T-ψ⁺ {y} r t =
  col (v0 _) (Ω+∈ (s≼s z≼) (C-a (s≼s e) t)) (s≼s e) (irr≡ (wf (Ω+ y)) _ (correct⁺ r))
  where e = Ω+-≼ (psi⁺-≽ r)

rr-+ : ∀ {x y} → RR x → T x → RR y → RR (x + y)
rr-+ rx tx rz = rx
rr-+ rx tx (rs r t) = rs (rr-+ rx tx r) (T-+ tx t)
rr-+ {x} rx tx (rl r t st) = rl (λ n → rr-+ rx tx (r n)) (λ n → T-+ tx (t n)) (λ n → +-mono (≼-refl x) (st n))

rr-· : ∀ {x} → RR x → T x → ∀ n → RR (x · n)
rr-· rx tx zero    = rz
rr-· rx tx (suc n) = rr-+ rx tx (rr-· rx tx n)

T-· : ∀ {x} → T x → ∀ n → T (x · n)
T-· tx zero    = C0 _
T-· tx (suc n) = T-+ tx (T-· tx n)

reg→rr : ∀ {y : Ordᶜ zero} → Reg₀ y → RR y
sel→T : ∀ {y : Ordᶜ zero} → Sel y → T y
sel→T {y} c = C-a (s≼s (add-≽ʳ Ω₁ (λ q → suc q) y)) c
reg→rr (rσ ())
reg→rr rz = rz
reg→rr (rs r c) = rs (reg→rr r) (sel→T c)
reg→rr (rl r c st) = rl (λ n → reg→rr (r n)) (λ n → sel→T (c n)) st

reg-≅ : ∀ {x y : Ordᶜ zero} → x ≅ y → Reg₀ x → Reg₀ y
reg-≅ e (rσ ())
reg-≅ z≅ rz = rz
reg-≅ (s≅ e) (rs r c) = rs (reg-≅ e r) (cg (≅→≈ᵛ (≅-sym e)) (C-a (s≼s (≅→≼ e)) c))
reg-≅ (l≅ h) (rl r c st) =
  rl (λ n → reg-≅ (h n) (r n))
     (λ n → cg (≅→≈ᵛ (≅-sym (h n))) (C-a (s≼s (≅→≼ (h n))) (c n)))
     (λ n → ≼-trans (s≼s (≅→≼ (≅-sym (h n)))) (≼-trans (st n) (≅→≼ (h (suc n)))))

reg-Fδ : ∀ n → Reg₀ (Fδ n)
reg-Fδ n = reg-ψ (reg-≅ (γ≅δ n) (reg-γ n))

sel-δ : ∀ n → Sel (δ n)
sel-δ n = cg (≅→≈ᵛ (≅-sym (γ≅δ n))) (C-a (s≼s (≅→≼ (γ≅δ n))) (N→Sel (n-γ n)))

sel-Fδ : ∀ n → Sel (Fδ n)
sel-Fδ n = sel-ψ (reg-≅ (γ≅δ n) (reg-γ n)) (sel-δ n)

rr-ψ⁺ : ∀ {y} → RR y → RR (ψ⁺ y)
rr-ψ⁺ rz = rl (λ n → reg→rr (reg-Fδ n)) (λ n → sel→T (sel-Fδ n)) st-δ
rr-ψ⁺ {suc b} (rs r t) = rl (rr-· (rr-ψ⁺ r) (T-ψ⁺ r t)) (T-· (T-ψ⁺ r t)) (·-strict (1≼ψ⁺ b))
rr-ψ⁺ {lim f} (rl r t st) =
  rl (λ n → rr-ψ⁺ (r n)) (λ n → T-ψ⁺ (r n) (t n))
     (λ n → step-from (correct⁺ (r n)) (correct⁺ (r (suc n))) (Ω+-≺ (st n))
                      (Ω+∈ (≼-trans (s≼s z≼) (Ω+-≺ (st n))) (C-a (Ω+-≺ (st n)) (t n)))
                      (v0 _))
```

## §2 链 $\eta$

```agda
η : ℕ → Ordᶜ zero
η zero    = 𝟏
η (suc n) = ψ⁺ (η n)

rr-η : ∀ n → RR (η n)
rr-η zero    = rs rz (C0 _)
rr-η (suc n) = rr-ψ⁺ (rr-η n)

t-η : ∀ n → T (η n)
t-η zero    = one∈ _ (s≼s z≼)
t-η (suc n) = T-ψ⁺ (rr-η n) (t-η n)

nr-η : ∀ n → NR (η n)
η-step : ∀ n → η n ≺ᵛ η (suc n)
η-step n = ub (correct⁺ (rr-η n)) (nr-η n) (bnd⁰ (η n))
nr-η zero    = one∈ _ (s≼s z≼)
nr-η (suc n) = col (v0 _) (Ω+∈ (≼-trans (s≼s z≼) e) (C-a (≺→≼ e) (nr-η n))) e
                   (irr≡ (wf (Ω+ (η n))) _ (correct⁺ (rr-η n)))
  where
  e : Ω+ (η n) ≺ᵛ Ω+ (ψ⁺ (η n))
  e = Ω+-≺ (η-step n)

Fη : ℕ → Ordᶜ zero
Fη n = ψ⁺ (η n)

Fη-step : ∀ n → Fη n ≺ᵛ Fη (suc n)
Fη-step n = η-step (suc n)

tη : Ordᶜ zero
tη = lim Fη

tη-prin : Prin tη
tη-prin = Flim-prin Fη-step (λ i → ψ̂-prin (correct⁺ (rr-η i)))
```

## §3 辅助: 下标的值

`forget u ≼ 0` 时 $\Omega_{u+1}\preccurlyeq\Omega_1$: 这种 $u$ 没有字面的前驱, 第 $u$ 层的树都没有 `limᵢ`. `1 ≼ forget u` 时 $\Omega_1\preccurlyeq\Omega_u$, 且 $u$ 有字面的前驱. 这两条把规格里的任意下标 $u$ 落到 "0 还是 $\ge1$" 上, 不比较两个下标.

```agda
lit⊥ : ∀ {j u} → j <ᴵ u → ¬ (forget u ≼ 𝟎 {zero})
lit⊥ zero ()
lit⊥ (suc q) ()
lit⊥ (lim n q) (l≼ h) = lit⊥ q (h n)

low : ∀ {u} → forget u ≼ 𝟎 {zero} → ∀ (x : Ordᶜ u) → x ≅ x → x ≼ ret x
low h zero e = z≼
low h (suc x) (s≅ e) = s≼s (low h x e)
low h (lim f) (l≅ k) = l≼ (λ n → ≼l n (low h (f n) (k n)))
low h (limᵢ q f) e = ⊥-elim (lit⊥ q h)
low () (up zero y) e
low (l≼ h) (up (self n) y) e = u≼ (low (h n) y (up-self (self n) e))

Ω⁺≼Ω₁ : ∀ {u} → forget u ≼ 𝟎 {zero} → Ω (suc u) ≼ Ω₁
Ω⁺≼Ω₁ h = i≼ (λ x ex → u≼ (≼-trans (low h x ex) (≺→≼ (bnd⁰ (ret x)))))

Ω₁≼Ωu : ∀ u → 𝟏 {zero} ≼ forget u → Ω₁ ≼ Ω u
Ω₁≼Ωu zero ()
Ω₁≼Ωu (suc w) e = i≼ (λ x ex → u≼ (≼i (emb x) (emb-≅ x) (≼u (≼emb x))))
Ω₁≼Ωu (lim f s) (≼l n p) = ≼l n (≼u (Ω₁≼Ωu (f n) p))

lit : ∀ u → 𝟏 {zero} ≼ forget u → Σ Ordᴵ λ j → j <ᴵ u
lit zero ()
lit (suc w) e = w , zero
lit (lim f s) (≼l n p) with lit (f n) p
... | j , q = j , lim n q

+-assoc′ : ∀ {k ℓ} (a b : Ordᶜ ℓ) (σ : Simᴵ k ℓ) (c : Ordᶜ k) → a + add b σ c ≼ add (a + b) σ c
+-assoc′ a b σ zero    = ≼-refl _
+-assoc′ a b σ (suc c) = s≼s (+-assoc′ a b σ c)
+-assoc′ a b σ (lim f) = l≼ (λ n → ≼l n (+-assoc′ a b σ (f n)))
+-assoc′ a b σ (limᵢ q f) = i≼ (λ x ex → ≼i x ex
  (subst₂ (λ u w → a + add b σ (f w) ≼ add (a + b) σ (f u))
          (sym (coe-into (<→◃ (σ q)) (<→◃ q) x))
          (sym (trans (cong (coe (<→◃ (σ q)) (<→◃ q)) (coe-into (<→◃ (σ q)) (<→◃ (σ q)) x)) (coe-into (<→◃ (σ q)) (<→◃ q) x)))
          (+-assoc′ a b σ (f (into (<→◃ q) x)))))
+-assoc′ a b σ (up zero x)     = +-assoc′ a b _ x
+-assoc′ a b σ (up (self n) x) = +-assoc′ a b _ x
```

## §4 托架

不变量是四条的积: `E` ($0$ 还是 $\ge1$), `D` ($<\Omega$ 还是 $\ge\Omega$), `A` ($<\Omega\Rightarrow<t$), `B` ($<\Omega+\Omega\Rightarrow$ 落在某个 $\Omega+\eta_n$ 以下). `E`, `D` 是判定, 但只对 $C_0$ 的成员: $v=0$ 时基底只有 $0$, 没有壁垒的问题 (比较 `gap→LPO`).

```agda
ΩΩ : Ordᶜ L₁
ΩΩ = Ω₁ + Ω₁

record J {m} (x : Ordᶜ m) : Set where
  constructor j
  field
    jE : (x ≼ 𝟎 {zero}) ⊎ (𝟏 {zero} ≼ x)
    jD : (x ≺ᵛ Ω₁) ⊎ (Ω₁ ≼ x)
    jA : BndI zero tη x
    jB : x ≺ᵛ ΩΩ → Σ ℕ λ n → x ≼ Ω+ (η n)
open J

η≺tη : ∀ i → η i ≺ᵛ tη
η≺tη i = ≼l i (η-step i)

≼η⁺ : ∀ {m} {x : Ordᶜ m} → x ≺ᵛ tη → Σ ℕ λ n → x ≼ η n
≼η⁺ (≼l n r) = suc n , ≺→≼ r

absorb : ∀ (z : Ordᶜ zero) → (up zero z) + Ω₁ ≼ Ω₁
absorb z = i≼ (λ x ex → ≼i (z + x) (≅-refl⁰ (z + x)) (≼u (add-mono (u≼ (≼-refl z)) (u≼ (≼-refl x)))))

j-b : ∀ {m} {x : Ordᶜ m} → x ≺ᵛ Ω zero → J x
j-b (s≼s q) = j (inj₁ q) (inj₁ (≼-≺ q (0≺Ω L₁)))
  (λ _ → ≼l 0 (≼-trans (s≼s q) (1≼ψ⁺ (η 0))))
  (λ _ → 0 , ≼-trans q z≼)

j-g : ∀ {m n} {x : Ordᶜ m} {y : Ordᶜ n} → y ≈ᵛ x → J x → J y
j-g (e , e′) (j jE jD jA jB) = j
  (case-E jE) (case-D jD) (Bnd-cg (e , e′) jA)
  (λ b → let i , d = jB (≼-≺ e′ b) in i , ≼-trans e d)
  where
  case-E : _ → _
  case-E (inj₁ p) = inj₁ (≼-trans e p)
  case-E (inj₂ p) = inj₂ (≼-trans p e′)
  case-D : _ → _
  case-D (inj₁ p) = inj₁ (≼-≺ e p)
  case-D (inj₂ p) = inj₂ (≼-trans p e′)

j-p : ∀ {m k} {x : Ordᶜ m} {y : Ordᶜ k} (σ : Simᴵ k m) → J x → J y → J (add x σ y)
j-p {x = x} {y = y} σ ix iy = j cE cD (Bnd-plus tη-prin σ (jA ix) (jA iy)) cB
  where
  cE : (add x σ y ≼ 𝟎 {zero}) ⊎ (𝟏 {zero} ≼ add x σ y)
  cE with jE ix | jE iy
  ... | inj₁ p | inj₁ q = inj₁ (add-mono {σ′ = λ r → r} p q)
  ... | inj₂ p | _      = inj₂ (≼-trans p (add-≽ˡ x σ y))
  ... | inj₁ _ | inj₂ q = inj₂ (≼-trans q (add-≽ʳ x σ y))
  cD : (add x σ y ≺ᵛ Ω₁) ⊎ (Ω₁ ≼ add x σ y)
  cD with jD ix | jD iy
  ... | inj₁ p | inj₁ q = inj₁ (Ω-prin L₁ σ p q)
  ... | inj₂ p | _      = inj₂ (≼-trans p (add-≽ˡ x σ y))
  ... | inj₁ _ | inj₂ q = inj₂ (≼-trans q (add-≽ʳ x σ y))
  cB : add x σ y ≺ᵛ ΩΩ → Σ ℕ λ n → add x σ y ≼ Ω+ (η n)
  cB b with jB ix (≼-≺ (add-≽ˡ x σ y) b) | jD iy
  ... | i , dx | inj₁ yΩ =
    let k′ , dy = ≼η⁺ (jA iy yΩ)
        n′ , dn = ≼η⁺ (tη-prin (λ q → q) (η≺tη i) (η≺tη k′))
    in n′ , ≼-trans (add-mono {σ′ = λ q → suc q} dx dy)
            (≼-trans (+-assoc Ω₁ (up zero (η i)) (λ q → suc q) (η k′))
                     (add-mono {σ = λ q → q} {σ′ = λ q → suc q} (≼-refl Ω₁) (≼-trans (add-mono {σ = λ q → suc q} {σ′ = λ q → q} (u≼ (≼-refl (η i))) (≼-refl (η k′))) dn)))
  ... | i , dx | inj₂ Ωy with jD ix
  ...   | inj₂ Ωx = ⊥-elim (≺ᵛ-irrefl (add x σ y) (≼-trans b (add-mono {σ = λ q → q} {σ′ = σ} Ωx Ωy)))
  ...   | inj₁ xΩ with bd⇒ xΩ | jB iy (≼-≺ (add-≽ʳ x σ y) b)
  ...     | z , ez , dz | i′ , dy =
    i′ , ≼-trans (add-mono {σ′ = λ q → q} (≼-trans (≺→≼ dz) (≼u (≼-refl z))) dy)
         (≼-trans (+-assoc′ (up zero z) Ω₁ (λ q → suc q) (η i′))
                  (add-mono {σ = λ q → suc q} {σ′ = λ q → suc q} (absorb z) (≼-refl (η i′))))

j-c : ∀ {u m n} {ξ : Ordᶜ m} {w : Ordᶜ n} → (w ≺ᵛ Ω (suc zero) → w ≺ᵛ tη) →
      (q : ξ ≺ᵛ ΩΩ) → Recₐ ΩΩ (wf ΩΩ) u ξ q w → J (forget u) → J ξ → J w
j-c {u} {ξ = ξ} {w = w} h q r iu iξ = j (inj₂ (1≼ψ̂ ac r)) cD h cB
  where
  ac = belowᵛ ΩΩ ξ q
  ΩΩ≺Ω₂ : ΩΩ ≺ᵛ Ω (suc L₁)
  ΩΩ≺Ω₂ = ⇒bd ΩΩ (add-≅ (Ω-refl L₁) (Ω-refl L₁)) (≼-refl ΩΩ)
  low-case : forget u ≼ 𝟎 {zero} → w ≺ᵛ Ω₁
  low-case fu = ≼-trans (lt′ ac r) (Ω⁺≼Ω₁ fu)
    where
    lt′ : ∀ {k} {ξ : Ordᶜ k} (ac : Acc ξ) → IsPsiₐ u ξ ac w → w ≺ᵛ Ω (suc u)
    lt′ (acc _) s = lt s
  cD : (w ≺ᵛ Ω₁) ⊎ (Ω₁ ≼ w)
  cD with jE iu
  ... | inj₁ fu = inj₁ (low-case fu)
  ... | inj₂ fu = inj₂ (≼-trans (Ω₁≼Ωu u fu) (Ω-floor ac r))
  cB : w ≺ᵛ ΩΩ → Σ ℕ λ n → w ≼ Ω+ (η n)
  cB b with jE iu
  ... | inj₁ fu = let n′ , d = ≼η⁺ (h (low-case fu)) in n′ , ≼-trans d (add-≽ʳ Ω₁ (λ q → suc q) (η n′))
  ... | inj₂ fu with jE iξ
  ...   | inj₁ ξ0 = 0 , ≼-trans (col-bound ac ΩO-1 ξ0 r (T0 L₁) (≼-≺ (≺→≼ b) ΩΩ≺Ω₂)) (add-≽ˡ Ω₁ (λ q → suc q) (η 0))
  ...   | inj₂ ξ1 = ⊥-elim (≺ᵛ-irrefl w (≼-trans b (≼-trans (≼l 2 (≼-refl ΩΩ)) big)))
    where
    bw : ψ₁ 𝟏 ≺ᵛ Ω (suc u)
    bw with lit u fu
    ... | j′ , q′ = ⇒bd (E.E₁ q′ (ψ₁ 𝟏)) (E.E-≅ q′ (ψ-≅ {p = zero} {σ = λ ()} {p′ = zero} {σ′ = λ ()} (≅ᴵ-refl L₁) (s≅ z≅)))
                       (E.≼E q′ (ψ₁ 𝟏) (ψ-≅ {p = zero} {σ = λ ()} {p′ = zero} {σ′ = λ ()} (≅ᴵ-refl L₁) (s≅ z≅)))
    big : ψ₁ 𝟏 ≼ w
    big = ψ̂-mono (wf (𝟏 {zero})) ac (Ω₁≼Ωu u fu) ξ1 ψ₁1 r bw

Bk : Bracket {zero} {L₁} {zero} ΩΩ Fη {lv = λ _ → L₁} (λ i → Ω+ (η i))
Bk = record
  { I = J ; i-b = j-b ; i-p = j-p ; i-g = j-g ; i-ub = jA ; i-br = jB ; i-c = j-c }

anchor-ΩΩ-η : IsPsi zero ΩΩ tη
anchor-ΩΩ-η = Tchain {f̂ = λ i → Ω+ (η i)} ΩO-0 (λ i → ≼i (η i) (≅-refl⁰ (η i)) (≼-refl (Ω+ (η i))))
  (λ i → correct⁺ (rr-η i)) Fη-step Bk
```

折叠的字面输出 $\psi^0(\Omega+\Omega)$ 的链是 `η′`, 与 `η` 只差 $\psi$ 与 $\psi^0$.

```agda
η′ : ℕ → Ordᶜ zero
η′ = iter (λ x → ψ {i = zero} {k = L₁} {ℓ = L₁} zero (λ r → r) (Ω+ x)) (Ω zero)

η≅η′ : ∀ n → η n ≅ η′ n
η≅η′ zero    = s≅ z≅
η≅η′ (suc n) = ψ⁰≅ψ {ℓ = L₁} {p = zero} {σ = λ r → r} (add-≅ (Ω-refl L₁) (η≅η′ n))

ψΩΩ≡ : ψ⁰ ΩΩ ≡ lim (λ n → ψ⁺ (η′ n))
ψΩΩ≡ = refl

tη≅ : tη ≅ ψ⁰ ΩΩ
tη≅ = l≅ (λ n → ψ⁰-≅ (add-≅ (Ω-refl L₁) (η≅η′ n)))

anchor-ΩΩ : IsPsi zero ΩΩ (ψ⁰ ΩΩ)
anchor-ΩΩ = IsPsi-t (≅→≈ᵛ tη≅) anchor-ΩΩ-η
```
