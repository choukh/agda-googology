# 折叠是和的作用: 验收

> **验收文件.** 只有这里读 `NoCumsum`, `Label` 一带. 入口 [TLRule](TLRule.lagda.md). 判决: **HOLDS**, 档次是序数值验收 (互相 $\preccurlyeq$). 主定理 `T≈`:
>
>     fr (ord Top) ≈ᵛ BTBOᴵ
>
> 新树的每个层都是**不带证书**的和. 对同一个层 $a$, 新折叠与旧折叠结构只差极限开头的项 (`Co-Ψ`, [TLRuleMain](TLRuleMain.lagda.md)); 层不同时用 `BTBOFull` 现成的保序映射 (`Bump`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLRuleAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Data.Sum using (_⊎_)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Align.Level hiding (below)
import OCF.Align.NoCumsum as NC
open NC using (BTBOᴵ)
open import OCF.Align.Value using (_≼_; _≈ᵛ_; z≼; s≼s; ≼l; l≼; ≼-refl; ≼-trans; ≅→≼; ≼-suc)
open import OCF.Align.Uniform using (Uniform)
open import OCF.Align.BTBOValNeg using (≺ᴵ→s≼; <→s≼; ≼-irr; forget-≅ᴵ; HS-≅; two-preds)
open import OCF.Align.BTBOFullEmb using (PEmb; Ψ-emb)
open import OCF.Align.BTBOFullEb using (V2)
open import OCF.Align.BTBOFullV3 using (V3; bkᴵ)
open import OCF.Align.BTBOFullV1 using (V1; PW₁; PW₂; PW₃)
open import OCF.Align.BTBOFullLv using (SV; svz; svs; svl; SV-≅; SV-L; pos-L; Pos; ps; pl; pos≺; posF; z<SV; St-F; SV-toLevel; ⊑→≼f)
open import OCF.Align.BTBOFull using (St-bk; tr₀-bk; γ-step)
open import OCF.Align.BTBOValBase using (tr₀)
import OCF.Free.Level as FL
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; Lg; ψ₀Ω; O; os; ol; o0)
import OCF.Align.CumReadCF as C
open import OCF.Align.CumReadCFEq using (_≈_)
open import OCF.Align.CumReadCFThm using (ord; ≈→≅; Y)
open import OCF.Align.CumUpAcceptSim using (Ix; iz; is; il; fr; Y-sim; ⊲→⊑)
import OCF.Align.TLRuleSum as N
open N using (cell; Ψ; Lg-Ψ; Top; ys)
open import OCF.Align.TLRuleMain using (Co; cz; cs; cl′; cd; ce; ce′; Co-Ψ)
open import OCF.Align.TLRuleDiag using (cellΣ; TopΣ; Lg-TopΣ; u; lu)
open import OCF.Align.TLRuleDiagRel using (coΣ)
```

## §1 层的对应

`VE a b`: 两个层同形, $b$ 的极限可以多开头的项. 前驱互相对上, 值相等.

```agda
data VE : Ordᴵ → Ordᴵ → Set where
  vz : VE zero zero
  vs : ∀ {a b} → VE a b → VE (suc a) (suc b)
  vl : ∀ {f g s t} → (∀ n → VE (f n) (g n)) → VE (lim f s) (lim g t)
  vd : ∀ {a} {g : ℕ → Ordᴵ} {t t′} → VE a (lim (λ m → g (suc m)) t′) → VE a (lim g t)
  vr : ∀ {a b b′} → VE a b → b ≅ᴵ b′ → VE a b′
  vL : ∀ {a a′ b} → a′ ≅ᴵ a → VE a b → VE a′ b

VE-refl : ∀ a → VE a a
VE-refl zero = vz
VE-refl (suc a) = vs (VE-refl a)
VE-refl (lim f s) = vl (λ n → VE-refl (f n))

Eqv : Ordᴵ → Ordᴵ → Set
Eqv c c′ = forget c ≼ forget c′ × forget c′ ≼ forget c

VEv : ∀ {a b} → VE a b → Eqv a b
VEv vz = z≼ , z≼
VEv (vs d) = s≼s (proj₁ (VEv d)) , s≼s (proj₂ (VEv d))
VEv (vl h) = l≼ (λ n → ≼l n (proj₁ (VEv (h n)))) , l≼ (λ n → ≼l n (proj₂ (VEv (h n))))
VEv (vd {g = g} {t} {t′} d) =
  ≼-trans (proj₁ (VEv d)) (l≼ (λ n → ≼l (suc n) (≼-refl _))) ,
  ≼-trans (l≼ go) (proj₂ (VEv d))
  where
  go : ∀ n → forget (g n) ≼ forget (lim (λ m → g (suc m)) t′)
  go zero = ≼l 0 (⊑→≼f (t 0))
  go (suc n) = ≼l n (≼-refl _)
VEv (vr d e) = ≼-trans (proj₁ (VEv d)) (≅→≼ (forget-≅ᴵ e)) , ≼-trans (≅→≼ (forget-≅ᴵ (≅ᴵ-sym e))) (proj₂ (VEv d))
VEv (vL e d) = ≼-trans (≅→≼ (forget-≅ᴵ e)) (proj₁ (VEv d)) , ≼-trans (proj₂ (VEv d)) (≅→≼ (forget-≅ᴵ (≅ᴵ-sym e)))

fwd : ∀ {a b c} → VE a b → c <ᴵ a → Σ Ordᴵ (λ c′ → c′ ≺ᴵ b × VE c c′)
fwd (vs d) zero = _ , via (≅ᴵ-refl _) zero , d
fwd (vs d) (suc q) with fwd d q
... | c′ , via e r , v = c′ , via e (suc r) , v
fwd (vl h) (lim n q) with fwd (h n) q
... | c′ , via e r , v = c′ , via e (lim n r) , v
fwd (vd d) q with fwd d q
... | c′ , via e (lim n r) , v = c′ , via e (lim (suc n) r) , v
fwd (vr d e) q with fwd d q
... | c′ , r , v = c′ , ≺ᴵ-respʳ r e , v
fwd (vL e d) q with <-≅ q e
... | via e′ q′ with fwd d q′
...   | c′ , r , v = c′ , r , vL e′ v

fwd≺ : ∀ {a b c} → VE a b → c ≺ᴵ a → Σ Ordᴵ (λ c′ → c′ ≺ᴵ b × VE c c′)
fwd≺ d (via e q) with fwd d q
... | c′ , r , v = c′ , r , vL e v

bwd : ∀ {a b c′} → VE a b → c′ <ᴵ b → Σ Ordᴵ (λ c → c ≺ᴵ a × VE c c′)
bwd (vs d) zero = _ , via (≅ᴵ-refl _) zero , d
bwd (vs d) (suc q) with bwd d q
... | c , via e r , v = c , via e (suc r) , v
bwd (vl h) (lim n q) with bwd (h n) q
... | c , via e r , v = c , via e (lim n r) , v
bwd (vd d) (lim (suc n) q) = bwd d (lim n q)
bwd (vd {t = t} d) (lim zero q) with sim (t 0) q
... | via e q′ with bwd d (lim 0 q′)
...   | c , r , v = c , r , vr v (≅ᴵ-sym e)
bwd (vr d e) q with <-≅ q (≅ᴵ-sym e)
... | via e′ q′ with bwd d q′
...   | c , r , v = c , r , vr v (≅ᴵ-sym e′)
bwd (vL e d) q with bwd d q
... | c , r , v = c , ≺ᴵ-respʳ r (≅ᴵ-sym e) , v

bwd≺ : ∀ {a b c′} → VE a b → c′ ≺ᴵ b → Σ Ordᴵ (λ c → c ≺ᴵ a × VE c c′)
bwd≺ d (via e q) with bwd d q
... | c , r , v = c , r , vr v (≅ᴵ-sym e)
```

## §2 前驱对上就有保序映射

比较走有界三歧, 矛盾走值. 不判定值.

```agda
PE : ∀ {a b} (M : ∀ {c} → c ≺ᴵ a → Σ Ordᴵ (λ c′ → c′ ≺ᴵ b × Eqv c c′)) → PEmb a b
PE {a} {b} M = record { map = m ; bnd = bd ; mono = mn ; coh = ch }
  where
  m : ∀ {c} → c ≺ᴵ a → Ordᴵ
  m r = proj₁ (M r)
  bd : ∀ {c} (r : c ≺ᴵ a) → m r ≺ᴵ b
  bd r = proj₁ (proj₂ (M r))
  ev : ∀ {c} (r : c ≺ᴵ a) → Eqv c (m r)
  ev r = proj₂ (proj₂ (M r))
  mn : ∀ {c d} (r : c ≺ᴵ a) (s : d ≺ᴵ a) → c ≺ᴵ d → m r ≺ᴵ m s
  mn r s x with two-preds (bd r) (bd s)
  ... | injᵃ y = y
  ... | injᵇ y = ⊥-elim (≼-irr (forget (m r))
          (≼-trans (s≼s (proj₂ (ev r))) (≼-trans (≺ᴵ→s≼ x) (≼-trans (proj₁ (ev s))
            (≼-trans (≼-suc (≼-refl _)) (≺ᴵ→s≼ y))))))
  ... | injᶜ y = ⊥-elim (≼-irr (forget (m r))
          (≼-trans (s≼s (proj₂ (ev r))) (≼-trans (≺ᴵ→s≼ x) (≼-trans (proj₁ (ev s)) (≅→≼ (forget-≅ᴵ (≅ᴵ-sym y)))))))
  ch : ∀ {c d} (r : c ≺ᴵ a) (s : d ≺ᴵ a) → c ≅ᴵ d → m r ≅ᴵ m s
  ch r s x with two-preds (bd r) (bd s)
  ... | injᵃ y = ⊥-elim (≼-irr (forget (m r))
          (≼-trans (≺ᴵ→s≼ y) (≼-trans (proj₂ (ev s)) (≼-trans (≅→≼ (forget-≅ᴵ (≅ᴵ-sym x))) (proj₁ (ev r))))))
  ... | injᵇ y = ⊥-elim (≼-irr (forget (m s))
          (≼-trans (≺ᴵ→s≼ y) (≼-trans (proj₂ (ev r)) (≼-trans (≅→≼ (forget-≅ᴵ x)) (proj₁ (ev s))))))
  ... | injᶜ y = y

PEf : ∀ {a b} → VE a b → PEmb a b
PEf d = PE (λ r → let c′ , q , v = fwd≺ d r in c′ , q , VEv v)

PEb : ∀ {a b} → VE a b → PEmb b a
PEb d = PE (λ r → let c , q , v = bwd≺ d r in c , q , (proj₂ (VEv v) , proj₁ (VEv v)))
```

## §3 严格性沿对应

```agda
mk⊑ : ∀ {a b} → (∀ {e} → e <ᴵ a → e ≺ᴵ b) → a ⊑ᴵ b
mk⊑ {a = zero} σ = z⊑
mk⊑ {a = suc a} σ with σ zero
... | via e q = s⊑ e q
mk⊑ {a = lim f s} σ = l⊑ (λ n → mk⊑ (λ q → σ (lim n q)))

SV-VE : ∀ {a b} → VE a b → SV b → SV a
SV-VE vz svz = svz
SV-VE (vs d) (svs u) = svs (SV-VE d u)
SV-VE (vl {f = f} {g} {s} {t} h) (svl u st) = svl (λ n → SV-VE (h n) (u n)) st′
  where
  st′ : ∀ n → Σ Ordᴵ (λ c → c ≺ᴵ f (suc n) × f n ⊑ᴵ c)
  st′ n with st n
  ... | c , r , k with bwd≺ (h (suc n)) r
  ...   | c₁ , r₁ , v₁ = c₁ , r₁ , mk⊑ σ
    where
    fn≼c₁ : forget (f n) ≼ forget c₁
    fn≼c₁ = ≼-trans (proj₁ (VEv (h n))) (≼-trans (⊑→≼f k) (proj₂ (VEv v₁)))
    σ : ∀ {e} → e <ᴵ f n → e ≺ᴵ c₁
    σ {e} q with two-preds (sim (s n) q) r₁
    ... | injᵃ y = y
    ... | injᵇ y = ⊥-elim (≼-irr (forget e) (≼-trans (<→s≼ q) (≼-trans fn≼c₁ (≼-trans (≼-suc (≼-refl _)) (≺ᴵ→s≼ y)))))
    ... | injᶜ y = ⊥-elim (≼-irr (forget e) (≼-trans (<→s≼ q) (≼-trans fn≼c₁ (≅→≼ (forget-≅ᴵ (≅ᴵ-sym y))))))
SV-VE (vd d) (svl u st) = SV-VE d (svl (λ n → u (suc n)) (λ n → st (suc n)))
SV-VE (vr d e) u = SV-VE d (SV-≅ e u)
SV-VE (vL e d) u = SV-≅ e (SV-VE d u)

Pos-VE : ∀ {a b} → VE a b → SV b → Pos b → Pos a
Pos-VE d u p = pos≺ (proj₁ (proj₂ (bwd d (z<SV u p))))
```

## §4 从第 0 层的对应到层的对应

```agda
fr≅ : ∀ {x y : FL.Ordᶜ FL.zero} → x FL.≅ y → fr x ≅ fr y
fr≅ FL.z≅ = z≅
fr≅ (FL.s≅ e) = s≅ (fr≅ e)
fr≅ (FL.l≅ h) = l≅ (λ n → fr≅ (h n))
fr≅ (FL.lᵢ≅ {p = ()} e h)
fr≅ (FL.upˡ {r = ()} e)
fr≅ (FL.upʳ {r = ()} e)

lv    : (a : A) → Lg a → Ordᴵ
Ix-lv : ∀ a (w : Lg a) → Ix a (lv a w)
lv azero w = zero
lv (asuc a) w = suc (lv a w)
lv (alim f) (st , ws) = lim (λ n → lv (f n) (ws n)) (λ n → ⊲→⊑ (st n) (Ix-lv (f n) (ws n)) (Ix-lv (f (suc n)) (ws (suc n))))
Ix-lv azero w = iz
Ix-lv (asuc a) w = is (Ix-lv a w)
Ix-lv (alim f) (st , ws) = il (λ n → Ix-lv (f n) (ws n))

forget-lv : ∀ a (w : Lg a) → fr (N.ord a) ≅ forget (lv a w)
forget-lv azero w = z≅
forget-lv (asuc a) w = s≅ (forget-lv a w)
forget-lv (alim f) (st , ws) = l≅ (λ n → forget-lv (f n) (ws n))

frO : O azero → Ordᶜ zero
frO y = fr (ord y)

CoV : ∀ {a y} → Co a y → (w : Lg a) (h : HS (frO y)) → VE (lv a w) (toLevel (frO y) h)
CoV cz w h = vz
CoV (cs d) w h = vs (CoV d w (hs⁻ h))
CoV (cl′ k) (st , ws) h = vl (λ n → CoV (k n) (ws n) (hl₁ h n))
CoV (cd g d) w h = vd (CoV d w (hl (λ n → hl₁ h (suc n)) (λ n → hl₂ h (suc n))))
CoV (ce {y = y} {y′} d e) w h′ =
  let E = fr≅ (≈→≅ y y′ e) in vr (CoV d w (HS-≅ E h′)) (toLevel-≅ (HS-≅ E h′) h′ E)
CoV (ce′ {y = y} {y′} d e) w h′ =
  let E = fr≅ (≈→≅ y′ y e) in vr (CoV d w (HS-≅ (≅-sym E) h′)) (toLevel-≅ (HS-≅ (≅-sym E) h′) h′ (≅-sym E))
```

## §5 层不同

`Bump`: 值 $a\preccurlyeq b$ 就有 $\psi^0(\Omega_a)\preccurlyeq\psi^0(\Omega_{\psi^0(\Omega_b)})$. 三步都是 `BTBOFull` 现成的.

```agda
Fψ : Ordᴵ → Ordᶜ zero
Fψ x = ψ⁰ (Ω x)

toFψ : Ordᴵ → Ordᴵ
toFψ x = toLevel (Fψ x) (Uniform x)

Bump : ∀ {a b} → SV a → SV b → forget a ≼ forget b → Fψ a ≼ Fψ (toFψ b)
Bump {a} {b} sa sb v =
  ≼-trans (Ψ-emb (PW₃ (V1 sa)))
  (≼-trans (Ψ-emb (PW₁ (V2 (bkᴵ a) (bkᴵ b) (St-bk sa) (St-bk sb)
                     (≼-trans (≅→≼ (tr₀-bk a)) (≼-trans v (≅→≼ (≅-sym (tr₀-bk b))))))))
           (Ψ-emb (PW₂ (Uniform b) (V3 sb))))

Fψ≅ : ∀ {x y} → x ≅ᴵ y → Fψ x ≼ Fψ y
Fψ≅ {x} e = Ψ-emb (PEf (vr (VE-refl x) e))
```

## §6 对角线

对任何一条层的序列, 只要第 0 项是 $1$, 相邻项由 `Co` 对上旧折叠. 新树的两条对角线 (`cell`, [TLRuleDiag](TLRuleDiag.lagda.md)) 都是实例.

```agda
module Diag (u : ℕ → A) (lu : ∀ n → Lg (u n)) (u₀ : u 0 ≡ asuc azero) (co : ∀ n → Co (u (suc n)) (ψ₀Ω (u n) (lu n))) where

  a : ℕ → Ordᴵ
  a n = lv (u n) (lu n)

  a₀V : VE (a 0) (suc zero)
  a₀V = go (u 0) (lu 0) u₀
    where
    go : ∀ x (w : Lg x) → x ≡ asuc azero → VE (lv x w) (suc zero)
    go .(asuc azero) w refl = vs vz

  SP   : ∀ n → SV (a n) × Pos (a n)
  STEP : ∀ n → VE (a (suc n)) (toFψ (a n))

  STEP n =
    let E = Y-sim (lu n) (Ix-lv (u n) (lu n)) (z<SV (proj₁ (SP n)) (proj₂ (SP n)))
        h = HS-≅ E (Uniform (a n))
    in vr (CoV (co n) (lu (suc n)) h) (toLevel-≅ h (Uniform (a n)) E)

  SP zero = SV-VE a₀V (svs svz) , Pos-VE a₀V (svs svz) ps
  SP (suc n) =
    SV-VE (STEP n) sv′ , Pos-VE (STEP n) sv′ (posF (a n) (Uniform (a n)))
    where
    sv′ : SV (toFψ (a n))
    sv′ = SV-toLevel (Fψ (a n)) (Uniform (a n)) (St-F (proj₁ (SP n)) (proj₂ (SP n)))

  fa≼ : ∀ n → forget (a (suc n)) ≼ Fψ (a n)
  fa≼ n = ≼-trans (proj₁ (VEv (STEP n))) (≅→≼ (forget-toLevel (Fψ (a n)) (Uniform (a n))))

  ≼fa : ∀ n → Fψ (a n) ≼ forget (a (suc n))
  ≼fa n = ≼-trans (≅→≼ (≅-sym (forget-toLevel (Fψ (a n)) (Uniform (a n))))) (proj₂ (VEv (STEP n)))

  Lv : ℕ → Ordᴵ
  Lv = NC.L

  γ≼L : ∀ m → NC.γ m ≼ forget (Lv m)
  γ≼L m = ≅→≼ (≅-sym (forget-toLevel (NC.γ m) (NC.cert m)))

  L≼γ : ∀ m → forget (Lv m) ≼ NC.γ m
  L≼γ m = ≅→≼ (forget-toLevel (NC.γ m) (NC.cert m))

  toF≅ : ∀ m → toFψ (Lv m) ≅ᴵ Lv (suc m)
  toF≅ m = toLevel-≅ (Uniform (Lv m)) (NC.cert (suc m)) (≅-refl⁰ (NC.γ (suc m)))

  g : ℕ → ℕ
  g zero = 0
  g (suc n) = suc (suc (g n))

  Up : ∀ n → forget (a n) ≼ forget (Lv (g n))
  Up zero = proj₁ (VEv a₀V)
  Up (suc n) =
    ≼-trans (fa≼ n)
    (≼-trans (Bump (proj₁ (SP n)) (SV-L (g n)) (Up n))
    (≼-trans (Fψ≅ (toF≅ (g n)))
             (γ≼L (suc (suc (g n))))))

  Dn : ∀ m → forget (Lv m) ≼ forget (a (g m))
  Dn zero = proj₂ (VEv a₀V)
  Dn (suc m) =
    ≼-trans (L≼γ (suc m))
    (≼-trans (Bump (SV-L m) (proj₁ (SP (g m))) (Dn m))
    (≼-trans (Ψ-emb (PEb (STEP (g m))))
             (≼fa (suc (g m)))))

  u≅ : ∀ n → fr (N.ord (u n)) ≅ forget (a n)
  u≅ n = forget-lv (u n) (lu n)

  T≈ᴳ : fr (N.ord (alim (λ n → u (suc n)))) ≈ᵛ BTBOᴵ
  T≈ᴳ =
    l≼ (λ n → ≼l (g (suc n)) (≼-trans (≅→≼ (u≅ (suc n))) (≼-trans (Up (suc n)) (≼-trans (L≼γ (g (suc n))) (γ-step (g (suc n))))))) ,
    l≼ (λ m → ≼l (suc (g m))
       (≼-trans (γ≼L (suc m)) (≼-trans (Dn (suc m)) (≅→≼ (≅-sym (u≅ (suc (suc (g m)))))))))
```

## §7 主定理

```agda
module D₁ = Diag (λ n → proj₁ (cell n)) (λ n → proj₂ (cell n)) refl (λ n → Co-Ψ (proj₁ (cell n)) (proj₂ (cell n)))

T≈ : fr (N.ord Top) ≈ᵛ BTBOᴵ
T≈ = D₁.T≈ᴳ

a : ℕ → Ordᴵ
a = D₁.a

≼fa : ∀ n → Fψ (a n) ≼ forget (a (suc n))
≼fa = D₁.≼fa

module D₂ = Diag (λ n → u (cellΣ n)) (λ n → lu (cellΣ n)) refl coΣ

-- 对角线也是和的那棵: 它自带 Lg
TΣ≈ : fr (N.ord TopΣ) ≈ᵛ BTBOᴵ
TΣ≈ = D₂.T≈ᴳ
```

## §8 差

基本列不同: 新树是和, 第 $n$ 项是部分和, 没有旧树 `rep` 开头的 $0$. 所以结构上不 $\cong$, FGH 在 0 处就不同. 这是编译过的否定, 只否定 $\cong$, 不否定序数值.

```agda
fgh₀ : FGH (fr (N.ord Top)) 0 ≡ 0
fgh₀ = refl

fghB₀ : FGH BTBOᴵ 0 ≡ 1
fghB₀ = refl

T≇ : ¬ (fr (N.ord Top) ≅ BTBOᴵ)
T≇ e with FGH-≅ e 0
... | ()
```
