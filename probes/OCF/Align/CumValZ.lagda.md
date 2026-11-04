# 高度 0 的世界树就是 `CumReadCF` 的树

> 接 [CumUpW](CumUpW.lagda.md), [CumReadCF](CumReadCF.lagda.md). `Bz x c`: 高度 0 的世界树 `𝓞 0 a u` 与 `C.O a` 同构造子相关, 世界透明. `ψ₀-≅`: 同下标上两个折叠逐项 $\cong$. 这条桥只覆盖没有闭包的层, 是 `CumVal` 基线 (`TΩ`) 用的. 全文 `--safe --without-K --lossy-unification`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CumValZ where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
import OCF.Free.Level as FL
open FL using (z≅; s≅; l≅) renaming (_≅_ to _≅₀_; ≅-sym to ≅₀-sym; ≅-trans to ≅₀-trans; ≅-refl⁰ to ≅₀-refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; Strict; ss; sl; Lg; ⊲-tr; z⊲; ≪∘; ≪S; ≪⊲; keep; rise; cmpN; rkT; tgS; lgS; Tg; Rk)
import OCF.Align.CumReadCF as C
open import OCF.Align.CumReadBase using (Ord₀)
open import OCF.Align.CumReadW using (one; Gw; gw; lgw; pos; g₀)
open import OCF.Align.CumReadCFThm using (ord)
open import OCF.Align.CumUpW hiding (ord)
open import OCF.Align.CumUpPsi using (plus≅)

W₀ : A → A → Set
W₀ a u = 𝓞 zero a u

data AccA (a : A) : Set where
  acc : (∀ {b} → b ≪ a → AccA b) → AccA a

accA : ∀ a {b} → b ≪ a → AccA b
accA (asuc a)  C.zero      = acc (accA a)
accA (asuc a)  (C.suc r)   = accA a r
accA (alim f)  (C.lim n r) = accA (f n) r

≪-irr : ∀ {a} → ¬ (a ≪ a)
≪-irr {a} = go (acc (accA a)) where
  go : ∀ {a} → AccA a → ¬ (a ≪ a)
  go (acc h) r = go (h r) r

clash : ∀ {k t} → k ≪ t → t ⊲ k → ⊥
clash s u = ≪-irr (≪∘ s u)
```

## §1 关系

```agda
module _ (a : A) (B< : ∀ {b} (R : Strict b a) {v} → Vs zero a R v → C.O b → Set) where
  data Bz₊ : ∀ {u} → W₀ a u → C.O a → Set where
    bz : ∀ {u} → Bz₊ {u} o0 C.o0
    bs : ∀ {u} {x : W₀ a u} {c} → Bz₊ x c → Bz₊ (os x) (C.os c)
    bl : ∀ {u} {F : ℕ → W₀ a u} {G} → (∀ n → Bz₊ (F n) (G n)) → Bz₊ (ol F) (C.ol G)
    bi : ∀ {u k} {r r′ : k ≪ a} {h : ∀ {v} → u ⊲ v → Gw v → Vs zero a (≪S r) v → W₀ a v} {h′ : C.Vs a (≪S r′) → C.O a} →
         (∀ {v} (q : u ⊲ v) (g : Gw v) (z : W₀ k v) (z′ : C.O k) → B< (≪S r) (inS (≪S r) z) z′ →
            Bz₊ (h q g (inS (≪S r) z)) (h′ (C.inS (≪S r′) z′))) →
         Bz₊ (oi r h) (C.oi r′ h′)
    be : ∀ {u b} {R : Strict b a} {stp : Stp R} {x : Vs zero a R u} {x′ : C.Vs a R} → B< R x (C.outS R x′) → Bz₊ (oe stp x) (C.oe R x′)
    bow : ∀ {u v} {p : u ⊲ v} {g : Gw u} {x : W₀ a u} {c} → Bz₊ x c → Bz₊ (ow p g x) c

Bz : ∀ {a u} → W₀ a u → C.O a → Set
BS : ∀ a {b} (R : Strict b a) {v} → Vs zero a R v → C.O b → Set
BC : ∀ a {b} (P : b ⊲ a) {v} → Vc zero a P v → C.O b → Set
Bz {a} = Bz₊ a (BS a)
BS (asuc b) (ss P) x c = BC b P x c
BS (alim f) (sl n P) x c = BC (f n) P x c
BC a C.self x c = Bz x c
BC (asuc b) (C.suc P) x c = BC b P x c
BC (alim f) (C.lim n P) x c = BC (f n) P x c

C→B : ∀ {a b u} (P : b ⊲ a) {x : W₀ b u} {c} → BC a P (inC P x) c → Bz x c
C→B C.self d = d
C→B (C.suc P) d = C→B P d
C→B (C.lim n P) d = C→B P d

B→C : ∀ {a b u} (P : b ⊲ a) {x : W₀ b u} {c} → Bz x c → BC a P (inC P x) c
B→C C.self d = d
B→C (C.suc P) d = B→C P d
B→C (C.lim n P) d = B→C P d

S→B : ∀ {a b u} (R : Strict b a) {x : W₀ b u} {c} → BS a R (inS R x) c → Bz x c
S→B (ss P) d = C→B P d
S→B (sl n P) d = C→B P d

B→S : ∀ {a b u} (R : Strict b a) {x : W₀ b u} {c} → Bz x c → BS a R (inS R x) c
B→S (ss P) d = B→C P d
B→S (sl n P) d = B→C P d

B-Ω : ∀ a → Bz (Ω̇ zero a) (C.Ω̇ a)
B-Ω azero    = bs bz
B-Ω (asuc c) = bi {r = C.zero} {r′ = C.zero} (λ q g z z′ d → be {stp = es} d)
B-Ω (alim f) = bl (λ n → be {stp = el n} (B-Ω (f n)))

B-Ωat : ∀ a {v} (g : Gw v) → Bz (Ω̇at zero a g) (C.Ω̇ a)
B-Ωat a g = bow (B-Ω a)
```

## §2 加法, 倍数

```agda
B-add  : ∀ {a b u₀ u′} {W : W₀ a u₀} {W′ : C.O a} (gu₀ : Gw u₀) (P : b ⊲ a) (P′ : b ⊲ a) {x : W₀ b u′} {x′ : C.O b} (gx : Gw u′)
         v (gv : Gw v) (u₀v : u₀ ⊲ v) (xv : u′ ⊲ v) (bv : azero ⊲ v) → Bz W W′ → Bz x x′ →
         Bz (add W gu₀ (sa P) x gx v gv u₀v xv bv) (C.add W′ P′ x′)
B-add⁰ : ∀ {a b u₀ u′} {W : W₀ a u₀} {W′ : C.O a} (gu₀ : Gw u₀) (P : b ⊲ a) (P′ : b ⊲ a) {x : W₀ b u′} {x′ : C.O b} (gx : Gw u′)
         m (gm : Gw m) (um : u₀ ⊲ m) (tm : u′ ⊲ m) (am : azero ⊲ m) → Bz W W′ → Bz x x′ →
         Bz (add⁰ W gu₀ (sa P) x gx m gm um tm am) (C.add W′ P′ x′)

B-add gu₀ P P′ gx v gv u₀v xv bv dW d with mx gu₀ gv u₀v xv bv
... | mx′ m gm um tm am mv = bow (B-add⁰ gu₀ P P′ gx m gm um tm am dW d)

B-add⁰ gu₀ P P′ gx m gm um tm am dW bz = bow dW
B-add⁰ gu₀ P P′ gx m gm um tm am dW (bs d) = bs (B-add gu₀ P P′ gx m gm um tm am dW d)
B-add⁰ gu₀ P P′ gx m gm um tm am dW (bl h) = bl (λ n → B-add gu₀ P P′ gx m gm um tm am dW (h n))
B-add⁰ {W = W} {W′} gu₀ P P′ gx m gm um tm am dW (bi {r = r} {r′ = r′} {h = h} {h′ = h′} H) = bi (λ {v} q g z z′ d →
  subst₂ (λ s s′ → Bz (add W gu₀ (sa P) (h (⊲-tr tm q) g (inS (≪S r) s)) g v g (⊲-tr um q) C.self (z⊲ v)) (C.add W′ P′ (h′ (C.inS (≪S r′) s′))))
         (sym (out-inS (≪S (≪∘ r P)) z)) (sym (C.out-inS (≪S (≪∘ r′ P′)) z′))
         (B-add gu₀ P P′ g v g (⊲-tr um q) C.self (z⊲ v) dW (H (⊲-tr tm q) g z z′ (B→S (≪S r) (S→B (≪S (≪∘ r P)) d)))))
B-add⁰ gu₀ P P′ gx m gm um tm am dW (be {stp = es} d) = B-add gu₀ (⊲-tr (C.suc C.self) P) (⊲-tr (C.suc C.self) P′) gx m gm um tm am dW d
B-add⁰ gu₀ P P′ gx m gm um tm am dW (be {stp = el n} d) = B-add gu₀ (⊲-tr (C.lim n C.self) P) (⊲-tr (C.lim n C.self) P′) gx m gm um tm am dW d
B-add⁰ gu₀ P P′ gx m gm um tm am dW (bow {p = p′} {g = g′} d) = B-add gu₀ P P′ g′ m gm um (⊲-tr p′ tm) am dW d

B-rep : ∀ {a u} {y : W₀ a u} {c : C.O a} (g : Gw u) → Bz y c → ∀ n → Bz (rep y g n) (C.rep c n)
B-rep g d zero = bz
B-rep g d (suc zero) = d
B-rep {u = u} g d (suc (suc m)) = B-add g C.self C.self g u g C.self C.self (z⊲ u) (B-rep g d (suc m)) d
```

## §3 第 0 层

```agda
B-em : ∀ {u} {y : Ord₀} {c : C.O azero} → ord c ≅₀ y → Bz (em {u} y) c
B-em {c = C.o0} z≅ = bz
B-em {c = C.os c} (s≅ e) = bs (B-em e)
B-em {c = C.ol G} (l≅ h) = bl (λ n → B-em (h n))
B-em {c = C.oi () _} e
B-em {c = C.oe () _} e

ord-add : ∀ (W y : C.O azero) (P : azero ⊲ azero) → ord (C.add W P y) ≅₀ ord W +₀ ord y
ord-add W C.o0 P = ≅₀-refl (ord W)
ord-add W (C.os y) P = s≅ (ord-add W y P)
ord-add W (C.ol F) P = l≅ (λ n → ord-add W (F n) P)
ord-add W (C.oi () h) P
ord-add W (C.oe () x) P

rep₀≅ : ∀ {y y′} → y ≅₀ y′ → ∀ n → rep₀ y n ≅₀ rep₀ y′ n
rep₀≅ e zero = z≅
rep₀≅ e (suc zero) = e
rep₀≅ e (suc (suc m)) = plus≅ (rep₀≅ e (suc m)) e

ord-rep : ∀ (c : C.O azero) n → ord (C.rep c n) ≅₀ rep₀ (ord c) n
ord-rep c zero = z≅
ord-rep c (suc zero) = ≅₀-refl (ord c)
ord-rep c (suc (suc m)) = ≅₀-trans (ord-add (C.rep c (suc m)) c C.self) (plus≅ (ord-rep c (suc m)) (≅₀-refl (ord c)))
```

## §4 折叠

```agda
B-ψ  : ∀ {a u t} {x : W₀ a u} {c : C.O a} (T : Tg t a) (w : Lg a) (gu : Gw u) v (gv : Gw v) (uv : u ⊲ v) (tv : t ⊲ v) (av : a ⊲ v) →
       Bz x c → Bz (ψ zero t x gu v gv uv tv av) (C.ψ t T w c)
B-ψ⁰ : ∀ {a u t} {x : W₀ a u} {c : C.O a} (T : Tg t a) (w : Lg a) (gu : Gw u) m (gm : Gw m) (um : u ⊲ m) (tm : t ⊲ m) (am : a ⊲ m) →
       Bz x c → Bz (ψ⁰ zero t x gu m gm um tm am) (C.ψ t T w c)
B₀   : ∀ {a u} {x : W₀ a u} {c : C.O a} (T : Tg azero a) (w : Lg a) (gu : Gw u) v (gv : Gw v) (uv : u ⊲ v) (av : a ⊲ v) →
       Bz x c → ψ₀ x gu v gv uv av ≅₀ ord (C.ψ azero T w c)
B₀⁰  : ∀ {a u} {x : W₀ a u} {c : C.O a} (T : Tg azero a) (w : Lg a) (gu : Gw u) m (gm : Gw m) (um : u ⊲ m) (am : a ⊲ m) →
       Bz x c → ψ₀⁰ x gu m gm um am ≅₀ ord (C.ψ azero T w c)

chainB : ∀ {a u k} {r r′ : k ≪ a} {h : ∀ {v} → u ⊲ v → Gw v → Vs zero a (≪S r) v → W₀ a v} {h′ : C.Vs a (≪S r′) → C.O a}
         (w : Lg a) (gu : Gw u) m (gm : Gw m) (um : u ⊲ m) (am : a ⊲ m) →
         (∀ {v} (q : u ⊲ v) (g : Gw v) (z : W₀ k v) (z′ : C.O k) → BS a (≪S r) (inS (≪S r) z) z′ → Bz (h q g (inS (≪S r) z)) (h′ (C.inS (≪S r′) z′))) →
         ∀ n → Bz (chainᵒ gm (λ z₁ → ψ zero k (h um gm (inS (≪S r) z₁)) gm m gm C.self (⊲-tr (≪⊲ r) am) am) n)
                  (C.chainᵒ (λ z → C.ψ k (inj₁ (≪⊲ r′)) w (h′ (C.inS (≪S r′) z))) n)
chainB {k = k} w gu m gm um am H zero = B-Ωat k gm
chainB {r = r} {r′} {h} {h′} w gu m gm um am H (suc n) =
  B-ψ (inj₁ (≪⊲ r′)) w gm m gm C.self (⊲-tr (≪⊲ r) am) am (H um gm _ _ (B→S (≪S r) (chainB {r = r} {r′} {h} {h′} w gu m gm um am H n)))

B-ψ {t = azero} T w gu v gv uv tv av d = bow (B-em (≅₀-sym (B₀ T w gu v gv uv av d)))
B-ψ {t = asuc t} T w gu v gv uv tv av d with mx gu gv uv tv av
... | mx′ m gm um tm am mv = bow (B-ψ⁰ T w gu m gm um tm am d)
B-ψ {t = alim f} T w gu v gv uv tv av d with mx gu gv uv tv av
... | mx′ m gm um tm am mv = bow (B-ψ⁰ T w gu m gm um tm am d)

B-ψ⁰ {t = t} T w gu m gm um tm am bz = B-Ωat t gm
B-ψ⁰ T w gu m gm um tm am (bs d) = bl (B-rep gm (B-ψ T w gu m gm um tm am d))
B-ψ⁰ T w gu m gm um tm am (bl h) = bl (λ n → B-ψ T w gu m gm um tm am (h n))
B-ψ⁰ {a = asuc b} T w gu m gm um tm am (be {R = ss C.self} {stp = es} d) = B-ψ (tgS (ss C.self) T w) (lgS (ss C.self) w) gu m gm um tm (⊲-tr (C.suc C.self) am) d
B-ψ⁰ {a = alim f} T w gu m gm um tm am (be {R = sl n C.self} {stp = el n} d) = B-ψ (tgS (sl n C.self) T w) (lgS (sl n C.self) w) gu m gm um tm (⊲-tr (C.lim n C.self) am) d
B-ψ⁰ T w gu m gm um tm am (bow {p = p} {g = g′} d) = B-ψ T w g′ m gm (⊲-tr p um) tm am d
B-ψ⁰ {t = t} T w gu m gm um tm am (bi {k = k} {r = r} {r′ = r′} {h = h} {h′ = h′} H) with cmpN (≪∘ r am) tm (lgw gm) | rkT r′ T w
... | keep s | keep s′ = bi (λ {v} q g z z′ d →
       subst₂ (λ y y′ → Bz (ψ zero t (h (⊲-tr um q) g (inS (≪S r) y)) g v g C.self (⊲-tr tm q) (⊲-tr am q)) (C.ψ t T w (h′ (C.inS (≪S r′) y′))))
              (sym (out-inS (≪S s) z)) (sym (C.out-inS (≪S s′) z′))
              (B-ψ T w g v g C.self (⊲-tr tm q) (⊲-tr am q) (H (⊲-tr um q) g z z′ (B→S (≪S r) (S→B (≪S s) d)))))
... | keep s | rise u′ = ⊥-elim (clash s u′)
... | rise u | keep s′ = ⊥-elim (clash s′ u)
... | rise u | rise u′ = bl (λ n → B-ψ T w gm m gm C.self tm am (H um gm _ _ (B→S (≪S r) (chainB {r = r} {r′} {h} {h′} w gu m gm um am H n))))

B₀ T w gu v gv uv av d with mx gu gv uv (z⊲ v) av
... | mx′ m gm um tm am mv = B₀⁰ T w gu m gm um am d

B₀⁰ T w gu m gm um am bz = s≅ z≅
B₀⁰ T w gu m gm um am (bs {c = c} d) = l≅ (λ n → ≅₀-trans (rep₀≅ (B₀ T w gu m gm um am d) n) (≅₀-sym (ord-rep (C.ψ azero T w c) n)))
B₀⁰ T w gu m gm um am (bl h) = l≅ (λ n → B₀ T w gu m gm um am (h n))
B₀⁰ {a = asuc b} T w gu m gm um am (be {R = ss C.self} {stp = es} d) = B₀ (tgS (ss C.self) T w) (lgS (ss C.self) w) gu m gm um (⊲-tr (C.suc C.self) am) d
B₀⁰ {a = alim f} T w gu m gm um am (be {R = sl n C.self} {stp = el n} d) = B₀ (tgS (sl n C.self) T w) (lgS (sl n C.self) w) gu m gm um (⊲-tr (C.lim n C.self) am) d
B₀⁰ T w gu m gm um am (bow {p = p} {g = g′} d) = B₀ T w g′ m gm (⊲-tr p um) am d
B₀⁰ T w gu m gm um am (bi {r = r} {r′ = r′} {h = h} {h′ = h′} H) with rkT r′ T w
... | keep ()
... | rise _ = l≅ (λ n → B₀ T w gm m gm C.self am (H um gm _ _ (B→S (≪S r) (chainB {r = r} {r′} {h} {h′} w gu m gm um am H n))))
```

## §5 同下标

```agda
ψ₀-Y : ∀ {η u} (gu : Gw u) (w : Lg η) v (gv : Gw v) (uv : u ⊲ v) (av : η ⊲ v) →
       ψ₀ (Ω̇at zero η gu) gu v gv uv av ≅₀ ord (C.ψ azero (inj₁ (z⊲ η)) w (C.Ω̇ η))
ψ₀-Y {η} gu w v gv uv av = B₀ (inj₁ (z⊲ η)) w gu v gv uv av (B-Ωat η gu)
```
