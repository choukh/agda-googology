# YiLeanVal 主引理：新折叠在一切输入层与目标层上保持关系

**验收文件，档位：编译定理。** `FOLD`：`RelF K y ξ`、外部派发与参照一侧的比较一致 (`Agree`)，推出 `RelF m (ψ p σ y) (Ψ m V x ξ)`；`FOLD⁰` 是目标为第 0 层、参照取 `ψ⁰` 的版本。
`lower-any`：对一切合法的第 0 层树 `η` 与结构对应的参照层号 `κ`，ψ₀(Ω_κ) ≼ 读回的 `F η` (下界，不是同值)。结点处参照一侧按 `<ᴵ-dec` 分情况，三种结果与树一侧的派发由 `Agree` 对齐。
不否定别的写法。底座在 [YiLeanValRel](YiLeanValRel.lagda.md)，加法在 [YiLeanValAdd](YiLeanValAdd.lagda.md)，实例在 [YiLeanValFin](YiLeanValFin.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLeanValFold where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (¬_)
open import OCF.Lean.YiLeanCore
open import OCF.Lean.YiLeanFold
open import OCF.Lean.YiLeanTw3 using (R; ⌜_⌝; lv; F)
open import OCF.Lean.YiLeanAccFin using (read; one≼)
open import OCF.Lean.YiLeanValRel
open import OCF.Lean.YiLeanValAdd
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼)
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using () renaming (iter to iterᴸ)
open L using (_≅ᴵ_; _<ᴵ_; _≺ᴵ_)
```

## 1 第一支与起点

```agda
nodeAt-br : ∀ {M} m (s : Pre m) (B : Bld M m) → Compat M m B → (gm : Raw (lev m s) → Raw M) →
  ∀ {ι} {z : L.Ordᶜ ι} → RelF M z (gm G.top) → RelF M z (nodeAt m s B gm)
nodeAt-br (suc k) (inj₁ _) B C gm d = Compat.cb C (inj₁ tt) gm d
nodeAt-br (suc k) (inj₂ p) B C gm d = nodeAt-br k p _ (Compat-s C) gm d
nodeAt-br (lim f) (n , p) B C gm d = nodeAt-br (f n) p _ (Compat-l C n) gm d
nodeAt-br (lc j g) (η , l , p) B C gm d = nodeAt-br (g η) p _ (Compat-c C η l) gm d

nodeAt-nd : ∀ {M} m (s : Pre m) (B : Bld M m) → Compat M m B → (gm : Raw (lev m s) → Raw M) →
  ∀ {j K′} {q : j <ᴵ K′} {f : L.U j (L.<→◃ q) → L.Ordᶜ K′} → Corr j (lev m s) →
  (∀ (y : L.Ordᶜ j) a → RelF (lev m s) y a → RelF M (f (L.into (L.<→◃ q) y)) (gm a)) →
  RelF M (L.limᵢ q f) (nodeAt m s B gm)
nodeAt-nd (suc k) (inj₁ _) B C gm c h = Compat.cn C (inj₁ tt) gm c h
nodeAt-nd (suc k) (inj₂ p) B C gm c h = nodeAt-nd k p _ (Compat-s C) gm c h
nodeAt-nd (lim f) (n , p) B C gm c h = nodeAt-nd (f n) p _ (Compat-l C n) gm c h
nodeAt-nd (lc j g) (η , l , p) B C gm c h = nodeAt-nd (g η) p _ (Compat-c C η l) gm c h

FIRSTn : ∀ m J (w : Way m J) gm gk {ι} {z : L.Ordᶜ ι} → RelF m z (gm G.top) → RelF m z (Ψn m J w gm gk)
FIRSTn m .(lev m s) (keep s refl) gm gk d = nodeAt-br m s G.lc (Compat-lc m) gm d
FIRSTn m J fold gm gk d = lr-any m 0 d

FIRSTN : ∀ m K (r : Pre K) (w : Way m (lev K r)) gm gk {ι} {z : L.Ordᶜ ι} →
  RelF m z (gm (Lay.tp (Lo K r))) → RelF m z (ΨN m K r w gm gk)
FIRSTN m (suc k) (inj₁ _) = FIRSTn m k
FIRSTN m (suc k) (inj₂ r) = FIRSTN m k r
FIRSTN m (lim f) (n , r) = FIRSTN m (f n) r
FIRSTN m (lc j g) (η , _ , r) = FIRSTN m (g η) r

OMEGA : ∀ {K} (V : Lv K) m (x : Ext m K) {i} → Corr i m → ∀ ξ → RelF m (L.Ω i) (Ψ m V x ξ)
OMEGA V m x c G.zero = START m c
OMEGA V m x c (G.suc a) = lr-any m 0 (OMEGA V m x c a)
OMEGA V m x c (G.lim F) = lr-any m 0 (OMEGA V m x c (F 0))
OMEGA {K} V m x c (G.lc r g) = FIRSTN m K r (x r) _ _ (OMEGA V m x c (g (Lay.tp (Lo K r))))
OMEGA (vs V) m x c (G.em _ a) = OMEGA V m _ c a
OMEGA (vl V st) m x c (G.em n a) = OMEGA (V n) m _ c a
OMEGA v0 m x c G.top = lr-any m 0 (START m c)
OMEGA {suc k} (vs V) m x c G.top = FIRSTn m k (x (inj₁ tt)) _ _ (OMEGA V m _ c G.top)
OMEGA (vl V st) m x c G.top = lr-any m 0 (OMEGA (V 0) m _ c G.top)
```

## 2 结点

两条链同步：参照从 `Ω j` 起每步 `ψ q`，树从 `top` 起每步加上推进用的折叠 (`CHAIN`)。保留时参照的输出结点挂在 `≅ᴵ` 的代表上，分支先 `tr⁻` 搬回 (`TRC-all`)。

```agda
module Chain {j K′} (q : j <ᴵ K′) (f : L.U j (L.<→◃ q) → L.Ordᶜ K′) where
  δ : ℕ → L.Ordᶜ j
  δ = iterᴸ (λ x → L.ψ q (λ r → r) (f (L.into (L.<→◃ q) x))) (L.Ω j)

  CHAIN : ∀ J → Pl J → Corr j J → (gk : Raw J → Raw J) →
    (∀ y a → RelF J y a → RelF J (L.ψ q (λ r → r) (f (L.into (L.<→◃ q) y))) (gk a)) →
    ∀ n → RelF J (δ n) (chain J gk n)
  CHAIN J PJ c gk hk zero = START J c
  CHAIN J PJ c gk hk (suc n) = ABSORB PJ (chain J gk n) (hk _ _ (CHAIN J PJ c gk hk n))

module Node {m} (Pm : Pl m) {i ℓ} (p : i <ᴵ ℓ) (ci : Corr i m)
  {j K′} (q : j <ᴵ K′) (f : L.U j (L.<→◃ q) → L.Ordᶜ K′) (σ : L.Simᴵ K′ ℓ) where
  open Chain q f

  KEEPc : ∀ J → Corr j J → (w : Way m J) → AgW w i → (gm : Raw J → Raw m) (gk : Raw J → Raw J) →
    (∀ y a → RelF J y a → RelF m (L.ψ p σ (f (L.into (L.<→◃ q) y))) (gm a)) →
    ∀ {j″} (e : j ≅ᴵ j″) (r : j″ <ᴵ i) →
    RelF m (L.limᵢ r (λ y → L.ψ p σ (f (L.into (L.<→◃ q) (L.tr⁻ e (L.out (L.<→◃ r) y))))))
      (Ψn m J w gm gk)
  KEEPc .(lev m s) c (keep s refl) ag gm gk hm e r =
    nodeAt-nd m s G.lc (Compat-lc m) gm (Corr-≅ (L.≅ᴵ-sym e) c) (λ z a pz →
      subst (λ w → RelF m (L.ψ p σ (f (L.into (L.<→◃ q) (L.tr⁻ e w)))) (gm a))
        (sym (L.out-into (L.<→◃ r) z)) (hm (L.tr⁻ e z) a (TRC.tr⁻ᴿ (TRC-all (lev m s)) e pz)))
  KEEPc J c fold ag gm gk hm e r = ⊥-elim (ag c (L.via e r))

  FOLDc : ∀ J → Pl J → Corr j J → (w : Way m J) → AgW w i → ¬ (j ≺ᴵ i) →
    (gm : Raw J → Raw m) (gk : Raw J → Raw J) →
    (∀ y a → RelF J y a → RelF m (L.ψ p σ (f (L.into (L.<→◃ q) y))) (gm a)) →
    (∀ y a → RelF J y a → RelF J (L.ψ q (λ r → r) (f (L.into (L.<→◃ q) y))) (gk a)) →
    RelF m (L.lim (λ n → L.ψ p σ (f (L.into (L.<→◃ q) (δ n))))) (Ψn m J w gm gk)
  FOLDc J PJ c (keep s e₀) ag nlt gm gk hm hk = ⊥-elim (nlt (ag c))
  FOLDc J PJ c fold ag nlt gm gk hm hk =
    llr-any m (λ n → lr-any m n (hm _ _ (CHAIN J PJ c gk hk n)))

  NODEn : ∀ J → Pl J → Corr j J → (w : Way m J) → AgW w i → (gm : Raw J → Raw m) (gk : Raw J → Raw J) →
    (∀ y a → RelF J y a → RelF m (L.ψ p σ (f (L.into (L.<→◃ q) y))) (gm a)) →
    (∀ y a → RelF J y a → RelF J (L.ψ q (λ r → r) (f (L.into (L.<→◃ q) y))) (gk a)) →
    RelF m (L.ψ p σ (L.limᵢ q f)) (Ψn m J w gm gk)
  NODEn J PJ c w ag gm gk hm hk with L.<ᴵ-dec (σ q) p
  ... | injᵃ (L.via e r) = KEEPc J c w ag gm gk hm e r
  ... | injᵇ ir = FOLDc J PJ c w ag (λ lt → L.≺ᴵ-irrefl (L.≺ᴵ-trans lt ir)) gm gk hm hk
  ... | injᶜ e = FOLDc J PJ c w ag (λ lt → L.≺ᴵ-irrefl (L.≺ᴵ-respʳ lt (L.≅ᴵ-sym e))) gm gk hm hk

  NODEN : ∀ K → Pl K → (r : Pre K) → Corr j (lev K r) → (w : Way m (lev K r)) → AgW w i →
    (gm : Lay.A (Lo K r) → Raw m) (gk : Lay.A (Lo K r) → Raw (lev K r)) →
    (∀ y a → RelP K r y a → RelF m (L.ψ p σ (f (L.into (L.<→◃ q) y))) (gm a)) →
    (∀ y a → RelP K r y a → RelF (lev K r) (L.ψ q (λ r → r) (f (L.into (L.<→◃ q) y))) (gk a)) →
    RelF m (L.ψ p σ (L.limᵢ q f)) (ΨN m K r w gm gk)
  NODEN (suc k) (ps P) (inj₁ _) = NODEn k P
  NODEN (suc k) (ps P) (inj₂ r) = NODEN k P r
  NODEN (lim f) (pl P) (n , r) = NODEN (f n) (P n) r
```

## 3 主引理

```agda
FOLDZ : ∀ m → Pl m → (x : Ext m zero) → ∀ {i ℓ} (p : i <ᴵ ℓ) → Corr i m → (σ : L.Simᴵ L.zero ℓ) →
  ∀ {y b : L.Ordᶜ L.zero} → y ≼ b → ∀ a → b ≡ read a → RelF m (L.ψ p σ y) (Ψ m v0 x a)
FOLDZ m Pm x p c σ z≼ a e = OMEGA v0 m x c a
FOLDZ m Pm x p c σ (s≼s d) (G.suc a) refl = SUCC Pm (FOLDZ m Pm x p c σ d a refl)
FOLDZ m Pm x p c σ (s≼s d) G.top refl = SUCC Pm (FOLDZ m Pm x p c σ d G.zero refl)
FOLDZ m Pm x p c σ (≼l n d) (G.lim F) refl = lr-any m n (FOLDZ m Pm x p c σ d (F n) refl)
FOLDZ m Pm x p c σ (l≼ h) a e = llr-any m (λ n → FOLDZ m Pm x p c σ (h n) a e)
FOLDZ m Pm x p c σ (≼i {p = ()} z ez d) a e
FOLDZ m Pm x p c σ (i≼ {p = ()} h) a e
FOLDZ m Pm x p c σ (≼u {r = ()} d) a e
FOLDZ m Pm x p c σ (u≼ {r = ()} d) a e

FOLD : ∀ {K} (V : Lv K) m → Pl m → (x : Ext m K) → ∀ {i ℓ} (p : i <ᴵ ℓ) → Corr i m → Agree x i →
  ∀ {κ} (σ : L.Simᴵ κ ℓ) {y : L.Ordᶜ κ} {ξ} → RelF K y ξ → RelF m (L.ψ p σ y) (Ψ m V x ξ)
FOLDs : ∀ {k} (V : Lv k) m → Pl m → (x : Ext m (suc k)) → ∀ {i ℓ} (p : i <ᴵ ℓ) → Corr i m → Agree x i →
  ∀ {κ} (σ : L.Simᴵ κ ℓ) {y : L.Ordᶜ κ} {ξ} → RelF (suc k) y ξ → RelF m (L.ψ p σ y) (Ψ m (vs V) x ξ)
FOLDl : ∀ {f} (V : ∀ n → Lv (f n)) (st : ∀ n → Shift (f n) (f (suc n))) m → Pl m → (x : Ext m (lim f)) →
  ∀ {i ℓ} (p : i <ᴵ ℓ) → Corr i m → Agree x i →
  ∀ {κ} (σ : L.Simᴵ κ ℓ) {y : L.Ordᶜ κ} {ξ} → RelF (lim f) y ξ → RelF m (L.ψ p σ y) (Ψ m (vl V st) x ξ)

FOLD v0 m Pm x p c ag {L.zero} σ {ξ = ξ} d = FOLDZ m Pm x p c σ d ξ refl
FOLD v0 m Pm x p c ag {L.suc _} σ ()
FOLD v0 m Pm x p c ag {L.lim _ _} σ ()
FOLD (vs V) = FOLDs V
FOLD (vl V st) = FOLDl V st

FOLDs V m Pm x p c ag σ zr = OMEGA (vs V) m x c _
FOLDs V m Pm x p c ag σ (ssr d) = SUCC Pm (FOLDs V m Pm x p c ag σ d)
FOLDs V m Pm x p c ag σ (sr d) = lr-any m 0 (FOLDs V m Pm x p c ag σ d)
FOLDs V m Pm x p c ag σ (lr n d) = lr-any m n (FOLDs V m Pm x p c ag σ d)
FOLDs V m Pm x p c ag σ (llr h) = llr-any m (λ n → FOLDs V m Pm x p c ag σ (h n))
FOLDs {k} V m Pm x p c ag σ (br {r = r} d) = FIRSTN m (suc k) r (x r) _ _ (FOLDs V m Pm x p c ag σ d)
FOLDs {k} V m Pm x p c ag σ (ndr {r = r} {g = g} {q = q} {f = f} cj h) =
  Node.NODEN Pm p c q f σ (suc k) (ps (Lv→Pl V)) r cj (x r) (ag r) _ _
    (λ y a pz → FOLDs V m Pm x p c ag σ (h y a pz))
    (λ y a pz → FOLDs V (lev (suc k) r) (Pl-lev (ps (Lv→Pl V)) r) (cmp (vs V) r) q cj
      (λ r′ → CMP (vs V) r r′ cj) (λ z → z) (h y a pz))
FOLDs V m Pm x p c ag σ (emr d) = FOLD V m Pm (λ r → x (inj₂ r)) p c (λ r → ag (inj₂ r)) σ d
FOLDs {k} V m Pm x p c ag σ (tnr tt d) = FOLDs V m Pm x p c ag σ {ξ = topS k} d
FOLDs V m Pm x p c ag σ (tlr i () d)
FOLDs V m Pm x p c ag σ (ur d) = FOLDs V m Pm x p c ag (λ q → σ (L.suc q)) d
FOLDs V m Pm x p c ag σ (us {n = n} d) = FOLDs V m Pm x p c ag (λ q → σ (L.lim n q)) d

FOLDl V st m Pm x p c ag σ zr = OMEGA (vl V st) m x c _
FOLDl V st m Pm x p c ag σ (ssr d) = SUCC Pm (FOLDl V st m Pm x p c ag σ d)
FOLDl V st m Pm x p c ag σ (sr d) = lr-any m 0 (FOLDl V st m Pm x p c ag σ d)
FOLDl V st m Pm x p c ag σ (lr n d) = lr-any m n (FOLDl V st m Pm x p c ag σ d)
FOLDl V st m Pm x p c ag σ (llr h) = llr-any m (λ n → FOLDl V st m Pm x p c ag σ (h n))
FOLDl {f} V st m Pm x p c ag σ (br {r = r} d) = FIRSTN m (lim f) r (x r) _ _ (FOLDl V st m Pm x p c ag σ d)
FOLDl {f} V st m Pm x p c ag σ (ndr {r = r} {g = g} {q = q} {f = h₀} cj h) =
  Node.NODEN Pm p c q h₀ σ (lim f) (pl (λ n → Lv→Pl (V n))) r cj (x r) (ag r) _ _
    (λ y a pz → FOLDl V st m Pm x p c ag σ (h y a pz))
    (λ y a pz → FOLDl V st (lev (lim f) r) (Pl-lev (pl (λ n → Lv→Pl (V n))) r) (cmp (vl V st) r) q cj
      (λ r′ → CMP (vl V st) r r′ cj) (λ z → z) (h y a pz))
FOLDl V st m Pm x p c ag σ (emr {i = n} d) = FOLD (V n) m Pm (λ r → x (n , r)) p c (λ r → ag (n , r)) σ d
FOLDl V st m Pm x p c ag σ (tnr () d)
FOLDl V st m Pm x p c ag σ (tlr n tt d) =
  lr-any m n (PSUM Pm (λ n → Ψ m (V n) (λ r → x (n , r)) G.top) n
    (FOLD (V n) m Pm (λ r → x (n , r)) p c (λ r → ag (n , r)) σ d))
FOLDl V st m Pm x p c ag σ (ur d) = FOLDl V st m Pm x p c ag (λ q → σ (L.suc q)) d
FOLDl V st m Pm x p c ag σ (us {n = n} d) = FOLDl V st m Pm x p c ag (λ q → σ (L.lim n q)) d
```

## 4 目标为第 0 层，参照取 `ψ⁰`

`ψ⁰` 从不保留，链与 `ψ` 的折叠情形相同；目标层 0 上树一侧的保留没有槽位。

```agda
NODE⁰n : ∀ J → Pl J → ∀ {j K′} (q : j <ᴵ K′) (f : L.U j (L.<→◃ q) → L.Ordᶜ K′) → Corr j J →
  (w : Way zero J) (gm : Raw J → R) (gk : Raw J → Raw J) →
  (∀ y a → RelF J y a → L.ψ⁰ (f (L.into (L.<→◃ q) y)) ≼ read (gm a)) →
  (∀ y a → RelF J y a → RelF J (L.ψ q (λ r → r) (f (L.into (L.<→◃ q) y))) (gk a)) →
  L.ψ⁰ (L.limᵢ q f) ≼ read (Ψn zero J w gm gk)
NODE⁰n J PJ q f c (keep () e) gm gk hm hk
NODE⁰n J PJ q f c fold gm gk hm hk = l≼ (λ n → ≼l n (hm _ _ (Chain.CHAIN q f J PJ c gk hk n)))

NODE⁰N : ∀ K → Pl K → (r : Pre K) → ∀ {j K′} (q : j <ᴵ K′) (f : L.U j (L.<→◃ q) → L.Ordᶜ K′) →
  Corr j (lev K r) → (w : Way zero (lev K r)) →
  (gm : Lay.A (Lo K r) → R) (gk : Lay.A (Lo K r) → Raw (lev K r)) →
  (∀ y a → RelP K r y a → L.ψ⁰ (f (L.into (L.<→◃ q) y)) ≼ read (gm a)) →
  (∀ y a → RelP K r y a → RelF (lev K r) (L.ψ q (λ r → r) (f (L.into (L.<→◃ q) y))) (gk a)) →
  L.ψ⁰ (L.limᵢ q f) ≼ read (ΨN zero K r w gm gk)
NODE⁰N (suc k) (ps P) (inj₁ _) = NODE⁰n k P
NODE⁰N (suc k) (ps P) (inj₂ r) = NODE⁰N k P r
NODE⁰N (lim f) (pl P) (n , r) = NODE⁰N (f n) (P n) r

FOLDZ⁰ : ∀ (x : Ext zero zero) {y b : L.Ordᶜ L.zero} → y ≼ b → ∀ a → b ≡ read a → L.ψ⁰ y ≼ read (Ψ zero v0 x a)
FOLDZ⁰ x z≼ a e = one≼ v0 x a
FOLDZ⁰ x (s≼s d) (G.suc a) refl = SUCC pz (FOLDZ⁰ x d a refl)
FOLDZ⁰ x (s≼s d) G.top refl = SUCC pz (FOLDZ⁰ x d G.zero refl)
FOLDZ⁰ x (≼l n d) (G.lim F) refl = ≼l n (FOLDZ⁰ x d (F n) refl)
FOLDZ⁰ x (l≼ h) a e = l≼ (λ n → FOLDZ⁰ x (h n) a e)
FOLDZ⁰ x (≼i {p = ()} z ez d) a e
FOLDZ⁰ x (i≼ {p = ()} h) a e
FOLDZ⁰ x (≼u {r = ()} d) a e
FOLDZ⁰ x (u≼ {r = ()} d) a e

FOLD⁰ : ∀ {K} (V : Lv K) (x : Ext zero K) {κ} {y : L.Ordᶜ κ} {ξ} → RelF K y ξ → L.ψ⁰ y ≼ read (Ψ zero V x ξ)
FOLD⁰s : ∀ {k} (V : Lv k) (x : Ext zero (suc k)) {κ} {y : L.Ordᶜ κ} {ξ} → RelF (suc k) y ξ →
  L.ψ⁰ y ≼ read (Ψ zero (vs V) x ξ)
FOLD⁰l : ∀ {f} (V : ∀ n → Lv (f n)) (st : ∀ n → Shift (f n) (f (suc n))) (x : Ext zero (lim f))
  {κ} {y : L.Ordᶜ κ} {ξ} → RelF (lim f) y ξ → L.ψ⁰ y ≼ read (Ψ zero (vl V st) x ξ)

FOLD⁰ v0 x {L.zero} {ξ = ξ} d = FOLDZ⁰ x d ξ refl
FOLD⁰ v0 x {L.suc _} ()
FOLD⁰ v0 x {L.lim _ _} ()
FOLD⁰ (vs V) = FOLD⁰s V
FOLD⁰ (vl V st) = FOLD⁰l V st

FOLD⁰s V x zr = one≼ (vs V) x _
FOLD⁰s V x (ssr d) = SUCC pz (FOLD⁰s V x d)
FOLD⁰s V x (sr d) = ≼l 0 (FOLD⁰s V x d)
FOLD⁰s V x (lr n d) = ≼l n (FOLD⁰s V x d)
FOLD⁰s V x (llr h) = l≼ (λ n → FOLD⁰s V x (h n))
FOLD⁰s {k} V x (br {r = r} d) = FIRSTN zero (suc k) r (x r) _ _ (FOLD⁰s V x d)
FOLD⁰s {k} V x (ndr {r = r} {g = g} {q = q} {f = f} cj h) =
  NODE⁰N (suc k) (ps (Lv→Pl V)) r q f cj (x r) _ _
    (λ y a pz → FOLD⁰s V x (h y a pz))
    (λ y a pz → FOLDs V (lev (suc k) r) (Pl-lev (ps (Lv→Pl V)) r) (cmp (vs V) r) q cj
      (λ r′ → CMP (vs V) r r′ cj) (λ z → z) (h y a pz))
FOLD⁰s V x (emr d) = FOLD⁰ V (λ r → x (inj₂ r)) d
FOLD⁰s {k} V x (tnr tt d) = FOLD⁰s V x {ξ = topS k} d
FOLD⁰s V x (tlr i () d)
FOLD⁰s V x (ur {y = y} d) = FOLD⁰s V x {y = y} d
FOLD⁰s V x (us {y = y} d) = FOLD⁰s V x {y = y} d

FOLD⁰l V st x zr = one≼ (vl V st) x _
FOLD⁰l V st x (ssr d) = SUCC pz (FOLD⁰l V st x d)
FOLD⁰l V st x (sr d) = ≼l 0 (FOLD⁰l V st x d)
FOLD⁰l V st x (lr n d) = ≼l n (FOLD⁰l V st x d)
FOLD⁰l V st x (llr h) = l≼ (λ n → FOLD⁰l V st x (h n))
FOLD⁰l {f} V st x (br {r = r} d) = FIRSTN zero (lim f) r (x r) _ _ (FOLD⁰l V st x d)
FOLD⁰l {f} V st x (ndr {r = r} {g = g} {q = q} {f = h₀} cj h) =
  NODE⁰N (lim f) (pl (λ n → Lv→Pl (V n))) r q h₀ cj (x r) _ _
    (λ y a pz → FOLD⁰l V st x (h y a pz))
    (λ y a pz → FOLDl V st (lev (lim f) r) (Pl-lev (pl (λ n → Lv→Pl (V n))) r) (cmp (vl V st) r) q cj
      (λ r′ → CMP (vl V st) r r′ cj) (λ z → z) (h y a pz))
FOLD⁰l V st x (emr {i = n} d) = FOLD⁰ (V n) (λ r → x (n , r)) d
FOLD⁰l V st x (tnr () d)
FOLD⁰l V st x (tlr n tt d) =
  ≼l n (PSUM pz (λ n → Ψ zero (V n) (λ r → x (n , r)) G.top) n (FOLD⁰ (V n) (λ r → x (n , r)) d))
FOLD⁰l V st x (ur {y = y} d) = FOLD⁰l V st x {y = y} d
FOLD⁰l V st x (us {y = y} d) = FOLD⁰l V st x {y = y} d
```

## 5 一般的可数层号

```agda
lower-any : ∀ η (l : Lgl zero η) {κ} → Corr κ ⌜ η ⌝ → L.ψ⁰ (L.Ω κ) ≼ read (F η l)
lower-any η l c = FOLD⁰ (lv η l) (λ _ → fold) (START ⌜ η ⌝ c)
```
