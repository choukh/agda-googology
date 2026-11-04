# 证书 (二): 规范位置的帧有上界, $c_1$, $c_1+1$ 的 `HPf`

> 不含记号. 结论写在 [GuardCert](GuardCert.lagda.md). `cover-false` ([GuardWeakNorm](GuardWeakNorm.lagda.md)) 说 "规范位置的帧 $\sqsubseteq$ 节点的层" 对一切位置是假的. 这里写真的那一半:
>
> - `fr-zero`: 节点 0: 第一支.
> - `fr-suc`: 节点是后继: 第一支, 或帧的值 $\cong k$ (`nv` 的同一个论证).
> - `fr-lim`: **节点是极限, 位置以 `suc self` 结尾 (`EndS`): 第一支, 或帧的值 $\cong k$.** `Reader` 的 `rec` 在 `suc` 那一步把 `l` 设成 `just`, 所以落到极限节点时走 `xL`, 不走 `xC`.
> - `fr-le`: 帧的值 $\sqsubseteq\eta$, 规范化只下降.
>
> `cover-false` 的反例 (位置 `lim 0 self`) 不以 `suc self` 结尾, 不在这里. 它只出现在 `rmk (self n)`, 由模式 `gd` 处理.
>
> `hp-c₁`, `hp-cT`: [GuardCertRel](GuardCertRel.lagda.md) 的 `HPf` 的实例.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GuardCertNf where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.GuardTightCum hiding (ψ; _+_)
open import OCF.Free.Aux using (≅ᴵ→⊑ᴵ)
open import OCF.Align.GuardTightLv
open Lv Dom₀ hiding (zero; suc; lim)
open import OCF.Align.GuardTightTab Dom₀ using (Strict; st-suc; st-lim; st-fst; st-bra; stCp; st⊙; _⊙_)
open import OCF.Align.GuardTightBase
open import OCF.Align.GuardReadCut using (Cu; cIn; cNw; cUn; read; Ab; LZ; Sp; s-up; s-suc; s-eq)
import OCF.Align.GuardTightUni as Uni
open Uni Dom₀ using (em; em-self; b0; b1; rbB-≈; rb-≈₁₁; ≅→⊑ᵒ; em-mono; idO; _⊑ᵒ_)
open import OCF.Align.GuardWeakRd using (module Reader; NZ; nz?; RdV; rvF; rvN; rdΩ₁; Tc-Ω₁; Nw; lz-lk)
open import OCF.Align.GuardWeakNorm using (cT; tcʷ; no-below)
open import OCF.Align.GuardTightCert using (c₁)
open import OCF.Align.GuardWeakRel using (⌜_⌝; ⌜≈⌝; ⌜≈⁻⌝; FrL; fs′; FrG; ZB; Emp)
open import OCF.Align.GuardCertRel
```

## §1 位置的读法: 帧的值

```agda
one : Ordᴵ
one = suc zero

G₁ : (η : Ordᴵ) → one ⊑ᴵ η → LG
G₁ η _ = ⌜ η ⌝

data FR (k : Ordᴵ) {η e k₁} {P : Cp k₁ ⌜ η ⌝} : RdO one ⌜ one ⌝ G₁ η e P → Set where
  frF : ∀ {rep} {d : Lk k₁ rep} {Q : Cp rep ⌜ one ⌝} {tr} → FR k (rdF d Q tr)
  frB : ∀ {rep a ea l} {d : Lk k₁ rep} {Q : Cp rep ⌜ a ⌝} {tr} → a ⊑ᴵ k → FR k (rdB a ea l d Q tr)

rd₁ : Rdr one ⌜ one ⌝ G₁
rd₁ = proj₁ tcʷ

fr-le : ∀ {η e k₁ k} (P : Cp k₁ ⌜ η ⌝) → η ⊑ᴵ k → FR k (rd₁ η e P)
fr-le {η} {e} P h with rd₁ η e P
... | rdF d Q tr = frF
... | rdB a ea l d Q tr = frB (⊑ᴵ-trans (⊲→⊑ l) h)

lc-absurd : ∀ {c t g k} → Lv.lc c t g ≈ ⌜ k ⌝ → ⊥
lc-absurd {k = zero} ()
lc-absurd {k = suc _} ()
lc-absurd {k = lim _ _} ()

-- 节点 0
fr-zero : ∀ {η e k} (P : Cp Lv.zero ⌜ η ⌝) → FR k (rd₁ η e P)
fr-zero {η = zero} {s⊑ _ ()} P
fr-zero {η = suc η} {s⊑ z≅ z₀} P = frF
fr-zero {η = lim f s} {s⊑ z≅ z₀} P = frF

-- 节点是后继
fr-suc : ∀ {η e k′ k} (P : Cp (Lv.suc k′) ⌜ η ⌝) → Lv.suc k′ ≈ ⌜ k ⌝ → FR k (rd₁ η e P)
fr-suc {η} {e} {k′} {k} P dk with rd₁ η e P | rdΩ₁ η e tt P
... | rdF d Q tr | rvF = frF
... | rdB (suc b) ea l (inj₂ refl) Lv.self tr | rvN .b w = frB (≅ᴵ→⊑ᴵ (⌜≈⁻⌝ dk))
... | rdB (suc b) ea l (inj₁ (Lv.s≈ d)) Lv.self tr | rvN .b w = frB (≅ᴵ→⊑ᴵ (⌜≈⁻⌝ (≈-trans (≈-sym (Lv.s≈ d)) dk)))
... | rdB (suc b) ea l (inj₂ refl) (Lv.suc Q) tr | rvN .b (inj₁ h) = ⊥-elim (no-below Q h)
... | rdB (suc b) ea l (inj₂ refl) (Lv.suc Q) tr | rvN .b (inj₂ ())
... | rdB (suc b) ea l (inj₁ (Lv.s≈ d)) (Lv.suc Q) tr | rvN .b (inj₁ h) = ⊥-elim (no-below Q h)
... | rdB (suc b) ea l (inj₁ (Lv.s≈ d)) (Lv.suc Q) tr | rvN .b (inj₂ ())
```

## §2 极限节点: `rec` 的规格

```agda
LimN : LG → Set
LimN Lv.zero = ⊥
LimN (Lv.suc _) = ⊥
LimN (Lv.lim _) = ⊤
LimN (Lv.lc _ _ _) = ⊥

lim-lk : ∀ {k rep} → Lk k rep → LimN k → LimN rep
lim-lk (inj₂ refl) n = n
lim-lk {k = Lv.lim _} (inj₁ (Lv.l≈ _)) n = tt

data IsSelf : ∀ {a b} → Cp a b → Set where
  iss : ∀ {c} → IsSelf (Lv.self {c = c})

data TlL {k a x y} : Cp k a → Maybe (x <ᴵ y) → Set where
  tE : ∀ {P l} → EndS P → TlL P l
  tS : ∀ {q} → (P : Cp k a) → IsSelf P → TlL P (just q)

module RecSpec
  (g01 : ⌜ zero ⌝ ⊴ ⌜ suc zero ⌝)
  (str : ∀ b → NZ b → ∀ {k} (P : Cp k ⌜ suc b ⌝) → Cu ⌜ b ⌝ P)
  (cnt : ∀ f s → ⌜ lim f s ⌝ ≈ Lv.lim (λ n → ⌜ f n ⌝))
  where
  open Reader ⌜_⌝ g01 str cnt

  data StrA {b k} {P′ : Cp k ⌜ b ⌝} : Cu ⌜ b ⌝ (Lv.suc P′) → Set where
    sa : ∀ {rep} {d : Lk k rep} {Q : Cp rep ⌜ b ⌝} {u} → (IsSelf P′ → IsSelf Q) → (EndS P′ → EndS Q) → StrA (cIn d Q u)

  module _ (H-str : ∀ b nz {k} (P′ : Cp k ⌜ b ⌝) → StrA (str b nz (Lv.suc P′))) (η₀ : Ordᴵ) (z₀ : zero <ᴵ η₀) where
    data LV {x k} {P : Cp k x} : Rx η₀ P → Set where
      lvF : ∀ {rep} {d : Lk k rep} {Q : Cp rep t₁} {u} → LV (xF d Q u)
      lvL : ∀ {rep a ea m} {d : Lk k rep} {Q : Cp rep ⌜ a ⌝} {u l} → k ≈ ⌜ a ⌝ → LV (xL a ea m d Q u l)

    lv-rxT : ∀ {x x′ k} {P : Cp k x} {P′ : Cp k x′} (t : ∀ E → AdmC E P → AdmC E P′) (r : Rx η₀ P′) → LV r → LV (rxT {P = P} t r)
    lv-rxT t _ lvF = lvF
    lv-rxT t _ (lvL e) = lvL e

    lv-rxL : ∀ {x x′ k rep} {P : Cp k x} {P′ : Cp rep x′} (d : Lk k rep) (t : ∀ E → AdmC E P → AdmC E P′) (r : Rx η₀ P′) → LV r → LV (rxL {P = P} d t r)
    lv-rxL (inj₂ refl) t r h = lv-rxT t r h
    lv-rxL (inj₁ d) t _ lvF = lvF
    lv-rxL (inj₁ d) t _ (lvL e) = lvL (≈-trans d e)

    lv-rec : ∀ x {k} → LimN k → (P : Cp k ⌜ x ⌝) (σ : Simᴵ x η₀) (l : Maybe (x <ᴵ η₀)) → TlL P l → LV (rec η₀ z₀ x P σ l)
    lv-rec zero n P σ l (tE ())
    lv-rec zero () .Lv.self σ .(just _) (tS Lv.self iss)
    lv-rec (suc b) n P σ l t with nz? b
    lv-rec (suc .zero) n P σ l t | inj₁ refl = lvF
    lv-rec (suc b) n (Lv.suc P′) σ l (tE es0) | inj₂ nz with str b nz (Lv.suc P′) | H-str b nz P′
    ... | cIn d Q u | sa i e = lv-rxL d u _ (lv-rec b (lim-lk d n) Q (λ r → σ (suc r)) (just (σ zero)) (tS Q (i iss)))
    lv-rec (suc b) n (Lv.suc P′) σ l (tE (es-s h)) | inj₂ nz with str b nz (Lv.suc P′) | H-str b nz P′
    ... | cIn d Q u | sa i e = lv-rxL d u _ (lv-rec b (lim-lk d n) Q (λ r → σ (suc r)) (just (σ zero)) (tE (e h)))
    lv-rec (suc b) () .Lv.self σ .(just _) (tS Lv.self iss) | inj₂ nz
    lv-rec (lim f s) n P σ (just q) (tS .Lv.self iss) = lvL (⌜≈⌝ (≅ᴵ-refl (lim f s)))
    lv-rec (lim f s) n P σ l (tE h) with mvC P (cnt f s) | end-mvC P (cnt f s) h
    ... | mvc d (Lv.lim m Q) u | es-l h′ = lv-rxL d u _ (lv-rec (f m) (lim-lk d n) Q (λ r → σ (lim m r)) nothing (tE h′))
```

## §3 实例

与 [GuardWeakRd](GuardWeakRd.lagda.md) 的 `rdΩ₁` 同样的参数, 所以 `rd₁` 定义上就是这个读法.

```agda
hm₀ : ∀ {z z′ : Ordᶜ zero} → z ⊑ᵒ z′ → up zero z ⊑ᵒ up zero z′
hm₀ h = Uni.up-l Dom₀ (Uni.up-r Dom₀ h)

st₀ : ∀ (z : Ordᶜ zero) → z ≅ z → Sp (up zero z) (up zero (suc z))
st₀ z ez = s-up (s-suc (Uni.up-l Dom₀ (≅→⊑ᵒ ez)) ez (s-eq (upˡ ez)))

ct₀ : ∀ (h : ℕ → Ordᶜ zero) → (∀ n → h n ≅ h n) → up zero (lim h) ≅ lim (λ n → up zero (h n))
ct₀ h he = upˡ (l≅ (λ n → upʳ (he n)))

g′ : ⌜ zero ⌝ ⊴ ⌜ suc zero ⌝
g′ = hm₀ {em zero} {em (suc zero)} (em-mono z⊑) (idO {b = b1} {b′ = b1})

str′ : ∀ b → NZ b → ∀ {k} (P : Cp k ⌜ suc b ⌝) → Cu ⌜ b ⌝ P
str′ b nz P = read b1 b1 (st₀ (em b) (em-self b)) P

cnt′ : ∀ f s → ⌜ lim f s ⌝ ≈ Lv.lim (λ n → ⌜ f n ⌝)
cnt′ g s = rb-≈₁₁ (ct₀ (λ n → em (g n)) (λ n → em-self (g n)))

module R₁ = RecSpec g′ str′ cnt′
open Reader ⌜_⌝ g′ str′ cnt′ using (Rx; xF; xN; xL; xC; rec; toRd)

mv-self : ∀ {k a b} (P : Cp k a) (e : a ≈ b) → IsSelf P → IsSelf (posM (mvC {k} {a} {b} P e))
mv-self .Lv.self e iss = iss

H-str : ∀ b nz {k} (P′ : Cp k ⌜ b ⌝) → R₁.StrA (str′ b nz (Lv.suc P′))
H-str b nz P′ with mvC P′ (rbB-≈ b0 b1 (≅-sym (upˡ {r = zero} {x = em b} {b = em b} (em-self b)))) | mv-self P′ (rbB-≈ b0 b1 (≅-sym (upˡ {r = zero} {x = em b} {b = em b} (em-self b)))) | end-mvC P′ (rbB-≈ b0 b1 (≅-sym (upˡ {r = zero} {x = em b} {b = em b} (em-self b))))
... | mvc d Q t | i | e = R₁.sa i e

fr-of-rx : ∀ {η e k₁ k} {P : Cp k₁ ⌜ η ⌝} {z₀} (r : Rx η P) → R₁.LV H-str η z₀ r → (∀ {a} → k₁ ≈ ⌜ a ⌝ → a ⊑ᴵ k) → FR k (toRd {η = η} {e = e} r)
fr-of-rx _ (R₁.lvF) h = frF
fr-of-rx _ (R₁.lvL d) h = frB (h d)

fr-lim : ∀ {η e f′ k} (P : Cp (Lv.lim f′) ⌜ η ⌝) → EndS P → Lv.lim f′ ≈ ⌜ k ⌝ → FR k (rd₁ η e P)
fr-lim {η = zero} {e = s⊑ _ ()} P h dk
fr-lim {η = suc b} {e = s⊑ z≅ z₀} P h dk =
  fr-of-rx (rec (suc b) z₀ (suc b) P (λ r → r) nothing) (R₁.lv-rec H-str (suc b) z₀ (suc b) tt P (λ r → r) nothing (tE h)) (λ d → ≅ᴵ→⊑ᴵ (⌜≈⁻⌝ (≈-trans (≈-sym d) dk)))
fr-lim {η = lim g s} {e = s⊑ z≅ z₀} P h dk =
  fr-of-rx (rec (lim g s) z₀ (lim g s) P (λ r → r) nothing) (R₁.lv-rec H-str (lim g s) z₀ (lim g s) tt P (λ r → r) nothing (tE h)) (λ d → ≅ᴵ→⊑ᴵ (⌜≈⁻⌝ (≈-trans (≈-sym d) dk)))

-- 任意节点, 位置以 suc self 结尾
fr-end : ∀ {η e k₁ k} (P : Cp k₁ ⌜ η ⌝) → EndS P → k₁ ≈ ⌜ k ⌝ → FR k (rd₁ η e P)
fr-end {k₁ = Lv.zero} P h dk = fr-zero P
fr-end {k₁ = Lv.suc k′} P h dk = fr-suc P dk
fr-end {k₁ = Lv.lim f′} P h dk = fr-lim P h dk
fr-end {k₁ = Lv.lc c t g} P h dk = ⊥-elim (lc-absurd dk)
```

## §4 规范化之后

```agda
FB : ∀ {k₁} → Cp k₁ c₁ → Ordᴵ → Set
FB Lv.self k = ⊥
FB (Lv.fst P) k = ⊤
FB (Lv.bra η e P) k = FR k (rd₁ η e P)

le-nfC : ∀ {k₁ k} (Q₀ : Cp k₁ c₁) → FB Q₀ k → FlrLe (pF (posN (nfC c₁ tcʷ Q₀))) k
le-nfC (Lv.fst P) h with nfC ⌜ one ⌝ (proj₁ (proj₂ tcʷ)) P
... | nfc d Q′ u r = le-emp (fr-emp (FrG one) Q′)
le-nfC (Lv.bra η e P) h with rd₁ η e P | h
... | rdF d Q tr | frF with nfC ⌜ one ⌝ (proj₁ (proj₂ tcʷ)) Q
...   | nfc d′ Q′ u r = le-emp (fr-emp (FrG one) Q′)
le-nfC (Lv.bra η e P) h | rdB a ea l d Q tr | frB le with nfC ⌜ a ⌝ (proj₂ (proj₂ tcʷ) a ea) Q
...   | nfc d′ Q′ u r = le-∪ (λ { _ hr → le }) (le-emp (fr-emp (FrG a) Q′))

le-nfS : ∀ {k₁ k} (R : Strict k₁ c₁) → FB (stCp R) k → FlrLe (pF (stCp (posS (nfS c₁ tcʷ R)))) k
le-nfS (st-fst P) h with nfC ⌜ one ⌝ (proj₁ (proj₂ tcʷ)) P
... | nfc d Q′ u r = le-emp (fr-emp (FrG one) Q′)
le-nfS (st-bra η e P) h with rd₁ η e P | h
... | rdF d Q tr | frF with nfC ⌜ one ⌝ (proj₁ (proj₂ tcʷ)) Q
...   | nfc d′ Q′ u r = le-emp (fr-emp (FrG one) Q′)
le-nfS (st-bra η e P) h | rdB a ea l d Q tr | frB le with nfC ⌜ a ⌝ (proj₂ (proj₂ tcʷ) a ea) Q
...   | nfc d′ Q′ u r = le-∪ (λ { _ hr → le }) (le-emp (fr-emp (FrG a) Q′))

fb-end : ∀ {k₁ k} (Q₀ : Cp k₁ c₁) → EndS Q₀ → k₁ ≈ ⌜ k ⌝ → FB Q₀ k
fb-end (Lv.fst P) (es-f h) dk = tt
fb-end (Lv.bra η e P) (es-b h) dk = fr-end P h dk

fb-zero : ∀ {k₁ k} (Q₀ : Cp k₁ c₁) → k₁ ≈ ⌜ k ⌝ → ZB k → FB Q₀ k
fb-zero {k = zero} Lv.self () z
fb-zero (Lv.fst P) dk z = tt
fb-zero {k = zero} (Lv.bra η e P) Lv.z≈ z = fr-zero P

fb-le : ∀ {k₁ k} (Q₀ : Cp k₁ c₁) → k₁ ≈ ⌜ k ⌝ → FlrLe (pF Q₀) k → FB Q₀ k
fb-le Lv.self dk c = ⊥-elim (lc-absurd dk)
fb-le (Lv.fst P) dk c = tt
fb-le (Lv.bra η e P) dk c = fr-le P (c _ (ml hr))

nF₁ : FrL c₁ → ⊥
nF₁ ()

nFT : FrL cT → ⊥
nFT (fs′ ())

-- c₁ 的实例
fb-c₁ : ∀ {k₁ a′ k} (P : Cp a′ c₁) (R′ : Strict k₁ a′) → k₁ ≈ ⌜ k ⌝ → InvS R′ k → FB (stCp (st⊙ P R′)) k
fb-c₁ P R′ dk (iE h) = fb-end (stCp (st⊙ P R′)) (EndT R′ h P) dk
fb-c₁ Lv.self R′ dk (iL n c) = fb-le (stCp R′) dk c
fb-c₁ (Lv.fst p) R′ dk (iL n c) = tt
fb-c₁ (Lv.bra η e p) R′ dk (iL n c) = ⊥-elim (n (fr-cp (FrG η) p))

hp-c₁ : HPf c₁ tcʷ
hp-c₁ P R′ dk =
  (λ z → le-nfS (st⊙ P R′) (fb-zero (stCp (st⊙ P R′)) dk z)) ,
  (λ iv → le-nfS (st⊙ P R′) (fb-c₁ P R′ dk iv) , iL nF₁ (le-nfS (st⊙ P R′) (fb-c₁ P R′ dk iv)))

-- c₁ + 1 的实例
le-sc : ∀ {k₁ k} (Q₀ : Cp k₁ c₁) → FB Q₀ k → FlrLe (pF (stCp (posS (nfS cT tcʷ (st-suc Q₀))))) k
le-sc {k₁} {k} Q₀ h with nfC c₁ tcʷ Q₀ | le-nfC Q₀ h
... | nfc d Q t r | h′ = h′

QT : ∀ {k₁ a′} (P : Cp a′ cT) (R′ : Strict k₁ a′) → Cp k₁ c₁
QT Lv.self (st-suc Q₀) = Q₀
QT (Lv.suc p) R′ = p ⊙ stCp R′

fb-cT : ∀ {k₁ a′ k} (P : Cp a′ cT) (R′ : Strict k₁ a′) → k₁ ≈ ⌜ k ⌝ → InvS R′ k → FB (QT P R′) k
fb-cT Lv.self (st-suc Q₀) dk (iE es0) = ⊥-elim (lc-absurd dk)
fb-cT Lv.self (st-suc Q₀) dk (iE (es-s h)) = fb-end Q₀ h dk
fb-cT Lv.self (st-suc Q₀) dk (iL n c) = fb-le Q₀ dk c
fb-cT (Lv.suc Lv.self) R′ dk (iE h) = fb-end (stCp R′) h dk
fb-cT (Lv.suc Lv.self) R′ dk (iL n c) = fb-le (stCp R′) dk c
fb-cT (Lv.suc (Lv.fst p)) R′ dk iv = tt
fb-cT (Lv.suc (Lv.bra η e p)) R′ dk (iE h) = fr-end (p ⊙ stCp R′) (end⊙ h p) dk
fb-cT (Lv.suc (Lv.bra η e p)) R′ dk (iL n c) = ⊥-elim (n (fr-cp (FrG η) p))

hp-cT : HPf cT tcʷ
hp-cT Lv.self (st-suc Q₀) dk =
  (λ z → le-sc Q₀ (fb-zero Q₀ dk z)) ,
  (λ iv → le-sc Q₀ (fb-cT Lv.self (st-suc Q₀) dk iv) , iL nFT (le-sc Q₀ (fb-cT Lv.self (st-suc Q₀) dk iv)))
hp-cT (Lv.suc p) R′ dk =
  (λ z → le-sc (p ⊙ stCp R′) (fb-zero (p ⊙ stCp R′) dk z)) ,
  (λ iv → le-sc (p ⊙ stCp R′) (fb-cT (Lv.suc p) R′ dk iv) , iL nFT (le-sc (p ⊙ stCp R′) (fb-cT (Lv.suc p) R′ dk iv)))
```
