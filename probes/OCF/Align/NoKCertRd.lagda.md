# $\mathbb U$ 上的紧读法: 切口由字面第一位置算出

> 不含记号. 结论写在 [NoKCert](NoKCert.lagda.md). 接 [LevelNoKBase](LevelNoKBase.lagda.md) 的 `Rdr`, `rdB`, `Tc`. 与 [GuardReadRd](GuardReadRd.lagda.md) 的差别: 那里要结构证据 `Rs` (对 `Ordᶜ` 的项), 这里读 `Legal`: **`Legal` 给的 `tg`, `dir` 是字面的第一位置, 所以切口 (`cut`) 是两个位置的同步下降, 不比较, 不判定值, 不读记号.** `no-cut` 否定的是切口由 `⊴` 算出 (`⊴` 不搬第一位置), 这里的输入是 `Cpᶠ`, 不在它的前提里.
>
> - `cut`: `ι : Cpᶠ a b` 是第一位置, `P : Cp p b` 是任意位置. 回答 $P$ 在 $a$ 这份拷贝里 (`inn`), 或者在它之上 (`abv`). 对 $b$ 结构递归; 极限处用 `FS` 的步进把两者搬到同一项. 碰到 `bra` 答 `abv`: 路径内部不动, `RdO` 要求对一切来源的 `AdmC` 搬运.
> - `rdN`: 节点 `lc k c t g` 的读法. 先问第一支, 再沿分支 $a$ 的第一路径下降 (`suc`, `lc`), 每一步问切口. 节点 $0$ 答第一支 (同 [GuardWeakRd](GuardWeakRd.lagda.md) 的 `zpos`).
> - `LimV`: 连续性的视图: $g(\lim f)=\lim h$, 且 $h\,n=g(f\,n)$. 这是 [GuardReadRd](GuardReadRd.lagda.md) 的 `cnt`. 它是节点上的**可选数据** (`Cnt`), 没有时极限分支不下降 (`here`), 仍是合法的读法. `cnt-Ω̂`: $\Omega$ 的节点都有; 分支里读回的闭包没有, 给 `nothing`.
>
> **定理 `Tc-of : ∀ x → Legal x → Cnt x → Tc (toU x)`, 一个定义, 不按阶段.** 这里只说 `Tc` 是读法, 不说紧: 紧的证据是 [NoKCertAccept](NoKCertAccept.lagda.md) 的界测试.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NoKCertRd where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; sym; trans)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ; module Trich)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc)
open import OCF.Align.LevelNoKLv using (module Lv)
open import OCF.Align.LevelFixCore
open import OCF.Align.LevelFixVal
open import OCF.Align.LevelNoKU
open Lv 𝕌 using (LG; Cpᶠ; AdmC; Src; Lk)
open import OCF.Align.LevelNoKBase XF using (Tc; Rdr; RdO; rdF; rdB; _⊲_)
open import OCF.Align.LevelNoKTab 𝕌 using (_⊙_; adm⊙)
```

## §1 第一路径上的步进

`FS`: 第一路径上极限的相邻项是字面的第一位置. `Legal` 给它.

```agda
FS : LG → Set
FS U.zero = ⊤
FS (U.suc k) = FS k
FS (U.lim f) = (∀ n → Cpᶠ (f n) (f (suc n))) × (∀ n → FS (f n))
FS (U.lc c t g) = FS t

Legal→FS : ∀ x → Legal x → FS (toU x)
Legal→FS LF.zero w = tt
Legal→FS (LF.suc k) w = Legal→FS k w
Legal→FS (LF.lim f) (st , w) = (λ n → CP→Cpᶠ (st n)) , (λ n → Legal→FS (f n) (w n))
Legal→FS (lc k c t g) (_ , _ , _ , _ , wt , _) = Legal→FS t wt

cpf-tr : ∀ {a b d} → Cpᶠ a b → Cpᶠ b d → Cpᶠ a d
cpf-tr p U.self = p
cpf-tr p (U.suc q) = U.suc (cpf-tr p q)
cpf-tr p (U.lim n q) = U.lim n (cpf-tr p q)
cpf-tr p (U.fst q) = U.fst (cpf-tr p q)

stepsF : ∀ {f : ℕ → LG} → (∀ n → Cpᶠ (f n) (f (suc n))) → ∀ {n m} → n <ᴺ m → Cpᶠ (f n) (f m)
stepsF s zero = s _
stepsF s (suc q) = cpf-tr (stepsF s q) (s _)

toP : ∀ {a b} → Cpᶠ a b → U.Cp a b
toP U.self = U.self
toP (U.suc p) = U.suc (toP p)
toP (U.lim n p) = U.lim n (toP p)
toP (U.fst p) = U.fst (toP p)

admF : ∀ E {a b} (p : Cpᶠ a b) → AdmC E (toP p)
admF E U.self = tt
admF E (U.suc p) = admF E p
admF E (U.lim n p) = admF E p
admF E (U.fst p) = admF E p
```

## §2 切口

```agda
data CutR {p : LG} (a : LG) {b : LG} (P : U.Cp p b) : Set where
  inn : (Q : U.Cp p a) → (∀ E → AdmC E P → AdmC E Q) → CutR a P
  abv : CutR a P

cut : ∀ {a b p} → FS b → Cpᶠ a b → (P : U.Cp p b) → CutR a P
cut fs U.self P = inn P (λ _ x → x)
cut fs (U.suc ι) U.self = abv
cut fs (U.suc ι) (U.suc P) with cut fs ι P
... | inn Q t = inn Q t
... | abv = abv
cut (st , w) (U.lim m ι) U.self = abv
cut (st , w) (U.lim m ι) (U.lim n P) with <ᴺ-dec n m
... | injᵃ n<m with cut (w m) ι (toP (stepsF st n<m) ⊙ P)
...   | inn Q t = inn Q (λ E x → t E (adm⊙ {E} (toP (stepsF st n<m)) (admF E (stepsF st n<m)) x))
...   | abv = abv
cut (st , w) (U.lim m ι) (U.lim n P) | injᵇ m<n with cut (w n) (cpf-tr ι (stepsF st m<n)) P
...   | inn Q t = inn Q t
...   | abv = abv
cut (st , w) (U.lim m ι) (U.lim _ P) | injᶜ refl with cut (w m) ι P
...   | inn Q t = inn Q t
...   | abv = abv
cut fs (U.fst ι) U.self = abv
cut fs (U.fst ι) (U.fst P) with cut fs ι P
... | inn Q t = inn Q t
... | abv = abv
cut fs (U.fst ι) (U.bra η e P) = abv

zpos : ∀ t → U.Cp U.zero t
zpos U.zero = U.self
zpos (U.suc b) = U.suc (zpos b)
zpos (U.lim f) = U.lim 0 (zpos (f 0))
zpos (U.lc c t g) = U.fst (zpos t)

zadm : ∀ E t → AdmC E (zpos t)
zadm E U.zero = tt
zadm E (U.suc b) = zadm E b
zadm E (U.lim f) = zadm E (f 0)
zadm E (U.lc c t g) = zadm E t
```

## §3 连续性的视图

```agda
record LimV (k : LF) (c : Raw k) (g : (η : Raw k) → Gd k c η → LF) : Set where
  constructor limv
  field
    hv : ∀ f → Gd k c (G.lim f) → ℕ → LF
    ev : ∀ f e → g (G.lim f) e ≡ LF.lim (hv f e)
    pv : ∀ f e n (e′ : Gd k c (f n)) → hv f e n ≡ g (f n) e′
open LimV

Cnt : LF → Set
Cnt LF.zero = ⊤
Cnt (LF.suc k) = Cnt k
Cnt (LF.lim f) = ∀ n → Cnt (f n)
Cnt (lc k c t g) = Maybe (LimV k c g) × Cnt t × (∀ η e → Cnt (g η e))

cnt₀ : ∀ x → Cnt x
cnt₀ LF.zero = tt
cnt₀ (LF.suc k) = cnt₀ k
cnt₀ (LF.lim f) = λ n → cnt₀ (f n)
cnt₀ (lc k c t g) = nothing , cnt₀ t , (λ η e → cnt₀ (g η e))

mapV : ∀ {k c g} (F : LF → LF) → (∀ h → F (LF.lim h) ≡ LF.lim (λ n → F (h n))) → LimV k c g → LimV k c (λ η e → F (g η e))
mapV F eqF (limv h e p) = limv (λ f d n → F (h f d n))
  (λ f d → trans (cong F (e f d)) (eqF (h f d)))
  (λ f d n d′ → cong F (p f d n d′))

mapM : ∀ {A B : Set} → (A → B) → Maybe A → Maybe B
mapM f nothing = nothing
mapM f (just x) = just (f x)

cnt-Ω̂ : ∀ x → Cnt x → Cnt (Ω̂ x)
cnt-Ω̂ LF.zero v = tt
cnt-Ω̂ (LF.suc k) v =
  just (limv (λ f e n → up k (f n)) (λ f e → refl) (λ f e n e′ → refl)) , cnt-Ω̂ k v , (λ η e → cnt₀ (up k η))
cnt-Ω̂ (LF.lim f) v = λ n → cnt-Ω̂ (f n) (v n)
cnt-Ω̂ (lc k c t g) (V , vt , vg) =
  mapM (mapV Ω̂ (λ h → refl)) V , cnt-Ω̂ t vt , (λ η e → cnt-Ω̂ (g η e) (vg η e))

cnt-add : ∀ x a → Cnt x → Cnt a → Cnt (x +ᴸ a)
cnt-add x LF.zero vx va = vx
cnt-add x (LF.suc a) vx va = cnt-add x a vx va
cnt-add x (LF.lim f) vx va = λ n → cnt-add x (f n) vx (va n)
cnt-add x (lc k c t g) vx (V , vt , vg) =
  mapM (mapV (x +ᴸ_) (λ h → refl)) V , cnt-add x t vx vt , (λ η e → cnt-add x (g η e) vx (vg η e))

cnt-tw : ∀ n → Cnt (tw n)
cnt-tw zero = tt
cnt-tw (suc n) = cnt-Ω̂ (tw n) (cnt-tw n)

cnt-Λ : Cnt Λ
cnt-Λ = cnt-tw

cnt-nat : ∀ n → Cnt (natF n)
cnt-nat zero = tt
cnt-nat (suc n) = cnt-nat n
```

## §4 节点的读法

`rdA a e P`: 分支 $a$ 里的位置 $P$. 对 $a$ 结构递归. 第一支 `tgf`, 第一路径上的前驱 `dirf`; 两者都是 `Legal` 的字面第一位置.

```agda
⊲-cp : ∀ {k c a b} (ea : Gd k c a) (eb : Gd k c b) → Cp k a b → _⊲_ {el k c} (gd ea) (gd eb)
⊲-cp {k} ea eb p (gd {η = X} _) (q , w) = Dn-cp k X p q , w

adm-subst : ∀ E {p a b} (eq : a ≡ b) (P : U.Cp p (toU a)) → AdmC E P → AdmC E (subst (λ z → U.Cp p (toU z)) eq P)
adm-subst E refl P x = x

adm-subst⁻ : ∀ E {p a b} (eq : a ≡ b) (P : U.Cp p (toU b)) → AdmC E P → AdmC E (subst (λ z → U.Cp p (toU z)) (sym eq) P)
adm-subst⁻ E refl P x = x

module Rd (k : LF) (c : Raw k) (t : LF) (g : (η : Raw k) → Gd k c η → LF) (L : Legal (lc k c t g)) (V : Maybe (LimV k c g)) where
  private
    wg = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ L))))
    tg₀ = proj₁ (proj₂ L)
    dr₀ = proj₁ (proj₂ (proj₂ L))

  R : ∀ a (e : Gd k c a) {p : LG} → U.Cp p (toU (g a e)) → Set
  R a e P = RdO (el k c) (toU t) (toUg k c g) (el k a) (gd e) P

  here : ∀ a (e : Gd k c a) {p} (P : U.Cp p (toU (g a e))) → R a e P
  here a e P = rdB (el k a) (gd e) (λ F q → q) (inj₂ refl) P (λ _ x → x)

  -- 把分支 b 里的回答搬到分支 a: b 是 a 的第一位置
  down : ∀ {a b} (e : Gd k c a) (eb : Gd k c b) → Cp k b a → {p p′ : LG} (P : U.Cp p (toU (g a e))) (Q : U.Cp p (toU (g b eb))) →
         (∀ E → AdmC E P → AdmC E Q) → R b eb Q → R a e P
  down e eb cp P Q tr (rdF d Q′ u) = rdF d Q′ (λ E x → u E (tr E x))
  down e eb cp P Q tr (rdB a′ ea′ l d Q′ u) = rdB a′ ea′ (λ F q → l F (⊲-cp eb e cp F q)) d Q′ (λ E x → u E (tr E x))

  ste : ∀ {a b} (eb : Gd k c b) (e : Gd k c a) → Cp k b a → Cpᶠ (toU (g b eb)) (toU (g a e))
  ste {a} {b} eb e cp = CP→Cpᶠ (dr₀ b eb a e (cp , proj₂ e))

  rdA : ∀ a (e : Gd k c a) {p} (P : U.Cp p (toU (g a e))) → R a e P
  rdM : ∀ f (e : Gd k c (G.lim f)) m (p₀ : Cp k c (f m)) (st : ∀ n → Cp k (f n) (f (suc n))) (lw : ∀ n → Lgl k (f n)) {p}
        (P : U.Cp p (toU (g (G.lim f) e))) → Maybe (LimV k c g) → R (G.lim f) e P
  rdL : ∀ f (e : Gd k c (G.lim f)) m (p₀ : Cp k c (f m)) (st : ∀ n → Cp k (f n) (f (suc n))) (lw : ∀ n → Lgl k (f n)) {p}
        (P : U.Cp p (toU (g (G.lim f) e))) → LimV k c g → R (G.lim f) e P

  rdA G.zero e P = here G.zero e P
  rdA (G.suc b) (inj₁ _ , l) P = here (G.suc b) (inj₁ _ , l) P
  rdA (G.suc b) (inj₂ q , l) {p} P with cut (Legal→FS _ (wg (G.suc b) (inj₂ q , l))) (ste {G.suc b} {b} (q , l) (inj₂ q , l) (inj₂ (inj₁ refl))) P
  ... | inn Q u = down {G.suc b} {b} (inj₂ q , l) (q , l) (inj₂ (inj₁ refl)) {p′ = p} P Q u (rdA b (q , l) Q)
  ... | abv = here (G.suc b) (inj₂ q , l) P
  rdA (G.lim f) (inj₁ x , l) P = here (G.lim f) (inj₁ x , l) P
  rdA (G.lim f) (inj₂ (m , q) , st , lw) P = rdM f (inj₂ (m , q) , st , lw) m q st lw P V
  rdA (G.lc r c′ t′ g′) (inj₁ x , l) P = here (G.lc r c′ t′ g′) (inj₁ x , l) P
  rdA (G.lc r c′ t′ g′) (inj₂ q , l) {p} P with cut (Legal→FS _ (wg (G.lc r c′ t′ g′) (inj₂ q , l))) (ste {G.lc r c′ t′ g′} {t′} (q , proj₁ (proj₂ (proj₂ (proj₂ l)))) (inj₂ q , l) (inj₂ (inj₁ refl))) P
  ... | inn Q u = down {G.lc r c′ t′ g′} {t′} (inj₂ q , l) (q , proj₁ (proj₂ (proj₂ (proj₂ l)))) (inj₂ (inj₁ refl)) {p′ = p} P Q u (rdA t′ (q , proj₁ (proj₂ (proj₂ (proj₂ l)))) Q)
  ... | abv = here (G.lc r c′ t′ g′) (inj₂ q , l) P
  rdA (G.em i T) e P = here (G.em i T) e P
  rdA G.top e P = here G.top e P

  rdM f e m q st lw P (just v) = rdL f e m q st lw P v
  rdM f e m q st lw {p} P nothing with cut (Legal→FS _ (wg (G.lim f) e)) (ste {G.lim f} {f m} (q , lw m) e (inj₂ (m , inj₁ refl))) P
  ... | inn Q u = down {G.lim f} {f m} e (q , lw m) (inj₂ (m , inj₁ refl)) {p′ = p} P Q u (rdA (f m) (q , lw m) Q)
  ... | abv = here (G.lim f) e P

  -- 连续: g (lim f) = lim h, 第 n 项在分支 f n 上
  rdL f e m q st lw {p} P v = go₁ (subst (λ z → U.Cp p (toU z)) (ev v f e) P) (λ E x → adm-subst E (ev v f e) P x)
    where
    Lh : Legal (LF.lim (hv v f e))
    Lh = subst Legal (ev v f e) (wg (G.lim f) e)
    stp : ∀ n → Cpᶠ (toU (hv v f e n)) (toU (hv v f e (suc n)))
    stp n = CP→Cpᶠ (proj₁ Lh n)
    dn : ∀ n (Q₀ : U.Cp p (toU (hv v f e n))) (qn : Cp k c (f n)) → (∀ E → AdmC E P → AdmC E Q₀) → R (G.lim f) e P
    dn n Q₀ qn tr =
      down {G.lim f} {f n} e (qn , lw n) (inj₂ (n , inj₁ refl)) {p′ = p} P Q₁ (λ E x → adm-subst E (pv v f e n (qn , lw n)) Q₀ (tr E x)) (rdA (f n) (qn , lw n) Q₁)
      where
      Q₁ : U.Cp p (toU (g (f n) (qn , lw n)))
      Q₁ = subst (λ z → U.Cp p (toU z)) (pv v f e n (qn , lw n)) Q₀
    go₁ : (P′ : U.Cp p (U.lim (λ n → toU (hv v f e n)))) → (∀ E → AdmC E P → AdmC E P′) → R (G.lim f) e P
    go₁ U.self _ = here (G.lim f) e P
    go₁ (U.lim n Q₀) ads with <ᴺ-dec n m
    ... | injᶜ refl = dn n Q₀ q ads
    ... | injᵇ m<n = dn n Q₀ (Cp-tr k q (stepsC k st m<n)) ads
    ... | injᵃ n<m = dn m (toP (stepsF stp n<m) ⊙ Q₀) q (λ E x → adm⊙ {E} (toP (stepsF stp n<m)) (admF E (stepsF stp n<m)) (ads E x))

  rdN : Rdr (el k c) (toU t) (toUg k c g)
  rdN (el .k a) (gd e) {U.zero} P = rdF (inj₂ refl) (zpos (toU t)) (λ E _ → zadm E (toU t))
  rdN (el .k a) (gd e) {U.suc p} P = top₁ a e P
    where
    top₁ : ∀ a (e : Gd k c a) {p′} (P : U.Cp p′ (toU (g a e))) → R a e P
    top₁ a e P with cut (Legal→FS _ (wg a e)) (CP→Cpᶠ (tg₀ a e)) P
    ... | inn Q u = rdF (inj₂ refl) Q u
    ... | abv = rdA a e P
  rdN (el .k a) (gd e) {U.lim h} P with cut (Legal→FS _ (wg a e)) (CP→Cpᶠ (tg₀ a e)) P
  ... | inn Q u = rdF (inj₂ refl) Q u
  ... | abv = rdA a e P
  rdN (el .k a) (gd e) {U.lc c₁ t₁ g₁} P with cut (Legal→FS _ (wg a e)) (CP→Cpᶠ (tg₀ a e)) P
  ... | inn Q u = rdF (inj₂ refl) Q u
  ... | abv = rdA a e P

Tc-of : ∀ x → Legal x → Cnt x → Tc (toU x)
Tc-of LF.zero w v = tt
Tc-of (LF.suc k) w v = Tc-of k w v
Tc-of (LF.lim f) (st , w) v = λ n → Tc-of (f n) (w n) (v n)
Tc-of (lc k c t g) L (V , vt , vg) = Rd.rdN k c t g L V , Tc-of t wt vt , tg′
  where
  wt = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ L))))
  tg′ : ∀ η e → Tc (toUg k c g η e)
  tg′ (el .k a) (gd e) = Tc-of (g a e) (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ L)))) a e) (vg a e)
```
