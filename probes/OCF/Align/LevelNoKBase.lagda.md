# 位置: 由 [LevelFixBase](LevelFixBase.lagda.md) 用脚本改写

> 不含记号. 结论写在 [LevelNoK](LevelNoK.lagda.md). 差别: `⊲` 是同一个下界之上两个证据的关系; `Dm`, `Cov` 带证据; `Lk`, `lkG` 移到了 [LevelNoKLv](LevelNoKLv.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LevelNoKX using (XU)

module OCF.Align.LevelNoKBase (X : XU) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Align.LevelNoKLv
open XU X using (𝔻)
open Lv 𝔻
open import OCF.Align.LevelNoKTab 𝔻 using (_⊙_; adm⊙; toCp; admTo; Strict; st-suc; st-lim; st-fst; st-bra; stCp; st⊙)
```

## §1 下降的分支值, 模 `≈` 或字面相等

`ea ⊲ e`: 同一个下界之上, $e$ 的上界都是 $e_a$ 的上界.

```agda
infix 4 _⊲_
_⊲_ : ∀ {c a η} → c ⊑ᴰ a → c ⊑ᴰ η → Set
_⊲_ {c} ea e = ∀ {X} (F : c ⊑ᴰ X) → e <ᵉ F → ea <ᵉ F

⊲-conv : ∀ {c c′ a η} (d : c ≅ᴰ c′) (ea : c ⊑ᴰ a) (e : c ⊑ᴰ η) → ea ⊲ e → conv d ea ⊲ conv d e
⊲-conv d ea e l F q =
  subst (λ z → conv d ea <ᵉ z) (sec d F)
    (<-conv d _ _ (l (conv⁻ d F) (subst (λ z → z <ᵉ conv⁻ d F) (ret d e) (<-conv⁻ d _ _ q))))

⊲-lk : ∀ {c c′ t t′ g g′ a η} (k : Lk (lc c t g) (lc c′ t′ g′)) (ea : c ⊑ᴰ a) (e : c ⊑ᴰ η) → ea ⊲ e → lkG k ea ⊲ lkG k e
⊲-lk (inj₁ o) ea e l = ⊲-conv (oc≅ o) ea e l
⊲-lk (inj₂ refl) ea e l = l

lkO : ∀ {c t g c′ t′ g′ c″ t″ g″} → Lk (lc c t g) (lc c′ t′ g′) → lc c′ t′ g′ ≈ lc c″ t″ g″ → lc c t g ≈ lc c″ t″ g″
lkO (inj₁ d) o = ≈-trans d o
lkO (inj₂ refl) o = o

lkO-conv : ∀ {c t g c′ t′ g′ c″ t″ g″ η} (k : Lk (lc c t g) (lc c′ t′ g′)) (o : lc c′ t′ g′ ≈ lc c″ t″ g″) (e : c ⊑ᴰ η) →
           conv (oc≅ (lkO k o)) e ≡ conv (oc≅ o) (lkG k e)
lkO-conv (inj₁ d) o e = oc-tr d o e
lkO-conv (inj₂ refl) o e = refl
```

## §2 读位置

`rdF`: 这个位置其实在第一支里, 不占任何分支. `rdB a ea l d Q tr`: 这个位置在分支 $a$ 里. `tr`: 对一切来源 (表, 帧) 的可容许性搬运. 这两条对恒等读法平凡; 对 $g$ 是 $b+\eta$ 也平凡, 因为路径的内部不动.

```agda
data RdO (c : D) (t : LG) (g : (η : D) → c ⊑ᴰ η → LG) (η : D) (e : c ⊑ᴰ η) {k : LG} (P : Cp k (g η e)) : Set where
  rdF : ∀ {rep} → Lk k rep → (Q : Cp rep t) → (∀ E → AdmC E P → AdmC E Q) → RdO c t g η e P
  rdB : ∀ {rep} (a : D) (ea : c ⊑ᴰ a) → ea ⊲ e → Lk k rep → (Q : Cp rep (g a ea)) → (∀ E → AdmC E P → AdmC E Q) → RdO c t g η e P

Rdr : (c : D) (t : LG) (g : (η : D) → c ⊑ᴰ η → LG) → Set
Rdr c t g = ∀ η e {k} (P : Cp k (g η e)) → RdO c t g η e P

rdId : ∀ {c t g} → Rdr c t g
rdId η e P = rdB η e (λ F q → q) (inj₂ refl) P (λ _ a → a)

Tc : LG → Set
Tc zero       = ⊤
Tc (suc k)    = Tc k
Tc (lim f)    = ∀ n → Tc (f n)
Tc (lc c t g) = Rdr c t g × Tc t × (∀ η e → Tc (g η e))

Tc-id : ∀ L → Tc L
Tc-id zero       = tt
Tc-id (suc k)    = Tc-id k
Tc-id (lim f)    = λ n → Tc-id (f n)
Tc-id (lc c t g) = rdId , Tc-id t , (λ η e → Tc-id (g η e))

Tc-cp : ∀ {k c} → Cp k c → Tc c → Tc k
Tc-cp self tc = tc
Tc-cp (suc P) tc = Tc-cp P tc
Tc-cp (lim n P) tc = Tc-cp P (tc n)
Tc-cp (fst P) (_ , tt′ , _) = Tc-cp P tt′
Tc-cp (bra η e P) (_ , _ , tg) = Tc-cp P (tg η e)

Tc-at : ∀ {k c} → k < c → Tc c → Tc k
Tc-at r tc = Tc-cp (toCp r) tc
```

## §3 覆盖

`Dm ρ y η`: 闭包 $y$ 的分支值 $\eta$ 被 $\rho$ 里同一个闭包的一个帧支配. `AdmR ρ P`: $P$ 沿途的 `bra` 都被 $\rho$ 支配. `pF P`: $P$ 自己的帧.

```agda
Dm : Fl → ∀ c t (g : (η : D) → c ⊑ᴰ η → LG) {η} → c ⊑ᴰ η → Set
Dm ρ c t g e = Σ Frm λ f → Mem ρ f × Σ (Lk (lc c t g) (κ f)) λ lk → lkG lk e ⊲ fe f

Cov : Fl → Fl → Set
Cov π ρ = ∀ {f} → Mem π f → Dm ρ (fc f) (ft f) (fg f) (fe f)

AdmR : Fl → ∀ {a c} → Cp a c → Set
AdmR ρ self      = ⊤
AdmR ρ (suc P)   = AdmR ρ P
AdmR ρ (lim n P) = AdmR ρ P
AdmR ρ (fst P)   = AdmR ρ P
AdmR ρ (bra {c = c} {t = t} {g = g} η e P) = Dm ρ c t g e × AdmR ρ P

pF : ∀ {a c} → Cp a c → Fl
pF self      = tz
pF (suc P)   = pF P
pF (lim n P) = pF P
pF (fst P)   = pF P
pF (bra {c = c} {t = t} {g = g} η e P) = tk (frm c t g η e) ∪ pF P

admC-wk : ∀ {π ρ a b} → Wk π ρ → (r : Cp a b) → AdmC (cov π) r → AdmC (cov ρ) r
admC-wk w self _ = tt
admC-wk w (suc r) a = admC-wk w r a
admC-wk w (lim n r) a = admC-wk w r a
admC-wk w (fst r) a = admC-wk w r a
admC-wk w (bra η e r) ((c₁ , t₁ , g₁ , e₁ , m , k) , a) = (c₁ , t₁ , g₁ , e₁ , w m , k) , admC-wk w r a

admP : ∀ {a c} (P : Cp a c) → AdmC (cov (pF P)) P
admP self = tt
admP (suc P) = admP P
admP (lim n P) = admP P
admP (fst P) = admP P
admP (bra {c = c} {t = t} {g = g} η e P) = (c , t , g , e , ml hr , inj₂ refl , refl) , admC-wk mr P (admP P)

covOf : ∀ {ρ a c} (P : Cp a c) → AdmR ρ P → Cov (pF P) ρ
covOf (suc P) a m = covOf P a m
covOf (lim n P) a m = covOf P a m
covOf (fst P) a m = covOf P a m
covOf (bra η e P) (d , a) (ml hr) = d
covOf (bra η e P) (d , a) (mr m) = covOf P a m

cov-exact : ∀ {π ρ} → Wk π ρ → Cov π ρ
cov-exact w {f} m = f , w m , inj₂ refl , (λ F q → q)

stCp-adm : ∀ {E k a b} (P : Cp a b) (R : Strict k a) → AdmC E P → AdmC E (stCp R) → AdmC E (stCp (st⊙ P R))
stCp-adm self R _ y = y
stCp-adm (suc P) R x y = adm⊙ P x y
stCp-adm (lim n P) R x y = adm⊙ P x y
stCp-adm (fst P) R x y = adm⊙ P x y
stCp-adm (bra η e P) R (u , x) y = u , adm⊙ P x y
```

## §4 规范化

`nfC`: 位置的规范化. 对层号结构递归: 读 `bra` 时**先**读外层闭包, 得到更低的分支或第一支, 再规范化里面. 表的来源 (`tabN`) 随分支下降; 帧的来源 (`relN`) 变成支配.

```agda
record NfC {k L : LG} (P : Cp k L) : Set where
  constructor nfc
  field
    {repN} : LG
    eqN    : Lk k repN
    posN   : Cp repN L
    tabN   : ∀ E → AdmC (tab E) P → AdmC (tab E) posN
    relN   : ∀ ρ → AdmC (cov ρ) P → AdmR ρ posN
open NfC public

belDown : ∀ {E c t g a η} {ea : c ⊑ᴰ a} {e : c ⊑ᴰ η} → ea ⊲ e → Bel (tab E) c t g e → Bel (tab E) c t g ea
belDown {ea = ea} {e} l (u , at′ , o , lt) = u , at′ , o , ⊲-conv (oc≅ o) ea e l (uF u) lt

domOf : ∀ ρ {c t g a η} {ea : c ⊑ᴰ a} {e : c ⊑ᴰ η} → ea ⊲ e → Bel (cov ρ) c t g e → Dm ρ c t g ea
domOf ρ {η = η} {ea} {e} l (c₁ , t₁ , g₁ , e₁ , m , k , eq) =
  frm c₁ t₁ g₁ η e₁ , m , k , subst (λ z → lkG k ea ⊲ z) (sym eq) (⊲-lk k ea e l)

nfC : ∀ L (tc : Tc L) {k} (P : Cp k L) → NfC P
nfC L tc self = nfc (inj₂ refl) self (λ _ _ → tt) (λ _ _ → tt)
nfC (suc b) tc (suc P) with nfC b tc P
... | nfc d Q t r = nfc d (suc Q) t r
nfC (lim f) tc (lim n P) with nfC (f n) (tc n) P
... | nfc d Q t r = nfc d (lim n Q) t r
nfC (lc c t g) (rd , tt′ , tg) (fst P) with nfC t tt′ P
... | nfc d Q u r = nfc d (fst Q) u r
nfC (lc c t g) (rd , tt′ , tg) (bra η e P) with rd η e P
... | rdF d Q tr with nfC t tt′ Q
...   | nfc d′ Q′ u r = nfc (lkC d d′) (fst Q′) (λ E a → u E (tr (tab E) (proj₂ a))) (λ ρ a → r ρ (tr (cov ρ) (proj₂ a)))
nfC (lc c t g) (rd , tt′ , tg) (bra η e P) | rdB a ea l d Q tr with nfC (g a ea) (tg a ea) Q
...   | nfc d′ Q′ u r =
  nfc (lkC d d′) (bra a ea Q′)
      (λ E x → belDown {E} {ea = ea} {e} l (proj₁ x) , u E (tr (tab E) (proj₂ x)))
      (λ ρ x → domOf ρ {ea = ea} {e} l (proj₁ x) , r ρ (tr (cov ρ) (proj₂ x)))

-- 严格位置的规范化: 头一步不是 self, 输出的头一步也不是 self
record NfS {k L : LG} (R : Strict k L) : Set where
  constructor nfs
  field
    {repS} : LG
    eqS    : Lk k repS
    posS   : Strict repS L
    tabS   : ∀ E → AdmC (tab E) (stCp R) → AdmC (tab E) (stCp posS)
    relS   : ∀ ρ → AdmC (cov ρ) (stCp R) → AdmR ρ (stCp posS)
open NfS public

nfS : ∀ L (tc : Tc L) {k} (R : Strict k L) → NfS R
nfS (suc b) tc (st-suc P) with nfC b tc P
... | nfc d Q t r = nfs d (st-suc Q) t r
nfS (lim f) tc (st-lim n P) with nfC (f n) (tc n) P
... | nfc d Q t r = nfs d (st-lim n Q) t r
nfS (lc c t g) (rd , tt′ , tg) (st-fst P) with nfC t tt′ P
... | nfc d Q u r = nfs d (st-fst Q) u r
nfS (lc c t g) (rd , tt′ , tg) (st-bra η e P) with rd η e P
... | rdF d Q tr with nfC t tt′ Q
...   | nfc d′ Q′ u r = nfs (lkC d d′) (st-fst Q′) (λ E a → u E (tr (tab E) (proj₂ a))) (λ ρ a → r ρ (tr (cov ρ) (proj₂ a)))
nfS (lc c t g) (rd , tt′ , tg) (st-bra η e P) | rdB a ea l d Q tr with nfC (g a ea) (tg a ea) Q
...   | nfc d′ Q′ u r =
  nfs (lkC d d′) (st-bra a ea Q′)
      (λ E x → belDown {E} {ea = ea} {e} l (proj₁ x) , u E (tr (tab E) (proj₂ x)))
      (λ ρ x → domOf ρ {ea = ea} {e} l (proj₁ x) , r ρ (tr (cov ρ) (proj₂ x)))
```

## §5 目标的规范化

路径 $k<c$ 与位置 `Cp (suc k) c` 是一回事 (`toCpS`, `fromCpS`): 路径的最后一步是 `zero`, 它就是 `suc k` 这个位置. 所以目标的规范化就是 `suc k` 的位置的规范化, 不要第二套读法. 这里的最小分支是 "$k<g\,a$ 的最小 $a$", 与位置 $k$ 自己的最小分支 ("$k\le g\,a$") 差一步.

```agda
toCpS : ∀ {k c} → k < c → Cp (suc k) c
toCpS zero        = self
toCpS (suc r)     = suc (toCpS r)
toCpS (lim n r)   = lim n (toCpS r)
toCpS (fst r)     = fst (toCpS r)
toCpS (bra η e r) = bra η e (toCpS r)

fromCpS : ∀ {k c} → Cp (suc k) c → k < c
fromCpS self        = zero
fromCpS (suc P)     = suc (fromCpS P)
fromCpS (lim n P)   = lim n (fromCpS P)
fromCpS (fst P)     = fst (fromCpS P)
fromCpS (bra η e P) = bra η e (fromCpS P)

admToS : ∀ {E k c} (r : k < c) → Adm E r → AdmC E (toCpS r)
admToS zero        _ = tt
admToS (suc r)     a = admToS r a
admToS (lim n r)   a = admToS r a
admToS (fst r)     a = admToS r a
admToS (bra η e r) (u , a) = u , admToS r a

admFromS : ∀ {E k c} (P : Cp (suc k) c) → AdmC E P → Adm E (fromCpS P)
admFromS self        _ = tt
admFromS (suc P)     a = admFromS P a
admFromS (lim n P)   a = admFromS P a
admFromS (fst P)     a = admFromS P a
admFromS (bra η e P) (u , a) = u , admFromS P a

record NfT {k c : LG} (r : k < c) : Set where
  constructor nft
  field
    {repT} : LG
    eqT    : Lk k repT
    pathT  : repT < c
    tabT   : ∀ E → Adm (tab E) r → Adm (tab E) pathT
open NfT public

nfT : ∀ c (tc : Tc c) {k} (r : k < c) → NfT r
nfT c tc r with nfC c tc (toCpS r)
... | nfc (inj₁ (s≈ d)) Q t _ = nft (inj₁ d) (fromCpS Q) (λ E a → admFromS Q (t E (admToS r a)))
... | nfc (inj₂ refl) Q t _ = nft (inj₂ refl) (fromCpS Q) (λ E a → admFromS Q (t E (admToS r a)))
```

## §6 位置沿 `≈` 的搬运

```agda
record MvC {k a b : LG} (P : Cp k a) : Set where
  constructor mvc
  field
    {repM} : LG
    eqM    : Lk k repM
    posM   : Cp repM b
    trfM   : ∀ E → AdmC E P → AdmC E posM
open MvC public

mvC : ∀ {k a b} (P : Cp k a) → a ≈ b → MvC {k} {a} {b} P
mvC self d = mvc (inj₁ d) self (λ _ _ → tt)
mvC (suc P) (s≈ e) with mvC P e
... | mvc d Q t = mvc d (suc Q) t
mvC (lim n P) (l≈ h) with mvC P (h n)
... | mvc d Q t = mvc d (lim n Q) t
mvC (fst P) (o≈ d′ e h h⁻ hˡ hʳ) with mvC P e
... | mvc d Q t = mvc d (fst Q) t
mvC (bra η e₁ P) (o≈ d′ e h h⁻ hˡ hʳ) with mvC P (h η e₁)
... | mvc d Q t = mvc d (bra η (conv d′ e₁) Q) (λ E u → Bel-resp {E} (o≈ d′ e h h⁻ hˡ hʳ) (proj₁ u) , t E (proj₂ u))

record MvS {k a b : LG} (R : Strict k a) : Set where
  constructor mvs
  field
    {repV} : LG
    eqV    : Lk k repV
    posV   : Strict repV b
    trfV   : ∀ E → AdmC E (stCp R) → AdmC E (stCp posV)
open MvS public

mvS : ∀ {k a b} (R : Strict k a) → a ≈ b → MvS {k} {a} {b} R
mvS (st-suc P) (s≈ e) with mvC P e
... | mvc d Q t = mvs d (st-suc Q) t
mvS (st-lim n P) (l≈ h) with mvC P (h n)
... | mvc d Q t = mvs d (st-lim n Q) t
mvS (st-fst P) (o≈ d′ e h h⁻ hˡ hʳ) with mvC P e
... | mvc d Q t = mvs d (st-fst Q) t
mvS (st-bra η e₁ P) (o≈ d′ e h h⁻ hˡ hʳ) with mvC P (h η e₁)
... | mvc d Q t = mvs d (st-bra η (conv d′ e₁) Q) (λ E u → Bel-resp {E} (o≈ d′ e h h⁻ hˡ hʳ) (proj₁ u) , t E (proj₂ u))
```
