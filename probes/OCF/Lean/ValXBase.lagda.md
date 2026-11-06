# ValX (三): 跨底折叠的记法, 回灌与新世界, 输出不低于 1

> 不含记号. 入口 [ValX](ValX.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, **不用 UIP**. 模块参数 `SL : ShLaw I` (回灌与世界的值律, 实例 `I₁` 在 [ValXTm](ValXTm.lagda.md) 证出). 只导入 stdlib, `OCF.Lean.CRw*`, `OCF.Lean.ValCRel`, `OCF.Lean.ValCBase` (不导入要 `uipC` 的 `ValCMono`), [ValXRel](ValXRel.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Lean.CRwIf
import OCF.Lean.ValXRel as XR
module OCF.Lean.ValXBase (I : CRwIf) (SL : XR.ShLaw I) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; subst₂; sym; trans; cong)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRwFold I
open import OCF.Lean.ValCRel I
open import OCF.Lean.ValCBase I
open import OCF.Lean.ValXRel I
open ShLaw SL
open Po public
open CRwIf I using (sh₀; nxt₀; Adm₀)
```

## §1 记法: 策略, 回灌, 新世界, 分支的折叠

```agda
FXa : Acc bX hz → (B : Cd) → LgB B → ∀ {t} → t ⊲ B → H t → (h : HX) → PH PSX B h → H t
FXa a B l {t} pt b h n = Φ bX hz a tt b⊥ t (cx B l pt) b h n

P : (κX : K XS) → Po (E XS κX)
P κX = pX (proj₁ κX) (proj₂ κX)

PGt : Cd → (κX : K XS) → (E XS κX → HX) → Set
PGt B κX g = ∀ e (a : PS.Ad PSX B κX e) → PH PSX (PS.nx PSX B κX e a) (g e)

-- 坐标层上的回灌
shL : ∀ κX → Cd → H (lvX κX) → H (lvX κX)
shL (c , inj₁ κ) B d = d
shL (hz , inj₂ _) B d = sh₀ B d
shL (hs _ , inj₂ _) B d = d
shL (hl _ , inj₂ _) B d = d
shL (hΩ () _ , inj₂ _) B d

shEq : ∀ κX B d → psh (P κX) B (toX κX d) ≡ toX κX (shL κX B d)
shEq (c , inj₁ κ) B d = refl
shEq (hz , inj₂ _) B d = refl
shEq (hs _ , inj₂ _) B d = refl
shEq (hl _ , inj₂ _) B d = refl
shEq (hΩ () _ , inj₂ _) B d

shL-mono : ∀ κX {B₁ B₂ d₁ d₂} → LeAt hz B₁ B₂ → LeAt (lvX κX) d₁ d₂ → LeAt (lvX κX) (shL κX B₁ d₁) (shL κX B₂ d₂)
shL-mono (c , inj₁ κ) w p = p
shL-mono (hz , inj₂ _) w p = shM w p
shL-mono (hs _ , inj₂ _) w p = p
shL-mono (hl _ , inj₂ _) w p = p
shL-mono (hΩ () _ , inj₂ _) w p

shL-infl : ∀ κX B d → LeAt (lvX κX) d (shL κX B d)
shL-infl (c , inj₁ κ) B d = L.≤-refl _ d
shL-infl (hz , inj₂ _) B d = shI d
shL-infl (hs c , inj₂ _) B d = L.≤-refl (hs c) d
shL-infl (hl f , inj₂ _) B d = L.≤-refl (hl f) d
shL-infl (hΩ () _ , inj₂ _) B d

moZ : ∀ c → MoAt hz c
moZ hz = tt
moZ (hs c) = moZ c
moZ (hl f) = λ n → moZ (f n)
moZ (hΩ () _)

shL-Mo : ∀ κX B d → MoAt (lvX κX) d → MoAt (lvX κX) (shL κX B d)
shL-Mo (c , inj₁ κ) B d m = m
shL-Mo (hz , inj₂ _) B d m = moZ _
shL-Mo (hs _ , inj₂ _) B d m = m
shL-Mo (hl _ , inj₂ _) B d m = m
shL-Mo (hΩ () _ , inj₂ _) B d m

nW : ∀ κX {B} → LgB B → H (lvX κX) → Cd
nW κX {B} l d = pnx (P κX) B (psh (P κX) B (toX κX d)) (pad-sh (P κX) (toX κX d) l)

lgW : ∀ κX {B} (l : LgB B) d → LgB (nW κX l d)
lgW κX l d = plg (P κX) (pad-sh (P κX) (toX κX d) l) l

ptW : ∀ κX {B} (l : LgB B) {t} → t ⊲ B → ∀ d → t ⊲ nW κX l d
ptW κX l pt d = ⊲ᴮ-tr pt (pnx↑ (P κX) (pad-sh (P κX) (toX κX d) l))

pgW : ∀ κX {B} (l : LgB B) {g : E XS κX → HX} → PGt B κX g → ∀ d → PH PSX (nW κX l d) (g (psh (P κX) B (toX κX d)))
pgW κX {B} l pg d = pg (psh (P κX) B (toX κX d)) (pad-sh (P κX) (toX κX d) l)

nW-up : ∀ κX {B} (l : LgB B) d → LeAt hz B (nW κX l d)
nW-up κX l d = ⊲→≤ (pnx↑ (P κX) (pad-sh (P κX) (toX κX d) l))

nW-mono : ∀ κX {B₁ B₂} (l₁ : LgB B₁) (l₂ : LgB B₂) → LeAt hz B₁ B₂ → ∀ {d₁ d₂} → LeAt (lvX κX) d₁ d₂ →
          LeAt hz (nW κX l₁ d₁) (nW κX l₂ d₂)
nW-mono (c , inj₁ κ) l₁ l₂ w p = w
nW-mono (hz , inj₂ _) l₁ l₂ w p = nxM _ _ (shM w p)
nW-mono (hs _ , inj₂ _) l₁ l₂ w p = w
nW-mono (hl _ , inj₂ _) l₁ l₂ w p = w
nW-mono (hΩ () _ , inj₂ _) l₁ l₂ w p
```

分支的折叠 `brE` (坐标是 `E` 的元素, 与折叠的子句字面相同) 与 `br` (坐标经 `toX`); 三个续 (留 / 同层 / 在上).

```agda
brE : ∀ (a : Acc bX hz) {B} (l : LgB B) {t} (pt : t ⊲ B) κX (g : E XS κX → HX) (pg : PGt B κX g) → H t → E XS κX → H t
brE a {B} l {t} pt κX g pg b e =
  Φ bX hz a tt b⊥ t (cx (pnx (P κX) B (psh (P κX) B e) (pad-sh (P κX) e l)) (plg (P κX) (pad-sh (P κX) e l) l)
                        (⊲ᴮ-tr pt (pnx↑ (P κX) (pad-sh (P κX) e l))))
    b (g (psh (P κX) B e)) (pg (psh (P κX) B e) (pad-sh (P κX) e l))

br : ∀ (a : Acc bX hz) {B} (l : LgB B) {t} (pt : t ⊲ B) κX (g : E XS κX → HX) (pg : PGt B κX g) → H t → H (lvX κX) → H t
br a l pt κX g pg b d = brE a l pt κX g pg b (toX κX d)

module _ (rs : ∀ s′ i → Lt s′ i bX hz → Acc s′ i) {B : Cd} (l : LgB B) {t : Cd} (pt : t ⊲ B) (b : H t)
         (κX : K XS) (g : E XS κX → HX) (pg : PGt B κX g) where
  KcX : (κ′ : K (T t)) → (E (T t) κ′ → E XS κX) → H t
  KcX κ′ fr = hΩ κ′ (λ c′ → brE (acc rs) l pt κX g pg b (fr c′))
  ScX : (H t → E XS κX) → H t
  ScX to = hl (chain b (λ b′ → brE (acc rs) l pt κX g pg b′ (to b′)))
  AcX : (i : Cd) → hs i ⊲ B → t ⊲ i → (H i → E XS κX) → H t
  AcX i pi q to = G (rs b⊥ i lx) (lg↓ pi l) t q b (hl (chain (top b⊥ i) (λ b′ → brE (acc rs) l (⊏⊑ pi) κX g pg b′ (to b′))))

pkX : ∀ κX {B} → hs (proj₁ κX) ⊲ B → hs (lvX κX) ⊲ B
pkX κX ev = ⊲ᴮ-tr (pK (hs (proj₁ κX)) (proj₂ κX)) ev

ΦΩX : ∀ rs {B} (l : LgB B) {t} (pt : t ⊲ B) b κX (g : E XS κX → HX) (ev : hs (proj₁ κX) ⊲ B) (pg : PGt B κX g) (Q : H t → Set) →
      Q (caseDc (pick S⊥ (toX κX) (pkX κX ev) (cmpB (pkX κX ev) pt tt l)) (KcX rs l pt b κX g pg) (ScX rs l pt b κX g pg) (AcX rs l pt b κX g pg)) →
      Q (FXa (acc rs) B l pt b (hΩ κX g) (ev , pg))
ΦΩX rs l pt b (c , κ) g ev pg Q p =
  subst (λ cv → Q (caseDc (dcx l pt ev cv) (KcX rs l pt b (c , κ) g pg) (ScX rs l pt b (c , κ) g pg) (AcX rs l pt b (c , κ) g pg)))
    (sym (clEq (hs c) κ)) p

```

**分支的值合法与比较** (由右边结点的 `MoX` 与回灌的律).

```agda
brMo : ∀ κX (g : E XS κX → HX) B → MoX (hΩ κX g) → ∀ d → MoAt (lvX κX) d → MoX (g (psh (P κX) B (toX κX d)))
brMo κX g B my d md = subst (λ z → MoX (g z)) (sym (shEq κX B d)) (proj₂ my (shL κX B d) (shL-Mo κX B d md))

brUp : ∀ κX (g : E XS κX → HX) B → MoX (hΩ κX g) → ∀ {x} c d → MoAt (lvX κX) c → MoAt (lvX κX) d →
       LeAt (lvX κX) c (shL κX B d) → x ≤X g (toX κX c) → x ≤X g (psh (P κX) B (toX κX d))
brUp κX g B my {x} c d mc md le p =
  subst (λ z → x ≤X g z) (sym (shEq κX B d)) (≤X-trans p (proj₁ my c (shL κX B d) mc (shL-Mo κX B d md) le))

brLe : ∀ κX (g g′ : E XS κX → HX) B₁ B₂ → LeAt hz B₁ B₂ → MoX (hΩ κX g′) →
       (∀ c → MoAt (lvX κX) c → g (toX κX c) ≤X g′ (toX κX c)) →
       ∀ d₁ d₂ → MoAt (lvX κX) d₁ → MoAt (lvX κX) d₂ → LeAt (lvX κX) d₁ d₂ →
       g (psh (P κX) B₁ (toX κX d₁)) ≤X g′ (psh (P κX) B₂ (toX κX d₂))
brLe κX g g′ B₁ B₂ w my h d₁ d₂ m1 m2 le =
  subst₂ (λ u v → g u ≤X g′ v) (sym (shEq κX B₁ d₁)) (sym (shEq κX B₂ d₂))
    (≤X-trans (h (shL κX B₁ d₁) (shL-Mo κX B₁ d₁ m1))
              (proj₁ my (shL κX B₁ d₁) (shL κX B₂ d₂) (shL-Mo κX B₁ d₁ m1) (shL-Mo κX B₂ d₂ m2) (shL-mono κX w le)))
```

## §2 输出不低于 1

```agda
oneX : ∀ (a : Acc bX hz) {B} (l : LgB B) {t} (pt : t ⊲ B) b x n → LeAt t (hs hz) (FXa a B l pt b x n)
oneX a l pt b hz n = Rel.s≤s Rel.z≤
oneX a l pt b (hs x) n = Rel.≤l 0 (oneX a l pt b x n)
oneX a l pt b (hl f) n = Rel.≤l 0 (oneX a l pt b (f 0) (n 0))
oneX (acc rs) {B} l {t} pt b (hΩ κX g) (ev , pg) =
  ΦΩX rs l pt b κX g ev pg (LeAt t (hs hz))
    (caseP (LeAt t (hs hz)) (pick S⊥ (toX κX) (pkX κX ev) (cmpB (pkX κX ev) pt tt l))
      (λ κ′ fr → Rel.≤Ω hz (LLe-z (lowT t) κ′ _) (LMo-z (lowT t) κ′)
         (oneX (acc rs) _ _ b (g (psh (P κX) B (fr (toK t κ′ hz)))) _))
      (λ to → Rel.≤l 0 (oneX (acc rs) _ _ b (g (psh (P κX) B (to b))) _))
      (λ i pi q to → one≤ (rs b⊥ i lx) (lg↓ pi l) t q b (hl (chain (top b⊥ i) (λ b′ → brE (acc rs) l (⊏⊑ pi) κX g pg b′ (to b′))))))
```

## §3 一般的坐标数据 (同分量的两个种类)

`Ω≤Ω` 允许同分量同层的不同种类 ([ValXRel](ValXRel.lagda.md)). 证明里两边的种类各带一份 "坐标数据" `KD κX k to`: 坐标从第 $k$ 层的高度经 `to` 进入种类 $\kappa_X$, 回灌在第 $k$ 层是 `shT`. 两份数据之间要 `KC`: 回灌与新世界对两边联合单调. 本种类的数据 `kdX`; 别的种类经层号相等 $e$ 搬过来 `kdE` (直接写出, 不对 $e$ 作模式匹配).

```agda
nWE : ∀ κX {B} → LgB B → E XS κX → Cd
nWE κX {B} l e = pnx (P κX) B (psh (P κX) B e) (pad-sh (P κX) e l)

lgE : ∀ κX {B} (l : LgB B) e → LgB (nWE κX l e)
lgE κX l e = plg (P κX) (pad-sh (P κX) e l) l

ptE : ∀ κX {B} (l : LgB B) {t} → t ⊲ B → ∀ e → t ⊲ nWE κX l e
ptE κX l pt e = ⊲ᴮ-tr pt (pnx↑ (P κX) (pad-sh (P κX) e l))

pgE : ∀ κX {B} (l : LgB B) {g : E XS κX → HX} → PGt B κX g → ∀ e → PH PSX (nWE κX l e) (g (psh (P κX) B e))
pgE κX {B} l pg e = pg (psh (P κX) B e) (pad-sh (P κX) e l)

brT : ∀ (a : Acc bX hz) {B} (l : LgB B) {t} (pt : t ⊲ B) κX (g : E XS κX → HX) (pg : PGt B κX g) {k} → (H k → E XS κX) → H t → H k → H t
brT a l pt κX g pg to b d = brE a l pt κX g pg b (to d)

record KD (κX : K XS) (k : Cd) (to : H k → E XS κX) : Set where
  field
    shT      : Cd → H k → H k
    shTeq    : ∀ B d → psh (P κX) B (to d) ≡ to (shT B d)
    shT-infl : ∀ B d → LeAt k d (shT B d)
    shT-Mo   : ∀ B d → MoAt k d → MoAt k (shT B d)
open KD public

record KC {κX κX′ : K XS} {k : Cd} {to : H k → E XS κX} {to′ : H k → E XS κX′} (K₁ : KD κX k to) (K₂ : KD κX′ k to′) : Set where
  field
    shC : ∀ {B₁ B₂ d₁ d₂} → LeAt hz B₁ B₂ → LeAt k d₁ d₂ → LeAt k (shT K₁ B₁ d₁) (shT K₂ B₂ d₂)
    nC  : ∀ {B₁ B₂} (l₁ : LgB B₁) (l₂ : LgB B₂) → LeAt hz B₁ B₂ → ∀ {d₁ d₂} → LeAt k d₁ d₂ →
          LeAt hz (nWE κX l₁ (to d₁)) (nWE κX′ l₂ (to′ d₂))
open KC public

kdX : ∀ κX → KD κX (lvX κX) (toX κX)
kdX κX = record { shT = shL κX ; shTeq = shEq κX ; shT-infl = shL-infl κX ; shT-Mo = shL-Mo κX }

kcX : ∀ κX → KC (kdX κX) (kdX κX)
kcX κX = record { shC = shL-mono κX ; nC = nW-mono κX }

ssyA : ∀ {a b : Cd} (e : a ≡ b) (x : H b) → subst H e (subst H (sym e) x) ≡ x
ssyA refl x = refl

ssyB : ∀ {a b : Cd} (e : a ≡ b) (x : H a) → subst H (sym e) (subst H e x) ≡ x
ssyB refl x = refl

kdE : ∀ κX′ {k} (e : k ≡ lvX κX′) → KD κX′ k (λ d → toX κX′ (subst H e d))
kdE κX′ {k} e = record
  { shT = λ B d → subst H (sym e) (shL κX′ B (subst H e d))
  ; shTeq = λ B d → trans (shEq κX′ B (subst H e d)) (cong (toX κX′) (sym (ssyA e _)))
  ; shT-infl = λ B d → subst (λ z → LeAt k z (subst H (sym e) (shL κX′ B (subst H e d)))) (ssyB e d)
                         (LeAt-tr (sym e) _ _ (shL-infl κX′ B (subst H e d)))
  ; shT-Mo = λ B d md → MoAt-tr (sym e) _ (shL-Mo κX′ B _ (MoAt-tr e d md)) }

MoT : ∀ κX k → (H k → E XS κX) → (E XS κX → HX) → Set
MoT κX k to g = (∀ d d′ → MoAt k d → MoAt k d′ → LeAt k d d′ → g (to d) ≤X g (to d′)) × (∀ d → MoAt k d → MoX (g (to d)))

moTE : ∀ κX′ {k} (e : k ≡ lvX κX′) (g′ : E XS κX′ → HX) → MoX (hΩ κX′ g′) → MoT κX′ k (λ d → toX κX′ (subst H e d)) g′
moTE κX′ refl g′ my = my

brMoT : ∀ {κX k to} (K : KD κX k to) (g : E XS κX → HX) B → MoT κX k to g → ∀ d → MoAt k d → MoX (g (psh (P κX) B (to d)))
brMoT K g B my d md = subst (λ z → MoX (g z)) (sym (shTeq K B d)) (proj₂ my (shT K B d) (shT-Mo K B d md))

brLeT : ∀ {κX κX′ k to to′} {K₁ : KD κX k to} {K₂ : KD κX′ k to′} (C : KC K₁ K₂) (g : E XS κX → HX) (g′ : E XS κX′ → HX) B₁ B₂ →
        LeAt hz B₁ B₂ → MoT κX′ k to′ g′ → (∀ c → MoAt k c → g (to c) ≤X g′ (to′ c)) →
        ∀ d₁ d₂ → MoAt k d₁ → MoAt k d₂ → LeAt k d₁ d₂ → g (psh (P κX) B₁ (to d₁)) ≤X g′ (psh (P κX′) B₂ (to′ d₂))
brLeT {K₁ = K₁} {K₂} C g g′ B₁ B₂ w my h d₁ d₂ m1 m2 le =
  subst₂ (λ u v → g u ≤X g′ v) (sym (shTeq K₁ B₁ d₁)) (sym (shTeq K₂ B₂ d₂))
    (≤X-trans (h (shT K₁ B₁ d₁) (shT-Mo K₁ B₁ d₁ m1))
              (proj₁ my (shT K₁ B₁ d₁) (shT K₂ B₂ d₂) (shT-Mo K₁ B₁ d₁ m1) (shT-Mo K₂ B₂ d₂ m2) (shC C w le)))

-- 决定沿层号相等搬运 (J)
pickTr : ∀ {X : Cd} {A : Set} {t k k′ : Cd} (e : k ≡ k′) (to′ : H k′ → A) (pk′ : hs k′ ⊲ X) (r : (t ⊲ hs k′) ⊎ (hs k′ ⊲ t)) →
         Σ ((t ⊲ hs k) ⊎ (hs k ⊲ t)) (λ r′ → pick S⊥ to′ pk′ r ≡ pick S⊥ (λ d → to′ (subst H e d)) (subst (λ z → hs z ⊲ X) (sym e) pk′) r′)
pickTr refl to′ pk′ r = r , refl
```

## 结论 (按档)

- **[定理, 只用 `ShLaw I`; 不用 UIP]** 记法 `FXa`, `P`, `PGt`, `brE`, `br`, `KcX`, `ScX`, `AcX`, `pkX`; `ΦΩX` (跨底折叠在 $\Omega$-结点处的展开); 回灌与新世界 `shL`, `shEq`, `shL-mono`, `shL-infl`, `shL-Mo`, `nW`, `nW-up`, `nW-mono`; 分支 `brMo`, `brUp`, `brLe`; **`oneX`** (跨底折叠的输出不低于 1); 一般的坐标数据 `KD`, `KC`, `kdX`, `kcX`, `kdE`, `MoT`, `moTE`, `brT`, `brMoT`, `brLeT`, `pickTr`, `nWE`, `lgE`, `ptE`, `pgE`.
