# Third (二): 对任一世界序的路径结构

> 不含记号. 入口 [Third](Third.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延. 只导入 stdlib, [CRwBase](CRwBase.lagda.md), [ThirdIf](ThirdIf.lagda.md), [ThirdTw](ThirdTw.lagda.md).
>
> **与 `CRwFold.PS` 的差.** 世界不再是可数树, 而是任一带自反传递序的类型 `Po` (第 $k$ 层的路径的世界是第 $k-1$ 个底的值, 序是固定低层世界里的第一位置). `psStep`, `psSup`, 塔上的 `PSL Q m` (对高度的 $\Omega$-结点也是 `psSup`), 上抬 `lift` 同 `CRwPath`, `RecBPath`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.ThirdPS where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdIf
open import OCF.Lean.ThirdTw using (Ix; FX; XSof)

record Po : Set₁ where
  field
    W   : Set
    _≤_ : W → W → Set
    rf  : ∀ {a} → a ≤ a
    tr  : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c

record PS (P : Po) (T : KS) : Set₁ where
  open Po P
  field
    Ev  : W → K T → Set
    Ad  : W → (κ : K T) → E T κ → Set
    nx  : (B : W) (κ : K T) (e : E T κ) → Ad B κ e → W
    ev↑ : ∀ {B B′} → B ≤ B′ → ∀ {κ} → Ev B κ → Ev B′ κ
    ad↓ : ∀ {B B′} → B ≤ B′ → ∀ {κ e} (a′ : Ad B′ κ e) → Σ (Ad B κ e) (λ a → nx B κ e a ≤ nx B′ κ e a′)
    nx↑ : ∀ {B κ e} (a : Ad B κ e) → B ≤ nx B κ e a

module _ {P : Po} {T : KS} (Q : PS P T) where
  open Po P
  open PS Q
  PH : W → HB T → Set
  PH B hz = ⊤
  PH B (hs h) = PH B h
  PH B (hl f) = ∀ n → PH B (f n)
  PH B (hΩ κ g) = Ev B κ × (∀ e (a : Ad B κ e) → PH (nx B κ e a) (g e))

  PH-mono : ∀ {B B′} → B ≤ B′ → ∀ h → PH B h → PH B′ h
  PH-mono q hz p = tt
  PH-mono q (hs h) p = PH-mono q h p
  PH-mono q (hl f) p = λ n → PH-mono q (f n) (p n)
  PH-mono q (hΩ κ g) (ev , p) =
    ev↑ q ev , λ e a′ → PH-mono (proj₂ (ad↓ q {κ} {e} a′)) (g e) (p e (proj₁ (ad↓ q {κ} {e} a′)))

  PH-⊞ : ∀ {B} a h → PH B a → PH B h → PH B (a ⊞ h)
  PH-⊞ a hz pa ph = pa
  PH-⊞ a (hs h) pa ph = PH-⊞ a h pa ph
  PH-⊞ a (hl f) pa ph = λ n → PH-⊞ a (f n) pa (ph n)
  PH-⊞ a (hΩ κ g) pa (ev , ph) = ev , λ e x → PH-⊞ a (g e) (PH-mono (nx↑ {κ = κ} {e} x) a pa) (ph e x)

psStep : ∀ {P T} → PS P T → PS P (step T)
psStep {P} {T} Q = record { Ev = Ev⁺ ; Ad = Ad⁺ ; nx = nx⁺ ; ev↑ = ev↑⁺ ; ad↓ = ad↓⁺ ; nx↑ = nx↑⁺ }
  where
  open Po P
  open PS Q
  Ev⁺ : W → K (step T) → Set
  Ev⁺ B (inj₁ κ) = Ev B κ
  Ev⁺ B (inj₂ _) = ⊤
  Ad⁺ : W → (κ : K (step T)) → E (step T) κ → Set
  Ad⁺ B (inj₁ κ) e = Ad B κ e
  Ad⁺ B (inj₂ _) c = Σ W (λ V → B ≤ V × PH Q V c)
  nx⁺ : (B : W) (κ : K (step T)) (e : E (step T) κ) → Ad⁺ B κ e → W
  nx⁺ B (inj₁ κ) e a = nx B κ e a
  nx⁺ B (inj₂ _) c a = proj₁ a
  ev↑⁺ : ∀ {B B′} → B ≤ B′ → ∀ {κ} → Ev⁺ B κ → Ev⁺ B′ κ
  ev↑⁺ q {inj₁ κ} ev = ev↑ q ev
  ev↑⁺ q {inj₂ _} ev = tt
  ad↓⁺ : ∀ {B B′} → B ≤ B′ → ∀ {κ e} (a′ : Ad⁺ B′ κ e) → Σ (Ad⁺ B κ e) (λ a → nx⁺ B κ e a ≤ nx⁺ B′ κ e a′)
  ad↓⁺ q {inj₁ κ} {e} a′ = ad↓ q {κ} {e} a′
  ad↓⁺ q {inj₂ _} (V , w , p) = (V , tr q w , p) , rf
  nx↑⁺ : ∀ {B κ e} (a : Ad⁺ B κ e) → B ≤ nx⁺ B κ e a
  nx↑⁺ {κ = inj₁ κ} {e} a = nx↑ {κ = κ} {e} a
  nx↑⁺ {κ = inj₂ _} (V , w , p) = w

psSup : ∀ {P} {J : Set} {G : J → KS} → ((i : J) → PS P (G i)) → PS P (sup J G)
psSup Q = record
  { Ev = λ B κ → PS.Ev (Q (proj₁ κ)) B (proj₂ κ)
  ; Ad = λ B κ → PS.Ad (Q (proj₁ κ)) B (proj₂ κ)
  ; nx = λ B κ → PS.nx (Q (proj₁ κ)) B (proj₂ κ)
  ; ev↑ = λ q {κ} → PS.ev↑ (Q (proj₁ κ)) q
  ; ad↓ = λ q {κ} {e} → PS.ad↓ (Q (proj₁ κ)) q {proj₂ κ} {e}
  ; nx↑ = λ {B} {κ} {e} → PS.nx↑ (Q (proj₁ κ)) {B} {proj₂ κ} {e} }

PH-up : ∀ {P T} (Q : PS P T) {B} c → PH Q B c → PH (psStep Q) B (up c)
PH-up Q hz p = tt
PH-up Q (hs c) p = PH-up Q c p
PH-up Q (hl f) p = λ n → PH-up Q (f n) (p n)
PH-up Q (hΩ κ g) (ev , p) = ev , λ e a → PH-up Q (g e) (p e a)

PH-ι : ∀ {P} {J : Set} {G : J → KS} (Q : (i : J) → PS P (G i)) i {B} c → PH (Q i) B c → PH (psSup Q) B (ι i c)
PH-ι Q i hz p = tt
PH-ι Q i (hs c) p = PH-ι Q i c p
PH-ι Q i (hl f) p = λ n → PH-ι Q i (f n) (p n)
PH-ι Q i (hΩ κ g) (ev , p) = ev , λ e a → PH-ι Q i (g e) (p e a)

-- 塔上的路径
module _ {P : Po} {U : KS} (Q : PS P U) where
  PSL : ∀ m → PS P (Tw U m)
  PSL hz = Q
  PSL (hs x) = psStep (PSL x)
  PSL (hl f) = psSup (λ n → PSL (f n))
  PSL (hΩ κ g) = psSup (λ e → PSL (g e))

triv : ∀ {P T} → PS P T
triv {P} = record { Ev = λ _ _ → ⊤ ; Ad = λ _ _ _ → ⊤ ; nx = λ B _ _ _ → B
              ; ev↑ = λ _ _ → tt ; ad↓ = λ q _ → tt , q ; nx↑ = λ _ → Po.rf P }

-- 上抬: 指标分量平凡 (含指标分量的旧种类), 第 c 个分量沿用
FQ : ∀ {P U} → PS P U → (i : Ix U) → PS P (FX U i)
FQ Q (inj₁ _) = triv
FQ Q (inj₂ c) = PSL Q (hs c)

lift : ∀ {P U} → PS P U → PS P (XSof U)
lift {P} {U} Q = psSup {P} {Ix U} {FX U} (FQ Q)
```
