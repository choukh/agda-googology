# 第 1 层的读回下界: 对一切合法的第 0 层树 (搬到收缩见证的折叠)

验收文件. [YiL1Read](YiL1Read.lagda.md) 逐字搬到 [YiWitFold](YiWitFold.lagda.md): 只换模块名与导入, 链内模块换成 `YiWit` 的搬运件, 塔的 `Lw-tw`, `lgl→Lw`, `Tw`, `T⁺ʷ`, `TΛ` 取 `WF` (YiWitFold), 折叠 `W.Ψ` 仍是 YiDlFold 的 `Fold dl`. 定理与原文同名; 下文的讲解是原文.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiWitL1Read where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_)
open import Data.Maybe.Base using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase
import OCF.Lean.YiLamFold as WL
import OCF.Lean.YiDlFold as W
import OCF.Lean.YiWitFold as WF
import OCF.Lean.YiNextAcc as NA
open NA using (_⊴_; z⊴; s⊴s; ⊴s; ⊴l; l⊴; ⊴b; nd; em⊴; u⊴; em-shift)
open import OCF.Lean.YiLamNFuel using (pol)
open import OCF.Lean.YiLamFold using (finOf)
open import OCF.Lean.YiWitVOne using (V2)
open import OCF.Lean.YiWitShpSq using (s₂)
import OCF.Lean.YiLeanCore as M
import OCF.Lean.YiLeanFold as MF
import OCF.Lean.YiLeanTw3 as MT
import OCF.Lean.YiLeanAccFin as MA
import OCF.Lean.YiLeanValFin as MV
open import OCF.Lean.YiLeanValRel using
  ( Corr; cz; cs; cl; RelF; START; Pl; pz; ps; AgW; Agree
  ; zr; ssr; sr; lr; llr; br; ndr; emr; tnr; tlr; ur; us )
open import OCF.Lean.YiLeanValFold using (FOLD)
open import OCF.Lean.YiNextValRel using (RR; LR; lz; ls; ll; rz; rs; rl; rc; rt; WR; XR; read≅; levR)
open import OCF.Lean.YiNextValFin using (toM; toM-R; toM-lgl; toM-LR)
open import OCF.Lean.YiDlVRel using (ΨRʷ; vLRʷ)
open import OCF.Lean.YiWitVBtbo using (Vw; lvRʷ)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≅→≼)
```

## 1 主线一侧的派发与目标层 1 上的主引理

```agda
d₁ : (J : M.LF) → MF.Way (M.suc M.zero) J
d₁ M.zero = MF.keep (inj₁ tt) refl
d₁ (M.suc k) = MF.fold
d₁ (M.lim f) = MF.fold
d₁ (M.lc k g) = MF.fold

x₁ : ∀ K → MF.Ext (M.suc M.zero) K
x₁ K r = d₁ (MF.lev K r)

ag₁ : ∀ J → AgW (d₁ J) (L.suc L.zero)
ag₁ M.zero cz = L.via L.z≅ L.zero
ag₁ (M.suc k) (cs c) (L.via () L.zero)
ag₁ (M.suc k) (cs c) (L.via e (L.suc ()))
ag₁ (M.lim f) (cl c) (L.via () L.zero)
ag₁ (M.lim f) (cl c) (L.via e (L.suc ()))
ag₁ (M.lc k g) ()

foldM₁ : ∀ (a : MT.R) (l : M.Lgl M.zero a) {κ} → Corr κ MT.⌜ a ⌝ → ∀ {ℓ} (p : L.suc L.zero L.<ᴵ ℓ) (σ : L.Simᴵ κ ℓ) →
  RelF (M.suc M.zero) (L.ψ p σ (L.Ω κ)) (MF.Ψ (M.suc M.zero) (MT.lv a l) (x₁ MT.⌜ a ⌝) M.G.top)
foldM₁ a l c p σ = FOLD (MT.lv a l) (M.suc M.zero) (ps pz) (x₁ MT.⌜ a ⌝) p (cs cz) (λ r → ag₁ (MF.lev MT.⌜ a ⌝ r)) σ
  (START MT.⌜ a ⌝ c)
```

## 2 派发相关, 互模拟

一致折叠在 `Tψ` 里的派发 `cmpw V2 s₂` 是燃料搜索 `dlev 1`: 层号字面为 0 时保留在根位置, 否则折叠.

```agda
wr₁ : ∀ {J J′} → LR J J′ → WR (M.suc M.zero) (suc zero) (d₁ J) (pol (λ n → n) (suc zero) J′)
wr₁ lz = tt
wr₁ (ls {k′ = k′} e) with finOf k′
... | just _ = tt
... | nothing = tt
wr₁ (ll e) = tt

T₁ : (a : R) → Lgl zero a → Raw (suc zero)
T₁ a l = W.Ψ (suc zero) (Vw a l) (λ r → W.cmpw V2 s₂ (a , l , r)) G.top

R₁ : ∀ a (l : Lgl zero a) →
  RR (M.suc M.zero) (suc zero) (MF.Ψ (M.suc M.zero) (MT.lv (toM a) (toM-lgl a l)) (x₁ MT.⌜ toM a ⌝) M.G.top) (T₁ a l)
R₁ a l = ΨRʷ (ls lz) v (λ r r′ q → wr₁ (levR (vLRʷ v) r r′ q)) rt
  where v = lvRʷ (toM-R a) (toM-lgl a l) l (toM-LR a l)
```

## 3 主线的关系换成 `NA._⊴_`

`top` 上主线的规则 `tnr` 落到 `topS` (嵌入的第 0 层树); 一致折叠一侧没有对应的结点, 所以结论放在任一 θ 之上 (`plus 1 θ top` 正是那个结点).

```agda
br-em₀ : ∀ θ {y : L.Ordᶜ L.zero} {a a′} → RelF (M.suc M.zero) y (M.G.em tt a) → RR M.zero zero a a′ →
  y ⊴ plus (suc zero) θ (G.em tt a′)
br-em₀ θ zr e = z⊴
br-em₀ θ (llr h) e = l⊴ (λ n → br-em₀ θ (h n) e)
br-em₀ θ {a′ = a′} (emr p) e = em-shift θ (≼-trans p (≅→≼ (read≅ e))) a′ refl

br-em₁ : ∀ θ {y : L.Ordᶜ (L.suc L.zero)} {a a′} → RelF (M.suc M.zero) y (M.G.em tt a) → RR M.zero zero a a′ →
  y ⊴ plus (suc zero) θ (G.em tt a′)
br-em₁ θ zr e = z⊴
br-em₁ θ (llr h) e = l⊴ (λ n → br-em₁ θ (h n) e)
br-em₁ θ (emr ()) e
br-em₁ θ (ur d) e = u⊴ (br-em₀ θ d e)

lowR : ∀ {y : L.Ordᶜ L.zero} a → y ≼ NA.read a → y ≼ MA.read (toM a)
lowR a q = ≼-trans q (≅→≼ (L.≅-sym (read≅ (toM-R a))))

br-top₀ : ∀ θ {y : L.Ordᶜ L.zero} → RelF (M.suc M.zero) y (M.G.lc (inj₁ tt) (λ a → M.G.em tt a)) →
  y ⊴ plus (suc zero) θ G.top
br-top₀ θ zr = z⊴
br-top₀ θ (llr h) = l⊴ (λ n → br-top₀ θ (h n))
br-top₀ θ (br d) = ⊴b (br-em₀ θ d rt)
br-top₀ θ (ndr {q = ()} c h)

br-top₁ : ∀ θ {y : L.Ordᶜ (L.suc L.zero)} → RelF (M.suc M.zero) y (M.G.lc (inj₁ tt) (λ a → M.G.em tt a)) →
  y ⊴ plus (suc zero) θ G.top
br-top₁ θ zr = z⊴
br-top₁ θ (llr h) = l⊴ (λ n → br-top₁ θ (h n))
br-top₁ θ (br d) = ⊴b (br-em₁ θ d rt)
br-top₁ θ (ndr {q = L.zero} cz h) = nd (λ y a q → br-em₁ θ (h y (toM a) (lowR a q)) (toM-R a))
br-top₁ θ (ndr {q = L.suc ()} c h)
br-top₁ θ (ur d) = u⊴ (br-top₀ θ d)

br₀ : ∀ θ {y : L.Ordᶜ L.zero} {t t′} → RelF (M.suc M.zero) y t → RR (M.suc M.zero) (suc zero) t t′ →
  y ⊴ plus (suc zero) θ t′
br₀ θ zr e = z⊴
br₀ θ (ssr d) (rs e) = s⊴s (br₀ θ d e)
br₀ θ (sr d) (rs e) = ⊴s (br₀ θ d e)
br₀ θ (lr n d) (rl e) = ⊴l n (br₀ θ d (e n))
br₀ θ (llr h) e = l⊴ (λ n → br₀ θ (h n) e)
br₀ θ (br {r = inj₁ _} d) (rc {r′ = inj₁ _} _ h) = ⊴b (br₀ θ d (h M.G.top G.top rt))
br₀ θ (ndr {q = ()} c h) e
br₀ θ (tnr tt d) rt = br-top₀ θ d
br₀ θ (tlr i () d) e

br₁ : ∀ θ {y : L.Ordᶜ (L.suc L.zero)} {t t′} → RelF (M.suc M.zero) y t → RR (M.suc M.zero) (suc zero) t t′ →
  y ⊴ plus (suc zero) θ t′
br₁ θ zr e = z⊴
br₁ θ (ssr d) (rs e) = s⊴s (br₁ θ d e)
br₁ θ (sr d) (rs e) = ⊴s (br₁ θ d e)
br₁ θ (lr n d) (rl e) = ⊴l n (br₁ θ d (e n))
br₁ θ (llr h) e = l⊴ (λ n → br₁ θ (h n) e)
br₁ θ (br {r = inj₁ _} d) (rc {r′ = inj₁ _} _ h) = ⊴b (br₁ θ d (h M.G.top G.top rt))
br₁ θ (ndr {r = inj₁ _} {q = L.zero} cz h) (rc {r′ = inj₁ _} _ hh) =
  nd (λ y a q → br₁ θ (h y (toM a) (lowR a q)) (hh (toM a) a (toM-R a)))
br₁ θ (ndr {q = L.suc ()} c h) e
br₁ θ (tnr tt d) rt = br-top₁ θ d
br₁ θ (tlr i () d) e
br₁ θ (ur d) e = u⊴ (br₀ θ d e)
```

## 4 结论

```agda
lower₁ : ∀ a (l : Lgl zero a) {κ} → Corr κ MT.⌜ toM a ⌝ → ∀ {ℓ} (p : L.suc L.zero L.<ᴵ ℓ) (σ : L.Simᴵ κ ℓ) θ →
  L.ψ p σ (L.Ω κ) ⊴ plus (suc zero) θ (T₁ a l)
lower₁ a l c p σ θ = br₁ θ (foldM₁ (toM a) (toM-lgl a l) c p σ) (R₁ a l)

κ₁ : ∀ a → Lgl zero a → L.Ordᴵ
κ₁ a l = L.toLevel (MA.read (toM a)) (MV.HS-read (toM a) (toM-lgl a l))

lower-read₁ : ∀ a (l : Lgl zero a) {ℓ} (p : L.suc L.zero L.<ᴵ ℓ) (σ : L.Simᴵ (κ₁ a l) ℓ) θ →
  L.ψ p σ (L.Ω (κ₁ a l)) ⊴ plus (suc zero) θ (T₁ a l)
lower-read₁ a l = lower₁ a l (MV.corr-read (toM a) (MV.HS-read (toM a) (toM-lgl a l)))
```
