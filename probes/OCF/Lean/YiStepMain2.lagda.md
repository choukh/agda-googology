# 主线的折叠在目标层 2 上, 与一致折叠互模拟

验收文件. 编译定理: `foldM₂` (主线 `FOLD` 取目标层 2, 派发 `d₂`: 层号字面为 0, 1 才保留; 参照 ψ₂(Ω_κ) 与主线的树 `RelF 2` 相关), `R₂ᵗ` (主线的树与 [YiStepTree](YiStepTree.lagda.md) 的派发 `cmpw V2 s₃` 下的一致折叠 `T₂ᵗ a l` 互模拟). 是 [YiL1Read](YiL1Read.lagda.md) `foldM₁`, `R₁` 在目标层 2 上的对应.
没有把 `RelF 2` 换成 `⊴²`: 层号 1 的结点规则 `n1` 的假设对一切 `⊴⁺` 相关的下标, `RelF 2` 的 `ndr` 只给 `RelF 1` 相关的 (见回报). 不陈述值.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiStepMain2 where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_)
open import Data.Maybe.Base using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.Level as L
import OCF.Lean.YiLeanCore as M
import OCF.Lean.YiLeanFold as MF
import OCF.Lean.YiLeanTw3 as MT
open import OCF.Lean.YiLeanValRel using (Corr; cz; cs; cl; RelF; START; pz; ps; AgW)
open import OCF.Lean.YiLeanValFold using (FOLD)
open import OCF.Lean.YiNextCore using (Raw; Lgl; module G) renaming (zero to zeroN; suc to sucN)
open import OCF.Lean.YiNextBase using (R)
import OCF.Lean.YiDlFold as W
open import OCF.Lean.YiLamNFuel using (pol)
open import OCF.Lean.YiLamFold using (finOf)
open import OCF.Lean.YiNextValRel using (RR; LR; lz; ls; ll; rt; WR; levR)
open import OCF.Lean.YiNextValFin using (toM; toM-R; toM-lgl; toM-LR)
open import OCF.Lean.YiDlVRel using (ΨRʷ; vLRʷ)
open import OCF.Lean.YiDlVBtbo using (Vw; lvRʷ)
open import OCF.Lean.YiDlVOne using (V2)
open import OCF.Lean.YiStepTree using (s₃; L2)
```

## 1 主线一侧

```agda
d₂ : (J : M.LF) → MF.Way (M.suc (M.suc M.zero)) J
d₂ M.zero = MF.keep (inj₂ (inj₁ tt)) refl
d₂ (M.suc M.zero) = MF.keep (inj₁ tt) refl
d₂ (M.suc (M.suc k)) = MF.fold
d₂ (M.suc (M.lim f)) = MF.fold
d₂ (M.suc (M.lc k g)) = MF.fold
d₂ (M.lim f) = MF.fold
d₂ (M.lc k g) = MF.fold

x₂ : ∀ K → MF.Ext (M.suc (M.suc M.zero)) K
x₂ K r = d₂ (MF.lev K r)

ag₂ : ∀ J → AgW (d₂ J) (L.suc (L.suc L.zero))
ag₂ M.zero cz = L.via L.z≅ (L.suc L.zero)
ag₂ (M.suc M.zero) (cs cz) = L.via (L.s≅ L.z≅) L.zero
ag₂ (M.suc (M.suc k)) (cs (cs c)) (L.via (L.s≅ ()) L.zero)
ag₂ (M.suc (M.suc k)) (cs (cs c)) (L.via (L.s≅ e) (L.suc (L.suc ())))
ag₂ (M.suc (M.lim f)) (cs (cl c)) (L.via (L.s≅ ()) L.zero)
ag₂ (M.suc (M.lim f)) (cs (cl c)) (L.via (L.s≅ e) (L.suc (L.suc ())))
ag₂ (M.suc (M.lc k g)) (cs ())
ag₂ (M.lim f) (cl c) (L.via () L.zero)
ag₂ (M.lim f) (cl c) (L.via () (L.suc L.zero))
ag₂ (M.lc k g) ()

foldM₂ : ∀ (a : MT.R) (l : M.Lgl M.zero a) {κ} → Corr κ MT.⌜ a ⌝ →
  ∀ {ℓ} (p : L.suc (L.suc L.zero) L.<ᴵ ℓ) (σ : L.Simᴵ κ ℓ) →
  RelF (M.suc (M.suc M.zero)) (L.ψ p σ (L.Ω κ)) (MF.Ψ (M.suc (M.suc M.zero)) (MT.lv a l) (x₂ MT.⌜ a ⌝) M.G.top)
foldM₂ a l c p σ = FOLD (MT.lv a l) (M.suc (M.suc M.zero)) (ps (ps pz)) (x₂ MT.⌜ a ⌝) p (cs (cs cz))
  (λ r → ag₂ (MF.lev MT.⌜ a ⌝ r)) σ (START MT.⌜ a ⌝ c)
```

## 2 互模拟

```agda
wr₂ : ∀ {J J′} → LR J J′ →
  WR (M.suc (M.suc M.zero)) (sucN (sucN zeroN)) (d₂ J) (pol (λ n → n) (sucN (sucN zeroN)) J′)
wr₂ lz = tt
wr₂ (ls lz) = tt
wr₂ (ls (ls {k′ = k′} e)) with finOf k′
... | just _ = tt
... | nothing = tt
wr₂ (ls (ll e)) = tt
wr₂ (ll e) = tt

T₂ᵗ : (a : R) → Lgl zeroN a → Raw L2
T₂ᵗ a l = W.Ψ L2 (Vw a l) (λ r → W.cmpw V2 s₃ (a , l , r)) G.top

R₂ᵗ : ∀ a (l : Lgl zeroN a) →
  RR (M.suc (M.suc M.zero)) L2 (MF.Ψ (M.suc (M.suc M.zero)) (MT.lv (toM a) (toM-lgl a l)) (x₂ MT.⌜ toM a ⌝) M.G.top) (T₂ᵗ a l)
R₂ᵗ a l = ΨRʷ (ls (ls lz)) v (λ r r′ q → wr₂ (levR (vLRʷ v) r r′ q)) rt
  where v = lvRʷ (toM-R a) (toM-lgl a l) l (toM-LR a l)
```
