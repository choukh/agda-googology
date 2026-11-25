# 根 Ω 调用处的两种供给重设计
验收文件；当前槽位版 `LocalStep` 在最小层有实例，且可重编实际回灌链。
仅向规范 Ω 根槽位要前缀仍不能从原 `Bdᵍ` 供给；用 β 的证据替代槽位底证据的 `BetaStep` 也被否定。
后一个否定针对一般 Ω 行，反例 g 并非规范 Ω 树的 g；不据此否定原 `LowKeep`。
入口：`local-one`、`local-chain`、`no-local-root`、`no-beta-step`。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSULocal where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiTBRow using (Rb; rb-no)
open import OCF.Lean.YiLKIface using (StartU; feed; OK)
open import OCF.Lean.YiGIInst using (Bdᵍ)
open import OCF.Lean.YiSUIface using (PrefixU)
open import OCF.Lean.YiSUMin using (rd-zero; step′-one)
open import OCF.Lean.YiSUSupport using (start-one)
open import OCF.Lean.YiSUBridge using (bd)
open import OCF.Lean.YiSUNeg using (ℓ; o; a; t; p; ν; nu; cof-a; g; c; low; branch; okB; small-step; whole-branch)
open import OCF.Lean.YiSUBound using (fin-bound; fs; fz; no-ω²)
open import OCF.Lean.YiGICheck using (leaf-fin)
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiGIRel as GR
import OCF.Align.EboLeanDef as E
open import OCF.Align.EboLeanBase using (<-≤; <ᵀ-irrefl)

PrefixAt : ∀ ℓ → Base ℓ → E.T → (p : Pos ℓ) → E.T → Set
PrefixAt ℓ B t p ν = GR.R (at ℓ p) (E.ψ ν t ∷ []) (proj₁ (B (at ℓ p) (posW ℓ p)))

LocalStep : L → Set
LocalStep ℓ = (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) → OK B
  → (t a : E.T) (p : Pos ℓ) (ν : E.T) → GR.Nu ℓ p ν → PrefixAt ℓ B t p ν
  → E.cof a ≡ E.cΩ ν → (g : Br ℓ p → Tr ℓ) (n : ℕ) (c : Br ℓ p)
  → GR.Low ℓ p (E.γT (t ++ a) ν n) c
  → GR.R ℓ (E.fsT a (E.γT (t ++ a) ν n)) (g c)
  → GR.Low ℓ p (E.γT (t ++ a) ν (suc n)) (feed ℓ o r B p g c)

local-one : LocalStep ℓ
local-one o r B gb t a (inj₂ (tt , inj₁ tt)) ν nu pref e g n c lc m with rd-zero nu
... | refl = step′-one o r B gb t all a (inj₂ (tt , inj₁ tt)) [] (GR.c0 refl) e g n c lc m
  where
  all : PrefixU B t
  all (inj₂ (tt , inj₁ tt)) κ q with rd-zero q
  ... | refl = pref
  all (inj₂ (tt , inj₂ ())) κ q
local-one o r B gb t a (inj₂ (tt , inj₂ ())) ν nu pref e g n c lc m

module Chain (ℓ : L) (start : StartU ℓ) (step : LocalStep ℓ)
  (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) (gb : OK B)
  (t a : E.T) (p : Pos ℓ) (ν : E.T) (nu : GR.Nu ℓ p ν) (pref : PrefixAt ℓ B t p ν)
  (e : E.cof a ≡ E.cΩ ν) (g : Br ℓ p → Tr ℓ)
  (hg : ∀ η c → GR.Low ℓ p η c → GR.R ℓ (E.fsT a η) (g c)) where
  local-chain : ∀ n → GR.Low ℓ p (E.γT (t ++ a) ν n)
    (iter (feed ℓ o r B p g) (fromBr ℓ p zero) (suc n))
  local-chain zero = start o r B gb t a p ν nu e g
  local-chain (suc n) = step o r B gb t a p ν nu pref e g n _ (local-chain n)
    (hg (E.γT (t ++ a) ν n) _ (local-chain n))

RootSlot : (ℓ : L) → Pos ℓ → Set
RootSlot (nd sS h) p = p ≡ inj₂ (tt , inj₁ tt)
RootSlot (nd sL h) p = ⊥
RootSlot (nd (sΩ k) h) p = p ≡ inj₁ (inj₁ tt)

LocalRootSupply : L → Set
LocalRootSupply ℓ = (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) (β : Tr⁺ zero) (t : E.T)
  → r ≡ MT.rbᶻ ℓ → Bdᵍ (o , r , B) (z≤ ℓ) β t
  → ∀ {a} → GR.R ℓ a (proj₁ (Ωt ℓ))
  → (p : Pos ℓ) → RootSlot ℓ p → (ν : E.T) → GR.Nu ℓ p ν → PrefixAt ℓ B t p ν

no-local-root : LocalRootSupply ℓ → ⊥
no-local-root supply = <ᵀ-irrefl (<-≤ (E.hd< (E.ar< E.[]<))
  (fin-bound (supply o (MT.rbᶻ ℓ) (B₀ ℓ) (next⁺ (Ωt zero)) t refl bd (leaf-fin 1) p refl ν nu) (fs fz)))

BetaStep : L → Set
BetaStep ℓ = (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) → OK B
  → (t a : E.T) (p : Pos ℓ) (ν : E.T) → GR.Nu ℓ p ν
  → E.cof a ≡ E.cΩ ν → (g : Br ℓ p → Tr ℓ)
  → (∀ η c → GR.Low ℓ p η c → GR.R ℓ (E.fsT a η) (g c))
  → (β : Tr⁺ zero) → H.M⁰ (E.ψ [] t ∷ []) (proj₁ β)
  → (n : ℕ) (c : Br ℓ p) → GR.Low ℓ p (E.γT (t ++ a) ν n) c
  → GR.Low ℓ p (E.γT (t ++ a) ν (suc n)) (feed ℓ o r B p g c)

no-beta-step : BetaStep ℓ → ⊥
no-beta-step step = no-ω²
  (step o (rb-no ℓ) (B₀ ℓ) okB t a p ν nu cof-a g whole-branch (next⁺ (Ωt zero)) small-step 0 c low)
```
