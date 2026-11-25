# 验收一侧: 有限层号加 ω 层的分级实例, `Leaf` 与 `LowKeep` 实填, 一处值的检验

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 判决: 编译定理, 无前提. 层号取 "有限的 n 或 ω" (`Lvω`), 块、折叠、行照 `YiAbsGFin` 填; 关系在有限层是 `YiDCRel.M̃`, 在 ω 层是 `YiLMLow.Mω` 的同一种封闭.
> 在 `gradedω`, `domsω` 上: `rd0ω`, `leafω̃` (读法: ω 层上 ν 是自然数或 ω), `lowKeepω` (有限层用 `lowKeepᶠ`, ω 层用 `LFω`; 量化域: 路线 `R₀`, 路径 `inl n (pthᶠ s)`, 底 `GBω`).
> 检验: 第 ω 层的 Ω 树折到第 0 层, 值不低于 ψ₀(Ω_ω) 的参照 (`valω`), 也不低于每个 ψ₀(Ω_m) 的 (`valωᴰ`); 推导 `hΩω` 存在. 不给出什么: 其余的律, 上折 (`Dn` 取空), ω 层作目标, 一般的 `lim g`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLMCheck where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps using (Ωt; Ωt-nz)
open import OCF.Lean.YiLegPath using (_≤_; self; ins; inl; inlu; Ev) renaming (Rt to Rtᴸ)
open import OCF.Lean.YiLegFold using (ψs; nzs; B₀)
open import OCF.Lean.YiAbsLeg using (hdΩ; ChT⁺; Bsᴸ; Btᴸ; dnᴸ)
import OCF.Align.EboLeanDef as E
open E using (HC; ψ; natT; _<ᵀ_; []<; hd<; lv<; ar<)
open import OCF.Align.EboLeanBase using (_≤ᵀ_; NF; n[]; n∷; nψ; nf-ψ; nf-Ω; GB; gp; gtl; gh; gw; gc)
open import OCF.Align.EboLeanTree using (hc)
open import OCF.Align.StandardOmega using (f1)
open import OCF.Align.Value using (_≼_)
open import OCF.Lean.YiNFOCase using (n1ᴮ; flatGB)
open import OCF.Lean.YiMEBase using (read; Rt; lower⁰)
open import OCF.Lean.YiANFam using (fin; slot; M; Nw; ψᴺ; Ωᴺ)
open import OCF.Lean.YiANKp using (≤ⁿ-refl)
open import OCF.Lean.YiAbsSimInst using (𝕍)
open import OCF.Lean.YiAbsFrame
open import OCF.Lean.YiAbsSim
open import OCF.Lean.YiAbsGIface
open import OCF.Lean.YiAbsGEbo using (refᴱ)
open import OCF.Lean.YiAbsGFin using (slT′)
open import OCF.Lean.YiASIface using (Sbᶠ; s0; pthᶠ; GBᴬ)
open import OCF.Lean.YiASProofLow using (lowKeepᶠ)
open import OCF.Lean.YiASProofMin using (mΩt)
open import OCF.Lean.YiDCRel using (M̃; Rdᴰ; app≤; rd0ᴰ; leafᴰ)
open import OCF.Lean.YiDCExit using (exitᴰ; nf-low; pre[]; ct-low)
open import OCF.Lean.YiLMLow
```

## 块, 折叠, 行

层号 `fn n` 读作 `fin n`, `ω` 读作 `lim fin`. ω 层的第 m 个孩子在层号 `fn m`, 槽位 (m, t) 的槽位层是 `fn (slot m t)`.

```agda
data Lvω : Set where
  fn : ℕ → Lvω
  ω  : Lvω

lv : Lvω → L
lv (fn n) = fin n
lv ω      = ωL

chLω : (ℓ : Lvω) → Ch (lv ℓ) → Lvω
chLω (fn (suc n)) _ = fn n
chLω ω            m = fn m

chTω : (ℓ : Lvω) (c : Ch (lv ℓ)) → ChT⁺ (lv ℓ) c → Tr (lv (chLω ℓ c))
chTω (fn (suc n)) _ (y , _) = y
chTω ω            m (y , _) = y

incω : ∀ {j} (ℓ : Lvω) (c : Ch (lv ℓ)) → lv j ≤ lv (chLω ℓ c) → lv j ≤ lv ℓ
incω (fn (suc n)) _ w = ins w
incω ω            m w = inl m w

incUω : ∀ {j} (ℓ : Lvω) → Ch (lv ℓ) → ((c : Ch (lv ℓ)) → lv j ≤ lv (chLω ℓ c)) → lv j ≤ lv ℓ
incUω (fn (suc n)) _ ws = ins (ws tt)
incUω ω            _ ws = inlu ws

blkω : Block
blkω = record
  { Lv = Lvω ; Tr = λ ℓ → Tr (lv ℓ) ; Ch = λ ℓ → Ch (lv ℓ) ; chL = chLω ; ChT = λ ℓ → ChT⁺ (lv ℓ) ; chT = chTω
  ; _⊑_ = λ j ℓ → lv j ≤ lv ℓ ; self = self ; inc = incω ; incU = incUω
  ; up = λ x c ye → up x c (proj₁ ye) (proj₂ ye) ; hd = hdΩ
  ; _◃_ = λ {ℓ} x y → lv ℓ ⊢ x ◃ y ; Leg = λ _ → ⊤ }

dnω : (ℓ : Lvω) → Bsᴸ (lv ℓ) → (c : Ch (lv ℓ)) → Tr (lv ℓ) → Bsᴸ (lv (chLω ℓ c))
dnω (fn (suc n)) b c x = dnᴸ (suc (fin n)) b c x
dnω ω            b m x = dnᴸ ωL b m x

foldω : Fold blkω
foldω = record
  { Bs = λ ℓ → Bsᴸ (lv ℓ) ; LegB = λ _ _ → ⊤ ; Bt = λ j → Btᴸ (lv j) ; LegT = λ _ _ → ⊤
  ; ψ  = λ ℓ b j w β x → ψs (lv ℓ) (proj₁ b) (proj₁ (proj₂ b)) (proj₂ (proj₂ b)) (lv j) w (proj₁ β) (proj₂ β) x
  ; ψβ = λ ℓ b j w β x → ψs (lv ℓ) (proj₁ b) (proj₁ (proj₂ b)) (proj₂ (proj₂ b)) (lv j) w (proj₁ β) (proj₂ β) x
                       , nzs (lv ℓ) (proj₁ b) (proj₁ (proj₂ b)) (proj₂ (proj₂ b)) (lv j) w (proj₁ β) (proj₂ β) x
  ; dn = dnω }

slLω : (ℓ : Lvω) → Pos (lv ℓ) → Lvω
slLω (fn (suc n)) p = fn (slot n p)
slLω ω            p = fn (slot (proj₁ p) (proj₂ p))

slTω : (ℓ : Lvω) (p : Pos (lv ℓ)) → Br (lv ℓ) p → Tr (lv (slLω ℓ p))
slTω (fn (suc n)) p = slT′ n p
slTω ω            p = slT′ (proj₁ p) (proj₂ p)

sucω : Lvω → Lvω
sucω (fn n) = fn (suc n)
sucω ω      = ω

rowsω : Rows blkω foldω
rowsω = record
  { sc = suc ; Sl = λ ℓ → Pos (lv ℓ) ; slL = slLω ; SlT = λ ℓ → Br (lv ℓ) ; slT = slTω ; nd = Ω
  ; Ωt = λ ℓ → Ωt (lv ℓ) ; Dn = λ _ _ → ⊥ ; upf = λ ()
  ; sucL = sucω ; ΩL = λ k _ → k ; lift = λ k _ → k }
```

## 关系, 读法, 量化域

`Bdω`, `Wlω` 在有限层逐字是 `YiASIface.gradedᴬ`, `domsᴬ` 的; ω 层作源时底值对着 ψ_j(t₀), 底满足 `GBω`, 路线是 `R₀` (`Gbω`), 路径是 `inl n (pthᶠ s)`. ω 层作目标不在量化域里.

```agda
ix : Lvω → E.T
ix (fn n) = natT n
ix ω      = ωᵀ

Rω : (ℓ : Lvω) → E.T → Tr (lv ℓ) → Set
Rω (fn n) s x = M̃ n s x
Rω ω      s x = Σ E.T λ t → (s ≤ᵀ t) × Mω t x

Rdω : Lvω → E.T → Set
Rdω (fn n) ν = Rdᴰ n ν
Rdω ω      ν = (Σ ℕ λ m → ν ≡ natT m) ⊎ (ν ≡ ωᵀ)

Nuω : (ℓ : Lvω) → Pos (lv ℓ) → E.T → Set
Nuω (fn (suc n)) p κ = Nw n p κ
Nuω ω            p κ = Nw (proj₁ p) (proj₂ p) κ

Bdω : (ℓ j : Lvω) → Bsᴸ (lv ℓ) → Btᴸ (lv j) → E.T → Set
Bdω (fn n) (fn j) b β t₀ = M j (ψᴺ j t₀) (proj₁ β) × GBᴬ n b t₀
Bdω ω      (fn j) b β t₀ = M j (ψᴺ j t₀) (proj₁ β) × GBω (proj₂ (proj₂ b)) t₀
Bdω ℓ      ω      b β t₀ = ⊥

Gbω : (ℓ : Lvω) → Bsᴸ (lv ℓ) → Set
Gbω (fn n) b = Σ ℕ λ N → n ≡ suc N
Gbω ω      b = proj₂ (proj₁ (proj₂ b)) ≡ R₀

Wlω : (j ℓ : Lvω) → lv j ≤ lv ℓ → Set
Wlω (fn j) (fn n) w = Σ (Sbᶠ n j) λ s → w ≡ pthᶠ s
Wlω (fn j) ω      w = Σ ℕ λ n → Σ (Sbᶠ n j) λ s → w ≡ inl n (pthᶠ s)
Wlω ω      ℓ      w = ⊥

gradedω : Graded blkω foldω rowsω refᴱ 𝕍
gradedω = record
  { ℓ₀ = fn 0 ; v = read ; R = Rω ; Rd = Rdω ; Nu = Nuω ; bt = proj₁
  ; cl = λ ℓ t → ψ (ix ℓ) t ∷ [] ; Cx = λ _ _ → E.T ; app = λ {_} {j} t₀ a → ψ (ix j) (t₀ ++ a) ∷ []
  ; Bd = λ {ℓ} {j} b w β t₀ → Bdω ℓ j b β t₀ }

domsω : Doms blkω foldω
domsω = record { Gx = λ _ _ → ⊤ ; Gb = Gbω ; Wl = λ {j} {ℓ} w → Wlω j ℓ w ; Gl = λ _ _ → ⊥ }
```

## 三条律

```agda
open Laws gradedω domsω using (Rd0; Leaf; LowKeep)

nat<ω : ∀ m → natT m <ᵀ ωᵀ
nat<ω zero    = []<
nat<ω (suc m) = hd< (ar< []<)

rd0ω : Rd0
rd0ω {ℓ = fn n} e = rd0ᴰ {ℓ = n} e
rd0ω {ℓ = ω}    e with rd0ᴰ {ℓ = 0} e
... | m , q , _ = inj₁ (m , q)

leafω̃ : Leaf
leafω̃ {ℓ = fn n} r                 = leafᴰ {ℓ = n} r
leafω̃ {ℓ = ω}    (inj₁ (m , refl)) = Ωω , inj₁ (hd< (lv< (nat<ω m))) , leafω
leafω̃ {ℓ = ω}    (inj₂ refl)       = Ωω , inj₂ refl , leafω

lowKeepω : LowKeep
lowKeepω {ℓ = fn n} {j = fn j} b w β t₀ gb wl bd gx (t , le , m) =
  ψᴺ j (t₀ ++ t) , app≤ j t₀ le , lowKeepᶠ b w β t₀ gb wl bd gx m
lowKeepω {ℓ = ω} {j = fn j} (ε , (ρc , _) , B) _ (β , nβ) t₀ refl (n , s , refl) (hβ , gb) gx (t , le , m) =
  ψᴺ j (t₀ ++ t) , app≤ j t₀ le , LFω s t₀ ε ρc B gb β nβ hβ m
lowKeepω {ℓ = fn n} {j = ω} b w β t₀ gb ()
lowKeepω {ℓ = ω}    {j = ω} b w β t₀ gb ()
```

## 检验: 第 ω 层的 Ω 树折到第 0 层

标准底, 底值是第 0 层 Ω 树, 前缀为空, 路径 `inl 0 self`. `valω` 是 `leafω` 接 `LFω` 接 `lower⁰`; `valωᴰ` 经接口上的两条与 `YiDCExit.exitᴰ`.
ψ₀(Ω_ω) 是可数标准形, 所以它的推导存在 (`hΩω`).

```agda
nωᵀ : NF ωᵀ
nωᵀ = n∷ (nψ n[] n1ᴮ (flatGB f1)) tt n[]

gΩω : GB [] Ωω Ωω
gΩω (gp (gh _))                                 = []<
gΩω (gp (gw _ (gp (gh _))))                     = hd< (lv< []<)
gΩω (gp (gw _ (gp (gw _ ()))))
gΩω (gp (gw _ (gp (gc _ (gp (gh _))))))         = []<
gΩω (gp (gw _ (gp (gc _ (gp (gw _ ()))))))
gΩω (gp (gw _ (gp (gc _ (gp (gc _ ()))))))
gΩω (gp (gw _ (gp (gc _ (gtl ())))))
gΩω (gp (gw _ (gtl ())))
gΩω (gp (gc _ ()))
gΩω (gtl ())

nfΩω : NF (ψᴺ 0 Ωω)
nfΩω = nf-ψ n[] (nf-Ω nωᵀ) gΩω

hΩω : HC (ψᴺ 0 Ωω)
hΩω = hc nfΩω (ct-low Ωω)

valω : (ε : Ev ωL) (ρc : (k : ℕ) → Rtᴸ (fin k)) (h : HC (ψᴺ 0 Ωω))
     → Rt h ≼ read (ψs ωL ε (ρc , R₀) (B₀ ωL) zero (inl 0 self) (Ωt zero) (Ωt-nz zero) (Ωt ωL))
valω ε ρc h = lower⁰ (LFω s0 [] ε ρc (B₀ ωL) gbω₀ (Ωt zero) (Ωt-nz zero) (mΩt 0) leafω) h

valωᴰ : ∀ m (ε : Ev ωL) (ρc : (k : ℕ) → Rtᴸ (fin k)) (h : HC (ψᴺ 0 (Ωᴺ m)))
      → Rt h ≼ read (ψs ωL ε (ρc , R₀) (B₀ ωL) zero (inl 0 self) (Ωt zero) (Ωt-nz zero) (Ωt ωL))
valωᴰ m ε ρc h =
  exitᴰ (lowKeepω {ℓ = ω} {j = fn 0} (ε , (ρc , R₀) , B₀ ωL) (inl 0 self) (Ωt zero , Ωt-nz zero) [] refl (0 , s0 , refl)
           (mΩt 0 , gbω₀) tt (leafω̃ {ℓ = ω} (inj₁ (m , refl))))
        (nf-low (pre[] m) (≤ⁿ-refl m)) nfΩω (ct-low Ωω) h
```
