# 判决的规格: 拒绝错的树 (底座)

> 底座, 不含记号. 结论写在 [VerdictSpec](VerdictSpec.lagda.md). 本文的路径 $p_1,p_2$ 是从验收节抄来的自然数列表, 陈述不读记号.
>
> - `reject-rise`: $\mathtt{S}=$ `rise` 在 $\Omega\cdot2$ 上不 `OK`: 目标 $\Omega+1$ 里有字面的路径到 $\Omega$. `accept-S₁`: 同一个层号, 同一个模式, 只改这一对的判决就 `OK`. `two-correct`: 两个不同的函数 `S₁`, `S₂`, 都正确, 都被问到, 树 `Eq`: 这是唯一性定理的非空实例. `tree-S₀≠S₁`: 这一对真的改变树, 在 `Zero.dev` 报告的路径上.
> - **关键的否定 `wrong-fold`.** `OK` 不提折叠. 所以把上升的链丢掉的折叠 (`PW`) 判决完全相同, 却不 `Eq` 于 `PF`. 判决的正确性**单独**不是规格; 规格是 "折叠方程加判决正确".

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.VerdictSpecReject where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; cong)
open import OCF.Align.InaccTreeBase using
  (Lv; zero; suc; lim; limᴼ; Ordᴸ; Pre; Low; at; outL; intoL; Tree; limᵢ; up; Ω; toLv; _+_; iter; Verdict; pen; rise; FGH; Sim; σ-id)
open import OCF.Align.InaccFloorTree using (Sib; Mode; fin; lt; sib; bel; upM; verdict; chM; natL; zv; module PF)
open import OCF.Align.VerdictSpecBase using (module Eqx; coe⁺)
open import OCF.Align.VerdictSpecUniq using (Kd; kp; kr; kd; module Uniq)
```

## §1 层号 $\Omega\cdot2$ 与第一个被问到的对

$\Omega\cdot2$ 的层号是 `A₂ = limᴼ 0 (x ↦ Ω+x)`. 模式 `lt q₂` 的目标是 $\Omega+1$. 走过分支 $x=1$ 之后模式成为 `sib`, 节点 $\Omega$ 对目标 $\Omega+1$: 这就是 `take 30 (p₁ ++ p₂) ++ [1]` 第一次问 `S` 的那一对 (对变量 `S` 归约到 `S LΩ (suc LΩ)`; 探针, 见 [VerdictSpecAccept](VerdictSpecAccept.lagda.md)).

```agda
Ω₁ : Ordᴸ (natL 1)
Ω₁ = Ω (natL 1)

LΩ : Lv
LΩ = toLv Ω₁

A₂ : Lv
A₂ = toLv (Ω₁ + Ω₁)

𝟏 𝟐 : Ordᴸ zero
𝟏 = Tree.suc Tree.zero
𝟐 = Tree.suc 𝟏

q₂ : Pre A₂
q₂ = inj₂ (𝟐 , inj₁ tt)

_ : at A₂ q₂ ≡ suc LΩ
_ = refl

m₂ : Mode A₂ (suc LΩ)
m₂ = lt q₂ refl

S₀ : Sib
S₀ _ _ = rise

module Reject (B₀ : Ordᴸ zero → Set) (𝟏∈ : B₀ 𝟏) where
  open Eqx S₀ B₀

  ¬rise : CVx {LΩ} {suc LΩ} rise → ⊥
  ¬rise (cvr k) = k (inj₁ tt) tt (≈ᴮ-refl LΩ)

  reject-rise : OK A₂ m₂ → ⊥
  reject-rise w = ¬rise (proj₁ (proj₂ w 𝟏 𝟏∈) (inj₁ tt) tt)

  -- 整个层号不好: `LvT` 要这一条链
  reject-LvT : B₀ 𝟐 → LvT A₂ → ⊥
  reject-LvT 𝟐∈ w with proj₁ w q₂ (𝟐∈ , tt)
  ... | inj₂ (ok , _) = reject-rise ok
```

## §2 改掉这一对就通过

`S₁`: 只在 "`limᴼ 0` 对它的后继" 上穿透. 这里 `B₀` 只含 1, 全部路径列得出来. 这说明 `OK` 不是空的条件, 也说明 `S₀` 错只错在这一对 (在这个 `B₀` 上). `Accept₁` 对任何在这一对上答对的 `S` 成立.

```agda
S₁ : Sib
S₁ j@(limᴼ zero _) (suc i@(limᴼ zero _)) = pen (inj₁ tt) (coe⁺ i j)
S₁ _ _ = rise

-- 模式 `bel` 永远 `OK`
module BelOK (S : Sib) (B₀ : Ordᴸ zero → Set) where
  open Eqx S B₀

  cvb : ∀ {k i} (σ : Sim k i) → SD σ → ∀ r → AdmB k r → CVx (verdict S {k} (bel σ) r)
  cvb {k} {i} σ s r d = cvp (proj₁ (σ r)) _ (s r d) (≈≡ refl (proj₂ (σ r)) (≈ᴮ-refl _)) (bl (proj₂ (σ r)))

  okBel : ∀ k {i} (σ : Sim k i) → SD σ → OK k (bel σ)
  okBel zero       σ s = tt
  okBel (suc k)    σ s = cvb σ s , okBel k _ (sd∘ι (suc k) tt σ s tt)
  okBel (lim f)    σ s = cvb σ s , (λ n → okBel (f n) _ (sd∘ι (lim f) n σ s tt))
  okBel (limᴼ k g) σ s = cvb σ s , (λ x b → okBel (g x) _ (sd∘ι (limᴼ k g) x σ s b))

-- 对 `S` 的唯一要求: 这一对答对
Ans₁ : Sib → Set
Ans₁ S = S LΩ (suc LΩ) ≡ pen (inj₁ tt) (coe⁺ LΩ LΩ)

B₁ : Ordᴸ zero → Set
B₁ x = x ≡ 𝟏

module Accept₁ (S : Sib) (h : Ans₁ S) where
  open Eqx S B₁
  open BelOK S B₁ using (okBel)

  P0Ω : P0 LΩ
  P0Ω _ refl = tt

  cv-LΩ : CVx {LΩ} {suc LΩ} (S LΩ (suc LΩ))
  cv-LΩ = subst CVx (sym h) (cvp (inj₁ tt) _ tt (≈ᴮ-refl LΩ) (bc P0Ω P0Ω))

  cv0 : CVx {zero} {suc LΩ} (zv (suc LΩ))
  cv0 = cvp {zero} {suc LΩ} (inj₂ (inj₁ (inj₁ tt))) (λ y → y) tt z≈ (bl {zero} {suc LΩ} {r = inj₂ (inj₁ (inj₁ tt))} refl)

  -- 所有节点层都是 0 或 Ω
  ok-1 : OK (natL 1) {suc LΩ} sib
  ok-1 = (λ { (inj₁ _) _ → cv0 }) , tt

  ok-LΩ : OK LΩ {suc LΩ} sib
  ok-LΩ = (λ where
             (inj₁ (inj₁ _)) _ → cv0
             (inj₂ (_ , inj₁ _)) (refl , _) → cv0)
        , (λ { x refl → ok-1 })

  ok-1+Ω : OK (suc LΩ) {suc LΩ} sib
  ok-1+Ω = (λ where
              (inj₁ _) _ → cv-LΩ
              (inj₂ (inj₁ (inj₁ _))) _ → cv0
              (inj₂ (inj₂ (_ , inj₁ _))) (refl , _) → cv0)
         , ok-LΩ

  accept-S : OK A₂ m₂
  accept-S =
    (λ where
       (inj₁ (inj₁ _)) _ → cv0
       (inj₂ (_ , inj₁ _)) (refl , _) → cv-LΩ
       (inj₂ (_ , inj₂ (inj₁ (inj₁ _)))) (refl , _) → cv0
       (inj₂ (_ , inj₂ (inj₂ (_ , inj₁ _)))) (refl , (refl , _)) → cv0)
    , (λ { x refl → ok-1+Ω })

  -- 目标是字面前驱的那条链不问 `S`
  no-self : ∀ (r : Pre LΩ) → AdmB LΩ r → at LΩ r ≈ᴮ LΩ → ⊥
  no-self (inj₁ (inj₁ _)) _ ()
  no-self (inj₂ (_ , inj₁ _)) (refl , _) ()

  ok-lt : OK (suc LΩ) {LΩ} (lt (inj₁ tt) refl)
  ok-lt = (λ where
             (inj₁ _) _ → cvr no-self
             (inj₂ r) d → cvp {at LΩ r} {LΩ} r _ d (≈ᴮ-refl _) (bl {at LΩ r} {LΩ} {r = r} refl))
        , okBel LΩ (σ-id LΩ) (sd-id {LΩ})

  zt : Zt LΩ
  zt = inj₁ (inj₁ tt) , tt , refl

  ch-LΩ : ChOK (suc LΩ) (inj₁ tt)
  ch-LΩ = inj₂ (ok-lt , zt)

  lvt-1 : LvT (natL 1)
  lvt-1 = (λ { (inj₁ _) _ → inj₁ refl }) , tt

  lvt-LΩ : LvT LΩ
  lvt-LΩ = (λ where
              (inj₁ (inj₁ _)) _ → inj₁ refl
              (inj₂ (_ , inj₁ _)) (refl , _) → inj₁ refl)
         , tt , (λ { x refl → lvt-1 })

  lvt-1+Ω : LvT (suc LΩ)
  lvt-1+Ω = (λ where
               (inj₁ _) _ → ch-LΩ
               (inj₂ (inj₁ (inj₁ _))) _ → inj₁ refl
               (inj₂ (inj₂ (_ , inj₁ _))) (refl , _) → inj₁ refl)
          , lvt-LΩ

  lvg-A₂ : LvG A₂
  lvg-A₂ = inj₁ refl , tt , (λ { x refl → ch-LΩ , lvt-LΩ })

  zt₊ : Zt (suc LΩ)
  zt₊ = inj₂ (inj₁ (inj₁ tt)) , tt , refl

accept-S₁ : Eqx.OK S₁ B₁ A₂ m₂
accept-S₁ = Accept₁.accept-S S₁ refl

-- 一个与 `S₁` 不同、在这个 `B₁` 上同样正确的判决: 差别在没有被问到的层号对上
S₂ : Sib
S₂ (lim f) (suc k) = pen (inj₁ tt) (coe⁺ k (lim f))
S₂ j i = S₁ j i

module TwoCorrect where
  open Uniq S₁ S₂ B₁
  module A₁ = Accept₁ S₁ refl
  module A₂′ = Accept₁ S₂ refl

  S₁≠S₂ : S₁ (lim natL) (natL 1) ≡ rise
  S₁≠S₂ = refl

  S₂≠S₁ : Σ _ λ b → S₂ (lim natL) (natL 1) ≡ pen (inj₁ tt) b
  S₂≠S₁ = _ , refl

  tg₊ : Tg (suc LΩ) (suc LΩ)
  tg₊ = tg (≈ᴮ-refl _) A₁.lvt-1+Ω A₂′.lvt-1+Ω A₁.zt₊ A₂′.zt₊ (tt , (λ { x refl → tt }) , λ { z z′ refl refl _ → ≈ᴮ-refl _ })

  r-A₂ : LvR A₂
  r-A₂ = tt , (λ { x refl → tt , (λ { y refl → tt }) , λ { z z′ refl refl _ → ≈ᴮ-refl _ } }) , (λ { z z′ refl refl _ → ≈ᴮ-refl _ })

  -- 两个不同的 `S`, 都正确, `S` 真的被问到: 树 `Eq`
  two-correct : Eq (suc LΩ) (L.ψᵖ m₂ (Ω A₂)) (R.ψᵖ m₂ (Ω A₂))
  two-correct = ψ≃ m₂ m₂ A₁.accept-S A₂′.accept-S tg₊ (Ω≃ (≈ᴮ-refl A₂) A₁.lvg-A₂ A₂′.lvg-A₂ r-A₂)
```

## §3 这一对真的改变树

`kdT`: 第 0 层树的头. `twalk`: 沿路径走 (先剥 `suc`). `Eq zero` 保持它们 (`walk-Eq`), 所以它们是 `Eq` 的不变量. 这里的路径就是 `Zero.dev` 报告的.

```agda
data H : Set where
  hz hs hl : H

hd : Ordᴸ zero → H
hd Tree.zero     = hz
hd (Tree.suc _)  = hs
hd (Tree.lim _)  = hl

strip : Ordᴸ zero → Ordᴸ zero
strip (Tree.suc x) = strip x
strip x            = x

kid : ℕ → Ordᴸ zero → Ordᴸ zero
kid n (Tree.lim f) = f n
kid n x            = x

twalk : List ℕ → Ordᴸ zero → Ordᴸ zero
twalk []      x = x
twalk (n ∷ p) x = twalk p (kid n (strip x))

p₁ p₂ : List ℕ
p₁ = 1 ∷ 0 ∷ 0 ∷ 2 ∷ 1 ∷ 0 ∷ 0 ∷ 3 ∷ 0 ∷ []
p₂ = 2 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 2 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 2 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 1 ∷ []

dev-path : List ℕ
dev-path = (p₁ ++ p₂) ++ (0 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ [])

module Trees (S S′ : Sib) (B₀ : Ordᴸ zero → Set) where
  open Uniq S S′ B₀

  strip-Eq : ∀ {x y : Ordᴸ zero} → Eq zero x {zero} y → Eq zero (strip x) {zero} (strip y)
  strip-Eq z≃ = z≃
  strip-Eq (s≃ e) = strip-Eq e
  strip-Eq (l≃ h) = l≃ h
  strip-Eq (i≃ {r = ()} _ _ _ _ _)
  strip-Eq (uˡ {d = ()} _ _)
  strip-Eq (uʳ {d = ()} _ _)

  kid-Eq : ∀ n {x y : Ordᴸ zero} → Eq zero x {zero} y → Eq zero (kid n x) {zero} (kid n y)
  kid-Eq n z≃ = z≃
  kid-Eq n (s≃ e) = s≃ e
  kid-Eq n (l≃ h) = h n
  kid-Eq n (i≃ {r = ()} _ _ _ _ _)
  kid-Eq n (uˡ {d = ()} _ _)
  kid-Eq n (uʳ {d = ()} _ _)

  hd-Eq : ∀ {x y : Ordᴸ zero} → Eq zero x {zero} y → hd x ≡ hd y
  hd-Eq z≃ = refl
  hd-Eq (s≃ e) = refl
  hd-Eq (l≃ h) = refl
  hd-Eq (i≃ {r = ()} _ _ _ _ _)
  hd-Eq (uˡ {d = ()} _ _)
  hd-Eq (uʳ {d = ()} _ _)

  walk-Eq : ∀ p {x y : Ordᴸ zero} → Eq zero x {zero} y → Eq zero (twalk p x) {zero} (twalk p y)
  walk-Eq []      e = e
  walk-Eq (n ∷ p) e = walk-Eq p (kid-Eq n (strip-Eq e))

  -- 走到一处种类不同, 就不 `Eq`
  refute : ∀ p {x y : Ordᴸ zero} → hd (twalk p x) ≢ hd (twalk p y) → Eq zero x {zero} y → ⊥
  refute p n e = n (hd-Eq (walk-Eq p e))

module T₀ = PF S₀
module T₁ = PF S₁

tree-S₀≠S₁ : hd (twalk dev-path T₀.TΩΩ) ≢ hd (twalk dev-path T₁.TΩΩ)
tree-S₀≠S₁ ()
```

## §4 关键的否定: 判决全对, 折叠错

`PW` 与 `PF` 只差上升的子句: 链不迭代, 永远取 $\Omega_{\text{节点层}}$. 这是 [Uniform4Expt](Uniform4Expt.lagda.md) 的 (B) 的形状: 链点缺了重入. **判决是同一个函数 `verdict S`, `OK` 根本不提折叠**, 所以 `S` 正确时 `PW` 也 "正确". 但 $\psi_0(\Omega_2)$ 上它与 `PF` 不 `Eq`, 对任何 `S`, `S′`, `B₀`.

```agda
module PW (S : Sib) where
  ψʷ : ∀ {k i} → Mode k i → Ordᴸ k → Ordᴸ i
  ψʷ {i = i} m Tree.zero    = Ω i
  ψʷ {i = i} m (Tree.suc a) = Tree.lim (iter (ψʷ m a +_) Tree.zero)
  ψʷ m (Tree.lim f) = Tree.lim (λ n → ψʷ m (f n))
  ψʷ {k} {i} m (limᵢ r f) with verdict S m r
  ... | pen r′ b = limᵢ r′ (λ y → ψʷ m (f (intoL k r (b (outL i r′ y)))))
  ... | rise     = Tree.lim (λ n → ψʷ m (f (intoL k r (Ω (at k r)))))
  ψʷ {suc k}    m (up d x) = ψʷ (upM (suc k) d m) x
  ψʷ {lim f}    m (up d x) = ψʷ (upM (lim f) d m) x
  ψʷ {limᴼ k g} m (up d x) = ψʷ (upM (limᴼ k g) d m) x

  Tʷ : Lv → Ordᴸ zero
  Tʷ L = ψʷ (fin 0 refl) (Ω L)

path₂ : List ℕ
path₂ = 1 ∷ 0 ∷ 0 ∷ []

module Wrong (S S′ : Sib) (B₀ : Ordᴸ zero → Set) where
  module F = PF S
  module W = PW S′
  open Trees S S′ B₀
  open Uniq S S′ B₀ using (Eq)

  wrong-kinds : hd (twalk path₂ (F.T (natL 2))) ≢ hd (twalk path₂ (W.Tʷ (natL 2)))
  wrong-kinds ()

  wrong-fold : Eq zero (F.T (natL 2)) {zero} (W.Tʷ (natL 2)) → ⊥
  wrong-fold = refute path₂ wrong-kinds
```
