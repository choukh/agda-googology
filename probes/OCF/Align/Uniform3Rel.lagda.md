# 统一形 (三): 依目标的地板见证与层对齐互模拟

> 接 [Uniform3](Uniform3.lagda.md). 把 RelativeBase §1、§7、§8 与 Relative §3、§5 中标签路线实际用到的部分搬到修正的折叠上. $\cong^\mathsf A$ 本身与地板无关, 直接从 Relative 导入.
>
> 改动: (1) `FlrLab[ c ]`/`FW[ c ]` 的前提 "$c\prec K$" 换成结论里的析取 "`Ign c K` 或有见证": 极限项 `fb K` 与 $c$ 不可比较 (比较蕴含 LPO), 所以 "$c\prec K$ 时才要见证" 这种写法在 `fb` 上判定不了; 静态信息总给得出这个析取. (2) `pickWᵗ` 在记号上比较见证. (3) `fold-≅0ᴬ`/`fold-≅1ᴬ` 的 `uᴬ (us n)` 子句与 `uz` 同形 (`flo-∼` 的极限子句是 `fb∼`). (4) 没有搬: `≅ˢ` 路线的 `≈[ c ]`、`AlignT`、`alignHigh`、`bRᵗ` (在 OmegaSqA 之后不再被用到).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Uniform3Rel where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Prefix using (Z; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; trˢ; tr⁻ˢ; addˢ; H1-pen)
import OCF.Align.EBO as E
open E using (T; PT; natT; fsT; cof; cΩ; Ωt; _<ᵀ_; cofA; []<) renaming (ψ to ψᵗ)
open import OCF.Align.Correspond using (Lab; l0; l1; lω)
open import OCF.Align.StandardOmega using (NF₁; NF₁-fsn)
open import OCF.Align.SystemOmega using (Occ; oh; od; os; ot)
open import OCF.Align.Stage2 using (Ωᵗ; tO)
open import OCF.Align.Stage2Label using (one⁰)
open import OCF.Align.OmegaKBase using (tΩ2)
open import OCF.Align.DecoupleBase using (ΩΩ)
open import OCF.Align.Decouple using (Idx; lvI; Ieq)
open import OCF.Align.GoodLBase
open import OCF.Align.OmegaExpBase using (cofW; H1W; gtW; ne-w; 1<γ)
open import OCF.Align.NonTightBase using (I₁)
open import OCF.Align.UniformS
open import OCF.Align.Uniform3Base
open import OCF.Align.Uniform3Depth1 using (_≈₁_; GA1; gr1)
open import OCF.Align.Uniform3 using (good∅ᴿ)
open import OCF.Align.Relative using (UpK; uz; us; Eqᴬ; zᴬ; sᴬ; lᴬ; lᵢᴬ; uᴬ; ŝᴬ; ĉᴬ; Rᴬ; _≅ᴬ_; R→≅ᴬ; ≅→Rᴬ; UpK-sym; ≅ᴬ-sym; R-flipᴬ; flipRᴬ;
  ≅ᴬ→≅ˢ₀; trˢ-≅ᴬ; tr⁻ˢ-≅ᴬ; backˢ-≅ᴬ; back⁻ˢ-≅ᴬ; ≅ᴬ-tr⁻ˢ; Ωˢ-≅ᴬ; R-convᴬ; addˢ-≅ᴬ) public
```

## §1 目标下界与可忽略的地板项

`Up c i`: 目标 $i\succeq c$. 计值中的一切目标都 $\succeq$ 起点目标 (派发只升目标: 穿透保持 $i$, 折叠的链在节点层 $j\succeq i$ 上算), 所以一个目标下界沿整个计值保持. `Ign c K`: 地板项 $K$ 平凡 ($\cong0$) 或 $\preceq c$. 关键观察 `ign-no`: 在目标 $i\succeq c$ 的弹栈里, `bound` 的当前最大者 $M\succeq i$ (`iM≼`), 可忽略的项永远不会严格超过它, 于是 `<ᴵ-dec` 永不走 "换最大者" 的分支.

```agda
Up : Ordᴵ → Ordᴵ → Set
Up c i = (c ≺ᴵ i) ⊎ (c ≅ᴵ i)

≺≼ : ∀ {a b d} → a ≺ᴵ b → (b ≺ᴵ d) ⊎ (b ≅ᴵ d) → a ≺ᴵ d
≺≼ s (inj₁ s′) = ≺ᴵ-trans s s′
≺≼ s (inj₂ e)  = ≺ᴵ-respʳ s e

≼≺ : ∀ {a b d} → (a ≺ᴵ b) ⊎ (a ≅ᴵ b) → b ≺ᴵ d → a ≺ᴵ d
≼≺ (inj₁ s) s′ = ≺ᴵ-trans s s′
≼≺ (inj₂ e) s′ = ≺ᴵ-respˡ e s′

Up-≅ : ∀ {c i i′} → Up c i → i ≅ᴵ i′ → Up c i′
Up-≅ (inj₁ s)  e = inj₁ (≺ᴵ-respʳ s e)
Up-≅ (inj₂ e′) e = inj₂ (≅ᴵ-trans e′ e)

Up-≺ : ∀ {c i j} → Up c i → i ≺ᴵ j → Up c j
Up-≺ u s = inj₁ (≼≺ u s)

Ign : Ordᴵ → Ordᴵ → Set
Ign c K = (K ≅ᴵ zero) ⊎ ((K ≺ᴵ c) ⊎ (K ≅ᴵ c))

```

```agda
one three : Ordᴵ
one = suc zero
three = suc (suc (suc zero))

s⊑s→≼ : ∀ {a c} → suc a ⊑ᴵ suc c → (a ≺ᴵ c) ⊎ (a ≅ᴵ c)
s⊑s→≼ (s⊑ e zero)    = inj₂ e
s⊑s→≼ (s⊑ e (suc q)) = inj₁ (via e q)

≼→⊑ : ∀ {a b} → (a ≺ᴵ b) ⊎ (a ≅ᴵ b) → a ⊑ᴵ b
≼→⊑ (inj₁ (via e q)) = ⊑ᴵ-trans (≅ᴵ→⊑ᴵ e) (Sim→⊑ᴵ (λ q′ → <ᴵ-trans q′ q))
≼→⊑ (inj₂ e) = ≅ᴵ→⊑ᴵ e

```

**可忽略的项, 带种类.** `IgnK c k`: `fk K` 项 (`isB` 为假) 要 `Ign c K`; `fb K` 项还可以是 $K\sqsubseteq c+1$. 后者弱于 $K\preceq c$: `K ⊑ suc c` 不给 $K$ 在 $c$ 里的字面子项 (极限 $K$ 与 $c$ 可以值相等而不 $\cong$), 但界 `Bd` 对 `fb K` 只要 $K\sqsubseteq\eta$, 所以够用.

```agda
IgnK : ∀ {K φ} → Ordᴵ → InF K φ → Set
IgnK {K} c k = Ign c K ⊎ ((isB k ≡ true) × (K ⊑ᴵ suc c))

IgnL : Ordᴵ → Flr → Set
IgnL c φ = ∀ {K} (k : InF K φ) → IgnK c k

floIgn : ∀ {c} k → k ⊑ᴵ suc c → IgnL c (flo k)
floIgn zero      le ()
floIgn (suc k″)  le ink = inj₁ (inj₂ (s⊑s→≼ le))
floIgn (lim f s) le inb = inj₂ (refl , le)

DemIgn : ∀ {K φ c η} (k : InF K φ) → IgnK c k → suc c ⊑ᴵ η → Dem η k
DemIgn k (inj₁ (inj₁ k0)) le = dem k (inj₂ k0)
DemIgn k (inj₁ (inj₂ kc)) le = dem k (inj₁ (≺-of-⊑ (⊑ᴵ-trans (sB kc) le)))
DemIgn {K} {η = η} k (inj₂ (b , kle)) le = subst (λ bb → DemB bb η K) (sym b) (⊑ᴵ-trans kle le)
```

## §2 依目标的地板见证

`FW[ c ]`/`FlrLab[ c ]`: 地板项要么对 $c$ 可忽略, 要么被前缀里出现的带 `Idx` 的下标支配. 弹栈行 `cloWᵗ` 用 `pickMax` 选一个支配一切的下标.

```agda
LW[_] : ∀ {φ} → Ordᴵ → Run φ → T → Set
LW[_] {φ} c R u = ∀ {i ℓ w} (ev : Ev ℓ φ) (p : i <ᴵ ℓ) (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false → Up c i →
                  LabL₊ i Ll (R ev p) (ψᵗ w u ∷ [])

LW→LW[] : ∀ {c φ} {R : Run φ} {u} → LW R u → LW[ c ] R u
LW→LW[] h ev p Iw ei ki u = h ev p Iw ei ki

FW[_] : Ordᴵ → Flr → T → PT → T → Set
FW[ c ] φ ps y ys = ∀ {K} (k : InF K φ) →
                    IgnK c k ⊎ Σ T λ w → Σ (Idx w) λ Iw → ((K ≺ᴵ lvI Iw) ⊎ (K ≅ᴵ lvI Iw)) × Ob w ps y ys

FW→FW[] : ∀ {c φ ps y ys} → FW φ ps y ys → FW[ c ] φ ps y ys
FW→FW[] F k with F k
... | inj₁ k0 = inj₁ (inj₁ (inj₁ k0))
... | inj₂ w = inj₂ w

FlrLab[_] : Ordᴵ → Flr → T → Set
FlrLab[ c ] φ ps = ∀ {K} (k : InF K φ) →
                   IgnK c k ⊎ Σ T λ w → Σ (Idx w) λ Iw → ((K ≺ᴵ lvI Iw) ⊎ (K ≅ᴵ lvI Iw)) × Occ w ps

FlrLab→[] : ∀ {c φ ps} → FlrLab φ ps → FlrLab[ c ] φ ps
FlrLab→[] F k with F k
... | inj₁ k0 = inj₁ (inj₁ (inj₁ k0))
... | inj₂ w = inj₂ w

FlrLab[]-ign : ∀ {c φ ps} → IgnL c φ → FlrLab[ c ] φ ps
FlrLab[]-ign G k = inj₁ (G k)

FW-popᵗ : ∀ {c fl π} → FlrLab[ c ] fl π → FW[ c ] (fl ⊔ fk zero) π ΩΩ []
FW-popᵗ F (inr ink) = inj₁ (inj₁ (inj₁ z≅))
FW-popᵗ F (inl k) with F k
... | inj₁ e = inj₁ e
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , λ θ → OccPre _ o)
```
**弹栈行与闭包定理.**

```agda
module _ {c φ} {ps : T} {y : PT} {ys : T} {t : Run (φ ⊔ fk zero)} {g : (η : Ordᴵ) → Run (φ ⊔ fk η)}
         (fw : FW[ c ] (φ ⊔ fk zero) ps y ys) (cs : cof (y ∷ ys) ≡ cΩ []) where

  pickWᵗ : ∀ {i ℓ w} → Up c i → (Iw : Idx w) → i ≅ᴵ lvI Iw → (B : Top i ℓ (φ ⊔ fk zero)) →
           Σ T λ w′ → Σ (Idx w′) λ Iw′ → (Bd B ⊑ᴵ suc (lvI Iw′)) × (∀ θ → Occ w′ (ψᵗ w (ps ++ fsT (y ∷ ys) θ) ∷ []))
  pickWᵗ {i} {ℓ} {w} u Iw ei B = Pick.pw Pk , Pick.pI Pk ,
      ubd B (≼→≺s (≼-trans (inj₂ ei) (Pick.pc Pk))) (λ k → pd k (Pick.pF Pk k)) , Pick.pP Pk
    where
    P′ : T → Set
    P′ w′ = ∀ θ → Occ w′ (ψᵗ w (ps ++ fsT (y ∷ ys) θ) ∷ [])
    wit : ∀ {K} (k : InF K (φ ⊔ fk zero)) → IgnK c k ⊎ (Σ T λ w₁ → Σ (Idx w₁) λ I₁ → (K ≼ lvI I₁) × P′ w₁)
    wit k with fw k
    ... | inj₁ g = inj₁ g
    ... | inj₂ (w₁ , I₁′ , kw , ob′) = inj₂ (w₁ , I₁′ , kw , (λ θ → od (ob′ θ)))
    Pk : Pick P′ (φ ⊔ fk zero) (IgnK c) (lvI Iw)
    Pk = pickMax (φ ⊔ fk zero) (IgnK c) wit Iw (λ θ → oh) (inj₂ (≅ᴵ-refl _))
    cW : suc c ⊑ᴵ suc (lvI (Pick.pI Pk))
    cW = sB (≼-trans u (≼-trans (inj₂ ei) (Pick.pc Pk)))
    pd : ∀ {K} (k : InF K (φ ⊔ fk zero)) → IgnK c k ⊎ (K ≼ lvI (Pick.pI Pk)) → Dem (suc (lvI (Pick.pI Pk))) k
    pd k (inj₁ g)  = DemIgn k g cW
    pd k (inj₂ kw) = dem k (inj₁ (≼→≺s kw))

  cloWᵗ : LW[ c ] t (ps ++ fsT (y ∷ ys) (natT 1)) →
          (∀ θ Y hY → Lab Y θ → NF₁ θ → natT 1 <ᵀ θ → LW[ c ] (g (toLevel Y hY)) (ps ++ fsT (y ∷ ys) θ)) →
          LW[ c ] (cloA 0 t g) (ps ++ (y ∷ ys))
  cloWᵗ h₀ hg {w = []} ev p Iw ei ki u = ⊥-elim (ne-w Iw ei ki refl)
  cloWᵗ h₀ hg {w = x ∷ xs} ev p Iw ei ki u =
    gŝ ki (trans (cofW (x ∷ xs) ps y ys) (trans (cong (cofA (x ∷ xs)) cs) (H1-pen x xs)))
       (proj₁ (proj₂ Pk)) (proj₁ (proj₂ (proj₂ Pk)))
       (λ θ → subst (Occ _) (sym (H1W x xs ps y ys cs θ)) (proj₂ (proj₂ (proj₂ Pk)) θ))
       (subst (LabL₊ _ Ll _) (sym (H1W x xs ps y ys cs (natT 1))) (h₀ ev p Iw ei ki u))
       (λ θ Y hY lY nθ lt e → subst (LabL₊ _ Ll _) (sym (H1W x xs ps y ys cs θ))
            (hg θ Y hY lY nθ lt (evη φ B (toLevel Y hY) e) (lim 0 (iF B)) Iw ei ki u))
    where
    B = bound (φ ⊔ fk zero) ev p
    Pk = pickWᵗ u Iw ei B

goodΩ̂0Wᵗ : ∀ {c fl} {P : Run fl} {π} → FlrLab[ c ] fl π → LW P π → LW[ c ] (Ω̂A 0 P) (π ++ ΩΩ ∷ [])
goodΩ̂0Wᵗ {fl = fl} {P} {π} F hP =
  cloWᵗ {t = fold 0 (fk zero) (λ e → e) P (Ωˢ (suc zero))} {g = λ η → fold 0 (fk η) (λ e q → e (suc q)) P (Ωˢ η)}
        (FW-popᵗ F) refl
        (LW→LW[] {R = fold 0 (fk zero) (λ e → e) P (Ωˢ (suc zero))}
                 (TlW.tlWV hP {φ = fk zero} {cv = λ e → e} {t = Ωˢ (suc zero)} (LabL-Ω one⁰ (hs hz) lab1 nf1 (≅ᴵ-refl _))))
        (λ θ Y hY lY nθ lt → LW→LW[] {R = fold 0 (fk (toLevel Y hY)) (λ e q → e (suc q)) P (Ωˢ (toLevel Y hY))}
                 (TlW.tlWV hP {φ = fk (toLevel Y hY)} {cv = λ e q → e (suc q)} {t = Ωˢ (toLevel Y hY)} (LabL-Ω Y hY lY nθ (≅ᴵ-refl _))))
```

## §3 三种地板

```agda
ψΩᵗ′ : T → T
ψΩᵗ′ b = ψᵗ Ωᵗ b ∷ []

FL-Ω₁ : ∀ b → FlrLab (fk one) (ψΩᵗ′ b)
FL-Ω₁ b ink = inj₂ (natT 1 , I₁ , inj₂ (≅ᴵ-refl _) , os oh)

FL-head : ∀ {K w u ys} (Iw : Idx w) → (K ≺ᴵ lvI Iw) ⊎ (K ≅ᴵ lvI Iw) → FlrLab (fk K) (ψΩᵗ′ (ψᵗ w u ∷ ys))
FL-head Iw kw ink = inj₂ (_ , Iw , kw , od oh)
```

## §4 折叠尊重 $\cong^\mathsf A$; 分支的互模拟

运行的层对齐互模拟 `_≈ᴬ_` 与行引理: Uniform2Base §7 的 `…R` 逐字, 只把 $\cong^\mathsf s$ 换成 $\cong^\mathsf A$. `limᵢRᴬ` 的折叠情形里链点经 `iter-R _≅ᴬ_` 层对齐地相关, 这正是 §1 缺的那一条.

```agda
infix 4 _≈ᴬ_
_≈ᴬ_ : ∀ {φ ψ} → Run φ → Run ψ → Set
_≈ᴬ_ {φ} {ψ} R R′ = ∀ {i i′ ℓ ℓ′} (ev : Ev ℓ φ) (p : i <ᴵ ℓ) (ev′ : Ev ℓ′ ψ) (p′ : i′ <ᴵ ℓ′) → i ≅ᴵ i′ → R ev p ≅ᴬ R′ ev′ p′

limRᴬ : ∀ {φ ψ} {F : ℕ → Run φ} {G : ℕ → Run ψ} → (∀ n → F n ≈ᴬ G n) → limA 0 F ≈ᴬ limA 0 G
limRᴬ h ev p ev′ p′ ei = lᴬ (λ n → h n ev p ev′ p′ ei)

sucRᴬ : ∀ {φ ψ} {R : Run φ} {R′ : Run ψ} → R ≈ᴬ R′ → sucRun R ≈ᴬ sucRun R′
sucRᴬ h ev p ev′ p′ ei = lᴬ (iter-R _≅ᴬ_ (λ e′ → addˢ-≅ᴬ (kd-≅ ei) (h ev p ev′ p′ ei) e′) zᴬ)

limᵢRᴬ : ∀ {φ ψ j j′} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {ac′ : ∀ {L} → Ev L ψ → j′ <ᴵ L}
         {H : Ordˢ j → Run φ} {H′ : Ordˢ j′ → Run ψ} →
         j ≅ᴵ j′ → (∀ x y → x ≅ᴬ y → H x ≈ᴬ H′ y) → limᵢA 0 ac H ≈ᴬ limᵢA 0 ac′ H′
limᵢRᴬ {ac = ac} {ac′ = ac′} {H = H} {H′ = H′} e h ev p ev′ p′ ei with <ᴵ-dec (ac ev) p | <ᴵ-dec (ac′ ev′) p′
... | injᵃ (via e₁ r₁) | injᵃ (via e₂ r₂) = lᵢᴬ (≅ᴵ-trans (≅ᴵ-sym e₁) (≅ᴵ-trans e e₂)) λ x y d →
  subst₂ (λ a b → H (tr⁻ˢ e₁ a) ev p ≅ᴬ H′ (tr⁻ˢ e₂ b) ev′ p′)
         (sym (out-intoˢ (<→◃ r₁) x)) (sym (out-intoˢ (<→◃ r₂) y))
         (h _ _ (tr⁻ˢ-≅ᴬ e₁ (≅ᴬ-tr⁻ˢ e₂ (R→≅ᴬ (<→◃ r₁) d))) ev p ev′ p′ ei)
... | injᵃ r | injᵇ s  = ⊥-elim (clash₁ e ei r s)
... | injᵃ r | injᶜ c′ = ⊥-elim (clash₂ e ei r c′)
... | injᵇ s | injᵃ r  = ⊥-elim (clash₁ (≅ᴵ-sym e) (≅ᴵ-sym ei) r s)
... | injᶜ c′ | injᵃ r = ⊥-elim (clash₂ (≅ᴵ-sym e) (≅ᴵ-sym ei) r c′)
... | injᵇ _ | injᵇ _  = lᴬ (λ m → h _ _ (iter-R _≅ᴬ_ (λ d → h _ _ d ev (ac ev) ev′ (ac′ ev′) e) (Ωˢ-≅ᴬ e) m) ev p ev′ p′ ei)
... | injᵇ _ | injᶜ _  = lᴬ (λ m → h _ _ (iter-R _≅ᴬ_ (λ d → h _ _ d ev (ac ev) ev′ (ac′ ev′) e) (Ωˢ-≅ᴬ e) m) ev p ev′ p′ ei)
... | injᶜ _ | injᵇ _  = lᴬ (λ m → h _ _ (iter-R _≅ᴬ_ (λ d → h _ _ d ev (ac ev) ev′ (ac′ ev′) e) (Ωˢ-≅ᴬ e) m) ev p ev′ p′ ei)
... | injᶜ _ | injᶜ _  = lᴬ (λ m → h _ _ (iter-R _≅ᴬ_ (λ d → h _ _ d ev (ac ev) ev′ (ac′ ev′) e) (Ωˢ-≅ᴬ e) m) ev p ev′ p′ ei)

ĉRᴬ : ∀ {φ ψ c c′ t₀ t₀′} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z} {g′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Z}
      {O₀ : Run φ} {O : (η : Ordᴵ) → c ⊑ᴵ η → Run φ} {O₀′ : Run ψ} {O′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Run ψ} →
      c ≅ᴵ c′ → t₀ ≅ᶻ t₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → g η e ≅ᶻ g′ η′ e′) →
      O₀ ≈ᴬ O₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → O η e ≈ᴬ O′ η′ e′) → ĉA 0 c t₀ g O₀ O ≈ᴬ ĉA 0 c′ t₀′ g′ O₀′ O′
ĉRᴬ ec dt dg h₀ h ev p ev′ p′ ei = ĉᴬ ec dt dg (h₀ ev p ev′ p′ ei) (λ η e η′ e′ eη → h η e η′ e′ eη ev p ev′ p′ ei)

ŝRᴬ : ∀ {φ ψ c c′} {T₀ : Run φ} {G : (η : Ordᴵ) → c ⊑ᴵ η → Run φ} {T₀′ : Run ψ} {G′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Run ψ} →
      c ≅ᴵ c′ → T₀ ≈ᴬ T₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → G η e ≈ᴬ G′ η′ e′) → ŝA 0 c T₀ G ≈ᴬ ŝA 0 c′ T₀′ G′
ŝRᴬ ec h₀ h ev p ev′ p′ ei = ŝᴬ (kd-≅ ei) ec (h₀ ev p ev′ p′ ei) (λ η e η′ e′ eη → h η e η′ e′ eη ev p ev′ p′ ei)

wkRᴬ : ∀ {φ φ′ ψ ψ′} {R : Run φ} {R′ : Run φ′} (le : ∀ {L} → Ev L ψ → Ev L φ) (le′ : ∀ {L} → Ev L ψ′ → Ev L φ′) →
       R ≈ᴬ R′ → wk 0 le R ≈ᴬ wk 0 le′ R′
wkRᴬ le le′ h ev p ev′ p′ ei = h (le ev) p (le′ ev′) p′ ei

cloRᴬ : ∀ {φ φ′} {t : Run (φ ⊔ fk zero)} {g : (η : Ordᴵ) → Run (φ ⊔ fk η)}
        {t′ : Run (φ′ ⊔ fk zero)} {g′ : (η : Ordᴵ) → Run (φ′ ⊔ fk η)} → φ ∼ᶠ φ′ →
        t ≈ᴬ t′ → (∀ η η′ → η ≅ᴵ η′ → g η ≈ᴬ g′ η′) → cloA 0 t g ≈ᴬ cloA 0 t′ g′
cloRᴬ {φ} {φ′} s ht hg ev p ev′ p′ ei =
  ŝᴬ (kd-≅ ei) (bound-≅ (⊔∼ s (fk∼ z≅)) ev p ev′ p′ ei) (ht ev p ev′ p′ ei)
     (λ η e η′ e′ eη → hg η η′ eη _ (lim 0 (iF (bound (φ ⊔ fk zero) ev p))) _ (lim 0 (iF (bound (φ′ ⊔ fk zero) ev′ p′))) ei)
```
`fold-≅0ᴬ`: 深度 0 的折叠 (`up zero` 子句两侧都弱化证据).

```agda
fold-≅0ᴬ : ∀ {fl fl′ φ φ′ k₁ k₂} {cv : ∀ {L} → Ev L φ → Simᴵ k₁ L} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ k₂ L}
           {P : Run fl} {P′ : Run fl′} {a : Ordˢ k₁} {b : Ordˢ k₂} →
           P ≈ᴬ P′ → a ≅ᴬ b → fold 0 φ cv P a ≈ᴬ fold 0 φ′ cv′ P′ b
fold-≅0ᴬ H zᴬ ev p ev′ p′ ei = H (proj₁ ev) p (proj₁ ev′) p′ ei
fold-≅0ᴬ H (sᴬ e) = sucRᴬ (fold-≅0ᴬ H e)
fold-≅0ᴬ H (lᴬ h) = limRᴬ (λ n → fold-≅0ᴬ H (h n))
fold-≅0ᴬ {k₁ = suc k′} {k₂ = suc k″} {cv = cv} {cv′ = cv′} H (uᴬ uz e) =
  wkRᴬ (λ ev → proj₁ ev , toFlo k′ (λ q → cv (proj₂ ev) (suc q))) (λ ev → proj₁ ev , toFlo k″ (λ q → cv′ (proj₂ ev) (suc q))) (fold-≅0ᴬ H e)
fold-≅0ᴬ {k₁ = lim f s} {k₂ = lim g t} {cv = cv} {cv′ = cv′} H (uᴬ (us n) e) =
  wkRᴬ (λ ev → proj₁ ev , toFlo (f n) (λ q → cv (proj₂ ev) (lim n q))) (λ ev → proj₁ ev , toFlo (g n) (λ q → cv′ (proj₂ ev) (lim n q))) (fold-≅0ᴬ H e)
fold-≅0ᴬ {k₁ = zero} {k₂ = zero} H (ŝᴬ k ec et eg) =
  ĉRᴬ ec (toZ-≅ (≅ᴬ→≅ˢ₀ et)) (λ η e η′ e′ eη → toZ-≅ (≅ᴬ→≅ˢ₀ (eg η e η′ e′ eη))) (fold-≅0ᴬ H et)
      (λ η e η′ e′ eη → fold-≅0ᴬ H (eg η e η′ e′ eη))
fold-≅0ᴬ {k₁ = zero} {k₂ = suc _}   H (ŝᴬ k ec et eg) = ⊥-elim (tf k)
fold-≅0ᴬ {k₁ = zero} {k₂ = lim _ _} H (ŝᴬ k ec et eg) = ⊥-elim (tf k)
fold-≅0ᴬ {k₁ = suc _}   {k₂ = zero} H (ŝᴬ k ec et eg) = ⊥-elim (tf (sym k))
fold-≅0ᴬ {k₁ = lim _ _} {k₂ = zero} H (ŝᴬ k ec et eg) = ⊥-elim (tf (sym k))
fold-≅0ᴬ {k₁ = suc _}   {k₂ = suc _}   H (ŝᴬ k ec et eg) = ŝRᴬ ec (fold-≅0ᴬ H et) (λ η e η′ e′ eη → fold-≅0ᴬ H (eg η e η′ e′ eη))
fold-≅0ᴬ {k₁ = suc _}   {k₂ = lim _ _} H (ŝᴬ k ec et eg) = ŝRᴬ ec (fold-≅0ᴬ H et) (λ η e η′ e′ eη → fold-≅0ᴬ H (eg η e η′ e′ eη))
fold-≅0ᴬ {k₁ = lim _ _} {k₂ = suc _}   H (ŝᴬ k ec et eg) = ŝRᴬ ec (fold-≅0ᴬ H et) (λ η e η′ e′ eη → fold-≅0ᴬ H (eg η e η′ e′ eη))
fold-≅0ᴬ {k₁ = lim _ _} {k₂ = lim _ _} H (ŝᴬ k ec et eg) = ŝRᴬ ec (fold-≅0ᴬ H et) (λ η e η′ e′ eη → fold-≅0ᴬ H (eg η e η′ e′ eη))
fold-≅0ᴬ H (ĉᴬ ec dt dg eo eO) = ĉRᴬ ec dt dg (fold-≅0ᴬ H eo) (λ η e η′ e′ eη → fold-≅0ᴬ H (eO η e η′ e′ eη))
fold-≅0ᴬ H (lᵢᴬ {p = q} e h) = limᵢRᴬ e (λ x y d → fold-≅0ᴬ H (h x y (≅→Rᴬ (<→◃ q) d)))
```
**深度 1.** `fold-≅1ᴬ` 的前提只有: 指数前缀的地板 $\sim$、指数前缀 $\approx^\mathsf A_1$、两侧尾巴层号 $\cong^\mathsf I$、根地板 $\sim$、尾巴 $\cong^\mathsf A$. 后继步的地板对齐不再是前提: `up zero` 处由 `flo-∼` 从层号 $\cong^\mathsf I$ 得到, `up (self n)` 处由 `l≅` 的第 $n$ 项. 与 Uniform2Depth1 的 `fold-≅1` 相比少了 `AlignD`, 与 RelativeBase 的 `fold-≅1ᵗ` 相比少了目标下界.

```agda
infix 4 _≈₁ᴬ_
_≈₁ᴬ_ : ∀ {φ ψ} → A 1 φ → A 1 ψ → Set
E ≈₁ᴬ E′ = ∀ {fl fl′} {P : Run fl} {P′ : Run fl′} → fl ∼ᶠ fl′ → P ≈ᴬ P′ → E P ≈ᴬ E′ P′

flo-∼ : ∀ {k k′} → k ≅ᴵ k′ → flo k ∼ᶠ flo k′
flo-∼ z≅     = fz∼
flo-∼ (s≅ e) = fk∼ e
flo-∼ (l≅ h) = fb∼ (l≅ h)

repRᴬ : ∀ {fl fl′ ψ ψ′} {Q : Run fl} {Q′ : Run fl′} {fr : A 1 ψ} {fr′ : A 1 ψ′} →
        fl ∼ᶠ fl′ → ψ ∼ᶠ ψ′ → Q ≈ᴬ Q′ → fr ≈₁ᴬ fr′ → ∀ m → repA 0 Q fr m ≈ᴬ repA 0 Q′ fr′ m
repRᴬ s sψ H F zero          = wkRᴬ proj₁ proj₁ H
repRᴬ s sψ H F (suc zero)    = F s H
repRᴬ s sψ H F (suc (suc m)) = wkRᴬ _ _ (F (⊔∼ s sψ) (repRᴬ s sψ H F (suc m)))

fold-≅1ᴬ : ∀ {flE flE′ φ φ′ k₁ k₂} {cv : ∀ {L} → Ev L φ → Simᴵ k₁ L} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ k₂ L}
           {E : A 1 flE} {E′ : A 1 flE′} {a : Ordˢ k₁} {b : Ordˢ k₂} →
           flE ∼ᶠ flE′ → E ≈₁ᴬ E′ → k₁ ≅ᴵ k₂ → φ ∼ᶠ φ′ → a ≅ᴬ b → fold 1 φ cv E a ≈₁ᴬ fold 1 φ′ cv′ E′ b
fold-≅1ᴬ sE HE ek sφ zᴬ s H = wkRᴬ _ _ (HE s H)
fold-≅1ᴬ sE HE ek sφ (sᴬ e) s H = limRᴬ (λ m → repRᴬ s (⊔∼ sE sφ) H (fold-≅1ᴬ sE HE ek sφ e) m)
fold-≅1ᴬ sE HE ek sφ (lᴬ h) s H = limRᴬ (λ n → fold-≅1ᴬ sE HE ek sφ (h n) s H)
fold-≅1ᴬ sE HE ek sφ (lᵢᴬ {p = q} e h) s H =
  limᵢRᴬ e (λ x y d → fold-≅1ᴬ sE HE ek sφ (h x y (≅→Rᴬ (<→◃ q) d)) s H)
fold-≅1ᴬ {k₁ = suc k′} {k₂ = suc k″} {cv = cv} {cv′ = cv′} sE HE (s≅ ek) sφ (uᴬ uz d) s H =
  wkRᴬ (λ { (u , (w , v)) → u , (w , toFlo k′ (λ q → cv v (suc q))) }) (λ { (u , (w , v)) → u , (w , toFlo k″ (λ q → cv′ v (suc q))) })
       (fold-≅1ᴬ sE HE ek (flo-∼ ek) d s H)
fold-≅1ᴬ {k₁ = lim f r} {k₂ = lim g t} {cv = cv} {cv′ = cv′} sE HE (l≅ hh) sφ (uᴬ (us n) d) s H =
  wkRᴬ (λ { (u , (w , v)) → u , (w , toFlo (f n) (λ q → cv v (lim n q))) }) (λ { (u , (w , v)) → u , (w , toFlo (g n) (λ q → cv′ v (lim n q))) })
       (fold-≅1ᴬ sE HE (hh n) (flo-∼ (hh n)) d s H)
fold-≅1ᴬ {k₁ = zero} {k₂ = zero} sE HE ek sφ (ŝᴬ k ec et eg) s H =
  ĉRᴬ ec (toZ-≅ (≅ᴬ→≅ˢ₀ et)) (λ η e η′ e′ eη → toZ-≅ (≅ᴬ→≅ˢ₀ (eg η e η′ e′ eη))) (fold-≅1ᴬ sE HE ek sφ et s H)
      (λ η e η′ e′ eη → fold-≅1ᴬ sE HE ek sφ (eg η e η′ e′ eη) s H)
fold-≅1ᴬ {k₁ = zero} {k₂ = suc _}   sE HE ek sφ (ŝᴬ k ec et eg) s H = ⊥-elim (tf k)
fold-≅1ᴬ {k₁ = zero} {k₂ = lim _ _} sE HE ek sφ (ŝᴬ k ec et eg) s H = ⊥-elim (tf k)
fold-≅1ᴬ {k₁ = suc _}   {k₂ = zero} sE HE ek sφ (ŝᴬ k ec et eg) s H = ⊥-elim (tf (sym k))
fold-≅1ᴬ {k₁ = lim _ _} {k₂ = zero} sE HE ek sφ (ŝᴬ k ec et eg) s H = ⊥-elim (tf (sym k))
fold-≅1ᴬ {k₁ = suc _} {k₂ = suc _} sE HE ek sφ (ŝᴬ k ec et eg) s H =
  ŝRᴬ ec (fold-≅1ᴬ sE HE ek sφ et s H) (λ η e η′ e′ eη → fold-≅1ᴬ sE HE ek sφ (eg η e η′ e′ eη) s H)
fold-≅1ᴬ {k₁ = suc _} {k₂ = lim _ _} sE HE ek sφ (ŝᴬ k ec et eg) s H =
  ŝRᴬ ec (fold-≅1ᴬ sE HE ek sφ et s H) (λ η e η′ e′ eη → fold-≅1ᴬ sE HE ek sφ (eg η e η′ e′ eη) s H)
fold-≅1ᴬ {k₁ = lim _ _} {k₂ = suc _} sE HE ek sφ (ŝᴬ k ec et eg) s H =
  ŝRᴬ ec (fold-≅1ᴬ sE HE ek sφ et s H) (λ η e η′ e′ eη → fold-≅1ᴬ sE HE ek sφ (eg η e η′ e′ eη) s H)
fold-≅1ᴬ {k₁ = lim _ _} {k₂ = lim _ _} sE HE ek sφ (ŝᴬ k ec et eg) s H =
  ŝRᴬ ec (fold-≅1ᴬ sE HE ek sφ et s H) (λ η e η′ e′ eη → fold-≅1ᴬ sE HE ek sφ (eg η e η′ e′ eη) s H)
fold-≅1ᴬ sE HE ek sφ (ĉᴬ ec dt dg eo eO) s H =
  ĉRᴬ ec dt dg (fold-≅1ᴬ sE HE ek sφ eo s H) (λ η e η′ e′ eη → fold-≅1ᴬ sE HE ek sφ (eO η e η′ e′ eη) s H)
```
**分支.** `selfΩ̂0ᴬ`: `Ω̂A 0` 是 $\approx^\mathsf A_1$ 的; `∅ᴿ-ᴬ`: 空前缀层对齐; **`bRᴬ`**: Uniform2 `BranchΩ.bR` 的层对齐形式, 对一切 $\eta\cong\eta'$ (不要标签、不要目标下界). `¬x₃y₃`: Uniform2 `¬AlignΩ₃` 的输入对不层对齐, 所以 $\Omega_3$ 的自互模拟 `Ωˢ-≅ᴬ` 根本不关联它们; `¬PLᴬPR`: §1 的反例的底不层对齐.

```agda
selfΩ̂0ᴬ : Ω̂A 0 ≈₁ᴬ Ω̂A 0
selfΩ̂0ᴬ {P = P} {P′ = P′} s H =
  cloRᴬ {t = fold 0 (fk zero) (λ e → e) P (Ωˢ (suc zero))} {g = λ η → fold 0 (fk η) (λ e q → e (suc q)) P (Ωˢ η)}
        {t′ = fold 0 (fk zero) (λ e → e) P′ (Ωˢ (suc zero))} {g′ = λ η → fold 0 (fk η) (λ e q → e (suc q)) P′ (Ωˢ η)}
        s (fold-≅0ᴬ H (Ωˢ-≅ᴬ (≅ᴵ-refl (suc zero)))) (λ η η′ eη → fold-≅0ᴬ H (Ωˢ-≅ᴬ eη))

∅ᴿ-ᴬ : ∅ᴿ ≈ᴬ ∅ᴿ
∅ᴿ-ᴬ ev p ev′ p′ ei = Ωˢ-≅ᴬ ei

bRᴬ : ∀ {η η′} (e : η ≅ᴵ η′) →
      fold 1 (fk η) (λ e q → e (suc q)) (Ω̂A 0) (Ωˢ η) ≈₁ᴬ fold 1 (fk η′) (λ e q → e (suc q)) (Ω̂A 0) (Ωˢ η′)
bRᴬ e = fold-≅1ᴬ (fk∼ z≅) selfΩ̂0ᴬ e (fk∼ e) (Ωˢ-≅ᴬ e)

```

## §5 层对齐的好性与目标类型


```agda
record GRᴬ {φ} (R : Run φ) (u : T) : Set where
  constructor grᴬ
  field
    gWᴬ : LW R u
    g0ᴬ : L0 R u
    gRᴬ : R ≈ᴬ R

GA0ᴬ : ∀ {fl} → Run fl → T → Set
GA0ᴬ {fl} P π = FlrLab fl π × GRᴬ P π

∅ᴿ-good : GA0ᴬ ∅ᴿ []
∅ᴿ-good = FlrLab-fz , grᴬ (gW (proj₂ good∅ᴿ)) (g0 (proj₂ good∅ᴿ)) ∅ᴿ-ᴬ

record GA1ᴬ {φ} (E : A 1 φ) (ζ : T) : Set where
  field
    fl1ᴬ : FlrLab φ ζ
    gw1ᴬ : ∀ {c fl} {P : Run fl} {π} → FlrLab[ c ] fl π → LW P π → LW[ c ] (E P) (π ++ ψΩᵗ ζ)
    g01ᴬ : ∀ {fl} {P : Run fl} {π} → GA0ᴬ P π → L0 (E P) (π ++ ψΩᵗ ζ)
    gr1ᴬ : E ≈₁ᴬ E

Branch : (η : Ordᴵ) → A 1 (fk zero ⊔ fk η)
Branch η = fold 1 (fk η) (λ e q → e (suc q)) (Ω̂A 0) (Ωˢ η)

record BranchΩᴬ : Set where
  field
    bW₀ : ∀ θ Y (hY : HS Y) → Lab Y θ → NF₁ θ → ∀ {fl} {P : Run fl} {π} → FlrLab[ toLevel Y hY ] fl π → LW P π →
          LW[ toLevel Y hY ] (Branch (toLevel Y hY) P) (π ++ ψΩᵗ (Ωt θ))
    bV₀ : ∀ θ Y (hY : HS Y) → Lab Y θ → NF₁ θ → ∀ {fl} {P : Run fl} {π} → GA0ᴬ P π →
          L0 (Branch (toLevel Y hY) P) (π ++ ψΩᵗ (Ωt θ))

bR-free : ∀ {η η′} → η ≅ᴵ η′ → Branch η ≈₁ᴬ Branch η′
bR-free = bRᴬ

TΩ2-target : Set
TΩ2-target = BranchΩᴬ → ∀ {ℓ} (ev : Ev ℓ (fz ⊔ (fk zero ⊔ (fk zero ⊔ fz)))) (z : zero <ᴵ ℓ) → Lab₀ (ψᵀ (Ψ (Ψ ∅ᵀ)) ev z) tΩ2

module Outlook (Hon : ∀ {k} → Ordˢ k → T → Set) where
  FullTlᴬ : Set
  FullTlᴬ = ∀ {flE} {E : A 1 flE} {ζ} → GA1ᴬ E ζ → ∀ {k} {t : Ordˢ k} {y} → LabL t y → t ≅ᴬ t → Hon t y →
            GA1ᴬ (fold 1 (flo k) (cvFlo k) E t) (ζ ++ y)

infix 4 _≈₂ᴬ_
_≈₂ᴬ_ : ∀ {φ ψ} → A 2 φ → A 2 ψ → Set
E ≈₂ᴬ E′ = ∀ {fl fl′} {F : A 1 fl} {F′ : A 1 fl′} → fl ∼ᶠ fl′ → F ≈₁ᴬ F′ → E F ≈₁ᴬ E′ F′

record GA2ᴬ {φ} (E : A 2 φ) (ζ : T) : Set where
  field
    fl2ᴬ : FlrLab φ ζ
    gv2ᴬ : ∀ {fl} {F : A 1 fl} {ζ′} → GA1ᴬ F ζ′ → GA1ᴬ (E F) (ζ′ ++ ψΩᵗ ζ)
    gr2ᴬ : E ≈₂ᴬ E

goodΩ̂₂-type : Set
goodΩ̂₂-type = GA2ᴬ (Ω̂A 1) []

Ψⁿ : ℕ → Σ Flr Sym
Ψⁿ zero    = fz , ∅ᵀ
Ψⁿ (suc n) = fk zero ⊔ proj₁ (Ψⁿ n) , Ψ (proj₂ (Ψⁿ n))

topO-type : Set
topO-type = ∀ n {ℓ} (ev : Ev ℓ (fz ⊔ proj₁ (Ψⁿ (suc n)))) (z : zero <ᴵ ℓ) → Lab₀ (ψᵀ (proj₂ (Ψⁿ (suc n))) ev z) (E.fsn tO (suc n))
```
