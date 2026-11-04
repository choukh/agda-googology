> **机械克隆, 验收用.** 由 `ScafLadderZUniform3Hon` 经 `Survey/scripts/ladderlab/mkworld.py` 复制, 只改模块名; 见 [LadderLab](LadderLab.lagda.md). 下面的文字是原文.

> **机械克隆.** 由 `Uniform3Hon` 经脚本复制, 只为把 `NF₁`, `Occ` 换成 [ScafLadderZStandardOmega](ScafLadderZStandardOmega.lagda.md), [ScafLadderZSystemOmega](ScafLadderZSystemOmega.lagda.md) 的版本; 见 [ScafLadder](ScafLadder.lagda.md). 下面的文字是原文.

# 统一形 (三): 诚实的输出 `Hn`

> 接 [Uniform3SqABase](Uniform3SqABase.lagda.md). $\psi_0(\psi_\Omega(\Omega_k))$ ($k\ge4$) 的目标 0 计值把链点 $x_m$ (第 $j$ 层的**输出**) 当尾巴重新折叠. 尾巴的后继行读地板 `flo k`, 只有标签首项的下标支配它时才有见证 (RelativeBase `FL-head`). `LabL` 允许 "伪树" (第 3 层的字面 `suc zero` 带标签 1, `limᵢ` 的分支是任意带标签的树), 那样的尾巴在目标 0 处确实没有证书 (`¬FL₄`). 本文的 `Hn t y` 记下输出实际有的结构: 只要标签是裸的 $\Omega_w$, 树就**字面地**是 `Ωˢ ℓ`; 否则逐行展开. 首项在 `fsn`/`fsT`/`pred` 下不变 (`Hu`), 所以 "首项见证地板" 沿非裸的行自动遗传.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderLabZUniform3Hon where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.LadderLabZPrefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; _+ˢ_; addˢ; tr⁻ˢ)
import OCF.Align.EBO as E
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; _<ᵀ_; cofA; 𝟏; trm; cmpᵀ; sucT; lt; eq; gt) renaming (ψ to ψᵗ)
open import OCF.Align.Correspond using (Lab; cof-ne; fs-rep)
open import OCF.Align.LadderLabZStandardOmega using (NF₁)
open import OCF.Align.LadderLabZDecouple using (Idx; lvI)
open import OCF.Align.LadderLabZGoodLBase
open import OCF.Align.LadderLabZUniformS
open import OCF.Align.LadderLabZUniform3Base
open import OCF.Align.LadderLabZUniform3Rel
open import OCF.Align.LadderLabZUniform3SqABase
open import OCF.Align.Stage2 using (Ωᵗ)
open import OCF.Align.LadderLabZStage2Label using (one⁰)
open import OCF.Align.LadderLabZDecoupleBase using (ΩΩ)
open import OCF.Align.LadderLabZDecouple using (Ilt; Ieq; kdI′; gtν; cofP)
open import OCF.Align.Bachmann using (pen→<; gt→≤)
open import OCF.Align.Closure using (Pen)
open import OCF.Align.LadderLabZSystemOmega using (Occ; oh; od; os; ot; oτ; TailOf; th; ts)
open import OCF.Align.LadderLabZOmegaExpBase using (πw; OccΣ; cofW; repW; ωW; γW; gtW; penW; H1W; ne-w; 1<γ; snoc)
open import OCF.Align.LadderLabZUniform3Depth1 using (c1Ω; cωΩ; cΩΩ; penΩ)
```

## §1 首项

```agda
-- 非裸的项: 不是单独的 ψ_w(0)
NB : T → Set
NB [] = ⊥
NB (x ∷ _ ∷ _) = ⊤
NB (ψᵗ u (_ ∷ _) ∷ []) = ⊤
NB (ψᵗ u [] ∷ []) = ⊥

NB-sum : ∀ {w} ps {y ys} → NB (ψᵗ w (ps ++ (y ∷ ys)) ∷ [])
NB-sum [] = tt
NB-sum (p ∷ ps) = tt

data Hu (u : T) : T → Set where
  hn : Hu u []
  hc : ∀ {v vs} → Hu u (ψᵗ u v ∷ vs)

Hu-rep : ∀ {u v} n → Hu u (replicate n (ψᵗ u v))
Hu-rep zero    = hn
Hu-rep (suc n) = hc

Hu-fsT₊ : ∀ u b c η → Hu u (E.fsT₊ u b c η)
Hu-fsT₊ u b c0 η = hc
Hu-fsT₊ u b c1 η = hc
Hu-fsT₊ u b cω η = hc
Hu-fsT₊ u b (cΩ ν) η = go (E.cmpᵀ (E.sucT ν) u)
  where
  go : ∀ m → Hu u (E.fsTc u b ν m η)
  go E.lt = hc
  go E.eq = hc
  go E.gt = hc

Hu-fsn₊ : ∀ u y ys n c (be : cof (y ∷ ys) ≡ c) → Hu u (trm (E.fsn↓₊ u y ys c be n))
Hu-fsn₊ u y ys n c0 be = hn
Hu-fsn₊ u y ys n c1 be = subst (Hu u) (sym (E.rep-trm u (E.pred-< (y ∷ ys) be) n)) (Hu-rep n)
Hu-fsn₊ u y ys n cω be = hc
Hu-fsn₊ u y ys n (cΩ ν) be = go (E.cmpᵀ (E.sucT ν) u)
  where
  go : ∀ m → Hu u (trm (E.fsn↓c u y ys ν be m n))
  go E.lt = hc
  go E.eq = hc
  go E.gt = hc

Hu-fsn : ∀ u v vs → NB (ψᵗ u v ∷ vs) → ∀ n → Hu u (fsn (ψᵗ u v ∷ vs) n)
Hu-fsn u v (z ∷ zs) nb n = hc
Hu-fsn u (y ∷ ys) [] nb n = Hu-fsn₊ u y ys n (cof (y ∷ ys)) refl

Hu-fsT : ∀ u v vs → NB (ψᵗ u v ∷ vs) → ∀ η → Hu u (fsT (ψᵗ u v ∷ vs) η)
Hu-fsT u v (z ∷ zs) nb η = hc
Hu-fsT u (y ∷ ys) [] nb η = Hu-fsT₊ u (y ∷ ys) (cof (y ∷ ys)) η

Hu-pred : ∀ u v vs → NB (ψᵗ u v ∷ vs) → cof (ψᵗ u v ∷ vs) ≡ c1 → Σ T λ v′ → Σ T λ vs′ → pred (ψᵗ u v ∷ vs) ≡ ψᵗ u v′ ∷ vs′
Hu-pred u v (z ∷ zs) nb c = v , pred (z ∷ zs) , refl
Hu-pred u (y ∷ ys) [] nb c = ⊥-elim (notc1 (cof (y ∷ ys)) c)
  where
  go′ : ∀ {ν} m → E.cofψ₊ u ν m ≡ c1 → ⊥
  go′ E.lt ()
  go′ E.eq ()
  go′ E.gt ()
  notc1 : ∀ c′ → cofA u c′ ≡ c1 → ⊥
  notc1 c0 ()
  notc1 c1 ()
  notc1 cω ()
  notc1 (cΩ ν) e = go′ (E.cmpᵀ (E.sucT ν) u) e
```

`HK K y`: $y$ 为空, 或首项下标 $u$ 带 `Idx` 且 $K\preceq\mathtt{lvI}\,u$. `FH φ y`: 地板的每一项平凡、$\cong1$ 或被首项见证.

```agda
HK : Ordᴵ → T → Set
HK K []            = ⊤
HK K (ψᵗ u v ∷ vs) = Σ (Idx u) λ I → K ≼ lvI I

FH : Flr → T → Set
FH φ y = ∀ {K} → InF K φ → (K ≅ᴵ zero) ⊎ (K ≅ᴵ one) ⊎ HK K y

HK-Hu : ∀ {K u z} → (Σ (Idx u) λ I → K ≼ lvI I) → Hu u z → HK K z
HK-Hu h hn = tt
HK-Hu h hc = h

FH-fsn : ∀ {φ y} → NB y → FH φ y → ∀ n → FH φ (fsn y n)
FH-fsn {y = ψᵗ u v ∷ vs} nb F n k with F k
... | inj₁ e = inj₁ e
... | inj₂ (inj₁ e) = inj₂ (inj₁ e)
... | inj₂ (inj₂ h) = inj₂ (inj₂ (HK-Hu h (Hu-fsn u v vs nb n)))

FH-fsT : ∀ {φ y} → NB y → FH φ y → ∀ η → FH φ (fsT y η)
FH-fsT {y = ψᵗ u v ∷ vs} nb F η k with F k
... | inj₁ e = inj₁ e
... | inj₂ (inj₁ e) = inj₂ (inj₁ e)
... | inj₂ (inj₂ h) = inj₂ (inj₂ (HK-Hu h (Hu-fsT u v vs nb η)))
```

## §2 `Hn`

```agda
data Hn {ℓ} : Ordˢ ℓ → T → Set where
  hΩ : ∀ {x w} → x ≡ Ωˢ ℓ → (I : Idx w) → ℓ ≅ᴵ lvI I → Hn x (ψᵗ w [] ∷ [])
  hz : ∀ {t} → Hn Ord₊ˢ.zero t
  hs : ∀ {t y} → NB t → Hn y (pred t) → Hn (Ord₊ˢ.suc y) t
  hl : ∀ {t} {F : ℕ → Ordˢ ℓ} → NB t → (∀ n → Hn (F n) (fsn t n)) → Hn (Ord₊ˢ.lim F) t
  hi : ∀ {t j} {q : j <ᴵ ℓ} {f : Uˢ j (<→◃ q) → Ordˢ ℓ} → NB t →
       (∀ η (x : Ordˢ j) → LabL x η → Hn (f (intoˢ (<→◃ q) x)) (fsT t η)) → Hn (Ord₊ˢ.limᵢ q f) t
  hĉ : ∀ {t c t₀} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z} {o₀ : Ordˢ ℓ} {o : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ} → NB t → cof t ≡ cω →
       (K : CCᴸ c t₀ g) → LabL₊ ℓ Ll o₀ (fsn t 0) → Hn o₀ (fsn t 0) →
       (∀ k → LabL₊ ℓ Ll (o (lvK K k) (dxK K k)) (fsn t (suc k))) → (∀ k → Hn (o (lvK K k) (dxK K k)) (fsn t (suc k))) →
       Hn (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) t
  hŝ : ∀ {t c} {t₀ : Ordˢ ℓ} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ} → NB t →
       Hn t₀ (fsT t (natT 1)) →
       (∀ θ (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → natT 1 <ᵀ θ → (e : c ⊑ᴵ toLevel Y hY) →
        Hn (g (toLevel Y hY) e) (fsT t θ)) →
       Hn (Ord₊ˢ.ŝ c t₀ g) t
```

**和.** `HSum`: `a` 的标签与 `Hn a (x ∷ [])`, 加上 $b$ 的任意标签 (伪树也行: 和的标签非裸, 不读 $b$ 的裸性), 给 `Hn (a + b) (x ∷ ys)`. 与 GoodLBase 的 `LSum` 同形.

```agda
HSumA : ∀ {ℓ} {a : Ordˢ ℓ} {σ : Simᴵ zero ℓ} {b : Ordˢ zero} {x ys} → LabL₊ ℓ Ll a (x ∷ []) → Hn a (x ∷ []) → Lab0ᴸ b ys → Hn (addˢ a σ b) (x ∷ ys)
HSumA {ys = []} ga la (lz c) = la
HSumA {ys = y ∷ ys} ga la (lz c) = ⊥-elim (cof-ne y ys c)
HSumA {ys = []} ga la (ls () l)
HSumA {ys = y ∷ ys} ga la (ls c l) = hs tt (HSumA ga la l)
HSumA {ys = []} ga la (ll () h)
HSumA {ys = y ∷ ys} ga la (ll c h) = hl tt (λ n → HSumA ga la (h n))
HSumA {ys = []} ga la (lŝ₀ () K h₀ hk)
HSumA {ys = y ∷ ys} ga la (lŝ₀ c K h₀ hk) = hĉ tt c K (LSumA ga h₀) (HSumA ga la h₀) (λ m → LSumA ga (hk m)) (λ m → HSumA ga la (hk m))
HSumA {ys = []} ga la (lĉ () K h₀ hk)
HSumA {ys = y ∷ ys} ga la (lĉ c K h₀ hk) = hĉ tt c K (LSumA ga h₀) (HSumA ga la h₀) (λ m → LSumA ga (hk m)) (λ m → HSumA ga la (hk m))

HSum  : ∀ {k ℓ} {a : Ordˢ ℓ} {σ : Simᴵ k ℓ} {b : Ordˢ k} {x ys} → kd ℓ ≡ false → LabL₊ ℓ Ll a (x ∷ []) → Hn a (x ∷ []) → LabL b ys → Hn (addˢ a σ b) (x ∷ ys)
HSum₊ : ∀ {k ℓ} {a : Ordˢ ℓ} {σ : Simᴵ k ℓ} {b : Ordˢ k} {x ys} → kd ℓ ≡ false → LabL₊ ℓ Ll a (x ∷ []) → Hn a (x ∷ []) → LabL₊ k Ll b ys → Hn (addˢ a σ b) (x ∷ ys)
HSum {k = zero} kl ga la at = HSumA ga la (atomL at)
HSum {k = suc _} kl ga la h = HSum₊ kl ga la h
HSum {k = lim _ _} kl ga la h = HSum₊ kl ga la h
HSum₊ {ys = []} kl ga la (gz c) = la
HSum₊ {ys = y ∷ ys} kl ga la (gz c) = ⊥-elim (cof-ne y ys c)
HSum₊ {ys = []} kl ga la (gs () h)
HSum₊ {ys = y ∷ ys} kl ga la (gs c h) = hs tt (HSum₊ kl ga la h)
HSum₊ {ys = []} kl ga la (gl () h)
HSum₊ {ys = y ∷ ys} kl ga la (gl c h) = hl tt (λ n → HSum₊ kl ga la (h n))
HSum₊ {σ = σ} kl ga la (gu {r = zero} h) = HSum {σ = λ q → σ (suc q)} kl ga la h
HSum₊ {σ = σ} kl ga la (gu {r = self n} h) = HSum {σ = λ q → σ (lim n q)} kl ga la h
HSum₊ {ys = []} kl ga la (gi () I ej h)
HSum₊ {a = a} {σ = σ} {x = x} {ys = y ∷ ys} kl ga la (gi {q = q} {f = f} c I ej h) =
  hi tt (λ η w l → subst (λ v → Hn (addˢ a σ (f (intoˢ (<→◃ q) v))) (x ∷ fsT (y ∷ ys) η))
                         (sym (out-intoˢ (<→◃ (σ q)) w)) (HSum₊ kl ga la (h η w (→Ll (<→◃ q) l))))
HSum₊ {ys = []} kl ga la (gĉ () K h₀ hk)
HSum₊ {ys = y ∷ ys} kl ga la (gĉ c K h₀ hk) = hĉ tt c K (LSum₊ kl ga h₀) (HSum₊ kl ga la h₀) (λ m → LSum₊ kl ga (hk m)) (λ m → HSum₊ kl ga la (hk m))
HSum₊ {k = zero} kl ga la (gŝ () c Ib bb ob h₀ hg)
HSum₊ {k = suc _} {ys = []} kl ga la (gŝ kk () Ib bb ob h₀ hg)
HSum₊ {k = suc _} {ys = y ∷ ys} kl ga la (gŝ kk c Ib bb ob h₀ hg) =
  hŝ tt (HSum₊ kl ga la h₀) (λ θ Y hY lY nθ lt e → HSum₊ kl ga la (hg θ Y hY lY nθ lt e))
HSum₊ {k = lim _ _} {ys = []} kl ga la (gŝ kk () Ib bb ob h₀ hg)
HSum₊ {k = lim _ _} {ys = y ∷ ys} kl ga la (gŝ kk c Ib bb ob h₀ hg) =
  hŝ tt (HSum₊ kl ga la h₀) (λ θ Y hY lY nθ lt e → HSum₊ kl ga la (hg θ Y hY lY nθ lt e))

HRep : ∀ {ℓ} {P : Ordˢ ℓ} {x} → kd ℓ ≡ false → LabL₊ ℓ Ll P (x ∷ []) → Hn P (x ∷ []) → ∀ n →
       Hn (iter (P +ˢ_) Ord₊ˢ.zero n) (replicate n x)
HRep kl gP lP zero    = hz
HRep kl gP lP (suc n) = HSum₊ kl gP lP (LRep kl gP n)
```

## §3 输出的诚实性: 行引理

`LWʰ[ c ] R u`: 在目标 $\succeq c$ 处, 输出既带标签又诚实. 行引理的签名与 OmegaSqABase §3 的 `…Wᶜ` 相同, 带标签的一半就调用原引理; 所以后面的递归可以逐字复制.

```agda
Out : ∀ {i} → Ordˢ i → T → Set
Out {i} x t = LabL₊ i Ll x t × Hn x t

LWʰ[_] : ∀ {φ} → Ordᴵ → Run φ → T → Set
LWʰ[_] {φ} c R u = ∀ {i ℓ w} (ev : Ev ℓ φ) (p : i <ᴵ ℓ) (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false → Up c i → Out (R ev p) (ψᵗ w u ∷ [])

LWʰ→ : ∀ {c φ} {R : Run φ} {u} → LWʰ[ c ] R u → LW[ c ] R u
LWʰ→ h ev p Iw ei ki u = proj₁ (h ev p Iw ei ki u)

wkLWʰ : ∀ {c φ ψ} {R : Run φ} (le : ∀ {L} → Ev L ψ → Ev L φ) {u} → LWʰ[ c ] R u → LWʰ[ c ] (wk 0 le R) u
wkLWʰ le h ev p = h (le ev) p

zWʰ : ∀ {c φ fl} {P : Run fl} {π} → LWʰ[ c ] P π → LWʰ[ c ] (wk 0 (proj₁ {B = λ _ → Ev _ φ}) P) (π ++ [])
zWʰ {π = π} h ev p Iw ei ki u = subst (λ v → Out _ (ψᵗ _ v ∷ [])) (sym (++-identityʳ π)) (h (proj₁ ev) p Iw ei ki u)

module _ {c φ} {ps : T} {y : PT} {ys : T} where
  limWʰ : ∀ {F : ℕ → Run φ} → cof (y ∷ ys) ≡ cω → (∀ n → LWʰ[ c ] (F n) (ps ++ fsn (y ∷ ys) n)) →
          LWʰ[ c ] (limA 0 F) (ps ++ (y ∷ ys))
  limWʰ {F} cc h {w = w} ev p Iw ei ki u =
    limWᶜ {F = F} cc (λ n → LWʰ→ (h n)) ev p Iw ei ki u ,
    hl (NB-sum ps) (λ n → subst (Hn _) (sym (ωW w ps y ys cc n)) (proj₂ (h n ev p Iw ei ki u)))

  sucWʰ : ∀ {R : Run φ} → cof (y ∷ ys) ≡ c1 → LWʰ[ c ] R (ps ++ pred (y ∷ ys)) → LWʰ[ c ] (sucRun R) (ps ++ (y ∷ ys))
  sucWʰ {R} cc h {w = w} ev p Iw ei ki u =
    sucWᶜ {R = R} cc (LWʰ→ h) ev p Iw ei ki u ,
    hl (NB-sum ps) (λ m → subst (Hn _) (sym (repW w ps y ys cc m)) (HRep ki (proj₁ (h ev p Iw ei ki u)) (proj₂ (h ev p Iw ei ki u)) m))

module _ {c φ c₀ t₀} {g : (η : Ordᴵ) → c₀ ⊑ᴵ η → Z} {ps : T} {y : PT} {ys : T} where
  ĉWʰ : ∀ {O₀ : Run φ} {O : (η : Ordᴵ) → c₀ ⊑ᴵ η → Run φ} → cof (y ∷ ys) ≡ cω → (K : CCᴸ c₀ t₀ g) →
        LWʰ[ c ] O₀ (ps ++ fsn (y ∷ ys) 0) → (∀ k → LWʰ[ c ] (O (lvK K k) (dxK K k)) (ps ++ fsn (y ∷ ys) (suc k))) →
        LWʰ[ c ] (ĉA 0 c₀ t₀ g O₀ O) (ps ++ (y ∷ ys))
  ĉWʰ {O₀} {O} cw K h₀ hk {w = w} ev p Iw ei ki u =
    ĉWᶜ {O₀ = O₀} {O = O} cw K (LWʰ→ h₀) (λ k → LWʰ→ (hk k)) ev p Iw ei ki u ,
    hĉ (NB-sum ps) (trans (cofW w ps y ys) (cong (cofA w) cw)) K
       (subst (LabL₊ _ Ll _) (sym (ωW w ps y ys cw 0)) (proj₁ (h₀ ev p Iw ei ki u)))
       (subst (Hn _) (sym (ωW w ps y ys cw 0)) (proj₂ (h₀ ev p Iw ei ki u)))
       (λ k → subst (LabL₊ _ Ll _) (sym (ωW w ps y ys cw (suc k))) (proj₁ (hk k ev p Iw ei ki u)))
       (λ k → subst (Hn _) (sym (ωW w ps y ys cw (suc k))) (proj₂ (hk k ev p Iw ei ki u)))

module _ {c φ c₀ w′} {ps : T} {y : PT} {ys : T} {T₀ : Run φ} {G : (η : Ordᴵ) → c₀ ⊑ᴵ η → Run φ}
         (cs : cof (y ∷ ys) ≡ cΩ []) (Iw′ : Idx w′) (bw : c₀ ⊑ᴵ suc (lvI Iw′)) (ob : Ob w′ ps y ys) where
  ŝWʰ : LWʰ[ c ] T₀ (ps ++ fsT (y ∷ ys) (natT 1)) →
        (∀ θ Y hY → Lab Y θ → NF₁ θ → natT 1 <ᵀ θ → (e : c₀ ⊑ᴵ toLevel Y hY) → LWʰ[ c ] (G (toLevel Y hY) e) (ps ++ fsT (y ∷ ys) θ)) →
        LWʰ[ c ] (ŝA 0 c₀ T₀ G) (ps ++ (y ∷ ys))
  ŝWʰ h₀ hg {w = []} ev p Iw ei ki u = ⊥-elim (ne-w Iw ei ki refl)
  ŝWʰ h₀ hg {w = x ∷ xs} ev p Iw ei ki u =
    ŝWᶜ cs Iw′ bw ob (LWʰ→ h₀) (λ θ Y hY lY nθ lt e → LWʰ→ (hg θ Y hY lY nθ lt e)) ev p Iw ei ki u ,
    hŝ (NB-sum ps)
       (subst (Hn _) (sym (H1W x xs ps y ys cs (natT 1))) (proj₂ (h₀ ev p Iw ei ki u)))
       (λ θ Y hY lY nθ lt e → subst (Hn _) (sym (H1W x xs ps y ys cs θ)) (proj₂ (hg θ Y hY lY nθ lt e ev p Iw ei ki u)))

module _ {c φ} {ps : T} {y : PT} {ys : T} {t : Run (φ ⊔ fk zero)} {g : (η : Ordᴵ) → Run (φ ⊔ fk η)}
         (fw : FW[ c ] (φ ⊔ fk zero) ps y ys) (cs : cof (y ∷ ys) ≡ cΩ []) where
  cloWʰ : LWʰ[ c ] t (ps ++ fsT (y ∷ ys) (natT 1)) →
          (∀ θ Y hY → Lab Y θ → NF₁ θ → natT 1 <ᵀ θ → LWʰ[ c ] (g (toLevel Y hY)) (ps ++ fsT (y ∷ ys) θ)) →
          LWʰ[ c ] (cloA 0 t g) (ps ++ (y ∷ ys))
  cloWʰ h₀ hg {w = []} ev p Iw ei ki u = ⊥-elim (ne-w Iw ei ki refl)
  cloWʰ h₀ hg {w = x ∷ xs} ev p Iw ei ki u =
    cloWᵗ {t = t} {g = g} fw cs (LWʰ→ h₀) (λ θ Y hY lY nθ lt → LWʰ→ (hg θ Y hY lY nθ lt)) ev p Iw ei ki u ,
    hŝ (NB-sum ps)
       (subst (Hn _) (sym (H1W x xs ps y ys cs (natT 1))) (proj₂ (h₀ ev p Iw ei ki u)))
       (λ θ Y hY lY nθ lt e → subst (Hn _) (sym (H1W x xs ps y ys cs θ))
            (proj₂ (hg θ Y hY lY nθ lt (evη φ B (toLevel Y hY) e) (lim 0 (iF B)) Iw ei ki u)))
    where
    B = bound (φ ⊔ fk zero) ev p
```

**`limᵢ` 行.** `limᵢWᴾ`: 输入谓词 `Inp` 的版本. 穿透情形 (目标 $\succ j$) 对一切带标签的输入 (`hPen`); 折叠情形只对链点 (`Inp`, 第 0 点 $\Omega_j$, 下一点由 `hStep`). 普通的 `limᵢWʰ` 是 `Inp = LabL` 的实例; $\Omega_{k+1}$ 尾巴在低目标处的行只有链点是诚实的, 用 `Inp` 记下.

```agda
module _ {c φ j ν} {ps : T} {y : PT} {ys : T} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {H : Ordˢ j → Run φ}
         (cc : cof (y ∷ ys) ≡ cΩ ν) (Iν : Idx ν) (ej : j ≅ᴵ lvI Iν) where

  limᵢWᴾ : (Inp : T → Ordˢ j → Set) → Inp (Ωt ν) (Ωˢ j) →
           (∀ η x → LabL x η → ∀ {i ℓ w} (ev : Ev ℓ φ) (p : i <ᴵ ℓ) (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false → Up c i → j ≺ᴵ i →
            Out (H x ev p) (ψᵗ w (ps ++ fsT (y ∷ ys) η) ∷ [])) →
           (∀ {η x} → Inp η x → kd j ≡ false → Up c j → ∀ {ℓ} (ev : Ev ℓ φ) → Inp (πw ν ps (fsT (y ∷ ys) η)) (H x ev (ac ev))) →
           (∀ {η x} → Inp η x → LWʰ[ c ] (H x) (ps ++ fsT (y ∷ ys) η)) →
           LWʰ[ c ] (limᵢA 0 ac H) (ps ++ (y ∷ ys))
  limᵢWᴾ Inp i₀ hPen hStep hOut {i = i} {w = w} ev p Iw ei ki u = go (cmpᵀ (sucT ν) w) refl
    where
    pen : Pen (cmpᵀ (sucT ν) w) → Out (limᵢA 0 ac H ev p) (πw w ps (y ∷ ys))
    pen pn with pen1A {ac = ac} {H = H} {ev = ev} {p = p} (≅ᴵ-refl j) jsi
      where
      jsi : j ≺ᴵ i
      jsi = ≺ᴵ-respʳ (≺ᴵ-respˡ ej (Ilt Iν Iw (pen→< ν w pn))) (≅ᴵ-sym ei)
    ... | j′ , e , r , eqn =
      subst (λ W → Out W (πw w ps (y ∷ ys))) (sym eqn)
        (gi cofE Iν (≅ᴵ-trans (≅ᴵ-sym e) ej)
            (λ η x l → subst (λ v → LabL₊ i Ll (H (tr⁻ˢ e v) ev p) (fsT (πw w ps (y ∷ ys)) η))
                             (sym (out-intoˢ (<→◃ r) x))
                             (subst (LabL₊ i Ll _) (sym (penW w ps y ys ν cc pn η))
                                    (proj₁ (hPen η (tr⁻ˢ e x) (LabL-tr⁻ e (Ll→ (<→◃ r) l)) ev p Iw ei ki u jsi′)))) ,
         hi (NB-sum ps)
            (λ η x l → subst (λ v → Hn (H (tr⁻ˢ e v) ev p) (fsT (πw w ps (y ∷ ys)) η))
                             (sym (out-intoˢ (<→◃ r) x))
                             (subst (Hn _) (sym (penW w ps y ys ν cc pn η))
                                    (proj₂ (hPen η (tr⁻ˢ e x) (LabL-tr⁻ e l) ev p Iw ei ki u jsi′)))))
      where
      cofE : cof (πw w ps (y ∷ ys)) ≡ cΩ ν
      cofE = trans (cofW w ps y ys) (trans (cong (cofA w) cc) (cofP pn))
      jsi′ : j ≺ᴵ i
      jsi′ = ≺ᴵ-respʳ (≺ᴵ-respˡ ej (Ilt Iν Iw (pen→< ν w pn))) (≅ᴵ-sym ei)
    fld : cmpᵀ (sucT ν) w ≡ gt → Out (limᵢA 0 ac H ev p) (πw w ps (y ∷ ys))
    fld em =
      subst (λ W → Out W (πw w ps (y ∷ ys))) (sym (fold1A {ac = ac} {H = H} {ev = ev} {p = p} ij))
        (gl (trans (cofW w ps y ys) (trans (cong (cofA w) cc) (cong (E.cofψ₊ w ν) em)))
            (λ m → subst (LabL₊ i Ll _) (sym (gtW w ps y ys ν cc em m)) (proj₁ (hOut (chainI m) ev p Iw ei ki u))) ,
         hl (NB-sum ps) (λ m → subst (Hn _) (sym (gtW w ps y ys ν cc em m)) (proj₂ (hOut (chainI m) ev p Iw ei ki u))))
      where
      gev : (lvI Iw ≺ᴵ lvI Iν) ⊎ (lvI Iw ≅ᴵ lvI Iν)
      gev with gt→≤ ν w em
      ... | inj₁ pw   = inj₁ (Ilt Iw Iν pw)
      ... | inj₂ refl = inj₂ (Ieq Iw Iν)
      ij : (i ≺ᴵ j) ⊎ (i ≅ᴵ j)
      ij with gev
      ... | inj₁ s  = inj₁ (≺ᴵ-respʳ (≺ᴵ-respˡ ei s) (≅ᴵ-sym ej))
      ... | inj₂ c′ = inj₂ (≅ᴵ-trans ei (≅ᴵ-trans c′ (≅ᴵ-sym ej)))
      kj : kd j ≡ false
      kj = trans (kd-≅ ej) (kdI′ Iν (gtν em (ne-w Iw ei ki)))
      uj : Up c j
      uj = Up-ij u ij
      chainI : ∀ m → Inp (γW ps (y ∷ ys) ν m) (chainA ac H ev m)
      chainI zero    = i₀
      chainI (suc m) = hStep (chainI m) kj uj ev
    go : ∀ m → cmpᵀ (sucT ν) w ≡ m → Out (limᵢA 0 ac H ev p) (πw w ps (y ∷ ys))
    go E.lt em = pen (inj₁ em)
    go E.eq em = pen (inj₂ em)
    go E.gt em = fld em

  limᵢWʰ : (∀ η x → LabL x η → LWʰ[ c ] (H x) (ps ++ fsT (y ∷ ys) η)) → LWʰ[ c ] (limᵢA 0 ac H) (ps ++ (y ∷ ys))
  limᵢWʰ hW = limᵢWᴾ (λ η x → LabL x η)
    (LabL-Ω (proj₁ Iν) (proj₁ (proj₂ Iν)) (proj₁ (proj₂ (proj₂ Iν))) (proj₂ (proj₂ (proj₂ Iν))) ej)
    (λ η x l ev p Iw ei ki u s → hW η x l ev p Iw ei ki u)
    (λ {η} {x} l kj uj ev → frL₊ kj (proj₁ (hW η x l ev (ac ev) Iν ej kj uj)))
    (λ {η} {x} l → hW η x l)
```

## §4 深度 0 的尾巴

与 OmegaSqABase `TlWᶜ` 逐字 (`LW[ c ]` 换成 `LWʰ[ c ]`, 行引理换成 `…Wʰ`).

```agda
module TlWʰ {c fl} {P : Run fl} {π : T} (hP : LWʰ[ c ] P π) where
  tlWAʰ : ∀ {φ} {cv : ∀ {L} → Ev L φ → Simᴵ zero L} {t : Ordˢ zero} {y} → Lab0ᴸ t y → LWʰ[ c ] (fold 0 φ cv P t) (π ++ y)
  tlWVʰ : ∀ {k φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {t : Ordˢ k} {y} → LabL t y → LWʰ[ c ] (fold 0 φ cv P t) (π ++ y)
  tlW₊ʰ : ∀ {k φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {t : Ordˢ k} {y} → LabL₊ k Ll t y → LWʰ[ c ] (fold 0 φ cv P t) (π ++ y)

  tlWAʰ {y = []} (lz cc) = zWʰ hP
  tlWAʰ {y = y ∷ ys} (lz cc) = ⊥-elim (cof-ne y ys cc)
  tlWAʰ {y = []} (ls () l)
  tlWAʰ {y = y ∷ ys} (ls cc l) = sucWʰ cc (tlWAʰ l)
  tlWAʰ {y = []} (ll () h)
  tlWAʰ {y = y ∷ ys} (ll cc h) = limWʰ cc (λ n → tlWAʰ (h n))
  tlWAʰ {y = []} (lŝ₀ () K h₀ hk)
  tlWAʰ {φ = φ} {cv = cv} {y = y ∷ ys} (lŝ₀ {t₀ = t₀} {g = g} cc K h₀ hk) =
    ĉWʰ {O₀ = fold 0 φ cv P t₀} {O = λ η e → fold 0 φ cv P (g η e)} cc K (tlWAʰ h₀) (λ k → tlWAʰ (hk k))
  tlWAʰ {y = []} (lĉ () K h₀ hk)
  tlWAʰ {φ = φ} {cv = cv} {y = y ∷ ys} (lĉ {o₀ = o₀} {o = o} cc K h₀ hk) =
    ĉWʰ {O₀ = fold 0 φ cv P o₀} {O = λ η e → fold 0 φ cv P (o η e)} cc K (tlWAʰ h₀) (λ k → tlWAʰ (hk k))

  tlWVʰ {k = zero}    at = tlWAʰ (atomL at)
  tlWVʰ {k = suc _}   h  = tlW₊ʰ h
  tlWVʰ {k = lim _ _} h  = tlW₊ʰ h

  tlW₊ʰ {y = []} (gz cc) = zWʰ hP
  tlW₊ʰ {y = y ∷ ys} (gz cc) = ⊥-elim (cof-ne y ys cc)
  tlW₊ʰ {y = []} (gs () l)
  tlW₊ʰ {y = y ∷ ys} (gs cc l) = sucWʰ cc (tlW₊ʰ l)
  tlW₊ʰ {y = []} (gl () h)
  tlW₊ʰ {y = y ∷ ys} (gl cc h) = limWʰ cc (λ n → tlW₊ʰ (h n))
  tlW₊ʰ {k = suc k′} {φ = φ} {cv = cv} (gu {r = zero} h) = λ ev p → tlWVʰ {φ = flo k′} {cv = cvFlo k′} h (proj₁ ev , toFlo k′ (λ q → cv (proj₂ ev) (suc q))) p
  tlW₊ʰ {k = lim f s} {φ = φ} {cv = cv} (gu {r = self n} h) = λ ev p → tlWVʰ {φ = flo (f n)} {cv = cvFlo (f n)} h (proj₁ ev , toFlo (f n) (λ q → cv (proj₂ ev) (lim n q))) p
  tlW₊ʰ {y = []} (gi () I ej h)
  tlW₊ʰ {y = y ∷ ys} (gi {q = q} cc I ej h) = limᵢWʰ cc I ej (λ η x l → tlW₊ʰ (h η x (→Ll (<→◃ q) l)))
  tlW₊ʰ {y = []} (gĉ () K h₀ hk)
  tlW₊ʰ {φ = φ} {cv = cv} {y = y ∷ ys} (gĉ {o₀ = o₀} {o = o} cc K h₀ hk) =
    ĉWʰ {O₀ = fold 0 φ cv P o₀} {O = λ η e → fold 0 φ cv P (o η e)} cc K (tlW₊ʰ h₀) (λ k → tlW₊ʰ (hk k))
  tlW₊ʰ {k = zero} (gŝ () cc Iw bw ob h₀ hg)
  tlW₊ʰ {k = suc _} {y = []} (gŝ kk () Iw bw ob h₀ hg)
  tlW₊ʰ {k = suc _} {φ = φ} {cv = cv} {y = y ∷ ys} (gŝ {t₀ = t₀} {g = g} kk cc Iw bw ob h₀ hg) =
    ŝWʰ {T₀ = fold 0 φ cv P t₀} {G = λ η e → fold 0 φ cv P (g η e)} cc Iw bw (λ θ → OccΣ π (ob θ)) (tlW₊ʰ h₀) (λ θ Y hY lY nθ lt e → tlW₊ʰ (hg θ Y hY lY nθ lt e))
  tlW₊ʰ {k = lim _ _} {y = []} (gŝ kk () Iw bw ob h₀ hg)
  tlW₊ʰ {k = lim _ _} {φ = φ} {cv = cv} {y = y ∷ ys} (gŝ {t₀ = t₀} {g = g} kk cc Iw bw ob h₀ hg) =
    ŝWʰ {T₀ = fold 0 φ cv P t₀} {G = λ η e → fold 0 φ cv P (g η e)} cc Iw bw (λ θ → OccΣ π (ob θ)) (tlW₊ʰ h₀) (λ θ Y hY lY nθ lt e → tlW₊ʰ (hg θ Y hY lY nθ lt e))
```

## §5 好帧的 W 部分与一般层号尾巴的输出 (层号条件下)

`GA1ʷ`: 只含地板标签与带诚实性的 W. `W₊ʰ` 与 OmegaSqABase `W₊` 逐字: 尾巴是**任意**带标签的树 (层号条件 `LvOK`), 输出诚实. 这正是链点 $x_{m+1}$ 的诚实性的来源: 链点在节点层 $j$ 上算, 尾巴的层号 $\sqsubseteq j+1$.

```agda
GWʰ : ∀ {φ} → Ordᴵ → A 1 φ → T → Set
GWʰ c F u = ∀ {fl} {P : Run fl} {π} → FlrLab[ c ] fl π → LWʰ[ c ] P π → LWʰ[ c ] (F P) (π ++ ψΩᵗ u)

record GA1ʷ {φ} (E : A 1 φ) (ζ : T) : Set where
  constructor ga1ʷ
  field
    fl1ʷ : FlrLabΩ φ ζ
    gw1ʷ : ∀ {c} → GWʰ c E ζ
open GA1ʷ public

module WGenʰ {flE} {E : A 1 flE} {ζ : T} (GE : GA1ʷ E ζ) where

  copyWʰ : ∀ {c ψ fl} {P : Run fl} {π x} {fr : A 1 ψ} → FlrLab[ c ] fl π → (∀ m → FlrLab[ c ] ψ (replicate (suc m) x)) →
           LWʰ[ c ] P π → (∀ {fl′} {Q : Run fl′} {ρ} → FlrLab[ c ] fl′ ρ → LWʰ[ c ] Q ρ → LWʰ[ c ] (fr Q) (ρ ++ x ∷ [])) →
           ∀ m → LWʰ[ c ] (repA 0 P fr m) (π ++ replicate m x)
  copyWʰ {ψ = ψ} F Fψ hP hF zero = zWʰ {φ = ψ} hP
  copyWʰ F Fψ hP hF (suc zero) = hF F hP
  copyWʰ {c = c} {π = π} {x = x} F Fψ hP hF (suc (suc m)) =
    wkLWʰ _ (subst (λ u → LWʰ[ c ] _ u) (snoc π (suc m) x) (hF (FlrLab[]-⊔ F (Fψ m)) (copyWʰ F Fψ hP hF (suc m))))

  WAʰ : ∀ {c φ} {cv : ∀ {L} → Ev L φ → Simᴵ zero L} {t : Ordˢ zero} {y} → FP c φ → Lab0ᴸ t y → GWʰ c (fold 1 φ cv E t) (ζ ++ y)
  WVʰ : ∀ {c k φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {t : Ordˢ k} {y} → FP c φ → LvOK c k → LabL t y → GWʰ c (fold 1 φ cv E t) (ζ ++ y)
  W₊ʰ : ∀ {c k φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {t : Ordˢ k} {y} → FP c φ → LvOK c k → LabL₊ k Ll t y →
       GWʰ c (fold 1 φ cv E t) (ζ ++ y)

  WAʰ {c = c} {y = []} fp (lz cc) F hP = wkLWʰ _ (subst (λ u → LWʰ[ c ] _ (_ ++ ψΩᵗ u)) (sym (++-identityʳ ζ)) (gw1ʷ GE F hP))
  WAʰ {y = y ∷ ys} fp (lz cc) F hP = ⊥-elim (cof-ne y ys cc)
  WAʰ {y = []} fp (ls () l) F hP
  WAʰ {c = c} {φ = φ} {cv = cv} {t = Ord₊ˢ.suc a} {y = y ∷ ys} fp (ls cc l) {P = P} {π = π} F hP =
    limWʰ {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {F = λ m → repA 0 P (fold 1 φ cv E a) m} (c1Ω ζ cc)
          (λ m → subst (λ u → LWʰ[ c ] _ (π ++ u)) (sym (repW Ωᵗ ζ y ys cc m))
                       (copyWʰ F (FP-rep (fl1ʷ GE) fp) hP (WAʰ fp l) m))
  WAʰ {y = []} fp (ll () h) F hP
  WAʰ {c = c} {φ = φ} {cv = cv} {t = Ord₊ˢ.lim G} {y = y ∷ ys} fp (ll cc h) {P = P} {π = π} F hP =
    limWʰ {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {F = λ m → fold 1 φ cv E (G m) P} (cωΩ ζ cc)
          (λ n → subst (λ u → LWʰ[ c ] _ (π ++ u)) (sym (ωW Ωᵗ ζ y ys cc n)) (WAʰ fp (h n) F hP))
  WAʰ {y = []} fp (lŝ₀ () K h₀ hk) F hP
  WAʰ {c = c} {φ = φ} {cv = cv} {y = y ∷ ys} fp (lŝ₀ {t₀ = t₀} {g = g} cc K h₀ hk) {P = P} {π = π} F hP =
    ĉWʰ {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {O₀ = fold 1 φ cv E t₀ P} {O = λ η e → fold 1 φ cv E (g η e) P}
        (cωΩ ζ cc) K (subst (λ u → LWʰ[ c ] _ (π ++ u)) (sym (ωW Ωᵗ ζ y ys cc 0)) (WAʰ fp h₀ F hP))
        (λ k → subst (λ u → LWʰ[ c ] _ (π ++ u)) (sym (ωW Ωᵗ ζ y ys cc (suc k))) (WAʰ fp (hk k) F hP))
  WAʰ {y = []} fp (lĉ () K h₀ hk) F hP
  WAʰ {c = c} {φ = φ} {cv = cv} {y = y ∷ ys} fp (lĉ {o₀ = o₀} {o = o} cc K h₀ hk) {P = P} {π = π} F hP =
    ĉWʰ {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {O₀ = fold 1 φ cv E o₀ P} {O = λ η e → fold 1 φ cv E (o η e) P}
        (cωΩ ζ cc) K (subst (λ u → LWʰ[ c ] _ (π ++ u)) (sym (ωW Ωᵗ ζ y ys cc 0)) (WAʰ fp h₀ F hP))
        (λ k → subst (λ u → LWʰ[ c ] _ (π ++ u)) (sym (ωW Ωᵗ ζ y ys cc (suc k))) (WAʰ fp (hk k) F hP))

  WVʰ {k = zero}    fp lv at = WAʰ fp (atomL at)
  WVʰ {k = suc _}   fp lv h  = W₊ʰ fp lv h
  WVʰ {k = lim _ _} fp lv h  = W₊ʰ fp lv h

  W₊ʰ {c = c} {y = []} fp lv (gz cc) F hP = wkLWʰ _ (subst (λ u → LWʰ[ c ] _ (_ ++ ψΩᵗ u)) (sym (++-identityʳ ζ)) (gw1ʷ GE F hP))
  W₊ʰ {y = y ∷ ys} fp lv (gz cc) F hP = ⊥-elim (cof-ne y ys cc)
  W₊ʰ {y = []} fp lv (gs () l) F hP
  W₊ʰ {c = c} {φ = φ} {cv = cv} {t = Ord₊ˢ.suc a} {y = y ∷ ys} fp lv (gs cc l) {P = P} {π = π} F hP =
    limWʰ {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {F = λ m → repA 0 P (fold 1 φ cv E a) m} (c1Ω ζ cc)
          (λ m → subst (λ u → LWʰ[ c ] _ (π ++ u)) (sym (repW Ωᵗ ζ y ys cc m))
                       (copyWʰ F (FP-rep (fl1ʷ GE) fp) hP (W₊ʰ fp lv l) m))
  W₊ʰ {y = []} fp lv (gl () h) F hP
  W₊ʰ {c = c} {φ = φ} {cv = cv} {t = Ord₊ˢ.lim G} {y = y ∷ ys} fp lv (gl cc h) {P = P} {π = π} F hP =
    limWʰ {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {F = λ m → fold 1 φ cv E (G m) P} (cωΩ ζ cc)
          (λ n → subst (λ u → LWʰ[ c ] _ (π ++ u)) (sym (ωW Ωᵗ ζ y ys cc n)) (W₊ʰ fp lv (h n) F hP))
  W₊ʰ {k = suc k′} {cv = cv} fp lv (gu {r = zero} h) F hP ev p =
    WVʰ {φ = flo k′} {cv = cvFlo k′} (FP-flo lv) (LvOK-pred lv) h F hP (proj₁ ev , (proj₁ (proj₂ ev) , toFlo k′ (λ q → cv (proj₂ (proj₂ ev)) (suc q)))) p
  W₊ʰ {k = lim f s} {cv = cv} fp lv (gu {r = self n} h) F hP ev p =
    WVʰ {φ = flo (f n)} {cv = cvFlo (f n)} (FP-flo′ (LvOK-self lv n)) (LvOK-self lv n) h F hP (proj₁ ev , (proj₁ (proj₂ ev) , toFlo (f n) (λ q → cv (proj₂ (proj₂ ev)) (lim n q)))) p
  W₊ʰ {y = []} fp lv (gi () I ej h) F hP
  W₊ʰ {c = c} {φ = φ} {cv = cv} {y = y ∷ ys} fp lv (gi {q = q} {f = f} cc I ej h) {P = P} {π = π} F hP =
    limᵢWʰ {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {ac = λ ev → cv (proj₂ (proj₂ ev)) q}
           {H = λ x → fold 1 φ cv E (f (intoˢ (<→◃ q) x)) P} (cΩΩ ζ cc I) I ej
           (λ η x l → subst (λ u → LWʰ[ c ] _ (π ++ u)) (sym (penΩ ζ cc I η)) (W₊ʰ fp lv (h η x (→Ll (<→◃ q) l)) F hP))
  W₊ʰ {y = []} fp lv (gĉ () K h₀ hk) F hP
  W₊ʰ {c = c} {φ = φ} {cv = cv} {y = y ∷ ys} fp lv (gĉ {o₀ = o₀} {o = o} cc K h₀ hk) {P = P} {π = π} F hP =
    ĉWʰ {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {O₀ = fold 1 φ cv E o₀ P} {O = λ η e → fold 1 φ cv E (o η e) P}
        (cωΩ ζ cc) K (subst (λ u → LWʰ[ c ] _ (π ++ u)) (sym (ωW Ωᵗ ζ y ys cc 0)) (W₊ʰ fp lv h₀ F hP))
        (λ k → subst (λ u → LWʰ[ c ] _ (π ++ u)) (sym (ωW Ωᵗ ζ y ys cc (suc k))) (W₊ʰ fp lv (hk k) F hP))
  W₊ʰ {k = zero} fp lv (gŝ () cc Iw bw ob h₀ hg)
  W₊ʰ {k = suc _} {y = []} fp lv (gŝ kk () Iw bw ob h₀ hg)
  W₊ʰ {c = c} {k = suc _} {φ = φ} {cv = cv} {y = y ∷ ys} fp lv (gŝ {w = w} {t₀ = t₀} {g = g} kk cc Iw bw ob h₀ hg) {P = P} {π = π} F hP =
    ŝWʰ {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {T₀ = fold 1 φ cv E t₀ P} {G = λ η e → fold 1 φ cv E (g η e) P}
        (cΩΩ ζ cc I0) Iw bw (λ θ → subst (λ u → Occ w (π ++ u)) (sym (penΩ ζ cc I0 θ)) (OccΣ π (od (OccΣ ζ (ob θ)))))
        (subst (λ u → LWʰ[ c ] _ (π ++ u)) (sym (penΩ ζ cc I0 (natT 1))) (W₊ʰ fp lv h₀ F hP))
        (λ θ Y hY lY nθ lt e → subst (λ u → LWʰ[ c ] _ (π ++ u)) (sym (penΩ ζ cc I0 θ)) (W₊ʰ fp lv (hg θ Y hY lY nθ lt e) F hP))
  W₊ʰ {k = lim _ _} {y = []} fp lv (gŝ kk () Iw bw ob h₀ hg)
  W₊ʰ {c = c} {k = lim _ _} {φ = φ} {cv = cv} {y = y ∷ ys} fp lv (gŝ {w = w} {t₀ = t₀} {g = g} kk cc Iw bw ob h₀ hg) {P = P} {π = π} F hP =
    ŝWʰ {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {T₀ = fold 1 φ cv E t₀ P} {G = λ η e → fold 1 φ cv E (g η e) P}
        (cΩΩ ζ cc I0) Iw bw (λ θ → subst (λ u → Occ w (π ++ u)) (sym (penΩ ζ cc I0 θ)) (OccΣ π (od (OccΣ ζ (ob θ)))))
        (subst (λ u → LWʰ[ c ] _ (π ++ u)) (sym (penΩ ζ cc I0 (natT 1))) (W₊ʰ fp lv h₀ F hP))
        (λ θ Y hY lY nθ lt e → subst (λ u → LWʰ[ c ] _ (π ++ u)) (sym (penΩ ζ cc I0 θ)) (W₊ʰ fp lv (hg θ Y hY lY nθ lt e) F hP))
```

## §6 $\Omega_\Omega$ 闭包

```agda
goodΩ̂0Wʰ : ∀ {c fl} {P : Run fl} {π} → FlrLab[ c ] fl π → LWʰ[ c ] P π → LWʰ[ c ] (Ω̂A 0 P) (π ++ ΩΩ ∷ [])
goodΩ̂0Wʰ {fl = fl} {P} {π} F hP =
  cloWʰ {t = fold 0 (fk zero) (λ e → e) P (Ωˢ (suc zero))} {g = λ η → fold 0 (fk η) (λ e q → e (suc q)) P (Ωˢ η)}
        (FW-popᵗ F) refl
        (TlWʰ.tlWVʰ hP {φ = fk zero} {cv = λ e → e} {t = Ωˢ (suc zero)} (LabL-Ω one⁰ (hs hz) lab1 nf1 (≅ᴵ-refl _)))
        (λ θ Y hY lY nθ lt → TlWʰ.tlWVʰ hP {φ = fk (toLevel Y hY)} {cv = λ e q → e (suc q)} {t = Ωˢ (toLevel Y hY)} (LabL-Ω Y hY lY nθ (≅ᴵ-refl _)))

goodΩ̂₀ʷ : GA1ʷ (Ω̂A 0) []
goodΩ̂₀ʷ = ga1ʷ (FlrLab→Ω FlrLab-z) goodΩ̂0Wʰ
```
