# EboLean3Base: 层号上的句法事实, $C$-集与 $\mathcal W$ 的基本引理

> **记号侧验收工作**, 读记号 (EBO 的项、序与标准形), 不进成品. [EboLean3](EboLean3.lagda.md) 良基证明的底座.
>
> 定义 ($C$, $M$, $\tau$, $\mathcal W$, `Ag`, $\mathbb W$) 取自 [EboLean2](EboLean2.lagda.md) §1, 本文不改. 这里是对它们的引理, 都是 EBO 专有的短证明 (对照 Setzer 1998 的位置写在每段开头). 要点: $C$ 按层号 $l$ 索引, 叶子是 $A$ 中 $<\Omega_l$ 的元素, 所以 Setzer 的 $\tilde a$ 就是 $\Omega_{\mathrm{hs}(a)}$, 4.7 (a) 是定义, 4.13 (b) (`𝒲-cong`) 不要 $A\subseteq M(A)$.
>
> `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EboLean3Base where

open import Level using (Level)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using ([]; _∷_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂; swap)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import OCF.Align.EboLeanDef using (T; ψ; 𝟏; Ωt; Ωs; sucT; _<ᵀ_; []<; hd<; tl<; lv<; ar<)
open import OCF.Align.EBO using (<-sucT)
open import OCF.Align.EboLeanBase using (_≤ᵀ_; _≤ᴾ_; <ᵀ-trans; <ᵀ-irrefl; <sucT; ≤-trans′; ≤-<; <-≤;
  dec≤; idx<; tail<; NF; n[]; n∷; nf-hd; nf-tl; nf-le; nfp-u; nf-Ω)
open import OCF.Align.EboLean2 using (Pred; hs; C; cl; c0; c+; cΩ; cψ; M; τ; 𝒲; sup; []≤; C-all)

private variable
  ℓ ℓ′ : Level
```

## §1 层号的句法事实

都对一切项成立 (字典序), 标明要 `NF` 的除外. $\Omega_v\le\psi_v(e)+\cdots$; $\psi_v(e)+\cdots<\Omega_k\Rightarrow v<k$; 于是 $y<\Omega_{l+1}\iff\mathrm{hs}(y)\le l$.

```agda
Ω≤ : ∀ v e ys → Ωt v ≤ᵀ (ψ v e ∷ ys)
Ω≤ v []      []      = inj₂ refl
Ω≤ v []      (_ ∷ _) = inj₁ (tl< []<)
Ω≤ v (_ ∷ _) ys      = inj₁ (hd< (ar< []<))

hd<Ω : ∀ {v e ys k} → (ψ v e ∷ ys) <ᵀ Ωt k → v <ᵀ k
hd<Ω (hd< (lv< p)) = p
hd<Ω (hd< (ar< ()))
hd<Ω (tl< ())

noleaf : ∀ {v e ys} → (ψ v e ∷ ys) <ᵀ Ωt v → ⊥
noleaf p = <ᵀ-irrefl (hd<Ω p)

<Ωt : ∀ a → a <ᵀ Ωt a
<Ωt a = idx< a [] []

hs≤ : ∀ a → hs a ≤ᵀ a
hs≤ []           = inj₂ refl
hs≤ (ψ v e ∷ as) = inj₁ (idx< v e as)

hs<Ω : ∀ {y k} → hs y <ᵀ k → y <ᵀ Ωt k
hs<Ω {y = []}     _ = []<
hs<Ω {y = ψ v e ∷ ys} p = hd< (lv< p)

Ωt-mono : ∀ {k l} → k ≤ᵀ l → Ωt k ≤ᵀ Ωt l
Ωt-mono (inj₁ p)    = inj₁ (hd< (lv< p))
Ωt-mono (inj₂ refl) = inj₂ refl

lvl : ∀ {y l} → y <ᵀ Ωs l → hs y ≤ᵀ l
lvl {y = []}     {l} _ = []≤ l
lvl {y = ψ v e ∷ ys} {l} p = <sucT l (hd<Ω p)

lvl⁻ : ∀ {y l} → hs y ≤ᵀ l → y <ᵀ Ωs l
lvl⁻ {l = l} p = hs<Ω (≤-< p (<-sucT l))

≤→<Ωs : ∀ {v l} → v ≤ᵀ l → v <ᵀ Ωs l
≤→<Ωs {l = l} p = ≤-< p (<ᵀ-trans (<-sucT l) (<Ωt (sucT l)))

hs-mono : ∀ {y m} → y ≤ᵀ m → hs y ≤ᵀ hs m
hs-mono (inj₂ refl) = inj₂ refl
hs-mono {y = []} {m} (inj₁ _) = []≤ (hs m)
hs-mono {ψ v e ∷ ys} {ψ w b ∷ ms} (inj₁ (hd< (lv< p))) = inj₁ p
hs-mono {ψ v e ∷ ys} {ψ w b ∷ ms} (inj₁ (hd< (ar< _))) = inj₂ refl
hs-mono {ψ v e ∷ ys} {ψ w b ∷ ms} (inj₁ (tl< _))       = inj₂ refl

Ω≤→ : ∀ {k v e ys} → Ωt k ≤ᵀ (ψ v e ∷ ys) → k ≤ᵀ v
Ω≤→ (inj₂ refl)              = inj₂ refl
Ω≤→ (inj₁ (hd< (lv< p)))     = inj₁ p
Ω≤→ (inj₁ (hd< (ar< _)))     = inj₂ refl
Ω≤→ (inj₁ (tl< _))           = inj₂ refl

-- 元素 m 的层以下就是 m 以下
Ωhs≤ : ∀ {z m} → z <ᵀ Ωt (hs m) → z ≤ᵀ m
Ωhs≤ {m = []} []<            = inj₂ refl
Ωhs≤ {m = []} (hd< (lv< ()))
Ωhs≤ {m = []} (hd< (ar< ()))
Ωhs≤ {m = []} (tl< ())
Ωhs≤ {m = ψ v e ∷ ms} p      = inj₁ (<-≤ p (Ω≤ v e ms))

one≤ᴾ : ∀ x → 𝟏 ≤ᴾ x
one≤ᴾ (ψ [] [])      = inj₂ refl
one≤ᴾ (ψ [] (_ ∷ _)) = inj₁ (ar< []<)
one≤ᴾ (ψ (_ ∷ _) _)  = inj₁ (lv< []<)

sucT≤ : ∀ {y a} → y <ᵀ a → sucT y ≤ᵀ a
sucT≤ {y = []} {x ∷ []}     []< with one≤ᴾ x
... | inj₁ p    = inj₁ (hd< p)
... | inj₂ refl = inj₂ refl
sucT≤ {y = []} {x ∷ _ ∷ _}  []< with one≤ᴾ x
... | inj₁ p    = inj₁ (hd< p)
... | inj₂ refl = inj₁ (tl< []<)
sucT≤ (hd< p) = inj₁ (hd< p)
sucT≤ (tl< {x = x} p) with sucT≤ p
... | inj₁ q = inj₁ (tl< q)
... | inj₂ e = inj₂ (cong (x ∷_) e)

nf-suc : ∀ {t} → NF t → NF (sucT t)
nf-suc n[] = nf-Ω n[]
nf-suc (n∷ {x} {xs = []} p _ _)     = n∷ p (one≤ᴾ x) (nf-Ω n[])
nf-suc (n∷ {xs = _ ∷ _} p h n) = n∷ p h (nf-suc n)

nf-h : ∀ {x xs} → NF (x ∷ xs) → NF (x ∷ [])
nf-h n = n∷ (nf-hd n) tt n[]

h<s : ∀ {x y ys} → (x ∷ []) <ᵀ (x ∷ y ∷ ys)
h<s = tl< []<

t<s : ∀ {x y ys} → NF (x ∷ y ∷ ys) → (y ∷ ys) <ᵀ (x ∷ y ∷ ys)
t<s {x} {y} {ys} n = tail< x (y ∷ ys) (nf-le n) (nf-tl n)
```

## §2 $C$-集

**同余** (Setzer 4.7 (c) 与 4.13 (b) 的 $C$ 部分): $C_A^l$ 只看 $A\cap\Omega_l$. **上推** (Setzer 4.7 (g) 的核心): $y<\Omega_k$ 时 $y$ 的推导不含 ψ-构造, 层号可以升. **首项下标** ($\tilde y$ 的 EBO 版): $y\in C^{\mathrm{hs}(y)}$ 蕴含 $\mathrm{hs}(y)\in C^{\mathrm{hs}(y)}$. **提升**: 层号 $\mathrm{hs}(y)\le k$ 时, 由 $M$ 或叶子得 $y\in C^k$.

```agda
module _ {A : Pred ℓ} {B : Pred ℓ′} {k : T} (f : ∀ {z} → z <ᵀ Ωt k → A z → B z) where
  C-cong : ∀ {y} → C A k y → C B k y
  C-cong (cl a p)     = cl (f p a) p
  C-cong c0           = c0
  C-cong (c+ x y)     = c+ (C-cong x) (C-cong y)
  C-cong (cΩ w)       = cΩ (C-cong w)
  C-cong (cψ q w c)   = cψ q (C-cong w) (C-cong c)

module _ {A : Pred ℓ} where
  C-up : ∀ {k k′ y} → k ≤ᵀ k′ → NF y → y <ᵀ Ωt k → C A k y → C A k′ y
  C-up kk ny p (cl a q)            = cl a (<-≤ q (Ωt-mono kk))
  C-up kk ny p c0                  = c0
  C-up kk ny p (c+ {ψ v e} dx dys) =
    c+ (C-up kk (nf-h ny) (<ᵀ-trans h<s p) dx) (C-up kk (nf-tl ny) (<ᵀ-trans (t<s ny) p) dys)
  C-up {k} kk ny p (cΩ dw)         = cΩ (C-up kk (nfp-u (nf-hd ny)) (<ᵀ-trans (hd<Ω p) (<Ωt k)) dw)
  C-up kk ny p (cψ q _ _)          = ⊥-elim (<ᵀ-irrefl (≤-< q (hd<Ω p)))

  C-hs : ∀ {v e ds} → C A v (ψ v e ∷ ds) → C A v v
  C-hs (cl _ p)     = ⊥-elim (noleaf p)
  C-hs (c+ dx _)    = C-hs dx
  C-hs (cΩ dv)      = dv
  C-hs (cψ _ dv _)  = dv

  inv+ : ∀ {v e y ys} → C A v (ψ v e ∷ y ∷ ys) → C A v (ψ v e ∷ []) × C A v (y ∷ ys)
  inv+ (cl _ p)    = ⊥-elim (noleaf p)
  inv+ (c+ dx dys) = dx , dys

  C-lift : ∀ {k y} → hs y ≤ᵀ k → (y <ᵀ Ωt k → A y) → C A (hs y) y → C A k y
  C-lift (inj₁ p)    a _ = cl (a (hs<Ω p)) (hs<Ω p)
  C-lift (inj₂ refl) _ c = c
```

**降层** (Setzer 4.7 (b), `C-anti`): $k\le k'$, $A\subseteq M(A)$ ⟹ $C_A^{k'}\subseteq C_A^k$. 叶子 $y\in A$ 若 $\ge\Omega_k$, 就改用 $y\in M(A)$ 的推导 (它不是叶子) 往下拆. 对项结构递归 (`antiT` 与主项的 `antiP`, `antiN` 互递归); 推导本身不变小, 所以不能对推导递归.

```agda
decΩ : ∀ k v e ys → ((ψ v e ∷ ys) <ᵀ Ωt k) ⊎ (k ≤ᵀ v)
decΩ k v e ys with dec≤ (Ωt k) (ψ v e ∷ ys)
... | inj₁ q = inj₂ (Ω≤→ q)
... | inj₂ p = inj₁ p

module _ {A : Pred ℓ} (h : ∀ {y} → A y → M A y) where
  antiT : ∀ {k k′} y → k ≤ᵀ k′ → C A k′ y → C A k y
  antiP : ∀ {k k′} v e → k ≤ᵀ k′ → C A k′ (ψ v e ∷ []) → C A k (ψ v e ∷ [])
  antiN : ∀ {k} v e → k ≤ᵀ v → C A v (ψ v e ∷ []) → C A k (ψ v e ∷ [])

  antiT [] _ _ = c0
  antiT (ψ v e ∷ []) q d = antiP v e q d
  antiT {k} (ψ v e ∷ tl@(_ ∷ _)) q (cl a p) =
    [ cl a , (λ kv → c+ (antiN v e kv (proj₁ (inv+ (h a)))) (antiT tl kv (proj₂ (inv+ (h a))))) ]′ (decΩ k v e tl)
  antiT (ψ v e ∷ tl@(_ ∷ _)) q (c+ dx dys) = c+ (antiP v e q dx) (antiT tl q dys)

  antiP {k} v e q (cl a p)   = [ cl a , (λ kv → antiN v e kv (h a)) ]′ (decΩ k v e [])
  antiP v [] q (cΩ dv)       = cΩ (antiT v q dv)
  antiP v e q (cψ q′ dv dc)  = cψ (≤-trans′ q q′) (antiT v q dv) (antiT e q dc)

  antiN v e _ (cl _ p)      = ⊥-elim (noleaf p)
  antiN v [] kv (cΩ dv)     = cΩ (antiT v kv dv)
  antiN v e kv (cψ _ dv dc) = cψ kv (antiT v kv dv) (antiT e kv dc)

  C-anti : ∀ {k k′ y} → k ≤ᵀ k′ → C A k′ y → C A k y
  C-anti q d = antiT _ q d
```

## §3 $\mathcal W$ 的基本引理

$0\in\mathcal W(A)$; $\mathcal W$-归纳 (Setzer Assumption 4.10 (b)); 分量 (和的首项、尾, 首项的下标) 都在 $\tau^A$ 里, 所以留在 $\mathcal W(A)$.

```agda
module _ {A : Pred ℓ} where
  0∈𝒲 : 𝒲 A []
  0∈𝒲 = sup n[] c0 (λ { (_ , _ , ()) })

  𝒲-NF : ∀ {a} → 𝒲 A a → NF a
  𝒲-NF (sup n _ _) = n

  𝒲-M : ∀ {a} → 𝒲 A a → M A a
  𝒲-M (sup _ m _) = m

  𝒲-τ : ∀ {a y} → 𝒲 A a → τ A a y → 𝒲 A y
  𝒲-τ (sup _ _ f) t = f t

  𝒲-ind : ∀ {ℓ″} {B : Pred ℓ″} → (∀ {a} → 𝒲 A a → (∀ {y} → τ A a y → B y) → B a) → ∀ {a} → 𝒲 A a → B a
  𝒲-ind st w@(sup _ _ f) = st w (λ t → 𝒲-ind st (f t))

  W-hs : ∀ {v e ds} → 𝒲 A (ψ v e ∷ ds) → 𝒲 A v
  W-hs {v} {e} {ds} w = 𝒲-τ w (nfp-u (nf-hd (𝒲-NF w)) , C-hs (𝒲-M w) , idx< v e ds)

  W-hd : ∀ {v e y ys} → 𝒲 A (ψ v e ∷ y ∷ ys) → 𝒲 A (ψ v e ∷ [])
  W-hd w = 𝒲-τ w (nf-h (𝒲-NF w) , proj₁ (inv+ (𝒲-M w)) , h<s)

  W-tl : ∀ {v e y ys} → 𝒲 A (ψ v e ∷ y ∷ ys) → 𝒲 A (y ∷ ys)
  W-tl w = 𝒲-τ w (nf-tl (𝒲-NF w) , proj₂ (inv+ (𝒲-M w)) , t<s (𝒲-NF w))
```

**同余** (Setzer 4.13 (b)): $A$, $B$ 在 $\Omega_l$ 以下一致, 则 $\mathcal W(A)$, $\mathcal W(B)$ 在层号 $\le l$ 的项上一致. 不要 $A\subseteq M(A)$ (Setzer 要, 为了经 $\tilde y$ 换写 $C^y$). `𝒲-cong≤` 是 "在 $c$ 以下一致 ⟹ 在 $\le c$ 处一致" 的形式.

```agda
Agree : T → Pred ℓ → Pred ℓ′ → Set _
Agree c A B = ∀ {z} → z <ᵀ c → (A z → B z) × (B z → A z)

flip : ∀ {c} {A : Pred ℓ} {B : Pred ℓ′} → Agree c A B → Agree c B A
flip ag p = swap (ag p)

𝒲-cong : ∀ {l y} {A : Pred ℓ} {B : Pred ℓ′} → Agree (Ωt l) A B → hs y ≤ᵀ l → 𝒲 A y → 𝒲 B y
𝒲-cong {l = l} {y} ag yl (sup n m f) =
  sup n (C-cong (λ p → proj₁ (ag (lt p))) m)
        (λ (nz , cz , z<) → 𝒲-cong ag (≤-trans′ (hs-mono (inj₁ z<)) yl)
                                    (f (nz , C-cong (λ p → proj₂ (ag (lt p))) cz , z<)))
  where
    lt : ∀ {z} → z <ᵀ Ωt (hs y) → z <ᵀ Ωt l
    lt p = <-≤ p (Ωt-mono yl)

𝒲-cong≤ : ∀ {c y} {A : Pred ℓ} {B : Pred ℓ′} → Agree c A B → y ≤ᵀ c → 𝒲 A y → 𝒲 B y
𝒲-cong≤ {y = []} _ _ _ = 0∈𝒲
𝒲-cong≤ {y = ψ v e ∷ ys} ag yc w = 𝒲-cong (λ p → ag (<-≤ (<-≤ p (Ω≤ v e ys)) yc)) (inj₂ refl) w

C-cong-at : ∀ {a y} {A : Pred ℓ} {B : Pred ℓ′} → Agree a A B → C A (hs a) y → C B (hs a) y
C-cong-at {a = []} {y} _ _ = C-all y
C-cong-at {a = ψ v e ∷ as} ag d = C-cong (λ p → proj₁ (ag (<-≤ p (Ω≤ v e as)))) d
```
