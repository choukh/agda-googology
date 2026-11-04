# 值验收 (一): 带字面标签的树的结构律

> **验收文件, 读记号.** 入口 [ValLab](ValLab.lagda.md). 这里只有记号与 `Lab`, 不碰证书.
>
> - `lab-≺`: 带字面标签的树的任何 $\prec$ 子树也带字面标签 (标签随基本列走).
> - `ω-term`: 一棵树同时带 $\psi_0(1)$ 与 $t$, 则 $t$ 就是 $\psi_0(1)$.
> - `classify`: $\omega$-共尾的 $s$ 若 $s[0]=\psi_0(1)$, 只有四个形状 $A$: $\psi_0(1)+a$, $\psi_0(1+a)$, $\psi_0(\Omega_a)$, $\psi_0(\psi_0(a))$, 其中 $a[0]=0$, 于是 $s[1]=A(p)$, $s[2]=A(p+p)$; 另有一个例外 $s=\psi_0(\Omega)$. 这是 `rule4` 的推广.
> - `chain-rule`: **对一切 $s$**: 若 `lim h` 带 $s$, $h_0$ 是 $\omega$, 且 $h_1$ 沿第 0 项走 $k$ 步到 $\omega$, 则 $h_2$ 沿第 0 项走 $k$ 步到的树 $\cong h_1$.
>
> `chain-rule` 不要求标准形, 对任意项成立. 它是下面否定的来源: 链行第 0 项固定是 $\omega$, 而后面的项不满足这条律 ([ValLabNeg](ValLabNeg.lagda.md)).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ValLabBase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; _∷_; []; replicate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Free.Level
open import OCF.Align.OrdLabZCorrespond using (Lab; l0; l1; lω; Lab-≅)
open import OCF.Align.OrdLabZStage2 using (Lab-uniq)
import OCF.Align.EBO as E
open E using (T; PT; 𝟏; natT; Ωt; cof; cofP; fsn; fsT; pred; γT; Cof; c0; c1; cω; cΩ; cmpᵀ; lt; eq; gt; sucT; cofA; cofψ0; cofψ₊; fsT0; fsT₊; fsTc) renaming (ψ to ψᵗ; _<ᵀ_ to _<ᵗ_)
open import OCF.Align.Bachmann using (cofA≢c1)
open import OCF.Align.Standard using (fsT-ne; cofψ0≢c1)
open import OCF.Align.Correspond using (cmp-suc[]; cof-ne; fs-rep; fs-ω; fsn↓c-gt; fsT-c1; fs-Ωω)
```

## §1 标签沿树走

```agda
lim-lab : ∀ {X t} {h : ℕ → Ordᶜ zero} → Lab X t → X ≅ lim h → (cof t ≡ cω) × (∀ n → Lab (h n) (fsn t n))
lim-lab (l0 c e) eh with ≅-trans (≅-sym eh) e
... | ()
lim-lab (l1 c e l) eh with ≅-trans (≅-sym eh) e
... | ()
lim-lab {h = h} (lω {F = F} c e H) eh = c , λ n → Lab-≅ (lp (≅-trans (≅-sym eh) e) n) (H n)
  where
  lp : ∀ {f g : ℕ → Ordᶜ zero} → lim f ≅ lim g → ∀ n → f n ≅ g n
  lp (l≅ k) = k

suc-lab : ∀ {X Y t} → Lab X t → X ≅ suc Y → (cof t ≡ c1) × Lab Y (pred t)
suc-lab (l0 c e) es with ≅-trans (≅-sym es) e
... | ()
suc-lab (l1 c e l) es with ≅-trans (≅-sym es) e
... | s≅ d = c , Lab-≅ d l
suc-lab (lω c e h) es with ≅-trans (≅-sym es) e
... | ()

zero-lab : ∀ {X t} → Lab X t → X ≅ zero {ℓ = zero} → t ≡ []
zero-lab {t = []} l e = refl
zero-lab {t = y ∷ ys} (l0 c e′) e = ⊥-elim (cof-ne y ys c)
zero-lab {t = y ∷ ys} (l1 c e′ l) e with ≅-trans (≅-sym e′) e
... | ()
zero-lab {t = y ∷ ys} (lω c e′ h) e with ≅-trans (≅-sym e′) e
... | ()

-- [] 的标签: 树是 0
lab[] : ∀ {X} → Lab X [] → X ≅ zero {ℓ = zero}
lab[] (l0 c e) = e
lab[] (l1 () e l)
lab[] (lω () e h)

-- 带标签的树的 ≺ 子树也带标签
lab-≺ : ∀ {c Y : Ordᶜ zero} {t} → c ≺ Y → Lab Y t → Σ T (Lab c)
lab-≺ h (l0 c e) with ≺-respʳ h e
... | ()
lab-≺ h (l1 c e l) with ≺-respʳ h e
... | ≺z d = _ , Lab-≅ d l
... | ≺s r = lab-≺ r l
lab-≺ h (lω c e H) with ≺-respʳ h e
... | ≺l n r = lab-≺ r (H n)
```

## §2 记号: $\omega$ 的标签唯一

```agda
Hd : PT
Hd = ψᵗ [] (𝟏 ∷ [])

ω̂ : T
ω̂ = Hd ∷ []

cofP≡c1 : ∀ x → cofP x ≡ c1 → x ≡ 𝟏
cofP≡c1 (ψᵗ [] []) e = refl
cofP≡c1 (ψᵗ (w ∷ ws) []) e = ⊥-elim (cofψ0≢c1 (w ∷ ws) (cof (w ∷ ws)) e)
cofP≡c1 (ψᵗ u (y ∷ ys)) e = ⊥-elim (cofA≢c1 u (cof (y ∷ ys)) e)

-- rule4 的加强: 第 0 项是 0 的 ω-共尾项的全部形状
data R4 : T → Set where
  r4 : ∀ u y ys → cof (y ∷ ys) ≡ c1 → R4 (ψᵗ u (y ∷ ys) ∷ [])

rule4′ : ∀ X → cof X ≡ cω → fsn X 0 ≡ [] → R4 X
rule4′ [] () f
rule4′ (x ∷ y ∷ ys) c ()
rule4′ (ψᵗ [] [] ∷ []) () f
rule4′ (ψᵗ (w ∷ ws) [] ∷ []) c f = ⊥-elim (go (cof (w ∷ ws)) refl c (trans (sym (E.fsn0-eq w ws 0 refl)) f))
  where
  go : ∀ k (ue : cof (w ∷ ws) ≡ k) → E.cofψ0 (w ∷ ws) k ≡ cω → E.trm (E.fsn↓0 w ws k ue 0) ≡ [] → ⊥
  go c0 ue c′ f′ = cof-ne w ws ue
  go c1 ue () f′
  go cω ue c′ ()
  go (cΩ μ) ue () f′
rule4′ (ψᵗ u (y ∷ ys) ∷ []) c f = go (cof (y ∷ ys)) refl c
  where
  go : ∀ k (be : cof (y ∷ ys) ≡ k) → E.cofA u k ≡ cω → R4 (ψᵗ u (y ∷ ys) ∷ [])
  go c0 be c′ = ⊥-elim (cof-ne y ys be)
  go c1 be c′ = r4 u y ys be
  go cω be c′ with trans (sym (E.fsn₊-eq u y ys 0 be)) f
  ... | ()
  go (cΩ ν) be c′ = ⊥-elim (gc (E.cmpᵀ (E.sucT ν) u) (trans (sym (E.fsn₊-eq u y ys 0 be)) f))
    where
    gc : ∀ m → E.trm (E.fsn↓c u y ys ν be m 0) ≡ [] → ⊥
    gc E.lt ()
    gc E.eq ()
    gc E.gt ()

-- 记 ω₀ 为任一带 ω̂ 的树
ω-parts : ∀ {w} → Lab w ω̂ → Σ (ℕ → Ordᶜ zero) λ f → (w ≅ lim f) × (f 0 ≅ zero {ℓ = zero}) × Σ (Ordᶜ zero) λ b → (f 1 ≅ suc b) × (b ≅ zero {ℓ = zero})
ω-parts (l0 () e)
ω-parts (l1 () e l)
ω-parts (lω {F = F} c e H) = F , e , lab[] (H 0) , P
  where
  P : Σ (Ordᶜ zero) λ b → (F 1 ≅ suc b) × (b ≅ zero {ℓ = zero})
  P with H 1
  ... | l0 () e′
  ... | lω () e′ h′
  ... | l1 c′ e′ l′ = _ , e′ , lab[] l′

uOf aOf : PT → T
uOf (ψᵗ u a) = u
aOf (ψᵗ u a) = a

ω-r4 : ∀ {t} → R4 t → cof (fsn t 1) ≡ c1 → t ≡ ω̂
ω-r4 (r4 u y ys be) c = go u (cong uOf E₁) (trans (sym (E.pred-suc (y ∷ ys) be)) (cong sucT (cong aOf E₁)))
  where
  E₁ : ψᵗ u (pred (y ∷ ys)) ≡ 𝟏
  E₁ = cofP≡c1 _ (subst (λ z → cof z ≡ c1) (fs-rep u y ys be 1) c)
  go : ∀ a {b} → a ≡ [] → b ≡ 𝟏 ∷ [] → ψᵗ a b ∷ [] ≡ ω̂
  go .[] refl refl = refl

ω-term : ∀ {w t} → Lab w ω̂ → Lab w t → t ≡ ω̂
ω-term {w} {t} lw l₂ with ω-parts lw
... | f , ef , f0 , b , f1 , b0 =
  ω-r4 (rule4′ t (proj₁ (lim-lab l₂ ef)) (zero-lab (proj₂ (lim-lab l₂ ef) 0) f0)) (proj₁ (suc-lab (proj₂ (lim-lab l₂ ef) 1) f1))
```

## §3 第 0 步

`stpc a k`: 把 $\psi_0(\Omega_a)$ 的基本列第 0 项翻到下标上, $k$ 是 `cof a`. 后继取前驱, $\omega$-共尾取第 0 项, $\Omega_{\nu+1}$-共尾取 $a[\Omega_\nu]$.

```agda
stpc : T → Cof → T
stpc a c0 = a
stpc a c1 = pred a
stpc a cω = fsn a 0
stpc a (cΩ ν) = fsT a (Ωt ν)

stpc-cons : ∀ p x xs k → stpc (p ∷ x ∷ xs) k ≡ p ∷ stpc (x ∷ xs) k
stpc-cons p x xs c0 = refl
stpc-cons p x xs c1 = refl
stpc-cons p x xs cω = refl
stpc-cons p x xs (cΩ ν) = refl

-- 规则 6: 下标 0
fs6 : ∀ y ys ν → cof (y ∷ ys) ≡ cΩ ν → ∀ n → fsn (ψᵗ [] (y ∷ ys) ∷ []) n ≡ ψᵗ [] (fsT (y ∷ ys) (γT (y ∷ ys) ν n)) ∷ []
fs6 y ys ν be n = trans (E.fsn₊-eq [] y ys n be) (trans (fsn↓c-gt [] y ys ν be _ (cmp-suc[] ν) n)
  (cong (λ z → ψᵗ [] z ∷ []) (trans (E.fsT↓-trm (y ∷ ys) be _) (cong (fsT (y ∷ ys)) (E.γ↓-trm (y ∷ ys) ν be n)))))

fsT0Ω : ∀ u c ν η → c ≡ cΩ ν → fsT0 u c η ≡ ψᵗ (fsT u η) [] ∷ []
fsT0Ω u .(cΩ ν) ν η refl = refl

-- 规则 6: 一般下标
fs6′ : ∀ u y ys ν → cof (y ∷ ys) ≡ cΩ ν → cmpᵀ (sucT ν) u ≡ gt → ∀ n → fsn (ψᵗ u (y ∷ ys) ∷ []) n ≡ ψᵗ u (fsT (y ∷ ys) (γT (y ∷ ys) ν n)) ∷ []
fs6′ u y ys ν be m n = trans (E.fsn₊-eq u y ys n be) (trans (fsn↓c-gt u y ys ν be _ m n)
  (cong (λ z → ψᵗ u z ∷ []) (trans (E.fsT↓-trm (y ∷ ys) be _) (cong (fsT (y ∷ ys)) (E.γ↓-trm (y ∷ ys) ν be n)))))

cofA[]Ω : ∀ ν → cofA [] (cΩ ν) ≡ cω
cofA[]Ω ν = cong (cofψ₊ [] ν) (cmp-suc[] ν)
```

## §4 四个形状

`Fam A`: $A$ 的第 0 步可以算出, 而且对前面加一项稳定. `Gd k` 说这一类共尾度上第 0 步还是 $A$ 的形状.

```agda
record Fam (A : T → T) : Set₁ where
  field
    A[]  : A [] ≡ ω̂
    inj  : ∀ x xs → A (x ∷ xs) ≡ ω̂ → ⊥
    Gd   : Cof → Set
    dec  : ∀ k → Gd k ⊎ (∀ x xs → cof (x ∷ xs) ≡ k → cof (A (x ∷ xs)) ≡ cω → cof (fsn (A (x ∷ xs)) 0) ≡ cω → ⊥)
    good : ∀ {k} → Gd k → ∀ x xs → cof (x ∷ xs) ≡ k → cof (A (x ∷ xs)) ≡ cω → fsn (A (x ∷ xs)) 0 ≡ A (stpc (x ∷ xs) k)
open Fam public

-- ω + a
A₁ : T → T
A₁ a = Hd ∷ a

F₁ : Fam A₁
F₁ = record { A[] = refl ; inj = λ x xs () ; Gd = Gd₁ ; dec = dc ; good = gd }
  where
  Gd₁ : Cof → Set
  Gd₁ cω = ⊤
  Gd₁ _  = ⊥
  dc : ∀ k → Gd₁ k ⊎ (∀ x xs → cof (x ∷ xs) ≡ k → cof (A₁ (x ∷ xs)) ≡ cω → cof (fsn (A₁ (x ∷ xs)) 0) ≡ cω → ⊥)
  dc c0 = inj₂ (λ x xs e _ _ → cof-ne x xs e)
  dc c1 = inj₂ (λ x xs e c _ → bad (trans (sym e) c))
    where
    bad : c1 ≡ cω → ⊥
    bad ()
  dc cω = inj₁ tt
  dc (cΩ ν) = inj₂ (λ x xs e c _ → bad (trans (sym e) c))
    where
    bad : cΩ ν ≡ cω → ⊥
    bad ()
  gd : ∀ {k} → Gd₁ k → ∀ x xs → cof (x ∷ xs) ≡ k → cof (A₁ (x ∷ xs)) ≡ cω → fsn (A₁ (x ∷ xs)) 0 ≡ A₁ (stpc (x ∷ xs) k)
  gd {k = cω} g x xs e c = refl

-- ψ₀(1 + a)
A₂ : T → T
A₂ a = ψᵗ [] (𝟏 ∷ a) ∷ []

F₂ : Fam A₂
F₂ = record { A[] = refl ; inj = λ x xs e → in₂ e ; Gd = Gd₂ ; dec = dc ; good = gd }
  where
  in₂ : ∀ {x xs} → ψᵗ [] (𝟏 ∷ x ∷ xs) ∷ [] ≡ ω̂ → ⊥
  in₂ ()
  Gd₂ : Cof → Set
  Gd₂ c1 = ⊥
  Gd₂ _  = ⊤
  dc : ∀ k → Gd₂ k ⊎ (∀ x xs → cof (x ∷ xs) ≡ k → cof (A₂ (x ∷ xs)) ≡ cω → cof (fsn (A₂ (x ∷ xs)) 0) ≡ cω → ⊥)
  dc c0 = inj₁ tt
  dc c1 = inj₂ (λ x xs e _ c → bad (subst (λ z → cof z ≡ cω) (fs-rep [] 𝟏 (x ∷ xs) e 0) c))
    where
    bad : cof [] ≡ cω → ⊥
    bad ()
  dc cω = inj₁ tt
  dc (cΩ ν) = inj₁ tt
  gd : ∀ {k} → Gd₂ k → ∀ x xs → cof (x ∷ xs) ≡ k → cof (A₂ (x ∷ xs)) ≡ cω → fsn (A₂ (x ∷ xs)) 0 ≡ A₂ (stpc (x ∷ xs) k)
  gd {k = c0} g x xs e c = ⊥-elim (cof-ne x xs e)
  gd {k = cω} g x xs e c = fs-ω [] 𝟏 (x ∷ xs) e 0
  gd {k = cΩ ν} g x xs e c = fs6 𝟏 (x ∷ xs) ν e 0

-- ψ₀(Ω_a)
A₃ : T → T
A₃ a = ψᵗ [] (ψᵗ a [] ∷ []) ∷ []

F₃ : Fam A₃
F₃ = record { A[] = refl ; inj = λ x xs e → in₃ e ; Gd = λ _ → ⊤ ; dec = λ k → inj₁ tt ; good = gd }
  where
  in₃ : ∀ {x xs} → ψᵗ [] (ψᵗ (x ∷ xs) [] ∷ []) ∷ [] ≡ ω̂ → ⊥
  in₃ ()
  gd : ∀ {k} → ⊤ → ∀ x xs → cof (x ∷ xs) ≡ k → cof (A₃ (x ∷ xs)) ≡ cω → fsn (A₃ (x ∷ xs)) 0 ≡ A₃ (stpc (x ∷ xs) k)
  gd {k = c0} g x xs e c = ⊥-elim (cof-ne x xs e)
  gd {k = c1} g x xs e c = trans (fs6 (ψᵗ (x ∷ xs) []) [] _ (cong (E.cofψ0 (x ∷ xs)) e) 0) (cong (λ z → ψᵗ [] z ∷ []) (fsT-c1 (x ∷ xs) _ e _))
  gd {k = cω} g x xs e c = trans (fs-ω [] (ψᵗ (x ∷ xs) []) [] (cong (E.cofψ0 (x ∷ xs)) e) 0) (cong (λ z → ψᵗ [] z ∷ []) (E.fsn0-eq x xs 0 e))
  gd {k = cΩ ν} g x xs e c = trans (fs6 (ψᵗ (x ∷ xs) []) [] ν (cong (E.cofψ0 (x ∷ xs)) e) 0) (cong (λ z → ψᵗ [] z ∷ []) (fsT0Ω (x ∷ xs) _ ν _ e))

-- ψ₀(ψ₀(a))
A₄ : T → T
A₄ a = ψᵗ [] (ψᵗ [] a ∷ []) ∷ []

F₄ : Fam A₄
F₄ = record { A[] = refl ; inj = λ x xs e → in₄ e ; Gd = Gd₄ ; dec = dc ; good = gd }
  where
  in₄ : ∀ {x xs} → ψᵗ [] (ψᵗ [] (x ∷ xs) ∷ []) ∷ [] ≡ ω̂ → ⊥
  in₄ ()
  Gd₄ : Cof → Set
  Gd₄ c1 = ⊥
  Gd₄ _  = ⊤
  bad : cof (𝟏 ∷ []) ≡ cω → ⊥
  bad ()
  dc : ∀ k → Gd₄ k ⊎ (∀ x xs → cof (x ∷ xs) ≡ k → cof (A₄ (x ∷ xs)) ≡ cω → cof (fsn (A₄ (x ∷ xs)) 0) ≡ cω → ⊥)
  dc c0 = inj₁ tt
  dc c1 = inj₂ (λ x xs e _ c → bad (subst (λ z → cof z ≡ cω)
     (trans (fs-ω [] (ψᵗ [] (x ∷ xs)) [] (cong (cofA []) e) 0) (cong (λ z → ψᵗ [] z ∷ []) (fs-rep [] x xs e 0))) c))
  dc cω = inj₁ tt
  dc (cΩ ν) = inj₁ tt
  gd : ∀ {k} → Gd₄ k → ∀ x xs → cof (x ∷ xs) ≡ k → cof (A₄ (x ∷ xs)) ≡ cω → fsn (A₄ (x ∷ xs)) 0 ≡ A₄ (stpc (x ∷ xs) k)
  gd {k = c0} g x xs e c = ⊥-elim (cof-ne x xs e)
  gd {k = cω} g x xs e c = trans (fs-ω [] (ψᵗ [] (x ∷ xs)) [] (cong (cofA []) e) 0) (cong (λ z → ψᵗ [] z ∷ []) (fs-ω [] x xs e 0))
  gd {k = cΩ ν} g x xs e c = trans (fs-ω [] (ψᵗ [] (x ∷ xs)) [] (trans (cong (cofA []) e) (cofA[]Ω ν)) 0) (cong (λ z → ψᵗ [] z ∷ []) (fs6 x xs ν e 0))
```

## §5 沿第 0 项走

```agda
data Zk : ℕ → Ordᶜ zero → Ordᶜ zero → Set where
  z0 : ∀ {x y} → x ≅ y → Zk 0 x y
  zs : ∀ {k x y} {f : ℕ → Ordᶜ zero} → x ≅ lim f → Zk k (f 0) y → Zk (suc k) x y

Zk→lim : ∀ {k x w} → Lab w ω̂ → Zk k x w → Σ (ℕ → Ordᶜ zero) λ g → x ≅ lim g
Zk→lim lw (z0 e) with ω-parts lw
... | f , ef , _ = f , ≅-trans e ef
Zk→lim lw (zs e z) = _ , e

z≇l : ∀ {x : Ordᶜ zero} {g : ℕ → Ordᶜ zero} → x ≅ zero {ℓ = zero} → x ≅ lim g → ⊥
z≇l a b with ≅-trans (≅-sym a) b
... | ()

walk : ∀ {A} (F : Fam A) k a p {w w₀ v y} → Lab w (A a) → Lab w₀ ω̂ → Zk k w w₀ → Lab v (A (p ∷ a)) → Zk k v y → Lab y (A (p ∷ []))
walk F zero [] p lw l₀ (z0 e) lv (z0 e′) = Lab-≅ (≅-sym e′) lv
walk F zero (x ∷ xs) p lw l₀ (z0 e) lv (z0 e′) = ⊥-elim (inj F x xs (ω-term l₀ (Lab-≅ (≅-sym e) lw)))
walk F (suc k) [] p lw l₀ (zs ew zk) lv z′ =
  ⊥-elim (z≇l (lab[] (proj₂ (lim-lab (subst (Lab _) (A[] F) lw) ew) 0)) (proj₂ (Zk→lim l₀ zk)))
walk {A} F (suc k) (x ∷ xs) p {v = v} {y = y} lw l₀ (zs {f = f} ew zk) lv (zs {f = g} ev zk′) = go (dec F (cof (x ∷ xs)))
  where
  Lf = lim-lab lw ew
  Lg = lim-lab lv ev
  go : Gd F (cof (x ∷ xs)) ⊎ (∀ x′ xs′ → cof (x′ ∷ xs′) ≡ cof (x ∷ xs) → cof (A (x′ ∷ xs′)) ≡ cω → cof (fsn (A (x′ ∷ xs′)) 0) ≡ cω → ⊥) → Lab y (A (p ∷ []))
  go (inj₂ bd) = ⊥-elim (bd x xs refl (proj₁ Lf) (proj₁ (lim-lab (proj₂ Lf 0) (proj₂ (Zk→lim l₀ zk)))))
  go (inj₁ gd′) = walk F k (stpc (x ∷ xs) (cof (x ∷ xs))) p
    (subst (Lab (f 0)) (good F gd′ x xs refl (proj₁ Lf)) (proj₂ Lf 0)) l₀ zk
    (subst (Lab (g 0)) (trans (good F gd′ p (x ∷ xs) refl (proj₁ Lg)) (cong A (stpc-cons p x xs (cof (x ∷ xs))))) (proj₂ Lg 0)) zk′
```

## §6 分类

```agda
data Cls (s : T) : Set₁ where
  cfam : ∀ {A} → Fam A → (p : PT) → fsn s 1 ≡ A (p ∷ []) → fsn s 2 ≡ A (p ∷ p ∷ []) → Cls s
  cex  : fsn s 1 ≡ ψᵗ [] ω̂ ∷ [] → Cls s

cons-inj : ∀ {x y : PT} {r t : T} → x ∷ r ≡ y ∷ t → (x ≡ y) × (r ≡ t)
cons-inj refl = refl , refl

r4→ : ∀ {X} → R4 X → Σ PT λ p → (fsn X 1 ≡ p ∷ []) × (fsn X 2 ≡ p ∷ p ∷ [])
r4→ (r4 u y ys be) = ψᵗ u (pred (y ∷ ys)) , fs-rep u y ys be 1 , fs-rep u y ys be 2

P₀ : ∀ X → cof X ≡ cω → fsn X 0 ≡ [] → Σ PT λ p → (fsn X 1 ≡ p ∷ []) × (fsn X 2 ≡ p ∷ p ∷ [])
P₀ X c f = r4→ (rule4′ X c f)

no-fsT[] : ∀ {d ν} → cof d ≡ cΩ ν → fsT d (Ωt ν) ≡ [] → ⊥
no-fsT[] {d} {ν} c e with subst (_ <ᵗ_) e (fsT-ne {d} {ν} {Ωt ν} c E.[]<)
... | ()

cofψ₊gt : ∀ u ν m → cofψ₊ u ν m ≡ cω → m ≡ gt
cofψ₊gt u ν lt ()
cofψ₊gt u ν eq ()
cofψ₊gt u ν gt e = refl

-- b[0] = 1
cω₁ : ∀ y ys → cof (y ∷ ys) ≡ cω → fsn (y ∷ ys) 0 ≡ 𝟏 ∷ [] → Cls (ψᵗ [] (y ∷ ys) ∷ [])
cω₁ y (y′ ∷ ys′) be e with cons-inj e
... | refl , r = cfam F₂ (proj₁ P) (trans (fs-ω [] 𝟏 (y′ ∷ ys′) be 1) (cong (λ z → ψᵗ [] (𝟏 ∷ z) ∷ []) (proj₁ (proj₂ P))))
                     (trans (fs-ω [] 𝟏 (y′ ∷ ys′) be 2) (cong (λ z → ψᵗ [] (𝟏 ∷ z) ∷ []) (proj₂ (proj₂ P))))
  where P = P₀ (y′ ∷ ys′) be r
cω₁ (ψᵗ [] []) [] () e
cω₁ (ψᵗ (w ∷ ws) []) [] be e = go (cof (w ∷ ws)) refl be
  where
  go : ∀ k (ue : cof (w ∷ ws) ≡ k) → cofψ0 (w ∷ ws) k ≡ cω → Cls (ψᵗ [] (ψᵗ (w ∷ ws) [] ∷ []) ∷ [])
  go c0 ue c = ⊥-elim (cof-ne w ws ue)
  go c1 ue ()
  go (cΩ ν) ue ()
  go cω ue c = cfam F₃ (proj₁ P) (trans (fs-Ωω w ws ue 1) (cong (λ z → ψᵗ [] (ψᵗ z [] ∷ []) ∷ []) (proj₁ (proj₂ P))))
                       (trans (fs-Ωω w ws ue 2) (cong (λ z → ψᵗ [] (ψᵗ z [] ∷ []) ∷ []) (proj₂ (proj₂ P))))
    where
    aOf₁ : T → T
    aOf₁ (ψᵗ z _ ∷ _) = z
    aOf₁ [] = []
    r : fsn (w ∷ ws) 0 ≡ []
    r = cong aOf₁ (trans (sym (E.fsn0-eq w ws 0 ue)) e)
    P = P₀ (w ∷ ws) ue r
cω₁ (ψᵗ u (y′ ∷ ys′)) [] be e = go (cof (y′ ∷ ys′)) refl be
  where
  S = ψᵗ u (y′ ∷ ys′) ∷ []
  go : ∀ k (ce : cof (y′ ∷ ys′) ≡ k) → cofA u k ≡ cω → Cls (ψᵗ [] S ∷ [])
  go c0 ce c = ⊥-elim (cof-ne y′ ys′ ce)
  go c1 ce c with trans (sym (fs-rep u y′ ys′ ce 0)) e
  ... | ()
  go cω ce c = aux u (cong (λ t → uOf′ t) e₁) (cong (λ t → aOf′ t) e₁)
    where
    uOf′ aOf′ : T → T
    uOf′ (ψᵗ a _ ∷ _) = a
    uOf′ [] = []
    aOf′ (ψᵗ _ a ∷ _) = a
    aOf′ [] = []
    e₁ : ψᵗ u (fsn (y′ ∷ ys′) 0) ∷ [] ≡ 𝟏 ∷ []
    e₁ = trans (sym (fs-ω u y′ ys′ ce 0)) e
    aux : ∀ a → a ≡ [] → fsn (y′ ∷ ys′) 0 ≡ [] → Cls (ψᵗ [] (ψᵗ a (y′ ∷ ys′) ∷ []) ∷ [])
    aux .[] refl r = cfam F₄ (proj₁ P)
       (trans (fs-ω [] (ψᵗ [] (y′ ∷ ys′)) [] (cong (cofA []) ce) 1) (cong (λ z → ψᵗ [] z ∷ []) (trans (fs-ω [] y′ ys′ ce 1) (cong (λ z → ψᵗ [] z ∷ []) (proj₁ (proj₂ P))))))
       (trans (fs-ω [] (ψᵗ [] (y′ ∷ ys′)) [] (cong (cofA []) ce) 2) (cong (λ z → ψᵗ [] z ∷ []) (trans (fs-ω [] y′ ys′ ce 2) (cong (λ z → ψᵗ [] z ∷ []) (proj₂ (proj₂ P))))))
      where P = P₀ (y′ ∷ ys′) ce r
  go (cΩ ν) ce c = ⊥-elim (no-fsT[] ce (cong aOf″ (trans (sym (fs6′ u y′ ys′ ν ce (cofψ₊gt u ν _ c) 0)) e)))
    where
    aOf″ : T → T
    aOf″ (ψᵗ _ a ∷ _) = a
    aOf″ [] = []

-- b[γ₀] = 1
cΩ₁ : ∀ y ys ν → cof (y ∷ ys) ≡ cΩ ν → fsT (y ∷ ys) (Ωt ν) ≡ 𝟏 ∷ [] → Cls (ψᵗ [] (y ∷ ys) ∷ [])
cΩ₁ y (y′ ∷ ys′) ν be e = ⊥-elim (no-fsT[] {y′ ∷ ys′} {ν} be (proj₂ (cons-inj e)))
cΩ₁ (ψᵗ [] []) [] ν () e
cΩ₁ (ψᵗ (w ∷ ws) []) [] ν be e = go (cof (w ∷ ws)) refl be
  where
  go : ∀ k (ue : cof (w ∷ ws) ≡ k) → cofψ0 (w ∷ ws) k ≡ cΩ ν → Cls (ψᵗ [] (ψᵗ (w ∷ ws) [] ∷ []) ∷ [])
  go c0 ue c = ⊥-elim (cof-ne w ws ue)
  go cω ue ()
  go (cΩ ν′) ue c = ⊥-elim (no-fsT[] {w ∷ ws} {ν} (trans ue (cong cΩ (E.cΩ-inj c))) (cong tOf (trans (sym (fsT0Ω (w ∷ ws) _ ν _ (trans ue (cong cΩ (E.cΩ-inj c))))) e)))
    where
    tOf : T → T
    tOf (ψᵗ a _ ∷ _) = a
    tOf [] = []
  go c1 ue c = fin (trans (sym (E.pred-suc (w ∷ ws) ue)) (cong sucT pr))
    where
    tOf : T → T
    tOf (ψᵗ a _ ∷ _) = a
    tOf [] = []
    e₂ : Ωt ν ≡ 𝟏 ∷ []
    e₂ = trans (sym (fsT-c1 (w ∷ ws) (cof (w ∷ ws)) ue (Ωt ν))) e
    pr : pred (w ∷ ws) ≡ []
    pr = trans (E.cΩ-inj c) (cong tOf e₂)
    fin : w ∷ ws ≡ 𝟏 ∷ [] → Cls (ψᵗ [] (ψᵗ (w ∷ ws) [] ∷ []) ∷ [])
    fin q = subst (λ v → Cls (ψᵗ [] (ψᵗ v [] ∷ []) ∷ [])) (sym q) (cex refl)
cΩ₁ (ψᵗ u (y′ ∷ ys′)) [] ν be e = go (cof (y′ ∷ ys′)) refl be e
  where
  go : ∀ k (ce : cof (y′ ∷ ys′) ≡ k) → cofA u k ≡ cΩ ν → E.fsT₊ u (y′ ∷ ys′) (cof (y′ ∷ ys′)) (Ωt ν) ≡ 𝟏 ∷ [] → Cls (ψᵗ [] (ψᵗ u (y′ ∷ ys′) ∷ []) ∷ [])
  go c0 ce c e′ = ⊥-elim (cof-ne y′ ys′ ce)
  go c1 ce () e′
  go cω ce () e′
  go (cΩ ν′) ce c e′ = gm (cmpᵀ (sucT ν′) u) refl c
    where
    aOf″ : T → T
    aOf″ (ψᵗ _ a ∷ _) = a
    aOf″ [] = []
    fT : ∀ c′ → c′ ≡ cΩ ν′ → ∀ m → m ≡ cmpᵀ (sucT ν′) u → (m ≡ lt ⊎ m ≡ eq) → E.fsT₊ u (y′ ∷ ys′) c′ (Ωt ν) ≡ ψᵗ u (fsT (y′ ∷ ys′) (Ωt ν)) ∷ []
    fT .(cΩ ν′) refl .lt me (inj₁ refl) rewrite sym me = refl
    fT .(cΩ ν′) refl .eq me (inj₂ refl) rewrite sym me = refl
    gm : ∀ m → m ≡ cmpᵀ (sucT ν′) u → cofψ₊ u ν′ m ≡ cΩ ν → Cls (ψᵗ [] (ψᵗ u (y′ ∷ ys′) ∷ []) ∷ [])
    gm gt me ()
    gm lt me c₂ = ⊥-elim (bad′ (trans ce (cong cΩ (E.cΩ-inj c₂))) (cong aOf″ (trans (sym (fT _ ce lt me (inj₁ refl))) e′)))
      where
      bad′ : cof (y′ ∷ ys′) ≡ cΩ ν → fsT (y′ ∷ ys′) (Ωt ν) ≡ [] → ⊥
      bad′ = no-fsT[]
    gm eq me c₂ = ⊥-elim (bad′ (trans ce (cong cΩ (E.cΩ-inj c₂))) (cong aOf″ (trans (sym (fT _ ce eq me (inj₂ refl))) e′)))
      where
      bad′ : cof (y′ ∷ ys′) ≡ cΩ ν → fsT (y′ ∷ ys′) (Ωt ν) ≡ [] → ⊥
      bad′ = no-fsT[]

classify : ∀ s → cof s ≡ cω → fsn s 0 ≡ ω̂ → Cls s
classify [] () e
classify (x ∷ y ∷ ys) c e with cons-inj e
... | refl , r = cfam F₁ (proj₁ P) (cong (Hd ∷_) (proj₁ (proj₂ P))) (cong (Hd ∷_) (proj₂ (proj₂ P)))
  where P = P₀ (y ∷ ys) c r
classify (ψᵗ [] [] ∷ []) () e
classify (ψᵗ (w ∷ ws) [] ∷ []) c e = go (cof (w ∷ ws)) refl c
  where
  go : ∀ k (ue : cof (w ∷ ws) ≡ k) → cofψ0 (w ∷ ws) k ≡ cω → Cls (ψᵗ (w ∷ ws) [] ∷ [])
  go c0 ue c′ = ⊥-elim (cof-ne w ws ue)
  go c1 ue ()
  go (cΩ ν) ue ()
  go cω ue c′ with trans (sym (E.fsn0-eq w ws 0 ue)) e
  ... | ()
classify (ψᵗ u (y ∷ ys) ∷ []) c e = go (cof (y ∷ ys)) refl c
  where
  uOf′ aOf′ : T → T
  uOf′ (ψᵗ a _ ∷ _) = a
  uOf′ [] = []
  aOf′ (ψᵗ _ a ∷ _) = a
  aOf′ [] = []
  go : ∀ k (be : cof (y ∷ ys) ≡ k) → cofA u k ≡ cω → Cls (ψᵗ u (y ∷ ys) ∷ [])
  go c0 be c′ = ⊥-elim (cof-ne y ys be)
  go c1 be c′ with trans (sym (fs-rep u y ys be 0)) e
  ... | ()
  go cω be c′ = aux u (cong uOf′ e₁) (cong aOf′ e₁)
    where
    e₁ : ψᵗ u (fsn (y ∷ ys) 0) ∷ [] ≡ ω̂
    e₁ = trans (sym (fs-ω u y ys be 0)) e
    aux : ∀ a → a ≡ [] → fsn (y ∷ ys) 0 ≡ 𝟏 ∷ [] → Cls (ψᵗ a (y ∷ ys) ∷ [])
    aux .[] refl r = cω₁ y ys be r
  go (cΩ ν) be c′ = aux u (cong uOf′ e₁) (cong aOf′ e₁)
    where
    e₁ : ψᵗ u (fsT (y ∷ ys) (Ωt ν)) ∷ [] ≡ ω̂
    e₁ = trans (sym (fs6′ u y ys ν be (cofψ₊gt u ν _ c′) 0)) e
    aux : ∀ a → a ≡ [] → fsT (y ∷ ys) (Ωt ν) ≡ 𝟏 ∷ [] → Cls (ψᵗ a (y ∷ ys) ∷ [])
    aux .[] refl r = cΩ₁ y ys ν be r
```

## §7 链律

```agda
ex-out : ∀ {k w w₀} → Lab w (ψᵗ [] ω̂ ∷ []) → Lab w₀ ω̂ → Zk k w w₀ → ⊥
ex-out lw l₀ (z0 e) with ω-term l₀ (Lab-≅ (≅-sym e) lw)
... | ()
ex-out lw l₀ (zs ew zk) = bad (proj₁ (lim-lab (proj₂ (lim-lab lw ew) 0) (proj₂ (Zk→lim l₀ zk))))
  where
  bad : c1 ≡ cω → ⊥
  bad ()

chain-rule : ∀ {s k y w₀} {h : ℕ → Ordᶜ zero} → Lab (lim h) s → Lab (h 0) ω̂ → Lab w₀ ω̂ → Zk k (h 1) w₀ → Zk k (h 2) y → y ≅ h 1
chain-rule {s} {k} {y} {w₀} {h} L l₀ lw z₁ z₂ = go (classify s (proj₁ Ls) (ω-term l₀ (proj₂ Ls 0)))
  where
  Ls = lim-lab L (≅-refl⁰ _)
  go : Cls s → y ≅ h 1
  go (cex e) = ⊥-elim (ex-out (subst (Lab (h 1)) e (proj₂ Ls 1)) lw z₁)
  go (cfam {A} F p e₁ e₂) =
    Lab-uniq (walk F k (p ∷ []) p (subst (Lab (h 1)) e₁ (proj₂ Ls 1)) lw z₁ (subst (Lab (h 2)) e₂ (proj₂ Ls 2)) z₂) (subst (Lab (h 1)) e₁ (proj₂ Ls 1))
```
