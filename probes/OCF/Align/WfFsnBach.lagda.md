# WfFsnBach: Bachmann 性质 (大小论证)

> **记号侧验收工作**, 不是最终定义, 不进成品. [WfFsn](WfFsn.lagda.md) 的第五段. 蓝本: Lean `ExBuchholz/Closure.lean` 的 `size_fs_W0` (1205), `G_size_succ_lt` (1286), `no_small_between` (1323), `bach_pre` (1796), `bachmann` (1820); 在我方定义上重写.
>
> **Bachmann 性质** (`bach`): $\psi_A(B)$ 标准, $B$ 的共尾度为 $\Omega_{\nu+1}$ ⟹ $G_A(B)<B[\Omega_\nu]$. 即 $B$ 在 γ-链首级处的基本列已经越过 $\psi_A$ 在 $B$ 里看到的一切. 规则 6 的 γ-链不变量 (下一段 `tow`) 只靠它.
>
> 证明是 Lean 的大小论证, 三件事: $|B[\Omega_\nu]|+1=|B|$ (`size-fΩ`, 基本列在首级处恰好少一个结点); $G_A(B)$ 的成员至少小两个结点 (`G-size2`); $B[\Omega_\nu]$ 与 $B$ 之间没有这么小的项 (`no-small`). 于是 $x\in G_A(B)$ 对 $B[\Omega_\nu]$ 三歧: 小于则得证, 等于则大小矛盾, 大于则 $x$ 夹在中间 (因 $x<B$, 标准形) 而又太小, 矛盾. 与 Lean 相比: 只用空前缀 (Lean 的 `bach_pre` 带前缀 $p$, 但 `bachmann` 只用 $p=0$), 所以不需要 `addT_between`; 正规叶 "$\nu\le p<\nu+1\Rightarrow p=\nu$" 是句法事实 (`<sucT`), 不要标准形; 也不要 Lean 的条件 $\nu+1>A$ (对一切 $A$ 成立).
>
> `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.WfFsnBach where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-trans; m≤m+n; m≤n+m; +-suc; +-identityʳ; +-cancelˡ-≤;
                                       1+n≰n; +-monoʳ-≤; +-monoˡ-≤; ≤-pred)
open import Data.Product.Base using (Σ; _×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

import OCF.Align.EBO as E
open E using (T; PT; ψ; _<ᵀ_; _<ᴾ_; []<; hd<; tl<; lv<; ar<; cof; c1; cΩ; pred; sucT; Ωt; pred-suc)
open import OCF.Align.Bachmann using (<ᵀ-irrefl; <ᵀ-asym; <sucT)
open import OCF.Align.WfFsnBase
open import OCF.Align.WfFsnView
open import OCF.Align.WfFsnTrian using (cons-btw; psi-btw; irrᴾ)
```

## §1 算术小件

```agda
sz1 : ∀ u a → size (ψ u a ∷ []) ≡ suc (size u + size a)
sz1 u a = +-identityʳ (suc (size u + size a))

sz-hd : ∀ p q s → suc (size p + size q) ≤ size (ψ p q ∷ s)
sz-hd p q s = m≤m+n (suc (size p + size q)) (size s)

sz-ne : ∀ {u} → NE u → 1 ≤ size u
sz-ne {ψ w c ∷ xs} ne = s≤s z≤n

szP-pos : ∀ x → 1 ≤ sizeP x
szP-pos (ψ u a) = s≤s z≤n

suc≤+ : ∀ m {n} → 1 ≤ n → suc m ≤ m + n
suc≤+ m {n} h = subst (_≤ m + n) (trans (+-suc m 0) (cong suc (+-identityʳ m))) (+-monoʳ-≤ m h)

ss : ∀ m n → suc (suc (m + n)) ≡ m + suc (suc n)
ss m n = sym (trans (+-suc m (suc n)) (cong suc (+-suc m n)))

-- n ≥ m 而 n+2 ≤ m+1: 矛盾
ctr : ∀ {m n k} → m ≤ n → suc (suc n) ≤ k → k ≡ suc m → ⊥
ctr {m} mn h refl = 1+n≰n (≤-trans (s≤s (s≤s mn)) h)

≤-≡ : ∀ {a b c} → a ≤ b → b ≡ c → a ≤ c
≤-≡ h refl = h

ne-c1 : ∀ {u} → cof u ≡ c1 → NE u
ne-c1 {_ ∷ _} _ = ne

ne-Ω : ∀ {u μ} → cof u ≡ cΩ μ → NE u
ne-Ω {_ ∷ _} _ = ne
```

## §2 三件事

**$|B[\Omega_\nu]|+1=|B|$.**

```agda
size-fΩ : ∀ {V ν} (w : VΩ V ν) → suc (size (fΩ w (Ωt ν))) ≡ size V
size-fΩ (ωs {x = x} w) = trans (sym (+-suc (sizeP x) _)) (cong (sizeP x +_) (size-fΩ w))
size-fΩ (ωr {u = u} e) =
  trans (cong suc (sz1 (pred u) [])) (trans (cong (λ m → suc (m + 0)) (sym su)) (sym (sz1 u [])))
  where
  su : size u ≡ suc (size (pred u))
  su = trans (cong size (sym (pred-suc u e))) (size-sucT (pred u))
size-fΩ (ωl {u = u} {μ = ν} e w) =
  trans (cong suc (sz1 (fΩ w (Ωt ν)) [])) (trans (cong (λ m → suc (m + 0)) (size-fΩ w)) (sym (sz1 u [])))
size-fΩ (ωp {u = u} {b} {μ = ν} be pen w) =
  trans (cong suc (sz1 u (fΩ w (Ωt ν))))
    (trans (cong suc (sym (+-suc (size u) _)))
      (trans (cong (λ m → suc (size u + m)) (size-fΩ w)) (sym (sz1 u b))))
```

**$G$ 的成员至少小两个结点** (Lean `G_size_succ_lt`): 视图保证首个结点的下标非空或后面还有项.

```agda
node2 : ∀ {u z w c} → NE w → InG u z (ψ w c ∷ []) → suc (suc (size z)) ≤ size (ψ w c ∷ [])
node2 {w = w} {c} nw i = ≤-≡ (go i) (sym (sz1 w c)) where
  go : ∀ {z} → InG _ z (ψ w c ∷ []) → suc (suc (size z)) ≤ suc (size w + size c)
  go (gp (gh _))   = s≤s (+-monoˡ-≤ (size c) (sz-ne nw))
  go (gp (gw _ p)) = s≤s (≤-trans (G-size p) (m≤m+n (size w) (size c)))
  go (gp (gc _ p)) = s≤s (≤-trans (G-size p) (m≤n+m (size c) (size w)))
  go (gtl ())

G-size2 : ∀ {V ν u z} → VΩ V ν → InG u z V → suc (suc (size z)) ≤ size V
G-size2 (ωs {x = x} {y} {ys} w) (gp p)  = ≤-trans (s≤s (GP-size p)) (suc≤+ (sizeP x) (sz-ne {y ∷ ys} ne))
G-size2 (ωs {x = x} {y} {ys} w) (gtl p) = ≤-trans (s≤s (G-size p)) (+-monoˡ-≤ (size (y ∷ ys)) (szP-pos x))
G-size2 (ωr e) i = node2 (ne-c1 e) i
G-size2 (ωl e w) i = node2 (ne-Ω e) i
G-size2 (ωp {u = u} {μ = ν} be pen w) i = node2 (pen-ne ν u pen) i
```

**中间没有小项** (Lean `no_small_between`).

```agda
not-self′ : ∀ {x x′ c₁} → x ≡ x′ → (x ∷ c₁) <ᵀ (x′ ∷ []) → ⊥
not-self′ e (hd< p) = irrᴾ e p
not-self′ e (tl< ())

no-small : ∀ {V ν} (w : VΩ V ν) y → suc (suc (size y)) ≤ size V → fΩ w (Ωt ν) <ᵀ y → y <ᵀ V → ⊥
no-small (ωs {x = x} {y = y′} {ys = ys} w) y sz q r with cons-btw q (inj₁ r)
... | c₀ , refl , q₀ , inj₂ refl = <ᵀ-irrefl r
... | c₀ , refl , q₀ , inj₁ r₀ =
  no-small w c₀ (+-cancelˡ-≤ (sizeP x) _ _ (subst (_≤ sizeP x + size (y′ ∷ ys)) (ss (sizeP x) (size c₀)) sz)) q₀ r₀
-- 正规叶 Ω_u, u = ν+1: 中间的项首项下标只能是 ν, 于是太大
no-small (ωr e) y sz q (hd< (ar< ()))
no-small (ωr e) y sz q (tl< ())
no-small (ωr {u = u} e) (ψ p q′ ∷ s) sz (hd< (lv< νp)) (hd< (lv< pu))
  with <sucT (pred u) (subst (p <ᵀ_) (sym (pred-suc u e)) pu)
... | inj₁ pν   = <ᵀ-asym νp pν
... | inj₂ refl = <ᵀ-irrefl νp
no-small (ωr {u = u} e) (ψ p q′ ∷ s) sz (hd< (ar< _)) (hd< (lv< pu)) =
  ctr (≤-trans (s≤s (m≤m+n (size (pred u)) (size q′))) (sz-hd (pred u) q′ s)) sz (reg-sz u e)
  where
  reg-sz : ∀ u → cof u ≡ c1 → size (ψ u [] ∷ []) ≡ suc (suc (size (pred u)))
  reg-sz u e = trans (sz1 u []) (cong suc (trans (+-identityʳ (size u))
                 (trans (cong size (sym (pred-suc u e))) (size-sucT (pred u)))))
no-small (ωr {u = u} e) (ψ p q′ ∷ s) sz (tl< _) (hd< (lv< pu)) =
  ctr (≤-trans (s≤s (m≤m+n (size (pred u)) (size q′))) (sz-hd (pred u) q′ s)) sz
      (trans (sz1 u []) (cong suc (trans (+-identityʳ (size u))
        (trans (cong size (sym (pred-suc u e))) (size-sucT (pred u))))))
-- 奇异叶 Ω_u: 中间的项首项下标夹在 u[W] 与 u 之间
no-small (ωl e w) y sz q (hd< (ar< ()))
no-small (ωl e w) y sz q (tl< ())
no-small (ωl {u = u} {μ = ν} e w) (ψ p q′ ∷ s) sz (hd< (lv< fp)) (hd< (lv< pu)) =
  no-small w p (≤-pred (≤-trans (s≤s (s≤s (≤-trans (s≤s (m≤m+n (size p) (size q′))) (sz-hd p q′ s))))
                                (≤-≡ sz (trans (sz1 u []) (cong suc (+-identityʳ (size u)))))))
           fp pu
no-small (ωl {u = u} {μ = ν} e w) (ψ p q′ ∷ s) sz (hd< (ar< _)) (hd< (lv< pu)) =
  ctr (≤-trans (subst (_≤ suc (size (fΩ w (Ωt ν)) + size q′)) (size-fΩ w)
                      (s≤s (m≤m+n (size (fΩ w (Ωt ν))) (size q′))))
               (sz-hd (fΩ w (Ωt ν)) q′ s))
      sz (trans (sz1 u []) (cong suc (+-identityʳ (size u))))
no-small (ωl {u = u} {μ = ν} e w) (ψ p q′ ∷ s) sz (tl< _) (hd< (lv< pu)) =
  ctr (≤-trans (subst (_≤ suc (size (fΩ w (Ωt ν)) + 0)) (size-fΩ w)
                      (s≤s (m≤m+n (size (fΩ w (Ωt ν))) 0)))
               (sz-hd (fΩ w (Ωt ν)) [] s))
      sz (trans (sz1 u []) (cong suc (+-identityʳ (size u))))
-- 穿透 ψ_u(b): 中间的项是 ψ_u(c₀)+…, c₀ 夹在 b[W] 与 b 之间
no-small (ωp {u = u} {b} {μ = ν} be pen w) y sz q r with psi-btw (inj₁ q) (inj₁ r)
... | c₀ , c₁ , refl , l₀ , inj₂ refl = not-self′ refl r
... | c₀ , c₁ , refl , inj₂ refl , inj₁ cb =
  ctr (sz-hd u (fΩ w (Ωt ν)) c₁) sz
      (trans (sz1 u b) (cong suc (trans (cong (size u +_) (sym (size-fΩ w))) (+-suc (size u) _))))
... | c₀ , c₁ , refl , inj₁ fc , inj₁ cb =
  no-small w c₀ (+-cancelˡ-≤ (size u) _ _ (subst (_≤ size u + size b) (ss (size u) (size c₀))
                   (≤-pred (≤-trans (s≤s (s≤s (sz-hd u c₀ c₁))) (≤-≡ sz (sz1 u b))))))
           fc cb
```

## §3 Bachmann 性质

```agda
bach : ∀ {A B ν} → NF (ψ A B ∷ []) → (w : VΩ B ν) → ∀ {x} → InG A x B → x <ᵀ fΩ w (Ωt ν)
bach {ν = ν} n w {x} i with tri x (fΩ w (Ωt ν))
... | inj₁ p = p
... | inj₂ (inj₁ refl) = ⊥-elim (1+n≰n (subst (suc (suc (size x)) ≤_) (sym (size-fΩ w)) (G-size2 w i)))
... | inj₂ (inj₂ q) = ⊥-elim (no-small w x (G-size2 w i) q (nfp-g (nf-hd n) i))
```
