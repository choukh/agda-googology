# EboBach: EBO 标准形上基本列的共尾性 (Bach)

> **记号侧验收工作**, 读记号, 不进成品. 判决: 编译过的定理, 无前提. `bach`: $s$ 是标准形, $s<t$ (`_<ᵀ_`) 时, $t$ 后继则 $s\le\mathrm{pred}\,t$; 余尾 ω 则有 $n$ 使 $s<t[n]$ (`fsn`); 余尾 $\Omega_{\kappa+1}$ 则有标准形 $\eta<\Omega_{\kappa+1}$ 使 $s<t[\eta]$ (`fsT`). 对 $t$ 不要求标准形. 规则 6 一支经 `below` (参数的 ν-成分都低于 $p$ 时 $\alpha<\beta$ 推出 $\alpha<\beta[p]$) 与 `Chain.R` (γ-链压住 ν-成分).
> 不否定什么: 不涉及树, 不说明 N1 的项模型或命名不变式成立. 基本列取 [EboLeanDef](EboLeanDef.lagda.md) 的 `fsn` 与 [EBO](EBO.lagda.md) 的 `fsT`, `γT`; 标准形取 [EboLeanBase](EboLeanBase.lagda.md) 的 `NF`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EboBach where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_; replicate; length)
open import Data.Nat.Base using (ℕ; zero; suc; _⊔_; _≤_; _≤′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; ≤⇒≤′)
open import Data.Product.Base using (Σ; _×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)

open import OCF.Align.EboLeanDef
open import OCF.Align.EBO using (pred-suc; <-sucT; []<sucT)
open import OCF.Align.EboLeanBase
```

## §1 小引理

```agda
𝟏≤ : ∀ x → 𝟏 ≤ᴾ x
𝟏≤ (ψ [] [])       = inj₂ refl
𝟏≤ (ψ [] (y ∷ ys)) = inj₁ (ar< []<)
𝟏≤ (ψ (w ∷ ws) a)  = inj₁ (lv< []<)

nf-sucT : ∀ {s} → NF s → NF (sucT s)
nf-sucT n[] = nf-Ω n[]
nf-sucT (n∷ {x = x} {xs = []} p h n)     = n∷ p (𝟏≤ x) (nf-sucT n)
nf-sucT (n∷ {xs = y ∷ ys} p h n) = n∷ p h (nf-sucT n)

suc<Ωs : ∀ {s} μ → s <ᵀ Ωs μ → sucT s <ᵀ Ωs μ
suc<Ωs μ []<      = hd< (lv< ([]<sucT μ))
suc<Ωs μ (hd< p)  = hd< p
suc<Ωs μ (tl< ())

<≤ᴾ : ∀ {x y z} → x <ᴾ y → y ≤ᴾ z → x <ᴾ z
<≤ᴾ p (inj₁ q)    = <ᴾ-trans p q
<≤ᴾ p (inj₂ refl) = p

rep< : ∀ {x s} → NF s → HdLe x s → s <ᵀ replicate (suc (length s)) x
rep< n[] _                    = []<
rep< (n∷ p h n) (inj₁ q)      = hd< q
rep< (n∷ p h n) (inj₂ refl)   = tl< (rep< n h)

cofψ₊-nz : ∀ u μ m → cofψ₊ u μ m ≡ c0 → ⊥
cofψ₊-nz u μ lt ()
cofψ₊-nz u μ eq ()
cofψ₊-nz u μ gt ()

cof-nz   : ∀ y ys → cof (y ∷ ys) ≡ c0 → ⊥
cofψ0-nz : ∀ w ws c → cof (w ∷ ws) ≡ c → cofψ0 (w ∷ ws) c ≡ c0 → ⊥
cof-nz y (z ∷ zs) e = cof-nz z zs e
cof-nz 𝟏 [] ()
cof-nz (ψ u (a ∷ as)) [] e = go (cof (a ∷ as)) e where
  go : ∀ c → cofA u c ≡ c0 → ⊥
  go c0 ()
  go c1 ()
  go cω ()
  go (cΩ μ) e′ = cofψ₊-nz u μ (cmpᵀ (sucT μ) u) e′
cof-nz (ψ (w ∷ ws) []) [] e = cofψ0-nz w ws (cof (w ∷ ws)) refl e
cofψ0-nz w ws c0 we e = cof-nz w ws we
cofψ0-nz w ws c1 we ()
cofψ0-nz w ws cω we ()
cofψ0-nz w ws (cΩ μ) we ()

cofΩ-ne : ∀ b {ν} → cof b ≡ cΩ ν → [] <ᵀ b
cofΩ-ne [] ()
cofΩ-ne (x ∷ xs) _ = []<
```

## §2 ν-成分低于 $p$ 时, $\alpha<\beta$ 推出 $\alpha<\beta[p]$

`Small ν p α`: 把 α 拆成主项, 下标 $>\nu$ 的主项穿进下标与参数, 下标 $\le\nu$ 的主项 (ν-成分, 都 $<\Omega_{\nu+1}$) 都 $<p$. 这是 Buchholz 的 "$K_\nu\alpha<\xi$" 的句法版, ξ 取单个主项 $p$.

```agda
data Small  (ν : T) (p : PT) : T → Set
data SmallP (ν : T) (p : PT) : PT → Set
data Small ν p where
  s[] : Small ν p []
  s∷  : ∀ {x xs} → SmallP ν p x → Small ν p xs → Small ν p (x ∷ xs)
data SmallP ν p where
  sLo : ∀ {w c} → w ≤ᵀ ν → ψ w c <ᴾ p → SmallP ν p (ψ w c)
  sHi : ∀ {w c} → ν <ᵀ w → Small ν p w → Small ν p c → SmallP ν p (ψ w c)

Small-up  : ∀ {ν p q X} → p ≤ᴾ q → Small ν p X → Small ν q X
SmallP-up : ∀ {ν p q x} → p ≤ᴾ q → SmallP ν p x → SmallP ν q x
Small-up l s[]       = s[]
Small-up l (s∷ a b)  = s∷ (SmallP-up l a) (Small-up l b)
SmallP-up l (sLo m q)   = sLo m (<≤ᴾ q l)
SmallP-up l (sHi m a b) = sHi m (Small-up l a) (Small-up l b)

lowSmall : ∀ {ν wp e X} → NF X → X ≤ᵀ ν → X ≤ᵀ wp → Small ν (ψ wp e) X
lowSmall n[] _ _ = s[]
lowSmall {X = ψ w c ∷ xs} (n∷ p h n) l₁ l₂ =
  s∷ (sLo (inj₁ (<-≤ (idx< w c xs) l₁)) (lv< (<-≤ (idx< w c xs) l₂)))
     (lowSmall n (≤-trans′ (inj₁ (tail< (ψ w c) xs h n)) l₁) (≤-trans′ (inj₁ (tail< (ψ w c) xs h n)) l₂))

idxSmall : ∀ {ν p w c} → NF w → SmallP ν p (ψ w c) → Small ν p w
idxSmall {p = ψ wp e} nw (sLo l r) = lowSmall nw l (sub≤ (inj₁ r))
idxSmall nw (sHi _ a _) = a

argSmall : ∀ {ν p w c} → ν <ᵀ w → SmallP ν p (ψ w c) → Small ν p c
argSmall m (sLo l _)   = ⊥-elim (≤¬> l m)
argSmall m (sHi _ _ b) = b

below  : ∀ β {ν} → cof β ≡ cΩ ν → ∀ {α p} → NF α → α <ᵀ β → Small ν p α → α <ᵀ fsT β (p ∷ [])
below0 : ∀ u c → cof u ≡ c → ∀ {ν} → cofψ0 u c ≡ cΩ ν →
         ∀ {α p} → NF α → α <ᵀ (ψ u [] ∷ []) → Small ν p α → α <ᵀ fsT0 u c (p ∷ [])
below₊ : ∀ u b c → cof b ≡ c → ∀ {ν} → cofA u c ≡ cΩ ν →
         ∀ {α p} → NF α → α <ᵀ (ψ u b ∷ []) → Small ν p α → α <ᵀ fsT₊ u b c (p ∷ [])
belowc : ∀ u b ν′ → cof b ≡ cΩ ν′ → ∀ m → cmpᵀ (sucT ν′) u ≡ m → ∀ {ν} → cofψ₊ u ν′ m ≡ cΩ ν →
         ∀ {α p} → NF α → α <ᵀ (ψ u b ∷ []) → Small ν p α → α <ᵀ fsTc u b ν′ m (p ∷ [])
below5 : ∀ u b {ν} → cof b ≡ cΩ ν → ν <ᵀ u →
         ∀ {α p} → NF α → α <ᵀ (ψ u b ∷ []) → Small ν p α → α <ᵀ (ψ u (fsT b (p ∷ [])) ∷ [])

below [] ()
below (x ∷ xs@(_ ∷ _)) e n []< s = []<
below (x ∷ xs@(_ ∷ _)) e n (hd< q) s = hd< q
below (x ∷ xs@(_ ∷ _)) e (n∷ _ _ n) (tl< q) (s∷ _ s) = tl< (below xs e n q s)
below (ψ u (y ∷ ys) ∷ []) e = below₊ u (y ∷ ys) (cof (y ∷ ys)) refl e
below (ψ (w ∷ ws) [] ∷ []) e = below0 (w ∷ ws) (cof (w ∷ ws)) refl e
below (𝟏 ∷ []) ()

below0 u c0 ue ()
below0 u cω ue ()
below0 u c1 ue refl n []< s = []<
below0 u c1 ue refl n (hd< (lv< q)) (s∷ (sLo _ r) _) = hd< r
below0 u c1 ue refl n (hd< (lv< q)) (s∷ (sHi m _ _) _) =
  ⊥-elim (≤¬> (<sucT (pred u) (subst (_ <ᵀ_) (sym (pred-suc u ue)) q)) m)
below0 u c1 ue refl n (hd< (ar< ())) s
below0 u c1 ue refl n (tl< ()) s
below0 u (cΩ ν′) ue refl n []< s = []<
below0 u (cΩ ν′) ue refl n (hd< (lv< q)) (s∷ sp _) =
  hd< (lv< (below u ue (nfp-u (nf-hd n)) q (idxSmall (nfp-u (nf-hd n)) sp)))
below0 u (cΩ ν′) ue refl n (hd< (ar< ())) s
below0 u (cΩ ν′) ue refl n (tl< ()) s

below₊ u b c0 be ()
below₊ u b c1 be ()
below₊ u b cω be ()
below₊ u b (cΩ ν′) be e = belowc u b ν′ be (cmpᵀ (sucT ν′) u) refl e

belowc u b ν′ be gt me ()
belowc u b ν′ be lt me refl = below5 u b be (<ᵀ-trans (<-sucT ν′) (lt→< (sucT ν′) u me))
belowc u b ν′ be eq me refl = below5 u b be (subst (ν′ <ᵀ_) (eq→≡ (sucT ν′) u me) (<-sucT ν′))

below5 u b be νu n []< s = []<
below5 u b be νu n (hd< (lv< q)) s = hd< (lv< q)
below5 u b be νu n (hd< (ar< q)) (s∷ sp _) =
  hd< (ar< (below b be (nfp-a (nf-hd n)) q (argSmall νu sp)))
below5 u b be νu n (tl< ()) s
```

## §3 Ω-基本列按下标严格单调

```agda
fsT-mono  : ∀ β {ν} → cof β ≡ cΩ ν → ∀ {ξ ξ′} → ξ <ᵀ ξ′ → fsT β ξ <ᵀ fsT β ξ′
fsT-mono0 : ∀ u c → cof u ≡ c → ∀ {ν} → cofψ0 u c ≡ cΩ ν → ∀ {ξ ξ′} → ξ <ᵀ ξ′ → fsT0 u c ξ <ᵀ fsT0 u c ξ′
fsT-mono₊ : ∀ u b c → cof b ≡ c → ∀ {ν} → cofA u c ≡ cΩ ν → ∀ {ξ ξ′} → ξ <ᵀ ξ′ → fsT₊ u b c ξ <ᵀ fsT₊ u b c ξ′
fsT-monoc : ∀ u b ν′ → cof b ≡ cΩ ν′ → ∀ m {ν} → cofψ₊ u ν′ m ≡ cΩ ν →
            ∀ {ξ ξ′} → ξ <ᵀ ξ′ → fsTc u b ν′ m ξ <ᵀ fsTc u b ν′ m ξ′
fsT-mono [] ()
fsT-mono (x ∷ xs@(_ ∷ _)) e q = tl< (fsT-mono xs e q)
fsT-mono (ψ u (y ∷ ys) ∷ []) e = fsT-mono₊ u (y ∷ ys) (cof (y ∷ ys)) refl e
fsT-mono (ψ (w ∷ ws) [] ∷ []) e = fsT-mono0 (w ∷ ws) (cof (w ∷ ws)) refl e
fsT-mono (𝟏 ∷ []) ()
fsT-mono0 u c0 ue ()
fsT-mono0 u cω ue ()
fsT-mono0 u c1 ue e q = q
fsT-mono0 u (cΩ ν′) ue e q = hd< (lv< (fsT-mono u ue q))
fsT-mono₊ u b c0 be ()
fsT-mono₊ u b c1 be ()
fsT-mono₊ u b cω be ()
fsT-mono₊ u b (cΩ ν′) be e = fsT-monoc u b ν′ be (cmpᵀ (sucT ν′) u) e
fsT-monoc u b ν′ be gt ()
fsT-monoc u b ν′ be lt e q = hd< (ar< (fsT-mono b be q))
fsT-monoc u b ν′ be eq e q = hd< (ar< (fsT-mono b be q))
```

## §4 规则 6: γ-链压住参数的 ν-成分

`pγ k` 是 $\gamma_k$ 的唯一主项. `R`: 若 $G_\nu(c)$ 的元素都 $<b$, 则有 $N$ 使 `Small ν (pγ N) c`. 下标恰为 ν 的成分 $\psi_\nu(d)$ 有 $d\in G_\nu(c)$, 故 $d<b$; 对 $d$ 递归, 再用 `below` 得 $d<b[\gamma_M]$, 即 $\psi_\nu(d)<\gamma_{M+1}$.

```agda
module Chain (b : T) {ν : T} (be : cof b ≡ cΩ ν) where

  pγ : ℕ → PT
  pγ zero    = ψ ν []
  pγ (suc k) = ψ ν (fsT b (γT b ν k))

  γ≡ : ∀ k → γT b ν k ≡ pγ k ∷ []
  γ≡ zero    = refl
  γ≡ (suc k) = refl

  γ-step : ∀ k → γT b ν k <ᵀ γT b ν (suc k)
  γ-step zero    = hd< (ar< (below b be n[] (cofΩ-ne b be) s[]))
  γ-step (suc k) = hd< (ar< (fsT-mono b be (γ-step k)))

  pγ-step : ∀ k → pγ k <ᴾ pγ (suc k)
  pγ-step zero    = ar< (below b be n[] (cofΩ-ne b be) s[])
  pγ-step (suc k) = ar< (fsT-mono b be (γ-step k))

  pγ-mono′ : ∀ {m n} → m ≤′ n → pγ m ≤ᴾ pγ n
  pγ-mono′ ≤′-refl     = inj₂ refl
  pγ-mono′ (≤′-step l) = ≤ᴾ-trans (pγ-mono′ l) (inj₁ (pγ-step _))

  pγ-mono : ∀ {m n} → m ≤ n → pγ m ≤ᴾ pγ n
  pγ-mono l = pγ-mono′ (≤⇒≤′ l)

  ∃S  : T → Set
  ∃S c = Σ ℕ (λ N → Small ν (pγ N) c)
  ∃SP : PT → Set
  ∃SP x = Σ ℕ (λ N → SmallP ν (pγ N) x)

  join : ∀ {x xs} → ∃SP x → ∃S xs → ∃S (x ∷ xs)
  join (M , a) (N , s) = M ⊔ N , s∷ (SmallP-up (pγ-mono (m≤m⊔n M N)) a) (Small-up (pγ-mono (m≤n⊔m M N)) s)

  joinHi : ∀ {w d} → ν <ᵀ w → ∃S w → ∃S d → ∃SP (ψ w d)
  joinHi h (M , a) (N , s) = M ⊔ N , sHi h (Small-up (pγ-mono (m≤m⊔n M N)) a) (Small-up (pγ-mono (m≤n⊔m M N)) s)

  R   : ∀ c → NF c → (∀ {e} → InG ν e c → e <ᵀ b) → ∃S c
  RP  : ∀ x → NFP x → (∀ {e} → InGP ν e x → e <ᵀ b) → ∃SP x
  RP′ : ∀ w d → NF w → NF d → GB w d d → (∀ {e} → InGP ν e (ψ w d) → e <ᵀ b) →
        (w <ᵀ ν) ⊎ (w ≡ ν) ⊎ (ν <ᵀ w) → ∃SP (ψ w d)
  fin : ∀ {w d} → w ≡ ν → NF d → d <ᵀ b → ∃S d → ∃SP (ψ w d)

  R [] _ _ = 0 , s[]
  R (x ∷ xs) n g = join (RP x (nf-hd n) (λ i → g (gp i))) (R xs (nf-tl n) (λ i → g (gtl i)))
  RP (ψ w d) (nψ nw nd gd) g = RP′ w d nw nd gd g (tri w ν)
  RP′ w d nw nd gd g (inj₁ l) = 0 , sLo (inj₁ l) (lv< l)
  RP′ w d nw nd gd g (inj₂ (inj₁ w≡ν)) =
    fin w≡ν nd db (R d nd (λ i → <ᵀ-trans (gd (G-mono (inj₂ w≡ν) i)) db))
    where db = g (gh (inj₂ (sym w≡ν)))
  RP′ w d nw nd gd g (inj₂ (inj₂ h)) =
    joinHi h (R w nw (λ i → g (gw (inj₁ h) i))) (R d nd (λ i → g (gc (inj₁ h) i)))
  fin {w} {d} w≡ν nd db (M , sm) =
    suc M , sLo (inj₂ w≡ν)
      (subst (λ v → ψ w d <ᴾ ψ v (fsT b (γT b ν M))) w≡ν
        (ar< (subst (λ g → d <ᵀ fsT b g) (sym (γ≡ M)) (below b be nd db sm))))

  rule6 : ∀ {u c} → u ≤ᵀ ν → NFP (ψ u c) → c <ᵀ b → Σ ℕ (λ N → c <ᵀ fsT b (γT b ν N))
  rule6 {u} {c} l (nψ nu nc gB) cb = go (R c nc (λ i → <ᵀ-trans (gB (G-mono l i)) cb)) where
    go : ∃S c → Σ ℕ (λ N → c <ᵀ fsT b (γT b ν N))
    go (N , sm) = N , subst (λ g → c <ᵀ fsT b g) (sym (γ≡ N)) (below b be nc cb sm)
```

## §5 Bach

```agda
bach-ω  : ∀ t → cof t ≡ cω → ∀ {s} → NF s → s <ᵀ t → Σ ℕ (λ n → s <ᵀ fsn t n)
bach-ω0 : ∀ u c → cof u ≡ c → cofψ0 u c ≡ cω → ∀ {s} → NF s → s <ᵀ (ψ u [] ∷ []) →
          Σ ℕ (λ n → s <ᵀ fsn0 u c n)
bach-ω₊ : ∀ u y ys c → cof (y ∷ ys) ≡ c → cofA u c ≡ cω → ∀ {s} → NF s → s <ᵀ (ψ u (y ∷ ys) ∷ []) →
          Σ ℕ (λ n → s <ᵀ fsn₊ u (y ∷ ys) c n)
bach-ωc : ∀ u b ν → cof b ≡ cΩ ν → ∀ m → cmpᵀ (sucT ν) u ≡ m → cofψ₊ u ν m ≡ cω →
          ∀ {s} → NF s → s <ᵀ (ψ u b ∷ []) → Σ ℕ (λ n → s <ᵀ fsnc u b ν m n)

bach-ω [] ()
bach-ω (x ∷ xs@(_ ∷ _)) e n []< = 0 , []<
bach-ω (x ∷ xs@(_ ∷ _)) e n (hd< q) = 0 , hd< q
bach-ω (x ∷ xs@(_ ∷ _)) e n (tl< q) with bach-ω xs e (nf-tl n) q
... | k , r = k , tl< r
bach-ω (ψ u (y ∷ ys) ∷ []) e = bach-ω₊ u y ys (cof (y ∷ ys)) refl e
bach-ω (ψ (w ∷ ws) [] ∷ []) e = bach-ω0 (w ∷ ws) (cof (w ∷ ws)) refl e
bach-ω (𝟏 ∷ []) ()

bach-ω0 u c0 ue ()
bach-ω0 u c1 ue ()
bach-ω0 u (cΩ ν) ue ()
bach-ω0 u cω ue _ n []< = 0 , []<
bach-ω0 u cω ue _ n (hd< (lv< q)) with bach-ω u ue (nfp-u (nf-hd n)) q
... | k , r = k , hd< (lv< r)
bach-ω0 u cω ue _ n (hd< (ar< ()))
bach-ω0 u cω ue _ n (tl< ())

bach-ω₊ u y ys c0 be _ = ⊥-elim (cof-nz y ys be)
bach-ω₊ u y ys c1 be _ {s} n q = suc (length s) , rep< n (hdle q)
  where
  b = y ∷ ys
  hdle : s <ᵀ (ψ u b ∷ []) → HdLe (ψ u (pred b)) s
  hdle []<            = tt
  hdle (hd< (lv< r))  = inj₁ (lv< r)
  hdle (hd< (ar< r)) with <sucT (pred b) (subst (_ <ᵀ_) (sym (pred-suc b be)) r)
  ... | inj₁ r′ = inj₁ (ar< r′)
  ... | inj₂ e  = inj₂ (cong (ψ u) e)
  hdle (tl< ())
bach-ω₊ u y ys cω be _ n []< = 0 , []<
bach-ω₊ u y ys cω be _ n (hd< (lv< q)) = 0 , hd< (lv< q)
bach-ω₊ u y ys cω be _ n (hd< (ar< q)) with bach-ω (y ∷ ys) be (nfp-a (nf-hd n)) q
... | k , r = k , hd< (ar< r)
bach-ω₊ u y ys cω be _ n (tl< ())
bach-ω₊ u y ys (cΩ ν) be e = bach-ωc u (y ∷ ys) ν be (cmpᵀ (sucT ν) u) refl e

bach-ωc u b ν be lt me ()
bach-ωc u b ν be eq me ()
bach-ωc u b ν be gt me _ n []< = 0 , []<
bach-ωc u b ν be gt me _ n (hd< (lv< q)) = 0 , hd< (lv< q)
bach-ωc u b ν be gt me _ n (hd< (ar< q)) with Chain.rule6 b be (gt→≤ ν u me) (nf-hd n) q
... | k , r = k , hd< (ar< r)
bach-ωc u b ν be gt me _ n (tl< ())
```

余尾 $\Omega_{\kappa+1}$: 见证 η 是标准形且 $<\Omega_{\kappa+1}$. 正则叶 $\Omega_{\kappa+1}[\eta]=\eta$ 取 $\eta=s+1$.

```agda
ΩW : T → T → (T → T) → Set
ΩW κ s F = Σ T (λ η → NF η × η <ᵀ Ωs κ × s <ᵀ F η)

bach-Ω  : ∀ t {κ} → cof t ≡ cΩ κ → ∀ {s} → NF s → s <ᵀ t → ΩW κ s (fsT t)
bach-Ω0 : ∀ u c → cof u ≡ c → ∀ {κ} → cofψ0 u c ≡ cΩ κ → ∀ {s} → NF s → s <ᵀ (ψ u [] ∷ []) →
          ΩW κ s (fsT0 u c)
bach-Ω₊ : ∀ u b c → cof b ≡ c → ∀ {κ} → cofA u c ≡ cΩ κ → ∀ {s} → NF s → s <ᵀ (ψ u b ∷ []) →
          ΩW κ s (fsT₊ u b c)
bach-Ωc : ∀ u b ν → cof b ≡ cΩ ν → ∀ m {κ} → cofψ₊ u ν m ≡ cΩ κ → ∀ {s} → NF s → s <ᵀ (ψ u b ∷ []) →
          ΩW κ s (fsTc u b ν m)

bach-Ω [] ()
bach-Ω (x ∷ xs@(_ ∷ _)) e n []< = [] , n[] , []< , []<
bach-Ω (x ∷ xs@(_ ∷ _)) e n (hd< q) = [] , n[] , []< , hd< q
bach-Ω (x ∷ xs@(_ ∷ _)) e n (tl< q) with bach-Ω xs e (nf-tl n) q
... | η , nη , ηl , r = η , nη , ηl , tl< r
bach-Ω (ψ u (y ∷ ys) ∷ []) e = bach-Ω₊ u (y ∷ ys) (cof (y ∷ ys)) refl e
bach-Ω (ψ (w ∷ ws) [] ∷ []) e = bach-Ω0 (w ∷ ws) (cof (w ∷ ws)) refl e
bach-Ω (𝟏 ∷ []) ()

bach-Ω0 u c0 ue ()
bach-Ω0 u cω ue ()
bach-Ω0 u c1 ue refl {s} n q =
  sucT s , nf-sucT n , suc<Ωs (pred u) (subst (λ v → s <ᵀ (ψ v [] ∷ [])) (sym (pred-suc u ue)) q) , <-sucT s
bach-Ω0 u (cΩ ν) ue refl n []< = [] , n[] , []< , []<
bach-Ω0 u (cΩ ν) ue refl n (hd< (lv< q)) with bach-Ω u ue (nfp-u (nf-hd n)) q
... | η , nη , ηl , r = η , nη , ηl , hd< (lv< r)
bach-Ω0 u (cΩ ν) ue refl n (hd< (ar< ()))
bach-Ω0 u (cΩ ν) ue refl n (tl< ())

bach-Ω₊ u b c0 be ()
bach-Ω₊ u b c1 be ()
bach-Ω₊ u b cω be ()
bach-Ω₊ u b (cΩ ν) be e = bach-Ωc u b ν be (cmpᵀ (sucT ν) u) e

bach-Ωc u b ν be gt ()
bach-Ωc u b ν be lt refl = bach-Ω5 where
  bach-Ω5 : ∀ {s} → NF s → s <ᵀ (ψ u b ∷ []) → ΩW ν s (λ η → ψ u (fsT b η) ∷ [])
  bach-Ω5 n []< = [] , n[] , []< , []<
  bach-Ω5 n (hd< (lv< q)) = [] , n[] , []< , hd< (lv< q)
  bach-Ω5 n (hd< (ar< q)) with bach-Ω b be (nfp-a (nf-hd n)) q
  ... | η , nη , ηl , r = η , nη , ηl , hd< (ar< r)
  bach-Ω5 n (tl< ())
bach-Ωc u b ν be eq refl = bach-Ω5 where
  bach-Ω5 : ∀ {s} → NF s → s <ᵀ (ψ u b ∷ []) → ΩW ν s (λ η → ψ u (fsT b η) ∷ [])
  bach-Ω5 n []< = [] , n[] , []< , []<
  bach-Ω5 n (hd< (lv< q)) = [] , n[] , []< , hd< (lv< q)
  bach-Ω5 n (hd< (ar< q)) with bach-Ω b be (nfp-a (nf-hd n)) q
  ... | η , nη , ηl , r = η , nη , ηl , hd< (ar< r)
  bach-Ω5 n (tl< ())

bach-suc : ∀ t → cof t ≡ c1 → ∀ {s} → s <ᵀ t → s ≤ᵀ pred t
bach-suc t e q = <sucT (pred t) (subst (_ <ᵀ_) (sym (pred-suc t e)) q)

bach-0 : ∀ t → cof t ≡ c0 → ∀ {s} → s <ᵀ t → ⊥
bach-0 [] e ()
bach-0 (y ∷ ys) e q = cof-nz y ys e
```

简报的陈述 (取 ≤ 的形式; 上面各条是严格的, 且不要求 $t$ 是标准形):

```agda
bach : ∀ {s t} → NF s → s <ᵀ t →
    (cof t ≡ c1 → s ≤ᵀ pred t)
  × (cof t ≡ cω → Σ ℕ (λ n → s ≤ᵀ fsn t n))
  × (∀ {κ} → cof t ≡ cΩ κ → Σ T (λ η → NF η × η <ᵀ Ωs κ × s ≤ᵀ fsT t η))
bach {s} {t} n q = (λ e → bach-suc t e q) , ω , Ω
  where
  ω : cof t ≡ cω → Σ ℕ (λ k → s ≤ᵀ fsn t k)
  ω e with bach-ω t e n q
  ... | k , r = k , inj₁ r
  Ω : ∀ {κ} → cof t ≡ cΩ κ → Σ T (λ η → NF η × η <ᵀ Ωs κ × s ≤ᵀ fsT t η)
  Ω e with bach-Ω t e n q
  ... | η , nη , ηl , r = η , nη , ηl , inj₁ r
```
