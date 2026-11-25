# 记号一侧带截断 (吸收) 的加法 `α ⊞ β`

> 验收文件 (读记号, 只在记号一侧, 不涉及树)。编译定理, 无前提: `⊞` 对右边严格单调 (`⊞-<ʳ`, 对一切项, 不要 `NF`), 保持标准形 (`⊞-NF`), 共尾度与 `pred` 随右边 (`⊞-cof`, `⊞-pred`), 基本列的精确式 (`⊞-fsn`) 与上界 (`fsn-⊞≤`); 部分和 `Σ⊞` 不低于末项且主项下封闭 (`Σ⊞-ge`, `Σ⊞-<prin`)。
> 编译否定: 与 `fsn` 的字面交换不成立 (`no-comm`, 反例 ω ⊞ ω² 在 0 处); 成立的是上面的不等式。首项不被吸收时 `⊞` 就是拼接 (`⊞-noabs`), 后项首项更高时整段吸收 (`⊞-abs`)。
> 树侧的用法见 [YiTAChain](YiTAChain.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTAAdd where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import OCF.Align.EboLeanDef
open import OCF.Align.EboLeanBase
  using (_≤ᵀ_; _≤ᴾ_; NF; NFP; n[]; n∷; nψ; nf-hd; nf-tl; nf-le; HdLe; GB[]; InG; gp; gtl; gh; gw; gc;
         lt→<ᴾ; eq→≡ᴾ; gt→<ᴾ; <ᴾ-trans; <ᴾ-irrefl; ≤ᴾ-trans; ≤-trans′; tail<; cofA≢c1)
open import OCF.Align.EboLean3Base using (one≤ᴾ)
```

## 定义

`tr y α`: α 中首个低于 y 的项之前的部分。标准形上它就是 α 里不低于 y 的项, `α ⊞ β` 是序数加法。

```agda
tr  : PT → T → T
trc : PT → PT → T → Cmp → T
tr y []       = []
tr y (x ∷ xs) = trc y x xs (cmpᴾ x y)
trc y x xs lt = []
trc y x xs eq = x ∷ tr y xs
trc y x xs gt = x ∷ tr y xs

infixl 6 _⊞_
_⊞_ : T → T → T
α ⊞ []       = α
α ⊞ (y ∷ ys) = tr y α ++ (y ∷ ys)

HdLt : T → PT → Set
HdLt []      y = ⊤
HdLt (x ∷ _) y = x <ᴾ y
```

## 截断的基本事实

```agda
decᴾ : ∀ x y → (x <ᴾ y) ⊎ (y ≤ᴾ x)
decᴾ x y with cmpᴾ x y in e
... | lt = inj₁ (lt→<ᴾ x y e)
... | eq = inj₂ (inj₂ (sym (eq→≡ᴾ x y e)))
... | gt = inj₂ (inj₁ (gt→<ᴾ x y e))

private
  nlt : ∀ x y → y ≤ᴾ x → cmpᴾ x y ≡ lt → ⊥
  nlt x y (inj₁ q) e = <ᴾ-irrefl (<ᴾ-trans (lt→<ᴾ x y e) q)
  nlt x y (inj₂ refl) e = <ᴾ-irrefl (lt→<ᴾ x y e)

  keep : ∀ {x y} xs m → (m ≡ lt → ⊥) → trc y x xs m ≡ x ∷ tr y xs
  keep xs lt n = ⊥-elim (n refl)
  keep xs eq n = refl
  keep xs gt n = refl

  cut : ∀ {x y} xs m → m ≡ lt → trc y x xs m ≡ []
  cut xs .lt refl = refl

  <ᴾ→lt′ : ∀ x y → x <ᴾ y → cmpᴾ x y ≡ lt
  <ᴾ→lt′ x y p with cmpᴾ x y in e
  ... | lt = refl
  ... | eq with eq→≡ᴾ x y e
  ...   | refl = ⊥-elim (<ᴾ-irrefl p)
  <ᴾ→lt′ x y p | gt = ⊥-elim (<ᴾ-irrefl (<ᴾ-trans p (gt→<ᴾ x y e)))

tr-keep : ∀ {x y} xs → y ≤ᴾ x → tr y (x ∷ xs) ≡ x ∷ tr y xs
tr-keep {x} {y} xs q = keep xs (cmpᴾ x y) (nlt x y q)

tr-cut : ∀ {x y} xs → x <ᴾ y → tr y (x ∷ xs) ≡ []
tr-cut {x} {y} xs p = cut xs (cmpᴾ x y) (<ᴾ→lt′ x y p)

hdlt-tr : ∀ {x y z} xs → x <ᴾ y → HdLt (tr z (x ∷ xs)) y
hdlt-tr {x} {y} {z} xs p with decᴾ x z
... | inj₁ r = subst (λ s → HdLt s y) (sym (tr-cut xs r)) tt
... | inj₂ q = subst (λ s → HdLt s y) (sym (tr-keep xs q)) p

tr-dr : ∀ y α → Σ T λ d → (tr y α ++ d ≡ α) × HdLt d y
tr-dr y [] = [] , refl , tt
tr-dr y (x ∷ xs) with decᴾ x y
... | inj₁ p = x ∷ xs , cong (_++ (x ∷ xs)) (tr-cut xs p) , p
... | inj₂ q with tr-dr y xs
...   | d , e , h = d , trans (cong (_++ d) (tr-keep xs q)) (cong (x ∷_) e) , h

tr-split : ∀ {z y} α → z ≤ᴾ y → Σ T λ r → (tr y α ++ r ≡ tr z α) × HdLt r y
tr-split [] _ = [] , refl , tt
tr-split {z} {y} (x ∷ xs) zy with decᴾ x y
... | inj₁ p = tr z (x ∷ xs) , cong (_++ tr z (x ∷ xs)) (tr-cut xs p) , hdlt-tr xs p
... | inj₂ q with tr-split xs zy
...   | r , e , h = r
  , trans (cong (_++ r) (tr-keep xs q)) (trans (cong (x ∷_) e) (sym (tr-keep xs (≤ᴾ-trans zy q)))) , h

tr-𝟏 : ∀ α → tr 𝟏 α ≡ α
tr-𝟏 [] = refl
tr-𝟏 (x ∷ xs) = trans (tr-keep xs (one≤ᴾ x)) (cong (x ∷_) (tr-𝟏 xs))
```

## 拼接

```agda
++-<ʳ : ∀ p {s t} → s <ᵀ t → p ++ s <ᵀ p ++ t
++-<ʳ [] q = q
++-<ʳ (x ∷ p) q = tl< (++-<ʳ p q)

++-≤ʳ : ∀ p {s t} → s ≤ᵀ t → p ++ s ≤ᵀ p ++ t
++-≤ʳ p (inj₁ q) = inj₁ (++-<ʳ p q)
++-≤ʳ p (inj₂ refl) = inj₂ refl

++-ge : ∀ p {t} → NF (p ++ t) → t ≤ᵀ p ++ t
++-ge [] _ = inj₂ refl
++-ge (x ∷ p) {t} nf = ≤-trans′ (++-ge p (nf-tl nf)) (inj₁ (tail< x (p ++ t) (nf-le nf) (nf-tl nf)))

nf-++ʳ : ∀ p {t} → NF (p ++ t) → NF t
nf-++ʳ [] nf = nf
nf-++ʳ (x ∷ p) nf = nf-++ʳ p (nf-tl nf)

++-cof : ∀ p y ys → cof (p ++ (y ∷ ys)) ≡ cof (y ∷ ys)
++-cof [] y ys = refl
++-cof (x ∷ []) y ys = refl
++-cof (x ∷ x′ ∷ p) y ys = ++-cof (x′ ∷ p) y ys

++-fsn : ∀ p y ys n → fsn (p ++ (y ∷ ys)) n ≡ p ++ fsn (y ∷ ys) n
++-fsn [] y ys n = refl
++-fsn (x ∷ []) y ys n = refl
++-fsn (x ∷ x′ ∷ p) y ys n = cong (x ∷_) (++-fsn (x′ ∷ p) y ys n)

++-pred : ∀ p y ys → pred (p ++ (y ∷ ys)) ≡ p ++ pred (y ∷ ys)
++-pred [] y ys = refl
++-pred (x ∷ []) y ys = refl
++-pred (x ∷ x′ ∷ p) y ys = cong (x ∷_) (++-pred (x′ ∷ p) y ys)
```

## 单调, 标准形, 共尾度, `pred`, 基本列

```agda
private
  hdlt< : ∀ {d y ys} → HdLt d y → d <ᵀ y ∷ ys
  hdlt< {d = []} _ = []<
  hdlt< {d = _ ∷ _} h = hd< h

  hdlt++ : ∀ r {z zs y ys} → HdLt r y → z <ᴾ y → r ++ (z ∷ zs) <ᵀ y ∷ ys
  hdlt++ [] _ p = hd< p
  hdlt++ (_ ∷ _) h _ = hd< h

⊞-<ʳ : ∀ α {μ β} → μ <ᵀ β → α ⊞ μ <ᵀ α ⊞ β
⊞-<ʳ α {μ = []} {y ∷ ys} []< with tr-dr y α
... | d , e , h = subst (_<ᵀ tr y α ++ (y ∷ ys)) e (++-<ʳ (tr y α) (hdlt< h))
⊞-<ʳ α {μ = z ∷ zs} {y ∷ ys} (hd< p) with tr-split α (inj₁ p)
... | r , e , h = subst (_<ᵀ tr y α ++ (y ∷ ys))
  (trans (sym (++-assoc (tr y α) r (z ∷ zs))) (cong (_++ (z ∷ zs)) e))
  (++-<ʳ (tr y α) (hdlt++ r h p))
⊞-<ʳ α {μ = y ∷ zs} {y ∷ ys} (tl< q) = ++-<ʳ (tr y α) (tl< q)

⊞-≤ʳ : ∀ α {μ β} → μ ≤ᵀ β → α ⊞ μ ≤ᵀ α ⊞ β
⊞-≤ʳ α (inj₁ p) = inj₁ (⊞-<ʳ α p)
⊞-≤ʳ α (inj₂ refl) = inj₂ refl

private
  hdle-tr : ∀ {x y ys} xs → HdLe x xs → y ≤ᴾ x → HdLe x (tr y xs ++ (y ∷ ys))
  hdle-tr [] h q = q
  hdle-tr {x} {y} {ys} (x′ ∷ xs) h q with decᴾ x′ y
  ... | inj₁ p = subst (λ s → HdLe x (s ++ (y ∷ ys))) (sym (tr-cut xs p)) q
  ... | inj₂ q′ = subst (λ s → HdLe x (s ++ (y ∷ ys))) (sym (tr-keep xs q′)) h

  nf-tr : ∀ {y ys} α → NF α → NF (y ∷ ys) → NF (tr y α ++ (y ∷ ys))
  nf-tr [] _ nb = nb
  nf-tr {y} {ys} (x ∷ xs) na nb with decᴾ x y
  ... | inj₁ p = subst (λ s → NF (s ++ (y ∷ ys))) (sym (tr-cut xs p)) nb
  ... | inj₂ q = subst (λ s → NF (s ++ (y ∷ ys))) (sym (tr-keep xs q))
        (n∷ (nf-hd na) (hdle-tr xs (nf-le na) q) (nf-tr xs (nf-tl na) nb))

⊞-NF : ∀ {α β} → NF α → NF β → NF (α ⊞ β)
⊞-NF {β = []} na _ = na
⊞-NF {α} {β = y ∷ ys} na nb = nf-tr α na nb

⊞-cof : ∀ α y ys → cof (α ⊞ (y ∷ ys)) ≡ cof (y ∷ ys)
⊞-cof α y ys = ++-cof (tr y α) y ys

⊞-fsn : ∀ α y ys n → fsn (α ⊞ (y ∷ ys)) n ≡ tr y α ++ fsn (y ∷ ys) n
⊞-fsn α y ys n = ++-fsn (tr y α) y ys n

private
  ψ0≢c1 : ∀ u c → cofψ0 u c ≡ c1 → ⊥
  ψ0≢c1 u c0 ()
  ψ0≢c1 u c1 ()
  ψ0≢c1 u cω ()
  ψ0≢c1 u (cΩ μ) ()

  c1-𝟏 : ∀ y → cofP y ≡ c1 → y ≡ 𝟏
  c1-𝟏 (ψ u (b ∷ bs)) e = ⊥-elim (cofA≢c1 u (cof (b ∷ bs)) e)
  c1-𝟏 (ψ (w ∷ ws) []) e = ⊥-elim (ψ0≢c1 (w ∷ ws) (cof (w ∷ ws)) e)
  c1-𝟏 (ψ [] []) e = refl

⊞-pred : ∀ α β → cof β ≡ c1 → pred (α ⊞ β) ≡ α ⊞ pred β
⊞-pred α [] ()
⊞-pred α (y ∷ []) e with c1-𝟏 y e
... | refl = trans (++-pred (tr 𝟏 α) 𝟏 []) (trans (++-identityʳ (tr 𝟏 α)) (tr-𝟏 α))
⊞-pred α (y ∷ z ∷ zs) e = ++-pred (tr y α) y (z ∷ zs)

pre≤ : ∀ α {y ys γ} → NF α → NF γ → γ ≤ᵀ (y ∷ ys) → tr y α ++ γ ≤ᵀ α ⊞ γ
pre≤ α {y} {γ = []} na nγ _ with tr-dr y α
... | [] , e , h = subst (tr y α ++ [] ≤ᵀ_) e (inj₂ refl)
... | d ∷ ds , e , h = subst (tr y α ++ [] ≤ᵀ_) e (inj₁ (++-<ʳ (tr y α) []<))
pre≤ α {y} {ys} {z ∷ zs} na nγ le with tr-split α (zy le)
  where
  zy : (z ∷ zs) ≤ᵀ (y ∷ ys) → z ≤ᴾ y
  zy (inj₁ (hd< p)) = inj₁ p
  zy (inj₁ (tl< _)) = inj₂ refl
  zy (inj₂ refl) = inj₂ refl
... | r , e , h = subst (tr y α ++ (z ∷ zs) ≤ᵀ_) (sym E1) (++-≤ʳ (tr y α) (++-ge r nfR))
  where
  E1 : tr z α ++ (z ∷ zs) ≡ tr y α ++ (r ++ (z ∷ zs))
  E1 = trans (cong (_++ (z ∷ zs)) (sym e)) (++-assoc (tr y α) r (z ∷ zs))
  nfR : NF (r ++ (z ∷ zs))
  nfR = nf-++ʳ (tr y α) (subst NF E1 (⊞-NF {α} {z ∷ zs} na nγ))

fsn-⊞≤ : ∀ α {y ys} n → NF α → NF (fsn (y ∷ ys) n) → fsn (y ∷ ys) n ≤ᵀ (y ∷ ys)
  → fsn (α ⊞ (y ∷ ys)) n ≤ᵀ α ⊞ fsn (y ∷ ys) n
fsn-⊞≤ α {y} {ys} n na nf le = subst (_≤ᵀ α ⊞ fsn (y ∷ ys) n) (sym (⊞-fsn α y ys n)) (pre≤ α na nf le)
```

## 吸收与部分和

```agda
⊞-noabs : ∀ {p s} → HdLe p s → (p ∷ []) ⊞ s ≡ p ∷ s
⊞-noabs {s = []} _ = refl
⊞-noabs {p} {y ∷ ys} h = cong (_++ (y ∷ ys)) (tr-keep [] h)

⊞-abs : ∀ {α y ys} → HdLt α y → α ⊞ (y ∷ ys) ≡ y ∷ ys
⊞-abs {α = []} _ = refl
⊞-abs {α = a ∷ as} {y} {ys} p = cong (_++ (y ∷ ys)) (tr-cut as p)

⊞-ge : ∀ α {β} → NF α → NF β → β ≤ᵀ α ⊞ β
⊞-ge [] {β = []} _ _ = inj₂ refl
⊞-ge (_ ∷ _) {β = []} _ _ = inj₁ []<
⊞-ge α {β = y ∷ ys} na nb = ++-ge (tr y α) (⊞-NF {α} {y ∷ ys} na nb)

⊞-<prin : ∀ {x} α β → α <ᵀ (x ∷ []) → β <ᵀ (x ∷ []) → α ⊞ β <ᵀ (x ∷ [])
⊞-<prin α [] a b = a
⊞-<prin [] (y ∷ ys) a b = b
⊞-<prin {x} (a ∷ as) (y ∷ ys) (hd< p) b with decᴾ a y
... | inj₁ q = subst (_<ᵀ x ∷ []) (sym (cong (_++ (y ∷ ys)) (tr-cut as q))) b
... | inj₂ q = subst (_<ᵀ x ∷ []) (sym (cong (_++ (y ∷ ys)) (tr-keep as q))) (hd< p)
⊞-<prin (a ∷ as) (y ∷ ys) (tl< ()) b

Σ⊞ : (ℕ → T) → ℕ → T
Σ⊞ γ zero    = γ zero
Σ⊞ γ (suc n) = Σ⊞ γ n ⊞ γ (suc n)

Σ⊞-NF : ∀ {γ} → (∀ n → NF (γ n)) → ∀ n → NF (Σ⊞ γ n)
Σ⊞-NF nf zero = nf zero
Σ⊞-NF {γ} nf (suc n) = ⊞-NF {Σ⊞ γ n} {γ (suc n)} (Σ⊞-NF nf n) (nf (suc n))

Σ⊞-ge : ∀ {γ} → (∀ n → NF (γ n)) → ∀ n → γ n ≤ᵀ Σ⊞ γ n
Σ⊞-ge nf zero = inj₂ refl
Σ⊞-ge {γ} nf (suc n) = ⊞-ge (Σ⊞ γ n) (Σ⊞-NF nf n) (nf (suc n))

Σ⊞-<prin : ∀ {γ x} → (∀ n → γ n <ᵀ (x ∷ [])) → ∀ n → Σ⊞ γ n <ᵀ (x ∷ [])
Σ⊞-<prin h zero = h zero
Σ⊞-<prin {γ} h (suc n) = ⊞-<prin (Σ⊞ γ n) (γ (suc n)) (Σ⊞-<prin h n) (h (suc n))
```

## 与 `fsn` 不字面交换

ω ⊞ ω² = ω², 它在 0 处的基本列项是 0; 而 ω ⊞ (ω²[0]) = ω ⊞ 0 = ω。

```agda
ωh : PT
ωh = ψ [] (𝟏 ∷ [])

ω′ ω²′ : T
ω′  = ωh ∷ []
ω²′ = ψ [] (𝟏 ∷ 𝟏 ∷ []) ∷ []

nf-1′ : NF (𝟏 ∷ [])
nf-1′ = n∷ (nψ n[] n[] GB[]) tt n[]

nf-ω′ : NF ω′
nf-ω′ = n∷ (nψ n[] nf-1′ g) tt n[]
  where
  g : ∀ {z} → InG [] z (𝟏 ∷ []) → z <ᵀ (𝟏 ∷ [])
  g (gp (gh _)) = []<
  g (gp (gw _ ()))
  g (gp (gc _ ()))
  g (gtl ())

nf-ω²′ : NF ω²′
nf-ω²′ = n∷ (nψ n[] (n∷ (nψ n[] n[] GB[]) (inj₂ refl) nf-1′) g) tt n[]
  where
  g : ∀ {z} → InG [] z (𝟏 ∷ 𝟏 ∷ []) → z <ᵀ (𝟏 ∷ 𝟏 ∷ [])
  g (gp (gh _)) = []<
  g (gp (gw _ ()))
  g (gp (gc _ ()))
  g (gtl (gp (gh _))) = []<
  g (gtl (gp (gw _ ())))
  g (gtl (gp (gc _ ())))
  g (gtl (gtl ()))

no-comm : (∀ {α β} → NF α → NF β → cof β ≡ cω → ∀ n → fsn (α ⊞ β) n ≡ α ⊞ fsn β n) → ⊥
no-comm f with f nf-ω′ nf-ω²′ refl 0
... | ()
```
