# 序数高度: 严格的 `Ordᴵ` 有精确的码

> **判决: HOLDS (编译过, 无条件).** 结论写在 [LadderOrd](LadderOrd.lagda.md). `Str η`: $\eta$ 里每个极限都严格递增 (`f n ≺ᴵ f (suc n)`). `code h : Code`, 且 `val (code h)` 与 $\eta$ 互相 `≼` (`code-val`). 所以带证书 `Str` 的 `Ordᴵ` 全部以原值作高度, 不只是 $\omega^2$ 这几个例子. 证书不读记号. 无证书的 `Ordᴵ` 用 `⌈_⌉` ([LadderOrdCode](LadderOrdCode.lagda.md)), 只保证不低; 想做到精确必须判定极限是否退化, 那推出 LPO (`viewE→LPO`, [LadderOrdNeg](LadderOrdNeg.lagda.md)).
>
> 做法: `cl g` 的值是 $\sum_j(g_j+1)$. $\lim f$ 取 $g_0$ 为 $f_0$ 的码, $g_{i+1}$ 为开区间 $(f_i,f_{i+1})$ 的码 (`above`). 开区间由字面路径算出.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderOrdStr where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import OCF.Free.Level using (Ordᴵ; zero; suc; lim; _<ᴵ_; _≅ᴵ_; _≺ᴵ_; via; _⊑ᴵ_; z≅; s≅; l≅; ≅ᴵ-sym)
open import OCF.Align.LadderOrdPos
open import OCF.Align.LadderOrdCode

data Str : Ordᴵ → Set where
  sz : Str zero
  ss : ∀ {a} → Str a → Str (suc a)
  sl : ∀ {f s} → (∀ n → Str (f n)) → (∀ n → f n ≺ᴵ f (suc n)) → Str (lim f s)

≅→≼ : ∀ {a b} → a ≅ᴵ b → a ≼ b
≅→≼ z≅ = z≼
≅→≼ (s≅ e) = s≼ (≅→≼ e)
≅→≼ (l≅ h) = l≼ (λ n → l≼ʳ n (≅→≼ (h n)))

<→s≼ : ∀ {a t} → a <ᴵ t → suc a ≼ t
<→s≼ zero = ≼-refl _
<→s≼ (suc q) = s≼ʳ (<→s≼ q)
<→s≼ (lim n q) = l≼ʳ n (<→s≼ q)

≺→s≼ : ∀ {a t} → a ≺ᴵ t → suc a ≼ t
≺→s≼ (via e q) = ≼-trans (s≼ (≅→≼ e)) (<→s≼ q)

≺→≼ : ∀ {a t} → a ≺ᴵ t → a ≼ t
≺→≼ x = ≼-trans (s≼ʳ (≼-refl _)) (≺→s≼ x)

-- 底单调
plus-mono : ∀ c {b b′} → b ≼ b′ → plus b c ≼ plus b′ c
Sb-mono : ∀ g j {b b′} → b ≼ b′ → Sb b g j ≼ Sb b′ g j
plus-mono cz x = x
plus-mono (cs c) x = s≼ (plus-mono c x)
plus-mono (cl g) x = l≼ (λ n → l≼ʳ n (Sb-mono g n x))
Sb-mono g zero x = x
Sb-mono g (suc j) x = s≼ (plus-mono (g j) (Sb-mono g j x))

pt : ∀ {a b} → a ≺ᴵ b → Ordᴵ
pt (via {a′ = a′} e q) = a′
ptq : ∀ {a b} (x : a ≺ᴵ b) → pt x <ᴵ b
ptq (via e q) = q
pte : ∀ {a b} (x : a ≺ᴵ b) → a ≅ᴵ pt x
pte (via e q) = e
```

## §1 码

```agda
above : ∀ {a t} → Str t → a <ᴵ t → Code
tailb : ∀ {f : ℕ → Ordᴵ} → (∀ n → Str (f n)) → (hr : ∀ n → f n ≺ᴵ f (suc n)) → ℕ → Code → ℕ → Code
above (ss h) zero = cz
above (ss h) (suc q) = cs (above h q)
above (sl hf hr) (lim j q) = cl (tailb hf hr j (above (hf j) q))
tailb hf hr j c₀ zero = c₀
tailb hf hr j c₀ (suc i) = above (hf (suc i + j)) (ptq (hr (i + j)))

code : ∀ {η} → Str η → Code
code sz = cz
code (ss h) = cs (code h)
code (sl hf hr) = cl (tailb hf hr 0 (code (hf 0)))
```

## §2 值

```agda
Eqv : Ordᴵ → Ordᴵ → Set
Eqv a b = (a ≼ b) × (b ≼ a)

f-step : ∀ {f : ℕ → Ordᴵ} → (∀ n → f n ≺ᴵ f (suc n)) → ∀ n → f n ≼ f (suc n)
f-step hr n = ≺→≼ (hr n)

f0≼ : ∀ {f : ℕ → Ordᴵ} → (∀ n → f n ≼ f (suc n)) → ∀ j → f 0 ≼ f j
f0≼ st zero = ≼-refl _
f0≼ st (suc j) = ≼-trans (f0≼ st j) (st j)

f≼+ : ∀ {f : ℕ → Ordᴵ} → (∀ n → f n ≼ f (suc n)) → ∀ j n → f n ≼ f (n + j)
f≼+ st j zero = f0≼ st j
f≼+ {f} st j (suc n) = f≼+ {λ i → f (suc i)} (λ i → st (suc i)) j n

above-val : ∀ {a t} (h : Str t) (q : a <ᴵ t) → Eqv (plus (suc a) (above h q)) t
tail-val : ∀ {f s} (hf : ∀ n → Str (f n)) (hr : ∀ n → f n ≺ᴵ f (suc n)) j c₀ b → b ≼ f j → Eqv (plus b c₀) (f j) →
           Eqv (plus b (cl (tailb hf hr j c₀))) (lim f s)
above-val (ss h) zero = ≼-refl _ , ≼-refl _
above-val (ss h) (suc q) = s≼ (proj₁ (above-val h q)) , s≼ (proj₂ (above-val h q))
above-val (sl hf hr) (lim j q) = tail-val hf hr j (above (hf j) q) (suc _) (<→s≼ q) (above-val (hf j) q)

tail-val {f} {s} hf hr j c₀ b bj e₀ = l≼ up , l≼ dn
  where
  S : ℕ → Ordᴵ
  S = Sb b (tailb hf hr j c₀)
  -- 第 i+1 项就是 f (i+j) 的后继
  Si : ∀ i → Eqv (S (suc i)) (suc (f (i + j)))
  Si zero = s≼ (proj₁ e₀) , s≼ (proj₂ e₀)
  Si (suc i) =
    let x = hr (i + j)
        A = above-val (hf (suc i + j)) (ptq x)
    in s≼ (≼-trans (plus-mono _ (≼-trans (proj₁ (Si i)) (s≼ (≅→≼ (pte x))))) (proj₁ A))
     , s≼ (≼-trans (proj₂ A) (plus-mono _ (≼-trans (s≼ (≅→≼ (≅ᴵ-sym (pte x)))) (proj₂ (Si i)))))
  up : ∀ n → S n ≼ lim f s
  up zero = l≼ʳ j bj
  up (suc n) = ≼-trans (proj₁ (Si n)) (l≼ʳ (suc (n + j)) (≺→s≼ (hr (n + j))))
  dn : ∀ n → f n ≼ plus b (cl (tailb hf hr j c₀))
  dn n = l≼ʳ (suc n) (≼-trans (≼-trans (f≼+ (f-step hr) j n) (s≼ʳ (≼-refl _))) (proj₂ (Si n)))

code-val : ∀ {η} (h : Str η) → Eqv (val (code h)) η
code-val sz = z≼ , z≼
code-val (ss h) = s≼ (proj₁ (code-val h)) , s≼ (proj₂ (code-val h))
code-val (sl hf hr) = tail-val hf hr 0 (code (hf 0)) zero z≼ (code-val (hf 0))
```

## §3 `val` 的像都是严格的

码上的 `val` 只差字面路径, 所以严格; 这说明 `Str` 不比码窄: 两边的值域相同.

```agda
Sb-≺ : ∀ b g i → Sb b g i ≺ᴵ Sb b g (suc i)
Sb-≺ b g i = via (≅-refl′ _) (le< (Sb b g i) (g i))
  where
  ≅-refl′ : ∀ a → a ≅ᴵ a
  ≅-refl′ zero = z≅
  ≅-refl′ (suc a) = s≅ (≅-refl′ a)
  ≅-refl′ (lim f s) = l≅ (λ n → ≅-refl′ (f n))

plus-Str : ∀ {b} → Str b → ∀ c → Str (plus b c)
Sb-Str : ∀ {b} → Str b → ∀ g j → Str (Sb b g j)
plus-Str h cz = h
plus-Str h (cs c) = ss (plus-Str h c)
plus-Str h (cl g) = sl (Sb-Str h g) (Sb-≺ _ g)
Sb-Str h g zero = h
Sb-Str h g (suc j) = ss (plus-Str (Sb-Str h g j) (g j))

val-Str : ∀ M → Str (val M)
val-Str = plus-Str sz
```
