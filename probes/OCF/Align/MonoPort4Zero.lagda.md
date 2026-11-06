# 一族关系, 结构版 (一): 第 0 层, 对一切实例与一切观测

> 不含记号. 入口 [MonoPort4](MonoPort4.lagda.md). 一族 $R_c$ 的底: 第 0 层输入按 `StrRelDef` 的结构关系 $\sqsubseteq_0$ (无左极限截断) 相关, 则在**任意实例** $\Lambda$、任意世界、**任意观测** (`OutLaws` 加 `PreLaw`, **不要 `LimLaw`**) 下, 两边动作不同时输出相关 (`snd₀ᴳ`). 观测要多一条: 它的 $T_0$ 分量是 $\sqsubseteq_0$ (`proj₀`), 因为节点上升时链的下一个点是上一段的 $T_0$ 输出, 又作坐标.
>
> - 和的结构全部由 [MonoPort3Gen](MonoPort3Gen.lagda.md) 的核给出; 这里只写: 上下文律 (`cl₀`, 上下文就是 $\sqsubseteq_0$, 由它的构造子与 `nwd` 拼出), `nw` 的两条, 自比 `rO` (对树归纳), 与对 $\sqsubseteq_0$ 推导的分派.
> - **`chain₀ᴳ`**: 第 0 层节点在 $T_0$ 上上升的链, 点按 $\sqsubseteq_0$ 相关, 输出两读数: 值 $\le$ 与 $\sqsubseteq_0$.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
open import OCF.Align.HtFeedTree using (H; LgH; hz; _⊲[_]_)
module OCF.Align.MonoPort4Zero (Λ : H) (lΛ : LgH Λ) {W : A} (lW : Lg W) (t₀ : hz ⊲[ W ] Λ) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; ≤l; l≤; ≤-refl)
open import OCF.Align.HtFeedTree using (D; accL; n0; n1; _⨾_; nl; ni; nκ; nw; sum; pt)
import OCF.Align.MonoPort3Gen as Gen
open import OCF.Align.StrRelDef lW using (_⊑₀_; z0; o1; sq; lm; wl; wr; pr; tr; u0l; u0r; u1l; u1r; al; al′; ar; ar′; refl₀; nwd; nwd′)
  renaming (preL to preLˢ)

open Gen Λ lΛ lW t₀ using (module P; o₀; preL; OutLaws; PreLaw; module Core)

preL≡ : ∀ {V} (d : ℕ → D hz V) k → preLˢ d k ≡ preL d k
preL≡ d zero = refl
preL≡ d (suc k) = cong (λ t → t ⨾ d k) (preL≡ d k)
```

## §1 核的第 0 层实例

```agda
module R0 (O : OutLaws) (Lpre : PreLaw O) (proj₀ : ∀ {Δ Δ′} → OutLaws._≼_ O Δ Δ′ → o₀ Δ ⊑₀ o₀ Δ′) where
  module K = Core O hz (accL hz) t₀ A (λ V → V) (λ V → V ⊲ W) (λ q → q) (λ w w′ → w ⊑₀ w′) (λ x x′ → x ⊑₀ x′)
  open K public

  cl₀ : CxLaws
  cl₀ = record
    { cxL = λ { (cx _) → cx (refl₀ _) }
    ; cxR = λ { (cx _) → cx (refl₀ _) }
    ; cx⨾ = λ { q q′ (cx hw) (inn hx) → cx (sq hw (wl (wr hx))) }
    ; cx0ˡ = λ { q (cx hw) → cx (tr (sq hw (wl z0)) (u1l (refl₀ _))) }
    ; cx0ʳ = λ { q (cx hw) → cx (tr (u1r (refl₀ _)) (sq hw (wr z0))) }
    ; cxas = λ { {x = x} {y} q (cx hw) _ _ → cx (ar′ (sq hw (nwd x y))) }
    ; cxas′ = λ { {x = x} {y} q (cx hw) _ _ → cx (al (sq hw (nwd′ x y))) }
    ; cxpre = λ { {w = w} {d = d} q q′ n (cx h) (inn he) → cx (tr (ar′ (sq (refl₀ w) (nwd (preL d n) (d n)))) (sq h (wl (wr he)))) }
    ; cxlim = λ { {w = w} {d = d} q n (cx h) (inn hd) → cx (tr (sq h (wl (wr hd))) (al (sq (refl₀ w) (nwd′ (preL d n) (d n))))) }
    }

  open Steps cl₀ public

  nwl : ∀ {Aᵢ Aⱼ : Act} {V₀ V V₂} {p : V₀ ⊲ V} {x : D hz V₀} {z : D hz V₂} → Sem Aᵢ Aⱼ x z → Sem Aᵢ Aⱼ (nw p x) z
  nwl {p = p} h q = h (C.⊲-tr p q)

  nwr : ∀ {Aᵢ Aⱼ : Act} {V₀ V V₁} {p : V₀ ⊲ V} {x : D hz V₀} {z : D hz V₁} → Sem Aᵢ Aⱼ z x → Sem Aᵢ Aⱼ z (nw p x)
  nwr {p = p} h q q′ = h q (C.⊲-tr p q′)

  -- 自比, 对树归纳
  rO : ∀ (A₀ : Act) → HA A₀ A₀ → ∀ {V} (x : D hz V) → Sem A₀ A₀ x x
  rO A₀ h n0 = n0S
  rO A₀ h n1 = n1S h
  rO A₀ h (x ⨾ y) = ⨾S (rO A₀ h x) (rO A₀ h x) (rO A₀ h x) (inn (refl₀ x)) (rO A₀ h y)
  rO A₀ h (nl d) = nlS (λ n → rO A₀ h (d n)) (λ n → rO A₀ h (d n)) (λ n → rO A₀ h (d n)) (λ n → inn (refl₀ (d n)))
  rO A₀ h (ni () u)
  rO A₀ h (nκ () u)
  rO A₀ h (nw p x) = nwl (nwr (rO A₀ h x))
```

## §2 定理: 结构关系推出输出相关

```agda
  Sem₀ : ∀ {V₁ V₂} → D hz V₁ → D hz V₂ → Set
  Sem₀ x x′ = ∀ (Aᵢ Aⱼ : Act) → HA Aᵢ Aᵢ → HA Aⱼ Aⱼ → HA Aᵢ Aⱼ → Sem Aᵢ Aⱼ x x′

  snd₀ᴳ : ∀ {V₁ V₂} {x : D hz V₁} {x′ : D hz V₂} → x ⊑₀ x′ → Sem₀ x x′
  snd₀ᴳ z0 Aᵢ Aⱼ hi hj hij = n0S
  snd₀ᴳ o1 Aᵢ Aⱼ hi hj hij = n1S hij
  snd₀ᴳ (sq {x = x} {x′ = x′} hx hy) Aᵢ Aⱼ hi hj hij =
    ⨾S (rO Aᵢ hi x) (rO Aⱼ hj x′) (snd₀ᴳ hx Aᵢ Aⱼ hi hj hij) (inn hx) (snd₀ᴳ hy Aᵢ Aⱼ hi hj hij)
  snd₀ᴳ (lm {d = d} {d′} hd) Aᵢ Aⱼ hi hj hij =
    nlS (λ n → rO Aᵢ hi (d n)) (λ n → rO Aⱼ hj (d′ n)) (λ n → snd₀ᴳ (hd n) Aᵢ Aⱼ hi hj hij) (λ n → inn (hd n))
  snd₀ᴳ (wl h) Aᵢ Aⱼ hi hj hij = nwl (snd₀ᴳ h Aᵢ Aⱼ hi hj hij)
  snd₀ᴳ (wr h) Aᵢ Aⱼ hi hj hij = nwr (snd₀ᴳ h Aᵢ Aⱼ hi hj hij)
  snd₀ᴳ (pr {x = x} {x′} {d} {d′} hx hd k) Aᵢ Aⱼ hi hj hij =
    subst (λ t → Sem Aᵢ Aⱼ (x ⨾ t) (x′ ⨾ nl d′)) (sym (preL≡ d k))
      (preS Lpre (rO Aᵢ hi x) (rO Aⱼ hj x′) (λ n → rO Aᵢ hi (d n)) (λ n → rO Aⱼ hj (d′ n))
            (snd₀ᴳ hx Aᵢ Aⱼ hi hj hij) (inn hx) (λ n → snd₀ᴳ (hd n) Aᵢ Aⱼ hi hj hij) (λ n → inn (hd n)) k)
  snd₀ᴳ (tr h h′) Aᵢ Aⱼ hi hj hij = trS (snd₀ᴳ h Aᵢ Aᵢ hi hi hi) (snd₀ᴳ h′ Aᵢ Aⱼ hi hj hij)
  snd₀ᴳ (u0l h) Aᵢ Aⱼ hi hj hij = u0ˡS (snd₀ᴳ h Aᵢ Aⱼ hi hj hij)
  snd₀ᴳ (u0r h) Aᵢ Aⱼ hi hj hij = u0ʳS (snd₀ᴳ h Aᵢ Aⱼ hi hj hij)
  snd₀ᴳ (u1l h) Aᵢ Aⱼ hi hj hij = u1ˡS (snd₀ᴳ h Aᵢ Aⱼ hi hj hij)
  snd₀ᴳ (u1r h) Aᵢ Aⱼ hi hj hij = u1ʳS (snd₀ᴳ h Aᵢ Aⱼ hi hj hij)
  snd₀ᴳ (al {x = x} {y} {z} h) Aᵢ Aⱼ hi hj hij =
    asˡS (rO Aᵢ hi x) (rO Aᵢ hi y) (rO Aᵢ hi z) (inn (refl₀ x)) (inn (refl₀ y)) (snd₀ᴳ h Aᵢ Aⱼ hi hj hij)
  snd₀ᴳ (al′ {x = x} {y} {z} h) Aᵢ Aⱼ hi hj hij =
    asˡ′S (rO Aᵢ hi x) (rO Aᵢ hi y) (rO Aᵢ hi z) (inn (refl₀ x)) (inn (refl₀ y)) (snd₀ᴳ h Aᵢ Aⱼ hi hj hij)
  snd₀ᴳ (ar {x = x} {y} {z} h) Aᵢ Aⱼ hi hj hij =
    asʳS (rO Aⱼ hj x) (rO Aⱼ hj y) (rO Aⱼ hj z) (inn (refl₀ x)) (inn (refl₀ y)) (snd₀ᴳ h Aᵢ Aⱼ hi hj hij)
  snd₀ᴳ (ar′ {x = x} {y} {z} h) Aᵢ Aⱼ hi hj hij =
    asʳ′S (rO Aⱼ hj x) (rO Aⱼ hj y) (rO Aⱼ hj z) (inn (refl₀ x)) (inn (refl₀ y)) (snd₀ᴳ h Aᵢ Aⱼ hi hj hij)
```

## §3 第 0 层节点上升的链

链在世界 $W$ 里, 点是第 0 层的树, 上下文是点的累加; 读数在 $T_0$ 上. 不变量: 上下文、点 $\sqsubseteq_0$, 两边 `Good`, 状态 `SRel`, 部分和 $\le$.

```agda
  module Chain (Aᵢ Aⱼ : Act) (hi : HA Aᵢ Aᵢ) (hj : HA Aⱼ Aⱼ) (hij : HA Aᵢ Aⱼ) where
    CC : Act → P.St W → ℕ → D hz W × (D hz W × P.St W)
    CC A₂ Y = P.Chn (accL hz) t₀ lW A₂ Y

    segs : Act → P.St W → ℕ → D hz W
    segs A₂ Y n = o₀ (Run A₂ (proj₁ (proj₂ (CC A₂ Y n))) C.self (proj₁ (CC A₂ Y n)) (proj₂ (proj₂ (CC A₂ Y n))))

    chain₀ᴳ : ∀ (Y Y′ : P.St W) b b′ → Good Y → Good Y′ → SRel Y Y′ → b ≤ b′ →
              (sum b (nl (segs Aᵢ Y)) ≤ sum b′ (nl (segs Aⱼ Y′))) × (nl (segs Aᵢ Y) ⊑₀ nl (segs Aⱼ Y′))
    chain₀ᴳ Y Y′ b b′ g g′ s cb =
      l≤ (λ n → ≤l n (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (go n))))))) ,
      lm (λ n → let (gc , (gd , (gy , (gy′ , (sy , _))))) = go n in
                proj₀ (proj₂ (snd₀ᴳ gd Aᵢ Aⱼ hi hj hij C.self C.self (c n) (c′ n) azero azero (Yn n) (Yn′ n) (cx gc) gy gy′ sy z≤)))
      where
      c  = λ n → proj₁ (CC Aᵢ Y n)
      c′ = λ n → proj₁ (CC Aⱼ Y′ n)
      δ  = λ n → proj₁ (proj₂ (CC Aᵢ Y n))
      δ′ = λ n → proj₁ (proj₂ (CC Aⱼ Y′ n))
      Yn  = λ n → proj₂ (proj₂ (CC Aᵢ Y n))
      Yn′ = λ n → proj₂ (proj₂ (CC Aⱼ Y′ n))
      go : ∀ n → (c n ⊑₀ c′ n) × ((δ n ⊑₀ δ′ n) × (Good (Yn n) × (Good (Yn′ n) ×
                 (SRel (Yn n) (Yn′ n) × (pt b (segs Aᵢ Y) n ≤ pt b′ (segs Aⱼ Y′) n)))))
      go zero = z0 , (proj₀ (proj₂ s) , (g , (g′ , (s , cb))))
      go (suc n) =
        let (gc , (gd , (gy , (gy′ , (sy , gb))))) = go n
            h = λ e₁ e₂ (eb : e₁ ≤ e₂) → snd₀ᴳ gd Aᵢ Aⱼ hi hj hij C.self C.self (c n) (c′ n) e₁ e₂ (Yn n) (Yn′ n) (cx gc) gy gy′ sy eb
        in sq gc gd ,
           (proj₀ (proj₂ (h azero azero z≤)) ,
            (G⊕ {Yn n} gy (rf (rO Aᵢ hi (δ n)) C.self (c n) (Yn n) (cx (refl₀ _)) gy) ,
             (G⊕ {Yn′ n} gy′ (rf (rO Aⱼ hj (δ′ n)) C.self (c′ n) (Yn′ n) (cx (refl₀ _)) gy′) ,
              (S⊕ gy gy′ sy (h _ _ (proj₁ sy)) ,
               proj₁ (h _ _ gb)))))
```
