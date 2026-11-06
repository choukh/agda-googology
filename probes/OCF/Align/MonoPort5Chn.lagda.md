# 第三站 (三): 节点上升的链, 对一切单世界层写一次

> 不含记号. 入口 [MonoPort5](MonoPort5.lagda.md). 节点在目标 $T_e$ ($e\le k$, $k$ 是节点层) 上上升时, 输出是层 $k$ 上一条链的各段输出的极限 (`RKi` 的 `rise` 句, 链是 `Chn`). 本文件对**任意实例、任意观测、任意第 $\ge1$ 层** $k$ (世界固定, 路径只在 `self`) 写一次链的引理 `chainG`: 只要
>
> - 链点之间的关系 `Pt`, 由它推出两动作的语义 (`sndP`),
> - 观测在 $T_k$ 上的分量落在 `Pt` 里 (`prj`),
> - 上下文关系含 `n0` 并对 "加一个链点" 封闭 (`cxn`, `cxc`; 链的上下文是 `c ⨾ δ`, 没有 `nw`),
>
> 两条链的各段输出逐项按观测相关, 第 0 层读数的极限 $\le$. 第 0 层的链 (`MonoPort4Zero.chain₀ᴳ`) 是同一个论证, 那里世界任意, 所以单写.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
open import OCF.Align.HtFeedTree using (H; LgH; hz; _⊲[_]_; AccY; D)
import OCF.Align.MonoPort3Gen as Gen
module OCF.Align.MonoPort5Chn (Λ : H) (lΛ : LgH Λ) {W : A} (lW : Lg W) (t₀ : hz ⊲[ W ] Λ)
  (O : Gen.OutLaws Λ lΛ lW t₀) (ly : H) (ac : AccY ly) (ll : ly ⊲[ W ] Λ)
  (Cx₀ In₀ : D ly W → D ly W → Set) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; ≤l; l≤; ≤-refl)
open import OCF.Align.HtFeedTree using (n0; _⨾_; nl; sum; pt)
open Gen Λ lΛ lW t₀ using (module P; o₀; module Core)

module K = Core O ly ac ll ⊤ (λ _ → W) (λ _ → ⊤) (λ _ → C.self) Cx₀ (λ x x′ → In₀ x x′)
open K

Tl : P.Tg W ly W
Tl = P.tg C.self ll lW

module Chain (cl : CxLaws) (Pt : D ly W → D ly W → Set)
  (sndP : ∀ {x x′} → Pt x x′ → ∀ (Aᵢ Aⱼ : Act) → HA Aᵢ Aᵢ → HA Aⱼ Aⱼ → HA Aᵢ Aⱼ → Sem Aᵢ Aⱼ {tt} {tt} x x′)
  (prj : ∀ {Δ Δ′} → Δ ≼ Δ′ → Pt (P.yc Δ Tl) (P.yc Δ′ Tl))
  (cxn : Cx n0 n0)
  (cxc : ∀ {c c′ δ δ′} → Cx c c′ → Pt δ δ′ → Pt δ δ → Pt δ′ δ′ → Cx (c ⨾ δ) (c′ ⨾ δ′))
  (Aᵢ Aⱼ : Act) (hi : HA Aᵢ Aᵢ) (hj : HA Aⱼ Aⱼ) (hij : HA Aᵢ Aⱼ) where
  open CxLaws cl

  CC : Act → P.St W → ℕ → D ly W × (D ly W × P.St W)
  CC A₂ Y = P.Chn ac ll lW A₂ Y

  outs : Act → P.St W → ℕ → P.Df W
  outs A₂ Y n = Run A₂ (proj₁ (proj₂ (CC A₂ Y n))) tt (proj₁ (CC A₂ Y n)) (proj₂ (proj₂ (CC A₂ Y n)))

  chainG : ∀ (Y Y′ : P.St W) b b′ → Good Y → Good Y′ → SRel Y Y′ → b ≤ b′ →
           (sum b (nl (λ n → o₀ (outs Aᵢ Y n))) ≤ sum b′ (nl (λ n → o₀ (outs Aⱼ Y′ n)))) × (∀ n → outs Aᵢ Y n ≼ outs Aⱼ Y′ n)
  chainG Y Y′ b b′ g g′ s cb =
    l≤ (λ n → ≤l n (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (go n))))))))) , (λ n → proj₂ (h n azero azero z≤))
    where
    c  = λ n → proj₁ (CC Aᵢ Y n)
    c′ = λ n → proj₁ (CC Aⱼ Y′ n)
    δ  = λ n → proj₁ (proj₂ (CC Aᵢ Y n))
    δ′ = λ n → proj₁ (proj₂ (CC Aⱼ Y′ n))
    Yn  = λ n → proj₂ (proj₂ (CC Aᵢ Y n))
    Yn′ = λ n → proj₂ (proj₂ (CC Aⱼ Y′ n))
    sg  = λ n → o₀ (outs Aᵢ Y n)
    sg′ = λ n → o₀ (outs Aⱼ Y′ n)
    go : ∀ n → Cx (c n) (c′ n) × (Pt (δ n) (δ′ n) × (Pt (δ n) (δ n) × (Pt (δ′ n) (δ′ n) ×
               (Good (Yn n) × (Good (Yn′ n) × (SRel (Yn n) (Yn′ n) × (pt b sg n ≤ pt b′ sg′ n)))))))
    h : ∀ n e₁ e₂ → e₁ ≤ e₂ → Obs e₁ e₂ (outs Aᵢ Y n) (outs Aⱼ Y′ n)
    h n e₁ e₂ eb = let (cc , (pd , (_ , (_ , (gy , (gy′ , (sy , _))))))) = go n in
      sndP pd Aᵢ Aⱼ hi hj hij tt tt (c n) (c′ n) e₁ e₂ (Yn n) (Yn′ n) cc gy gy′ sy eb
    go zero = cxn , (prj (proj₂ s) , (prj g , (prj g′ , (g , (g′ , (s , cb))))))
    go (suc n) =
      let (cc , (pd , (pdd , (pdd′ , (gy , (gy′ , (sy , gb))))))) = go n
          oi = sndP pdd Aᵢ Aᵢ hi hi hi tt tt (c n) (c n) azero azero (Yn n) (Yn n) (cxL cc) gy gy (sr gy) z≤
          oj = sndP pdd′ Aⱼ Aⱼ hj hj hj tt tt (c′ n) (c′ n) azero azero (Yn′ n) (Yn′ n) (cxR cc) gy′ gy′ (sr gy′) z≤
      in cxc cc pd pdd pdd′ ,
         (prj (proj₂ (h n azero azero z≤)) ,
          (prj (proj₂ oi) , (prj (proj₂ oj) ,
           (G⊕ {Yn n} gy (proj₂ oi) , (G⊕ {Yn′ n} gy′ (proj₂ oj) ,
            (S⊕ gy gy′ sy (h n _ _ (proj₁ sy)) , proj₁ (h n _ _ gb)))))))
```
