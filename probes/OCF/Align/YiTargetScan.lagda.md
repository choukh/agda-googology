# 单次基本列的唯一比较与新 γ 目标

scan 沿基本列真正递归的位置前进，但不计算基本列输出或 γ 链。
结果保存共尾层 ν 和旧目标 u；该步可能新增的目标仅取 ν，丢弃旧目标 u。
后续历史环境用它生成候选，不能因当前比较的目标是什么就临时加进去。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiTargetScan where

open import Data.List.Base using ([]; _∷_)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Product.Base using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import OCF.Align.EboLeanDef using (T; ψ; sucT; Cof; c0; c1; cω; cΩ; cof)
open import OCF.Align.YiSpineTrace using (FsnCall; hit; sum-tail; arg-step; index-step)
open import OCF.Align.YiTargetBase

scan : T → Maybe (T × T)
scan₀ : T → Cof → Maybe (T × T)
scan₊ : T → T → Cof → Maybe (T × T)

scan [] = nothing
scan (x ∷ y ∷ ys) = scan (y ∷ ys)
scan (ψ u (b ∷ bs) ∷ []) = scan₊ u (b ∷ bs) (cof (b ∷ bs))
scan (ψ (v ∷ vs) [] ∷ []) = scan₀ (v ∷ vs) (cof (v ∷ vs))
scan (ψ [] [] ∷ []) = nothing

scan₀ u c0 = nothing
scan₀ u c1 = nothing
scan₀ u cω = scan u
scan₀ u (cΩ ν) = nothing

scan₊ u b c0 = nothing
scan₊ u b c1 = nothing
scan₊ u b cω = scan b
scan₊ u b (cΩ ν) = just (ν , u)

call-scan : ∀ {t l u} → FsnCall t l u →
  Σ T (λ ν → l ≡ sucT ν × scan t ≡ just (ν , u))
call-scan (hit {b = []} ())
call-scan (hit {u} {b = b ∷ bs} {ν} e) =
  ν , refl , cong (scan₊ u (b ∷ bs)) e
call-scan (sum-tail {x = ψ _ _} {y = y} {ys} c) = call-scan {t = y ∷ ys} c
call-scan (arg-step {u} {b = []} () c)
call-scan (arg-step {u} {b = b ∷ bs} e c) with call-scan {t = b ∷ bs} c
... | ν , eq , p = ν , eq , trans (cong (scan₊ u (b ∷ bs)) e) p
call-scan (index-step {u = []} () c)
call-scan (index-step {u = v ∷ vs} e c) with call-scan {t = v ∷ vs} c
... | ν , eq , p = ν , eq , trans (cong (scan₀ (v ∷ vs)) e) p

scan-call : ∀ t {ν u} → scan t ≡ just (ν , u) → FsnCall t (sucT ν) u
scan₀-call : ∀ v c {ν u} → cof v ≡ c → scan₀ v c ≡ just (ν , u) →
  FsnCall (ψ v [] ∷ []) (sucT ν) u
scan₊-call : ∀ v b c {ν u} → cof b ≡ c → scan₊ v b c ≡ just (ν , u) →
  FsnCall (ψ v b ∷ []) (sucT ν) u

scan-call [] ()
scan-call (x ∷ y ∷ ys) p = sum-tail (scan-call (y ∷ ys) p)
scan-call (ψ v b@(_ ∷ _) ∷ []) p = scan₊-call v b (cof b) refl p
scan-call (ψ v@(_ ∷ _) [] ∷ []) p = scan₀-call v (cof v) refl p
scan-call (ψ [] [] ∷ []) ()

scan₀-call v c0 e ()
scan₀-call v c1 e ()
scan₀-call v cω e p = index-step e (scan-call v p)
scan₀-call v (cΩ μ) e ()

scan₊-call v b c0 e ()
scan₊-call v b c1 e ()
scan₊-call v b cω e p = arg-step e (scan-call b p)
scan₊-call v b (cΩ μ) e refl = hit e

just-pair-inj : ∀ {a b c d : T} → just (a , b) ≡ just (c , d) → a ≡ c × b ≡ d
just-pair-inj refl = refl , refl

call-unique : ∀ {t l u l′ u′} → FsnCall t l u → FsnCall t l′ u′ → l ≡ l′ × u ≡ u′
call-unique p q with call-scan p | call-scan q
... | ν , e , s | μ , f , t with just-pair-inj (trans (sym s) t)
...   | νμ , uv = trans e (trans (cong sucT νμ) (sym f)) , uv

call-tags : ∀ {P t l u} → AllTags P t → FsnCall t l u → P u
call-tags b (hit {b = []} ())
call-tags (h , tu , tb , ts) (hit {b = _ ∷ _} e) = h
call-tags (h , tu , tb , ts) (sum-tail {x = ψ _ _} {y = y} {ys} c) = call-tags {t = y ∷ ys} ts c
call-tags (h , tu , tb , ts) (arg-step {b = b} c e) = call-tags {t = b} tb e
call-tags (h , tu , tb , ts) (index-step {u = u} c e) = call-tags {t = u} tu e
```

call-scan／scan-call 精确对应 FsnCall；call-unique 证明一次 fsn 至多发生
一处此类比较。它们没有枚举未来 γ 分支，也没有声称同一层号跨上下文只有一个目标。
