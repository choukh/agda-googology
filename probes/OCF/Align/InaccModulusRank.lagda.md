# 层号判决的范数模: 按下标深度分层, 得到 `GV` 与标签 (验收)

> **验收节.** 给定基类 `B` 与 `Prem B` (`B` 对 `fsn`, `pred` 封闭; 单调; 有界共尾性), 下标类 `Nω` = 所有下标层层都在 `B` 且可数的项. **`agrω`: `Dᵐ` 在 `Nω` 上满足 `GV`. `label`: 下标在 `Nω` 的任意可数项都带标签.** 分层是证明的需要: `L u` 的单步要 `u` 的下标上的 `GV`, 所以对深度 `d` 递归. 判决本身不分层. 结论在 [InaccModulus](InaccModulus.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.InaccModulusRank where

open import Data.Nat using (ℕ; zero; suc; _≤_; _≤′_; ≤′-refl; ≤′-step; _⊔_; z≤n)
open import Data.Nat.Properties using (≤⇒≤′; m≤m⊔n; m≤n⊔m)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Align.InaccStrikeBase using (Funext; dz)
open import OCF.Align.InaccStrikeCommute using (GV; module Tr; module Main)
open import OCF.Align.InaccTreeAccept using (LabN)
open import OCF.Align.InaccModulusBase using (Dᵐ)
open import OCF.Align.InaccModulusLift2 using (module Lift₂)
open import OCF.Align.Standard using (sz)
open import OCF.Align.InaccModulusTerm
import OCF.Align.EBO as E
open E using (T; cof; c0; c1; cω; cΩ; pred; fsn; cmpᵀ; lt; eq) renaming (ψ to ψᵗ)

record Prem (B : T → Set) : Set where
  field
    B-nil : B []
    B-pr  : ∀ {t} → B t → Cnt t → cof t ≡ c1 → B (pred t)
    B-fs  : ∀ {t} → B t → Cnt t → cof t ≡ cω → ∀ n → B (fsn t n)
    mono  : ∀ {t} → B t → Cnt t → cof t ≡ cω → ∀ n → cmpᵀ (fsn t n) (fsn t (suc n)) ≡ lt
    cofb  : ∀ {s t} → B s → Cnt s → B t → Cnt t → cof t ≡ cω → cmpᵀ s t ≡ lt →
            Σ ℕ λ n → (n ≤ suc (sz s)) × (cmpᵀ s (fsn t n) ≡ lt)

module Strata (fe : Funext) {B : T → Set} (pm : Prem B) where
  open Prem pm

  Nr : ℕ → T → Set
  Nr zero    t = t ≡ []
  Nr (suc d) t = B t × Cnt t × Sub (Nr d) t

  Nr-mono : ∀ d {t} → Nr d t → Nr (suc d) t
  Nr-mono zero refl = B-nil , tt , tt
  Nr-mono (suc d) {t} (b , c , s) = b , c , Sub-map (Nr-mono d) t s

  Nr-≤′ : ∀ {d e t} → d ≤′ e → Nr d t → Nr e t
  Nr-≤′ ≤′-refl     n = n
  Nr-≤′ {e = suc e} (≤′-step p) n = Nr-mono e (Nr-≤′ p n)

  Nr-≤ : ∀ {d e t} → d ≤ e → Nr d t → Nr e t
  Nr-≤ p n = Nr-≤′ (≤⇒≤′ p) n

  clN : ∀ d → ClN (Nr d)
  clN zero = record
    { N-nil = refl
    ; N-sub = λ { refl → tt }
    ; N-pr  = λ { refl () }
    ; N-fs  = λ { refl () }
    ; N-nc  = λ { refl () }
    }
  clN (suc d) = record
    { N-nil = B-nil , tt , tt
    ; N-sub = λ {u} n → Sub-map (Nr-mono d) u (proj₂ (proj₂ n))
    ; N-pr  = λ {u} (b , c , s) e → B-pr b c e , Cnt-pred u c , Closed.Sub-pred (clN d) u s
    ; N-fs  = λ {u} (b , c , s) e n → B-fs b c e n , Cnt-fsn u n c , Closed.Sub-fsn (clN d) u n s
    ; N-nc  = λ {u} (_ , c , _) e → Cnt-noΩ u c e
    }

  agr : ∀ d u v → Nr d u → Nr d v → GV (cmpᵀ u v) (Dᵐ (Tr.L Dᵐ u) (Tr.L Dᵐ v))
  agr zero _ _ refl refl = tt
  agr (suc d) = Lift₂.agr′ fe (Closed.clQ (clN d)) (agr d) (Nr (suc d))
    (λ n → proj₂ (proj₂ n))
    (λ n e m → ClN.N-fs (clN (suc d)) n e m)
    (λ n e → ClN.N-pr (clN (suc d)) n e)
    (λ n e → ClN.N-nc (clN (suc d)) n e)
    (λ (b , c , _) e n → mono b c e n)
    (λ (bs , cs , _) (bt , ct , _) e l → cofb bs cs bt ct e l)

  -- 全部深度的并
  Nω : T → Set
  Nω t = Σ ℕ λ d → Nr d t

  clNω : ClN Nω
  clNω = record
    { N-nil = 0 , refl
    ; N-sub = λ {u} (d , n) → Sub-map (d ,_) u (ClN.N-sub (clN d) n)
    ; N-pr  = λ (d , n) e → d , ClN.N-pr (clN d) n e
    ; N-fs  = λ (d , n) e m → d , ClN.N-fs (clN d) n e m
    ; N-nc  = λ (d , n) e → ClN.N-nc (clN d) n e
    }

  agrω : ∀ u v → Nω u → Nω v → GV (cmpᵀ u v) (Dᵐ (Tr.L Dᵐ u) (Tr.L Dᵐ v))
  agrω u v (d , nu) (e , nv) =
    agr (d ⊔ e) u v (Nr-≤ (m≤m⊔n d e) nu) (Nr-≤ (m≤n⊔m d e) nv)

  -- 有限的项只用到有限深度
  collect : ∀ t → Sub Nω t → Σ ℕ λ d → Sub (Nr d) t
  collect [] s = 0 , tt
  collect (ψᵗ u a ∷ xs) ((d , nu) , sa , sx) with collect a sa | collect xs sx
  ... | e , ea | f , ex =
    D , Nr-≤ (m≤m⊔n d (e ⊔ f)) nu ,
        Sub-map (λ n → Nr-≤ (trans≤ (m≤m⊔n e f) (m≤n⊔m d (e ⊔ f))) n) a ea ,
        Sub-map (λ n → Nr-≤ (trans≤ (m≤n⊔m e f) (m≤n⊔m d (e ⊔ f))) n) xs ex
    where
      D = d ⊔ (e ⊔ f)
      trans≤ : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
      trans≤ z≤n q = z≤n
      trans≤ (Data.Nat.s≤s p) (Data.Nat.s≤s q) = Data.Nat.s≤s (trans≤ p q)

  -- 层层下标的条件
  Hc : T → Set
  Hc [] = ⊤
  Hc (ψᵗ u a ∷ xs) = (B u × Cnt u × Hc u) × Hc a × Hc xs

  Hc→Sub : ∀ t → Hc t → Sub Nω t
  Hc→Sub [] h = tt
  Hc→Sub (ψᵗ u a ∷ xs) ((b , c , hu) , ha , hx) with collect u (Hc→Sub u hu)
  ... | d , su = (suc d , b , c , su) , Hc→Sub a ha , Hc→Sub xs hx

  open Main fe Dᵐ (Sub Nω) Nω (Closed.clQ clNω) agrω

  P : T → Set
  P t = Cnt t × Sub Nω t

  open Lab P proj₂
    (λ {t} (c , s) e n → Cnt-fsn t n c , Closed.Sub-fsn clNω t n s)
    (λ {t} (c , s) e → Cnt-pred t c , Closed.Sub-pred clNω t s)
    (λ {t} (c , _) e → Cnt-noΩ t c e)

  label : ∀ t → Cnt t → Hc t → LabN (dz (Tr.S Dᵐ t)) t
  label t c h = Commute t (c , Hc→Sub t h)
```
