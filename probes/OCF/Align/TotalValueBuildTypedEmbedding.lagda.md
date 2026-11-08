# 累计嵌入被完整 typed 折叠消费

复用 BTBOFullEmb 的有界 PE 证明，重基到实际 Free 层并连接本轮
BoundedEmbedding 与 Run.add。没有修改原程序、旧定理或成品证书。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TotalValueBuildTypedEmbedding where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; _×_)
open import OCF.Align.OrdLabZLevel
open import OCF.Align.ValueJudgeBase using (_≼_)
open import OCF.Align.TotalValueBuildTypedLe using (module LeE)

record PEmb (a b : Ordᴵ) : Set where
  field
    map  : ∀ {c} → c ≺ᴵ a → Ordᴵ
    bnd  : ∀ {c} (r : c ≺ᴵ a) → map r ≺ᴵ b
    mono : ∀ {c d} (r : c ≺ᴵ a) (s : d ≺ᴵ a) → c ≺ᴵ d → map r ≺ᴵ map s
    coh  : ∀ {c d} (r : c ≺ᴵ a) (s : d ≺ᴵ a) → c ≅ᴵ d → map r ≅ᴵ map s

module PE {a b : Ordᴵ} (P : PEmb a b) where
  open PEmb P

  data E : Ordᴵ → Ordᴵ → Set where
    top : ∀ {x x′} → x ≅ᴵ a → x′ ≅ᴵ b → E x x′
    sub : ∀ {x x′} (r : x ≺ᴵ a) → x′ ≅ᴵ map r → E x x′

  E-resp : ∀ {x y x′ y′} → E x y → x ≅ᴵ x′ → y ≅ᴵ y′ → E x′ y′
  E-resp (top e e′) d d′ = top (≅ᴵ-trans (≅ᴵ-sym d) e) (≅ᴵ-trans (≅ᴵ-sym d′) e′)
  E-resp (sub r e′) d d′ = sub (≺ᴵ-respˡ (≅ᴵ-sym d) r) (≅ᴵ-trans (≅ᴵ-sym d′) (≅ᴵ-trans e′ (coh r (≺ᴵ-respˡ (≅ᴵ-sym d) r) d)))

  open LeE E E-resp ⊥

  lt′ : ∀ {x x′ y y′} → E x x′ → E y y′ → x ≺ᴵ y → x′ ≺ᴵ y′
  lt′ (top e e′) (top d d′) r = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respˡ (≅ᴵ-sym e) (≺ᴵ-respʳ r d)))
  lt′ (top e e′) (sub s d′) r = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-trans (≺ᴵ-respˡ (≅ᴵ-sym e) r) s))
  lt′ (sub s e′) (top d d′) r = ≺ᴵ-respˡ e′ (≺ᴵ-respʳ (bnd s) (≅ᴵ-sym d′))
  lt′ (sub s e′) (sub t d′) r = ≺ᴵ-respˡ e′ (≺ᴵ-respʳ (mono s t r) (≅ᴵ-sym d′))

  eq′ : ∀ {x x′ y y′} → E x x′ → E y y′ → x ≅ᴵ y → x′ ≅ᴵ y′
  eq′ (top e e′) (top d d′) r = ≅ᴵ-trans e′ (≅ᴵ-sym d′)
  eq′ (top e e′) (sub s d′) r = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respˡ (≅ᴵ-sym (≅ᴵ-trans (≅ᴵ-sym r) e)) s))
  eq′ (sub s e′) (top d d′) r = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respˡ (≅ᴵ-sym (≅ᴵ-trans r d)) s))
  eq′ (sub s e′) (sub t d′) r = ≅ᴵ-trans e′ (≅ᴵ-trans (coh s t r) (≅ᴵ-sym d′))

  low : ∀ {d c c′} → E c c′ → d ≺ᴵ c → Σ (d ≺ᴵ a) (λ r → map r ≺ᴵ c′)
  low (top e e′) q = let r = ≺ᴵ-respʳ q e in r , ≺ᴵ-respʳ (bnd r) (≅ᴵ-sym e′)
  low (sub s e′) q = let r = ≺ᴵ-trans q s in r , ≺ᴵ-respʳ (mono r s q) (≅ᴵ-sym e′)

  Ω′ : ∀ {x c c′} → x ⊑ᴵ c → E c c′ → Le (Ω x) (Ω c′)
  Ω′ {c′ = c′} z⊑ ec = Le-one c′ (≅ᴵ-refl c′)
  Ω′ {c′ = c′} (s⊑ e q) ec with low ec (via e q)
  ... | r , via e₂ q₂ = walk c′ (≅ᴵ-refl c′) (sub r e₂′) q₂
    where e₂′ = ≅ᴵ-sym e₂
  Ω′ (l⊑ k) ec = Lll (λ n → Lul (Ω′ (k n) ec))

  ℒ : Laws
  ℒ = record { lt-pres = lt′ ; eq-pres = eq′ ; Ωlaw = Ω′ ⊑ᴵ-refl ; Ωc = λ () }

  open WithLaws ℒ

  Ψ-emb′ : ψ⁰ (Ω a) ≼ ψ⁰ (Ω b)
  Ψ-emb′ = Ψ⁰-emb (top (≅ᴵ-refl a) (≅ᴵ-refl b))

Ψ-emb : ∀ {a b} → PEmb a b → ψ⁰ (Ω a) ≼ ψ⁰ (Ω b)
Ψ-emb P = PE.Ψ-emb′ P
```


```agda
import OCF.Align.TotalValueBuildIf as I
import OCF.Align.TotalValueBuildEmbedding as B
import OCF.Free.TotalOrbitRun as R

from-bounded : ∀ {a b} → I.BoundedEmbedding a b → PEmb a b
from-bounded e = record
  { map = I.BoundedEmbedding.map e
  ; bnd = I.BoundedEmbedding.bound e
  ; mono = I.BoundedEmbedding.ordered e
  ; coh = I.BoundedEmbedding.coherent e }

bounded-ψ : ∀ {a b} → I.BoundedEmbedding a b → ψ⁰ (Ω a) ≼ ψ⁰ (Ω b)
bounded-ψ e = Ψ-emb (from-bounded e)

cumulative-ψ : ∀ c a → ψ⁰ (Ω a) ≼ ψ⁰ (Ω (R.add c a))
cumulative-ψ c a = bounded-ψ (B.cumulative c a)
```

cumulative-ψ 消费实际 add 的有界嵌入，涵盖全部层号，不是只比较有限
样本。它作用于旧 typed ψ⁰Ω；通过 BaseRead 与纯累计解释的值桥后才能
进入新 base 回调。仍未给 rowC 的 Ωd/cap 环境模拟。
