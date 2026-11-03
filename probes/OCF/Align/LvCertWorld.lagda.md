# 世界的接口: 闭包定理要世界做什么 (底座)

> 不含记号. 结论写在 [LvCert](LvCert.lagda.md). 任务要求对世界抽象, 因为并行路线可能把 ℕ 高度换成层号键. 这里写的是**接口与否定的核心**, 不是闭包定理: 闭包定理没有写成 (见 `LvCert`).
>
> `Worlds`: 闭包只通过 `prj`, `toPrj`, `ofPrj`, `upd`, `upd-ok` 碰世界. [UniformLvTree](UniformLvTree.lagda.md) 的 ℕ 高度是实例 (`worldℕ`). `selfVis`: 第 $k$ 层的地板在第 $k$ 层可见. **`noSame`: 对任何实例, 只要嵌入的地板 `tk k τ` 与闭包同键, 闭包的第 0 点层号就 $\succ\tau$.** 所以 [LvCertNeg](LvCertNeg.lagda.md) 的否定的形状不依赖键的类型: 换键只有在 "$W$ 的闭包与外层闭包不同键" 时才能绕开, 而它们是同一个层号 $D$ 上的闭包 (判断).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvCertWorld where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)

open import OCF.Align.Level using (Ordᴵ; _<ᴵ_; _⊑ᴵ_; _≺ᴵ_; via; s⊑; ⊑ᴵ-trans; ≺ᴵ-irrefl; Simᴵ; zero; suc)
open import OCF.Align.Uniform3Base using (Flr; fz; fk; _⊔_; Ev; Bd; bound; liftEv)
import OCF.Align.UniformLvTree as T
open import OCF.Align.LvCertNeg using (Kin; kz; kl; kr; Bd-in)

record Worlds : Set₁ where
  field
    Key  : Set
    Fl   : Set
    Wd   : Set
    Evt  : Wd → Fl → Set
    tk   : Key → Ordᴵ → Fl
    _∪_  : Fl → Fl → Fl
    prj  : Key → Fl → Flr
    at   : Wd → Key → Ordᴵ
    upd  : Wd → Key → Ordᴵ → Wd
    Wok  : Wd → Set
    upd-ok : ∀ w k x → Wok w → zero <ᴵ x → Wok (upd w k x)
    toPrj : ∀ {w} k π → Evt w π → Ev (at w k) (prj k π)
    ofPrj : ∀ {w x} k π → Ev x (prj k π) → Evt w π → Evt (upd w k x) π
    selfVis : ∀ k τ → Kin τ (prj k (tk k τ))
    visL : ∀ k τ a b → Kin τ (prj k b) → Kin τ (prj k (a ∪ b))

worldℕ : Worlds
worldℕ = record
  { Key = ℕ ; Fl = T.Fᵗ ; Wd = ℕ → Ordᴵ ; Evt = T.Evt ; tk = T.tk ; _∪_ = T._∪_ ; prj = T.prj
  ; at = λ w k → w k ; upd = T.upd ; Wok = T.Wok ; upd-ok = T.upd-ok
  ; toPrj = λ k π e → T.toPrj k π e ; ofPrj = λ k π a e → T.ofPrj k π a e
  ; selfVis = self ; visL = λ k τ a b x → kr x }
  where
  self : ∀ k τ → Kin τ (T.prj k (T.tk k τ))
  self zero    τ = kz
  self (suc k) τ = self′ k τ
    where
    self′ : ∀ k τ → Kin τ (T.sel k k (fk τ))
    self′ zero τ = kz
    self′ (suc k) τ = self′ k τ

module Core (W : Worlds) where
  open Worlds W

  -- 同键的地板进界: 闭包的第 0 点层号 ⊒ 界 ⊒ τ+1
  noSame : ∀ {i ℓ} k π τ → Kin τ (prj k π) → (ev : Ev ℓ (prj k π ⊔ fk zero)) (p : i <ᴵ ℓ) (head : Ordᴵ) →
           Bd (bound (prj k π ⊔ fk zero) ev p) ⊑ᴵ head → suc τ ⊑ᴵ head
  noSame k π τ h ev p head b = ⊑ᴵ-trans (Bd-in (kl h) ev p) b

  -- 而第 0 点若与 τ 的展开相同, 就矛盾
  clash : ∀ {τ head} → suc τ ⊑ᴵ head → head ⊑ᴵ τ → ⊥
  clash x y with ⊑ᴵ-trans x y
  ... | s⊑ e q = ≺ᴵ-irrefl (via e q)
```
