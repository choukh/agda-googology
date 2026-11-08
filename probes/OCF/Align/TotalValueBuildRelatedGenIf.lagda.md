# 关系 marker 的遗传生成域

这是新的验收用域，不改已冻强域或原 Q、折叠、成品。
qi 只接原结构自相关坐标，qĉ 继续保留其原 Z 反馈相容字段。层内递归沿原 ◃，含极限的
self 分量；高度递归沿 HtB.Rec。因低谓词先已定义，回调前提中的
低 Gen 不是当前归纳类型的负出现。marker 同时要求低坐标在域内、
以及 body 自身的 Core 与 body 对原 ι 的 Rq 关系。
此替代接口允许随后以结构关系运输 marker，不借函数外延。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.TotalValueBuildRelatedGenIf (𝕊 : HtB) where
open import Data.Nat using (ℕ)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Free.Level
open import OCF.Free.Eq using (_≅ᶻ_; _≅ˢ_)
open import OCF.Free.Floor using (Flr)
open import OCF.Align.LadderOrdTree 𝕊
open import OCF.Align.LadderOrdRel 𝕊

GX : Ht → Set₁
GX m = ∀ {a φ χ} → Q m a φ χ → Set

module _ (m : Ht) (a : Ordᴵ)
  (GU : ∀ {k} → k ◃ a → ∀ {φ χ} → Q m k φ χ → Set)
  (GV : ∀ {n} → n <ᴸ m → GX n) where
  Core : ∀ {φ χ} → Q m a φ χ → Set
  Core q0 = ⊤
  Core (qs x) = Core x
  Core (ql f) = ∀ i → Core (f i)
  Core (qi ac f) = ∀ x → x ≅ˢ x → Core (f x)
  Core (qŝ c t g) = Core t × (∀ η e → Core (g η e))
  Core (qĉ c t g o h) = (t ≅ᶻ t) ×
    (∀ η e η′ e′ → η ≅ᴵ η′ → g η e ≅ᶻ g η′ e′) ×
    Core o × (∀ η e → Core (h η e))
  Core (qclo t g) = Core t × (∀ η → Core (g η))
  Core (qcl q ψ s t g) = Core t × (∀ η → Core (g η))
  Core (qwk le lc x) = Core x
  Core (qΩ↓ q fe ac h) = ∀ ξ ζ z → GV q (outV q z) → Core (h ξ ζ z)
  Core (qΩ fe r h) = ∀ ξ ζ z → GU (<→◃ r) (outU (<→◃ r) z) → Core (h ξ ζ z)
  Core (omk r z x) = GU (◃₁→◃ r) (outU (◃₁→◃ r) z) ×
    Core x × Rq m a a x (ι (◃₁→◃ r) (outU (◃₁→◃ r) z))

GAt : ∀ m (v : ∀ {n} → n <ᴸ m → GX n) a → ∀ {φ χ} → Q m a φ χ → Set
Low : ∀ m (v : ∀ {n} → n <ᴸ m → GX n) a {k} → k ◃ a → ∀ {φ χ} → Q m k φ χ → Set
GAt m v a x = Rq m a a x x × Core m a (Low m v a) v x
Low m v (suc k) zero x = GAt m v k x
Low m v (suc a) (suc r) x = Low m v a r x
Low m v (lim f s) (self i) x = GAt m v (f i) x
Low m v (lim f s) (lim i r) x = Low m v (f i) r x

GStep : ∀ m → (∀ {n} → n <ᴸ m → GX n) → GX m
GStep m v {a} x = GAt m v a x
GHeight : ∀ m {n} → n <ᴸ m → GX n
GHeight = Rec GX GStep
Gen : ∀ m a {φ χ} → Q m a φ χ → Set
Gen m = GAt m (GHeight m)

low-out : ∀ {m a k φ χ} (r : k ◃ a) {x : Q m k φ χ} →
  Low m (GHeight m) a r x → Gen m k x
low-out zero p = p
low-out (suc r) p = low-out r p
low-out (self i) p = p
low-out (lim i r) p = low-out r p

low-in : ∀ {m a k φ χ} (r : k ◃ a) {x : Q m k φ χ} →
  Gen m k x → Low m (GHeight m) a r x
low-in zero p = p
low-in (suc r) p = low-in r p
low-in (self i) p = p
low-in (lim i r) p = low-in r p

height-out : ∀ {m n a φ χ} (q : n <ᴸ m) {x : Q n a φ χ} → GHeight m q x → Gen n a x
height-out {m} q {x = x} p = subst (λ F → F x) (Rec-β GX GStep m q) p
height-in : ∀ {m n a φ χ} (q : n <ᴸ m) {x : Q n a φ χ} → Gen n a x → GHeight m q x
height-in {m} q {x = x} p = subst (λ F → F x) (sym (Rec-β GX GStep m q)) p
```
