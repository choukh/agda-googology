# 实际编码分支上的异层模拟接口

只观察原运行器实际使用的code坐标。Ω字段要求在两条反馈链的异坐标
上递归相关，而不是从Same推出任意分支函数同余。关系没有比较层号；
需要表示嵌入时，另带字面Ctx证据。sound是待构造结论，不是关系字段。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaEmbedIf where
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy using (LH; Lv)
open import OCF.Lean.LHRecLeg using (Ctx)
open import OCF.Lean.FrozenWorldLift using (Same)
open import OCF.Lean.GeneralOmegaConsumeIf using (code)

data Coded (x y : LH) : HB (Lv x) → HB (Lv y) → Set where
  cz : Coded x y hz hz
  cs : ∀ {a b} → Coded x y a b → Coded x y (hs a) (hs b)
  cl : ∀ {f g} → (∀ n → Coded x y (f n) (g n)) → Coded x y (hl f) (hl g)
  co : ∀ {κ κ′ f g} →
    (∀ {d e} → Same d e → Coded x y (f (code x κ d)) (g (code y κ′ e))) →
    Coded x y (hΩ κ f) (hΩ κ′ g)

record EmbeddedPair (x y : LH) (a : HB (Lv x)) (b : HB (Lv y)) : Set₁ where
  field
    context : Ctx (Lv y) (Lv x)
    branches : Coded x y a b
```

这个接口不要求所有raw树自相关；后续实际地板实例必须给branches。
尤其lΩ的层号函数未被假定保持Same，不能把此接口存在误报为全塔桥。
