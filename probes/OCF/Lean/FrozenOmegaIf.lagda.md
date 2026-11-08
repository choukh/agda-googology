# 固定公共世界中的 Ω 层分类接口

接口定稿 2026-11-06。与 Third 的区别：把每个节点的可入位置证据
放进种类本身，而不是在原始树上后验地证明路径。坐标类型不改，
故分支必须对所有原始坐标返回受限树；这可能排除原地板，不能隐瞒。
与 LvOm 的共同限制是固定外层世界，本文件不宣称已经解决外层增长。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.FrozenOmegaIf where
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdIf using (Tw; Pos)

SafeTw : (U : KS) → Wd U → HB U → KS
SafeTw U w m = record
  { K = Σ (K (Tw U m)) (Pos U w m)
  ; E = λ κ → E (Tw U m) (proj₁ κ)
  ; Wd = Wd (Tw U m) ; LgW = LgW (Tw U m)
  ; _≤w_ = _≤w_ (Tw U m) ; ≤w-tr = ≤w-tr (Tw U m)
  ; Bd = λ κ → Bd (Tw U m) (proj₁ κ)
  ; Pr = λ κ → Pr (Tw U m) (proj₁ κ)
  ; Bd↑ = λ {κ} q b → Bd↑ (Tw U m) {κ = proj₁ κ} q b
  ; cmpK = λ {κ} b b′ l → cmpK (Tw U m) {κ = proj₁ κ} b b′ l
  ; bot = λ κ → bot (Tw U m) (proj₁ κ)
  ; botBd = λ κ v → botBd (Tw U m) (proj₁ κ) v }

erase : ∀ {U w m} → HB (SafeTw U w m) → HB (Tw U m)
erase hz = hz
erase (hs a) = hs (erase a)
erase (hl f) = hl (λ n → erase (f n))
erase (hΩ (κ , p) g) = hΩ κ (λ c → erase (g c))

record Direct (U : KS) (w : Wd U) (lw : LgW U w)
              (m : HB U) (lm : LgB m) : Set₁ where
  field
    fold : ∀ t → t ⊲[ w ] m → HB (SafeTw U w m) → HB (SafeTw U w t)
```

`Direct` 尚不预设输出合法、值或内部 View；必须另证。每一目标与输入
层都带同一合法公共界 m。原 `Tw` 的定义受记号启发，本实验没有新增
层号构造子。种类限制来自已编译的位置否定与反变坐标失败，而非值验收。
