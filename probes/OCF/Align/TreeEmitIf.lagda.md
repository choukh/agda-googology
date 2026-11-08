# 对真实树侧闭项融合底输出：共享合同

本实验继承旧 Ladder 树作为输入数据，不修改旧定义。新解释器必须
逐 Q 构造直接生成 Z，并保留原非零目标的 chain／Ψ／ψᵠ 回调。
验收对同一实际输入逐点给 Pointwise，再由原轨道运输 Goodᴺ。
这不是将已算好的 V 包装为新闭项。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.TreeEmitIf (𝕊 : HtB) where

open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; toZ)
open import OCF.Free.Floor using (Ev; Flr; flo)
open import OCF.Free.Tree using (Fl)
open import OCF.Free.Eq using (_≅ˢ_)
open import OCF.Free.OrbitRewriteIf using (Pointwise)
open import OCF.Align.LadderOrdTree 𝕊

record EmitContract : Set where
  field
    emit : ∀ {m c φ χ w ℓ} → Ok w → Eh h₀ m w χ →
      Q m c φ χ → Ev ℓ φ → zero <ᴵ ℓ → Z
    sound : ∀ {m c φ χ w ℓ} (ok : Ok w) (e : Eh h₀ m w χ)
      (x : Q m c φ χ) (ev : Ev ℓ φ) (p : zero <ᴵ ℓ) →
      Pointwise (toZ (ψ̄ᵠ ok e x ev p)) (emit ok e x ev p)

-- 与本实验相邻但更强的候选律；不能由零参数 D-val 冒充。
record RawDownErase : Set where
  field
    erase : ∀ {n m k w} (r : n <ᴸ m) (ok : Ok w)
      (e₀ : Eh h₀ n w (κ Fl))
      (e₁ : Eh h₀ m w (cap (κ Fl) n (flo k)))
      (x : Q n k Fl (κ Fl)) (ev : Ev (suc zero) Fl) →
      ψ̄ᵠ ok e₀ x ev zero ≅ˢ ψ̄ᵠ ok e₁ (ι↓ {α = zero} r x) ev zero
```

第二个合同若有反例，只否定任意裸 Q 上的搬运删除，不否定原 Ω̇
实际生成域中的相容性。所有比较使用原世界和字面层路径。
