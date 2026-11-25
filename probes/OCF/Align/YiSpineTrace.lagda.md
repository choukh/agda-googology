# 实际可数基本列轨道上的 fsnc 比较调用

本篇是第 4 层诊断，可读记号；不写树侧 ψ，也不改已有定义。
`Reach` 从实际 EBO 塔的可数项开始，只沿前驱和 ω 基本列展开。
`FsnCall` 逐条记录 `EboLeanDef.fsn` 内部到 `fsnc` 的调用路径；
它不把共尾度计算或 `fsTc` 的其他比较混入。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiSpineTrace where

open import Data.Nat.Base using (ℕ)
open import Data.List.Base using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import OCF.Align.EboLeanDef
  using (T; ψ; sucT; pred; cof; c1; cω; cΩ; fsn; EBOψ;
         HC; h0; h1; hω; Cmp; lt; eq; gt; cmpᵀ; cofA; cofψ₊)
open import OCF.Align.EboLean3Tree using (hc-tower)

data Reach : T → Set where
  tower : ∀ k → Reach (EBOψ k)
  pred-step : ∀ {t} → Reach t → cof t ≡ c1 → Reach (pred t)
  fs-step : ∀ {t} → Reach t → cof t ≡ cω → ∀ n → Reach (fsn t n)

hc-pred : ∀ {t} → HC t → cof t ≡ c1 → HC (pred t)
hc-pred (h0 e) f with trans (sym e) f
... | ()
hc-pred (h1 e h) f = h
hc-pred (hω e h) f with trans (sym e) f
... | ()

hc-fsn : ∀ {t} → HC t → cof t ≡ cω → ∀ n → HC (fsn t n)
hc-fsn (h0 e) f n with trans (sym e) f
... | ()
hc-fsn (h1 e h) f n with trans (sym e) f
... | ()
hc-fsn (hω e h) f n = h n

reach-hc : ∀ {t} → Reach t → HC t
reach-hc (tower k) = hc-tower k
reach-hc (pred-step r e) = hc-pred (reach-hc r) e
reach-hc (fs-step r e n) = hc-fsn (reach-hc r) e n

data FsnCall : T → T → T → Set where
  hit : ∀ {u b ν} → cof b ≡ cΩ ν →
    FsnCall (ψ u b ∷ []) (sucT ν) u
  sum-tail : ∀ {x y ys left right} → FsnCall (y ∷ ys) left right →
    FsnCall (x ∷ y ∷ ys) left right
  arg-step : ∀ {u b left right} → cof b ≡ cω → FsnCall b left right →
    FsnCall (ψ u b ∷ []) left right
  index-step : ∀ {u left right} → cof u ≡ cω → FsnCall u left right →
    FsnCall (ψ u [] ∷ []) left right

record Actual (left right : T) : Set where
  constructor actual
  field
    source : T
    reached : Reach source
    countable-limit : cof source ≡ cω
    call : FsnCall source left right
open Actual public
```

这些规则精确反映外层 `fsn` 的内部递归：和进入尾部，ω 参数进入参数，
奇异 Ω 的 ω 下标进入下标；参数为 Ω 共尾时调用 `fsnc`。
这里无需保存 n：上述路由和该次比较的两个操作数不依赖 n。
`fsnc` 调用的 `fsT`、γ 链中没有再次调用 `EboLeanDef.fsnc`；
那些函数自身的其他比较不属于本篇集合。

## 每次实际 fsnc 比较都走 gt

父项为 ω 共尾时，`cofψ₊` 的 lt／eq 行都返回 Ω 共尾，故实际到达
`fsnc` 的那次比较只能是 gt。证明同时覆盖内部递归，不依赖有限搜索，
也不额外假定父码标准形。

```agda
route-gt : ∀ u ν m → cofψ₊ u ν m ≡ cω → m ≡ gt
route-gt u ν lt ()
route-gt u ν eq ()
route-gt u ν gt e = refl

call-gt : ∀ {t left right} → cof t ≡ cω → FsnCall t left right →
  cmpᵀ left right ≡ gt
call-gt e (hit {b = []} ())
call-gt e (hit {u} {b = b@(_ ∷ _)} {ν} eb) =
  route-gt u ν (cmpᵀ (sucT ν) u) (trans (sym (cong (cofA u) eb)) e)
call-gt e (sum-tail {y = y} {ys} r) = call-gt {t = y ∷ ys} e r
call-gt e (arg-step {b = b} eb r) = call-gt {t = b} eb r
call-gt e (index-step {u = u} eu r) = call-gt {t = u} eu r

actual-gt : ∀ {left right} → Actual left right → cmpᵀ left right ≡ gt
actual-gt a = call-gt {t = source a} (countable-limit a) (call a)

actual-hc : ∀ {left right} (a : Actual left right) → HC (source a)
actual-hc a = reach-hc (reached a)

-- 集合非空：实际塔项 ψ₀(Ω) 调用 fsnc，操作数为 1 与 0。
first-call : Actual (sucT []) []
first-call = actual (EBOψ 1) (tower 1) refl (hit {u = []} {ν = []} refl)
```

`actual-gt` 是码侧比较结论，不是 CP 可比性定理。
实际树侧解释及公共位置证据仍须另给；不能从码比较为 gt 推出树侧存在位置。
