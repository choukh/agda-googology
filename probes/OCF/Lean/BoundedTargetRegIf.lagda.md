# 目标0的第1层反馈证书

先检验实际第二部分和所需字段，不把本证书冒充全有限层解法。
只增强将被消去的第1层新Ω：在固定合法坐标界1内，对全部底世界
保单调。P底种类不要求增强自身单调，只让其子树携带证书。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.BoundedTargetRegIf where
open import Data.Unit using (⊤)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.BoundedFoldIf using (T)

Base = T hz
Layer = T (hs hz)
one : HB Base
one = hs hz

SeedMono : (HB Base → HB Layer) → Set
SeedMono g = ∀ {W c d} → c ⊲[ W ] one → d ⊲[ W ] one → c ⊲[ W ] d →
  g c ⊲[ (W , one) ] g d

Reg : HB Layer → Set
Reg hz = ⊤
Reg (hs a) = Reg a
Reg (hl f) = ∀ n → Reg (f n)
Reg (hΩ (inj₁ κ) g) = ∀ c → Reg (g c)
Reg (hΩ (inj₂ _) g) = SeedMono g × (∀ c → Reg (g c))
```

两个被比较的坐标均带同一个字面界 one 的证据；one 无条件合法。
这里全raw分支字段仅针对本层目标0位置证明：低层P中的种类全被保留。
不将同一字段直接推广到更高被消去坐标层。合法性另外消费原始LgB，
Reg不代替它，也不预设Reg⇒LgB。
