# 升界只剩一种? 否定一路 (四): `OwnFam` 的条件实例

> 不含记号. 入口 [NegRsOwn](NegRsOwn.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP.
>
> 接口 `RsOwnIf.PW.OwnFam` 在 `K₁` 的底拷贝族 `κ₁ f` 上 (下标 `inj₂ (jx f)` 含函数): 给 `DecJ` (`NegRsOwnPre`), 就有实例 `decJ→OwnFam` (rs 逐分量, 只看该分量的旧世界, 精确置自己, 别处不动). 所以对 `OwnFam` 不可能有 "⇒ ⊥" 的定理 (元层判断: `DecJ` 经典地成立, 经典逻辑与 MLTT 相容); 能指望的只有 "⇒ 分离子/WLPO", 本路**未走通** (断点见 `NegRsOwnPre` §4). 同一个实例也满足 `Keep` (`decJ→keepFam`), 与 `keepFam-sep` 相容: `DecJ` 本身推出分离子 (`decJ→sep`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegRsOwnFam where

open import Data.Nat using (ℕ)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (H₀)
open import OCF.Align.LvKtIf using (FN)
open import OCF.Align.NegGenFoldUpd using (jx)
open import OCF.Align.NegKindLvRaise using (tp₁)
open import OCF.Align.NegRsOwnPre using (DecJ; module WithDecJ)
open import OCF.Align.NegRsOwnShape using (decJ→RsK)
open import OCF.Align.RsOwnIf

open PW (⊤ ⊎ H₀) (FN S₀)

decJ→OwnFam : DecJ → OwnFam tp₁ (ℕ → H₀) (λ f → inj₂ (jx f)) (λ f → (0 , tt))
decJ→OwnFam D = record
  { R = decJ→RsK D
  ; vi = λ f → record
      { Φ = λ { (inj₁ tt) x v → x ; (inj₂ c) x v → pick (isJ c f) c x v }
      ; rs≡ = λ { w v (inj₁ tt) → refl ; w v (inj₂ c) → refl } } }
  where
  open DecJ D
  open WithDecJ D
```

## 结论 (按档)

- **[定理, 条件 `DecJ`]** **`decJ→OwnFam`**. 合读 `NegRsOwnPre.ownB₁-sep`: `OwnFam` 再加 "别处无条件只增" 就推出分离子; `OwnFam` 本身未否定.
