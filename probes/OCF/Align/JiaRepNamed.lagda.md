# 第二轮的可数包作为关系实例

只在已经携码的输入上建立关系，不定义 raw 树到码的函数。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.JiaRepNamed where

open import Data.List.Base using ([])
open import OCF.Align.EboLean3Omega using (Acc′; acc)
open import OCF.Align.JiaBase using (Tree)
open import OCF.Align.JiaRep
open RelLayer using (rz; rs; rl)
import OCF.Align.JiaCountPack as C

tracks-rep : (a : Acc′ []) → ∀ {x c} → C.Tracks a c x → Rep a x c
tracks-rep (acc h) C.tz = rz
tracks-rep (acc h) (C.ts r) = rs (tracks-rep (acc h) r)
tracks-rep (acc h) (C.tl e r) = rl e (λ n → tracks-rep (acc h) (r n))

named-rep : ∀ {c} (a : Acc′ []) (x : C.Named c) → Rep a (C.erase a x) c
named-rep a x = tracks-rep a (C.erase-tracks a x)
```
