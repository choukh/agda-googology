# 塔第 2、3 项的实际请求与根表检查
验收文件，不读记号；first2/first3 复用已核验的 YiMTHit 路径，记录两处实际格。
这些是具体实际格的见证，不是请求格的穷举；候选根表在任一零孩子格上都有条目。
源表继承底缺格见 YiFOBase；候选读回内部生成格见 YiFOInner，值问题另见 YiFOValue。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFOCells where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWPath using (self)
import OCF.Lean.YiMTHit as H
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiCWTable as CW

first2 : H.HitTw H.P₂ᶻ 2
first2 = H.hit-tw2ᶻ
first3 : H.HitTw H.P₂ᶻ 3
first3 = H.step H.P₂ᶻ 2 first2

isJ : {A : Set} → Maybe A → Bool
isJ (just _) = true
isJ nothing = false
candidate-zero : ∀ n (c : Tr (tw n)) → isJ (CW.tbᵗ n zero c) ≡ true
candidate-zero n zero = refl
candidate-zero n (suc c) = refl
candidate-zero n (lim f a) = refl
candidate-zero n (Ω p g) = refl
candidate-zero n (up x c y e) = refl
```
