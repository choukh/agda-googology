# 从 LevelNoKTree 生成 NoKCertTree: 只取折叠 (module Fold 到文件末), 改 owk 一行
s=open('LevelNoKTree.lagda.md',encoding='utf8').read()
a=s.index("module Fold (c : LG)")
b=s.index("-- ψ_n(Ω_L): 任何带证书的层号")
body=s[a:b]
old="  ψ E T st (owk w x) = ψ E T (λ m → st (w m)) x\n"
assert old in body
new="  ψ E T st (owk {π = π′} w x) with lowerSt π′ (cov-exact w) st\n  ... | σ , st′ , cv₁ = ocv cv₁ (ψ E T st′ x)\n"
body=body.replace(old,new)
body=body.replace("module Fold (c : LG)","module FoldO (c : LG)")
hdr='''# 折叠: `owk` 也收窄输出

> 不含记号. 结论写在 [NoKCert](NoKCert.lagda.md). 由 [LevelNoKTree](LevelNoKTree.lagda.md) 的折叠用脚本取来 (`module Fold` 到文件末), **只差一行**: `owk` 收窄输入的同时也收窄输出的地板, 与 `ocv` 同一行. 这是 [GuardBridgeTree](GuardBridgeTree.lagda.md) 的 `T₀′` 的同一处改法, 那里由测试逼出: 否则过两遍折叠后保留的闭包读到不依赖的外层帧. 数据树 `O`, `ι`, `Ω̇`, `Sel` 之前的都不动, 类型也不动.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LevelNoKX using (XU)

module OCF.Align.NoKCertTree (X : XU) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ; module Trich)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc)
open import OCF.Align.LevelNoKLv
open XU X
open Lv 𝔻
open import OCF.Align.LevelNoKTab 𝔻 using (kdec; Dec′; _⊙_; adm⊙; toCp; admTo; Strict; st-suc; st-lim; st-fst; st-bra; stCp; st⊙)
open import OCF.Align.LevelNoKBase X
open import OCF.Align.LevelNoKTree X hiding (module Fold; Tn)

'''
tail='''
-- ψ_n(Ω_L)
Tn : (L : LG) → Cfˢ L → Tc L → (n : ℕ) → O (natL n) tz
Tn L (w , s) tc n = FoldO.ψ L w s tc ∅ (FoldO.tn n) (λ ()) (Ω̇ L tc)
```
'''
open('NoKCertTree.lagda.md','w',encoding='utf8').write(hdr+body+tail)
