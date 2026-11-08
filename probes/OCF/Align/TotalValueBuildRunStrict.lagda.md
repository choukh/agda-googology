# 新 run 的真实纯输出保持严格层号

这里不宣称所有 Z 输出严格。输入是原 typed 严格树与纯读取关系；
每个极限的后项正性由旧严格步进给出，再由已证 pure-lower 搬到实际
新运行。累计和以其前项加后项的一个实际前驱作严格隔点，不需要假设新坐标序列严格。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TotalValueBuildRunStrict where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Ordˢ; toZ)
open import OCF.Align.OrdLabZPrefix using (_~_; z~; s~; l~; lᵢ~; upˡ; upʳ)
open import OCF.Align.TotalValueBuildStrict using (SV; svz; svs; svl)
open import OCF.Align.TotalValueBuildStrictBase using (St; stz; sts; stl)
open import OCF.Align.TotalValuePureLower using (pure-lower)
open import OCF.Align.ValueJudgeBase using (_≼_; s≼s; ≼l; z≼; ≼-trans)
import OCF.Free.TotalOrbitRun as R
import OCF.Free.TotalOrbitBuild as A

positive : ∀ {a} → suc (zero {ℓ = zero}) ≼ A.read a → Σ Ordᴵ (λ b → b ≺ᴵ a)
positive {suc a} (s≼s h) = a , via (≅ᴵ-refl a) zero
positive {lim f s} (≼l n h) with positive {f n} h
... | b , via e q = b , via e (lim n q)

add-prec : ∀ a {b c} → b ≺ᴵ c → R.add a b ≺ᴵ R.add a c
add-prec a (via e q) = via (R.add-cong a e) (R.add-path a q)

add-sv : ∀ {a b} → SV a → SV b → SV (R.add a b)
add-sv a svz = a
add-sv a (svs b) = svs (add-sv a b)
add-sv {a = a} da (svl db st) = svl (λ n → add-sv da (db n))
  (λ n → R.add a (proj₁ (st n)) , add-prec a (proj₁ (proj₂ (st n))) ,
    R.add-mono a (proj₂ (proj₂ (st n))))

sum-sv : ∀ f → (∀ n → SV (f n)) → ∀ n → SV (R.sum f n)
sum-sv f d zero = d zero
sum-sv f d (suc n) = add-sv (sum-sv f d n) (d (suc n))

complete-sv : ∀ f → (∀ n → SV (f n)) →
  (∀ n → Σ Ordᴵ (λ b → b ≺ᴵ f (suc n))) → SV (R.complete f)
complete-sv f d pos = svl (sum-sv f d)
  (λ n → R.add (R.sum f n) (proj₁ (pos n)) ,
    add-prec (R.sum f n) (proj₂ (pos n)) , R.prefix (R.sum f n) (proj₁ (pos n)))

pure-strict : ∀ {x : Ordˢ zero} {y : Ordᶜ zero} →
  St y → x ~ y → SV (R.run (toZ x))
pure-strict stz z~ = svz
pure-strict (sts s) (s~ p) = svs (pure-strict s p)
pure-strict (stl d step) (l~ {f = f} p) =
  complete-sv (λ n → R.run (toZ (f n))) (λ n → pure-strict (d n) (p n))
    (λ n → positive (≼-trans (s≼s z≼) (≼-trans (step n) (pure-lower (p (suc n))))))
```
