# 当前 P 分量与 RecB 第一底的具体路径差别

当前 P 的第 c 分量高度是 1+c，RecB 第一底的第 c 分量高度是 c+1。
有限自然数上二者规约一致，不能据此把所有分量直接改标签接入 RecB.desc。
这里给合法极限坐标，并明确否定最直接的所需路径，不否定其它编码。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedDescentValuePath where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy using (LH; lz; ls; ll)
open import OCF.Lean.LHRecLay using (ΩL; upL; _⊕L_)

one c shifted entered : Cd
one = hs hz
c = hl (λ _ → one)
shifted = one ⊞ c
entered = hs (hs c)

legal-c : LgB c
legal-c = (λ n → hself) , (λ n → tt)
legal-shifted : LgB shifted
legal-shifted = Lg-⊞ one c tt legal-c
legal-entered : LgB entered
legal-entered = legal-c
original-position : c ⊲ entered
original-position = hsuc (hsuc hself)

depth : Cd → ℕ
depth hz = zero
depth (hs a) = suc (depth a)
depth (hl f) = depth (f zero)

no-one : ∀ {x} → x ⊲ one → x ≡ shifted → ⊥
no-one hself ()
no-one (hsuc hself) ()
no-c : ∀ {x} → x ⊲ c → x ≡ shifted → ⊥
no-c hself eq with cong depth eq
... | ()
no-c (hlim n p) eq = no-one p eq
no-shifted-c : shifted ⊲ c → ⊥
no-shifted-c p = no-c p refl
no-direct-height-position : shifted ⊲ entered → ⊥
no-direct-height-position (hsuc (hsuc p)) = no-shifted-c p

actual-component-height : ΩL lz ⊕L upL lz c ≡ ll (λ _ → ls (ls lz))
actual-component-height = refl
recb-component-height : upL lz (hs c) ≡ ls (ll (λ _ → ls lz))
recb-component-height = refl
```

路径失败发生在已有合法坐标与其实际后继进入界，不是任意不合法树样本。
RecB 的强度读法仍是判断；这个结果只排除上述直接高度路径复用。

局部修复确实可执行：保留独立的坐标公共界 B，将分量塔高度的公共界取
1+B，而不是沿用 RecB 的 B+1。下式已经由现有加法位置律给出；尚缺
指标回灌更新后这两类界的联动不变量。

```agda
shift-position : ∀ {a B : Cd} → a ⊲ B → (one ⊞ a) ⊲ (one ⊞ B)
shift-position = ⊞-⊲ one
shift-legal : ∀ B → LgB B → LgB (one ⊞ B)
shift-legal B l = Lg-⊞ one B tt l
```
