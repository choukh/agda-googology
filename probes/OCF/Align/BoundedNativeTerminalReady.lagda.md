# 按实际采样世界验收末段折叠

末段初界为0，但递归回灌会更新界。Ready把证书与实际界b绑定：
既给当前位置证明所需的有界分支，也给回灌坐标c处的Ready c。
这是一项充分条件，不要求输入Ω在所有合法世界上同时单调。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedNativeTerminalReady where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (mul; top)
open import OCF.Lean.LHRecFl using (up-⊲)
import OCF.Lean.Fold1Fold as F
import OCF.Align.BoundedDescentValueBridgeTerminal as Last

U : KS
U = step S⊥

Ready : Cd → HB U → Set
Ready b hz = ⊤
Ready b (hs a) = Ready b a
Ready b (hl f) = (∀ n → f n ⊲[ (tt , b) ] f (suc n)) × (∀ n → Ready b (f n))
Ready b (hΩ (inj₁ ()) g)
Ready b (hΩ (inj₂ _) g) =
  (∀ {c d} → c ⊲ b → d ⊲ b → c ⊲ d → g c ⊲[ (tt , b) ] g d) ×
  (∀ c → c ⊲ b → Ready b (g c)) ×
  (∀ c → LgB c → Ready c (g c))

fold : Cd → HB U → Cd
fold b h = F.Φ (hs hz) tt hz (hsuc hself) (tt , b) h

position : ∀ b {a h} → Ready b h → a ⊲[ (tt , b) ] h → fold b a ⊲ fold b h
position b r hself = hself
position b r (hsuc p) = ⊲ᴮ-tr (position b r p) (hlim 0 hself)
position b (st , r) (hlim n p) = hlim n (position b (r n) p)
position b {h = hΩ (inj₁ ()) g} r (hLim e p)
position b {h = hΩ (inj₂ _) g} (mo , bounded , sampled) (hLim {c = c} e p) =
  ⊲ᴮ-tr (position b (bounded c e) p)
    (⊲ᴮ-tr (position b (bounded b hself) (mo e hself e)) (hlim 0 hself))

module Orbit (b : Cd) (g : Cd → HB U) where
  module C = F.Col _⊞_ _⊞_ (tt , b) b (λ W e → tt , e)
    (λ W e → fold (proj₂ W) (g e)) (λ W e → fold (proj₂ W) (g e))

  current : ∀ n → C.cw n ≡ (tt , C.ce n)
  current zero = refl
  current (suc n) = refl

mul-legal : ∀ (x : Cd) → LgB x → ∀ n → LgB (mul x n)
mul-legal x lx zero = lx
mul-legal x lx (suc n) = Lg-⊞ _ _ (mul-legal x lx n) lx

legal : ∀ b → LgB b → ∀ h → Ready b h → LgB (fold b h)
legal b lb hz r = tt
legal b lb (hs h) r =
  (λ n → ⊞-fst _ _) , (λ n → mul-legal _ (legal b lb h r) n)
legal b lb (hl f) (st , r) =
  (λ n → position b (r (suc n)) (st n)) , (λ n → legal b lb (f n) (r n))
legal b lb (hΩ (inj₁ ()) g) r
legal b lb (hΩ (inj₂ _) g) (mo , bounded , sampled) =
  (λ n → ⊞-fst _ _) , sums-legal
  where
  open Orbit b g
  coordinates-legal : ∀ n → LgB (C.ce n)
  outputs-legal : ∀ n → LgB (C.oo n)
  coordinates-legal zero = lb
  coordinates-legal (suc n) = Lg-⊞ _ _ (coordinates-legal n) (outputs-legal n)
  outputs-legal n rewrite current n =
    legal (C.ce n) (coordinates-legal n) (g (C.ce n))
      (sampled (C.ce n) (coordinates-legal n))
  sums-legal : ∀ n → LgB (C.oO n)
  sums-legal zero = outputs-legal zero
  sums-legal (suc n) = Lg-⊞ _ _ (sums-legal n) (outputs-legal (suc n))

terminal-legal : ∀ h → Ready hz h → LgB (Last.terminal h)
terminal-legal h r = legal hz tt h r

-- 根界0只有坐标0：免去根的全局分支单调，但保留所有真实采样义务。
root-ready : ∀ g → (∀ c → LgB c → Ready c (g c)) → Ready hz (hΩ (inj₂ tt) g)
root-ready g sampled =
  (λ { hself hself p → hself }) ,
  (λ { .hz hself → sampled hz tt }) , sampled

terminal-root-legal : ∀ g → (∀ c → LgB c → Ready c (g c)) →
  LgB (Last.terminal (hΩ (inj₂ tt) g))
terminal-root-legal g sampled = terminal-legal (hΩ (inj₂ tt) g) (root-ready g sampled)

up-ready : ∀ b c → LgB c → Ready b (up c)
up-ready b hz l = tt
up-ready b (hs c) l = up-ready b c l
up-ready b (hl f) (st , l) =
  (λ n → up-⊲ (st n)) , (λ n → up-ready b (f n) (l n))

top-ready : ∀ b → LgB b → Ready b (top (hs hz))
top-ready b lb =
  (λ bc bd p → up-⊲ p) ,
  (λ c bc → up-ready b c (lgB⊲ bc tt lb)) ,
  (λ c lc → up-ready c c lc)

actual-ready : Ready hz Last.actual-input
actual-ready = top-ready hz tt
```

根Ω只需在初界0内的单调；这个字段退化为自身关系。两个分支字段
的世界不同，不能只证明根Ready0就忽略采样界c。实际native-output
是否满足Ready仍须另证，本篇未预设该实例或任意输入保合法。
实际 top1 输入给出非恒定的可满足实例。root-ready 进一步把目标根界0
的义务归约为各合法采样c处的Ready c，不比较来自不同c的整棵输出。

直接接到已有下降闭项，剩余条件仍指向原始分支。

```agda
import OCF.Align.BoundedNativeFloor as Native

private
  branch-of : HB U → Cd → HB U
  branch-of (hΩ (inj₂ _) g) c = g c
  branch-of _ c = hz

native-branch : Cd → HB U
native-branch = branch-of Native.native-output

native-shape : Native.native-output ≡ hΩ (inj₂ tt) native-branch
native-shape = refl

native-countable-legal : (∀ c → LgB c → Ready c (native-branch c)) →
  LgB Native.countable-output
native-countable-legal sampled = terminal-root-legal native-branch sampled
```

native-shape 的 refl 核对了实际闭项确实走 root Ω 分支；未用 fallback
构造新的输入。native-countable-legal 尚无实际全部分支的实例，不能
把条件定理写成当前 countable-output 已合法。
