# 当前 P 分量的原生坐标保真分类

不把 LH 分量强转成 CRw.Tw。Native c 是当前 P 真正使用的分量，
其零层已经是 step S⊥；先把 P 跨底降到 Native0，才能再降到 Cd。
分类中的坐标保持原类型，往返是字面等式，不借函数外延将 Same 变成相等。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedDescentValueBridge where
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy using (Lv; lz; ls)
open import OCF.Lean.LHRecLay using (_⊕L_; upL; ΩL)

Native : Cd → KS
Native c = Lv (ls lz ⊕L upL lz c)
Source : KS
Source = Lv (ΩL (ls lz))

-- 按实际分量高度分类，坐标to/fr无需搬运任何布劳威尔树。
data Class (c : Cd) (A : Set) : Set where
  base : (κ : K (Native hz)) →
    (to : E (Native hz) κ → A) (fr : A → E (Native hz) κ) →
    (∀ a → to (fr a) ≡ a) → (∀ e → fr (to e) ≡ e) → Class c A
  rank : (i : Cd) → hs i ⊲ c →
    (to : HB (Native i) → A) (fr : A → HB (Native i)) →
    (∀ a → to (fr a) ≡ a) → (∀ e → fr (to e) ≡ e) → Class c A

raise : ∀ {c d A} → c ⊲ d → Class c A → Class d A
raise p (base κ to fr a b) = base κ to fr a b
raise p (rank i q to fr a b) = rank i (⊲ᴮ-tr q p) to fr a b

classify : ∀ c κ → Class c (E (Native c) κ)
classify hz κ = base κ (λ e → e) (λ e → e) (λ e → refl) (λ e → refl)
classify (hs c) (inj₁ κ) = raise (hsuc hself) (classify c κ)
classify (hs c) (inj₂ _) = rank c hself (λ e → e) (λ e → e) (λ e → refl) (λ e → refl)
classify (hl f) (n , κ) = raise (hlim n hself) (classify (f n) κ)

-- 每个分量证据直指同一B；指标分量始终属于原生零层。
Position : Cd → K Source → Set
Position B (inj₁ _ , κ) = ⊤
Position B (inj₂ c , κ) = c ⊲ B

classify-source : ∀ B κ → Position B κ → Class B (E Source κ)
classify-source B (inj₁ _ , κ) p =
  base κ (λ e → e) (λ e → e) (λ e → refl) (λ e → refl)
classify-source B (inj₂ c , κ) p = raise p (classify c κ)

-- 留下的零层种类在任意目标Native t中都有显式坐标往返。
base-kind : ∀ t → K (Native hz) → K (Native t)
base-kind hz κ = κ
base-kind (hs t) κ = inj₁ (base-kind t κ)
base-kind (hl f) κ = 0 , base-kind (f 0) κ
base-to : ∀ t κ → E (Native hz) κ → E (Native t) (base-kind t κ)
base-to hz κ e = e
base-to (hs t) κ e = base-to t κ e
base-to (hl f) κ e = base-to (f 0) κ e
base-fr : ∀ t κ → E (Native t) (base-kind t κ) → E (Native hz) κ
base-fr hz κ e = e
base-fr (hs t) κ e = base-fr t κ e
base-fr (hl f) κ e = base-fr (f 0) κ e
base-frto : ∀ t κ e → base-fr t κ (base-to t κ e) ≡ e
base-frto hz κ e = refl
base-frto (hs t) κ e = base-frto t κ e
base-frto (hl f) κ e = base-frto (f 0) κ e
base-tofr : ∀ t κ e → base-to t κ (base-fr t κ e) ≡ e
base-tofr hz κ e = refl
base-tofr (hs t) κ e = base-tofr t κ e
base-tofr (hl f) κ e = base-tofr (f 0) κ e
```

Class 的 rank 路径是 hs i⊲B，实际跨底分类可与目标 t⊲B 在同一合法
B 下比较。所有 Class 实例由 classify-source 产生，没有任意分量相容前提。
下一步仍须写带动态 Position 的跨底运行器及实际输入路径证书；本篇没有
宣称现有 mixed 输出已经可以直接降到底。

## 留下 rank 时的实际目标坐标

路径来自同一公共界内的分类结果；沿已有 Ctx 直接得到保真坐标，不进行
整个 LH/CRw 树类型之间的重编码。

```agda
open import OCF.Lean.BoundedContextRun using (path-context)
open import OCF.Lean.LHRecLeg using (ek; toC; frC; frto)

along : ∀ {i t : Cd} → hs i ⊲ t → K (Native t)
along p = ek (path-context (ls lz) lz p) (inj₂ tt)
to-along : ∀ {i t : Cd} (p : hs i ⊲ t) → HB (Native i) → E (Native t) (along p)
to-along p = toC (path-context (ls lz) lz p) (inj₂ tt)
fr-along : ∀ {i t : Cd} (p : hs i ⊲ t) → E (Native t) (along p) → HB (Native i)
fr-along p = frC (path-context (ls lz) lz p) (inj₂ tt)
along-roundtrip : ∀ {i t : Cd} (p : hs i ⊲ t) c → fr-along p (to-along p c) ≡ c
along-roundtrip p = frto (path-context (ls lz) lz p) (inj₂ tt)
```
