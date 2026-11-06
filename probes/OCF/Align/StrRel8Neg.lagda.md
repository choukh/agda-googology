# 结构关系, 第八轮: 左边 `nw` 的反例

> 入口见 [StrRel8](StrRel8.lagda.md). 编译反例: 由 $x\sqsubseteq^{+}x'$ **推不出** $\mathrm{nw}\,p\,x$ 与 $x'$ 在 `SemS` 下相关. 两边是同一形状的 `nκ` (每格的分支都是 `1`), 左边的树世界是 0, 右边是 1; 左边加一层 `nw` 抬到树世界 1. 运行世界两边都是 1, 路径都是 `self`, 状态都是空状态, 前提全部可满足. 左边的 `nκ` 从 0 走到 1, 第 0 格走过位置 0, 读数非零; 右边从 1 走到 1, 每格都是空走法, 读数全是 0.
>
> 范围: 推翻的是**不带前段对齐的** `nw` 规则 (左边单边的 `x ⊑ x′ ⇒ nw p x ⊑ x′`, 也包括两边的 `x ⊑ x′ ⇒ nw p x ⊑ nw p′ x′`, 取 $p'=$ `self`, 因为 `Run (nw self x′) q = Run x′ q`). 不推翻 "$\mathrm{nw}\,p\,x\sqsubseteq x$" (右边同一棵树、同一树世界): 那时右边也从 $V_0$ 出发.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel8Neg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Bool using (Bool; true; false; _∨_; T)
open import Data.Sum using (inj₁)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; z⊲; Lg; Tg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ⊲→≤)
open import OCF.Align.SumOneTree using (D; Dl; n0; n1; nκ; nw; sum; sum-fst; pt; drp; cnt; LW)
import OCF.Align.SumOneClosed as F
open import OCF.Align.KValSem using (ac₁)
open import OCF.Align.StrRel5Nest using (stepA)
open import OCF.Align.LayerTrOne using (one)
open import OCF.Align.StrRel4Walk using (aS)
open import OCF.Align.StrRel4Pr using (z0; vsᴾ)
open import OCF.Align.StrRel7Coh using (Y∅; ch∅)
open import OCF.Align.StrRel7Snd using (_⊑⁺_; κ⁺; n1⁺; SemS)
```

## 1 "非零" 沿 ≤ 上传

```agda
Nz : A → Set
Nz azero = ⊥
Nz (asuc _) = ⊤
Nz (alim f) = Σ ℕ (λ n → Nz (f n))

nzm : ∀ {a b} → a ≤ b → Nz a → Nz b
nzm z≤ ()
nzm (s≤ h) t = tt
nzm (≤l n h) t = n , nzm h t
nzm (l≤ h) (n , t) = nzm (h n) t

nzS : ∀ {W} {b} (x : D azero W) → Nz b → Nz (sum b x)
nzS {b = b} x = nzm (⊲→≤ (sum-fst b x))

-- 有限步的检查 (只用来给出具体的证据, 可靠性是定理)
chk : ℕ → A → Bool
chk k azero = false
chk k (asuc _) = true
chk zero (alim f) = false
chk (suc k) (alim f) = chk k (f 0) ∨ chk k (f 1)

chk-ok : ∀ k a → T (chk k a) → Nz a
chk-ok k (asuc a) t = tt
chk-ok (suc k) (alim f) t with chk k (f 0) | chk-ok k (f 0) | chk k (f 1) | chk-ok k (f 1)
... | true | h | _ | _ = 0 , h tt
... | false | _ | true | h = 1 , h tt

-- 路径是 self 时走法的输出是 0
data IsSelf {a : A} : ∀ {b} → a ⊲ b → Set where
  is : IsSelf (C.self {a})

wz : ∀ {ly W₀ V₁} {ac : F.AccY ly} {u : ∀ {c} → W₀ ⊲ c → Lg c → Dl ly c} {b a} {p : a ⊲ b} → IsSelf p →
     ∀ {ap : W₀ ⊲ a} {lb : Lg b} {bV : b ⊲ V₁} {lV : Lg V₁} {ll : LW ly V₁} {A₀ : F.Ig ly V₁} {co : Dl ly V₁} {Y : F.St V₁} {t}
       {τ : Tg t V₁} {lt : Lg t} → F.yc (F.Walk ac u b p ap lb bV lV ll A₀ co Y) τ lt ≡ n0
wz is = refl
```

## 2 反例

```agda
xL : D one azero
xL = nκ tt (λ _ _ → n1)

xR : D one one
xR = nκ tt (λ _ _ → n1)

hx : xL ⊑⁺ xR
hx = κ⁺ (λ _ _ _ _ _ → n1⁺)

-- 右边: 每格的路径都是 self, 所以每格读数都是 0
uR : ∀ {c} → one ⊲ c → Lg c → D one c
uR _ _ = n1

cR : ℕ → F.Cl one one (cnt one)
cR = F.κc ac₁ uR C.self tt C.self stepA n0 Y∅

d₀ : ∀ n → D azero (F.v (cR n))
d₀ n = F.yc (F.κΔ ac₁ uR C.self stepA (cR n)) (inj₁ (z⊲ (F.v (cR n)))) tt

isS : ∀ n → IsSelf (F.av (cR n))
q0 : ∀ n → d₀ n ≡ n0
isS zero = is
isS (suc n) = subst (λ x → IsSelf (sum-fst (F.v (cR n)) x)) (sym (q0 n)) is
q0 n = wz (isS n)

DR : ℕ → D azero one
DR n = drp (d₀ n)

pt0 : ∀ n → ¬ Nz (pt azero DR n)
pt0 zero = λ ()
pt0 (suc n) = subst (λ x → ¬ Nz (sum (pt azero DR n) (drp x))) (sym (q0 n)) (pt0 n)

¬nwˡ : ¬ SemS (nw (C.suc C.self) xL) xR
¬nwˡ s = noR (nzm (vsᴾ h (z≤ {azero})) yesL)
  where
  τ = inj₁ (z⊲ one)
  h = s tt tt C.self C.self (≤-refl one) C.self C.self (aS C.self tt) n0 n0 Y∅ Y∅ ch∅ ((λ _ _ → z0) , z0) τ τ
  yesL : Nz (sum azero (F.yc (F.Run ac₁ (nw (C.suc C.self) xL) C.self tt C.self stepA n0 Y∅) τ tt))
  yesL = chk-ok 6 _ tt
  noR : ¬ Nz (sum azero (F.yc (F.Run ac₁ xR C.self tt C.self stepA n0 Y∅) τ tt))
  noR (n , t) = pt0 n t
```
