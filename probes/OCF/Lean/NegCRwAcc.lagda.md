# C 线重写成一个折叠, 否定一路 (一): 形状证书与 ℕ-极限子句的两难

> 不含记号. 入口 [NegCRw](NegCRw.lagda.md). 本篇**不依赖**构造一路 CRw 的接口. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **问题.** C 线的三段折叠 (`TySupFold.Φ`, `PathOutFold.Ψ`, `X1UpFold.ΦU`) 的 ℕ-极限子句都是部分和 (累加, `Σ⁺`), 证书都是 "由形状给出, 对一切输入" (`Sh-Φ`, `Sh-Ψ`). 作者本轮要求把三段重写成一个对层号递归的折叠. 本篇问: 重写后是否仍逃不开累加. 写成定理的部分是一个两难:
>
> 1. **`AccNM.acc-not-mono` (定理, 对一切种类结构, 只看三个值).** 任何 "$0\mapsto1$, $1\mapsto\hat\omega$, ℕ-极限取部分和" 的折叠, 在合法输入 $\lim(0,1,1,\dots)$ 上不保第一位置: $1\lhd\lim(0,1,1,\dots)$, 但 $F\,1\not\lhd F\lim(0,1,1,\dots)$. 只要求三条字面等式 (逐点, 不要外延), 所以对一切这样写的折叠成立. 实例: C 线三段折叠 `TySupFold.Φ` (对一切 `R`), **`PathOutFold.Ψ` (对一切 `P`, 本篇新增)**, `X1UpFold.ΦU` (对一切 `U`) (§3, `Φ-acc`, `Ψ-acc`, `ΦU-acc`). 前两条与 `NegTySupMono.Φ-not-mono`, `NegX1UpInst.ΦU-not-mono` 同, 这里换成只看三个值的陈述, 构造一路的新折叠只要满足三条 `refl` 就能直接套用.
> 2. **`shape-cocone→chain` (定理, 对一切种类结构).** 若折叠 $F$ 的输出对**一切**输入合法 (形状证书, `LgB`), 且每个 ℕ-极限的每一项的像都是极限的像的第一位置 (余锥性, `Cocone`), 则 $F$ 的像两两字面可比 (在一个合法世界里). 推论 **`pt-shape→chain`**: 逐点的 ℕ-极限子句 ($F(\lim f)=\lim(F\circ f)$) 满足余锥性.
> 3. **`fab3-no-shape` (定理, 实例).** [Fab3Typed](../Align/Fab3Typed.lagda.md) 的 `Ψ` 是逐点的 (`refl`), 它的像不两两可比 ($\lim(1,1,\dots)$ 与 $\lim(\hat\omega,\hat\omega,\dots)$ 互不为第一位置, `fab3-incomp`), 所以它**没有**形状证书: 存在输入使输出不合法. 这与 Fab3Typed 的做法一致: 它的证书读输入的合法 (`Ψ-lg`), 靠单调 (`Ψ-mono`).
>
> **两难 (定理的合取, 只对这两种子句).** 部分和满足形状证书但不保第一位置 (1); 逐点满足余锥性, 有不可比的像就没有形状证书 (2, 3). 所以若 CRw 的折叠保留 "证书由形状给出, 对一切输入", 它的 ℕ-极限子句不能是逐点的; 若写成部分和, 它不单调, 中间层留下的结点不满足 `LgB` (同 `NegTySupC.kept-not-LgB-ICd`). 不累加的出路是让证书读输入合法并证单调 (Fab3Typed 在后继层的塔上做到了; sup 层与 `lΩ` 层号上未写).
>
> **前提实例.** 1: 输入 $\lim(0,1,1,\dots)$ 合法 (`NegTySupMono.NotMono.Lg-hI`), $1\lhd$ 它 (`one⊲hI`); 三条等式在 C 线三段折叠上都是 `refl` (§3). 2: 合法世界存在 (例如 `S⊥` 的 `tt`); 余锥性对逐点子句成立 (`pt→cocone`). 3: Fab3Typed 的 `Ψ` 在 `S⊥` 上, 世界 `(tt , hz)`.
>
> **只否定什么.** 只否定: (a) 部分和子句的折叠保字面第一位置; (b) 逐点子句的折叠 (像不两两可比时) 有对一切输入的形状证书. **不否定**: 证书读输入合法时的逐点折叠 (Fab3Typed 就是这样, 单调与合法都是定理); ℕ-极限的其他写法 (既不逐点, 也不是部分和, 例如只对合法输入定义的折叠, 或输出带别的形状的); "剩下的只有这两种写法" 是**判断**, 不是定理. 本篇没有关闭任何路线, 没有值的结论.
>
> **对纲领与目标.** 纲领 1, 2 不受影响 (都是对合法项的陈述). 目标 "让树自足" 的判据 "有树侧的合法性标准": 1 说部分和的折叠在中间层不保树自己的第一位置; 2 说要保第一位置 (余锥性) 又不读输入合法, 只有像退化成一条链才行. 所以 "去掉累加" 与 "证书只看形状" 二者不可兼得 (对这两种子句). 这条是摆脱侧的信息: 它指出 C 线的累加是由 "证书只看形状" 逼出的, 不是由记号逼出的.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegCRwAcc where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy using (S⊥)
```

## §0 有限树与几条字面事实

```agda
module _ {S : KS} where
  num : ℕ → HB S
  num zero = hz
  num (suc n) = hs (num n)

  at : HB S → ℕ → HB S
  at (hl f) n = f n
  at x n = x

  -- 有限树下面没有 ℕ-极限
  lim-not-fin : ∀ {w} {f : ℕ → HB S} k → ¬ (hl f ⊲[ w ] num k)
  lim-not-fin zero ()
  lim-not-fin (suc k) (hsuc p) = lim-not-fin k p

  -- 剥掉右边的有限尾巴 (左边是 ℕ-极限)
  strip : ∀ {w} {f : ℕ → HB S} k {y : HB S} → hl f ⊲[ w ] y ⊞ num k → hl f ⊲[ w ] y
  strip zero p = p
  strip (suc k) (hsuc p) = strip k p

  hs≢hz : ∀ {x : HB S} → ¬ (hs x ≡ hz)
  hs≢hz ()

  hl≢hz : ∀ {f : ℕ → HB S} → ¬ (hl f ≡ hz)
  hl≢hz ()

  hs≢hl : ∀ {x : HB S} {f : ℕ → HB S} → ¬ (hs x ≡ hl f)
  hs≢hl ()

  hs-inj : ∀ {x y : HB S} → hs x ≡ hs y → x ≡ y
  hs-inj refl = refl
```

## §1 部分和的折叠不保第一位置 (只看三个值)

`fI`: $\lim(0,1,1,\dots)$ 的项. 三个值: $a_0$ ("$F\,0$"), $a_1$ ("$F\,1$"), $a_L$ ("$F\lim(0,1,1,\dots)$"). 假设: $a_0=1$; $a_1=\lim M$, $M\,n=n+1$; $a_L=\lim G$, $G\,0=a_0$, $G\,(n+1)=G\,n\boxplus a_1$ (部分和). 结论: $a_1\not\lhd a_L$ (任一世界).

```agda
fI : ∀ {S : KS} → ℕ → HB S
fI zero = hz
fI (suc n) = hs hz

module AccNM {S′ : KS} (a₀ a₁ aL : HB S′) (M G : ℕ → HB S′)
  (e₀ : a₀ ≡ num 1) (e₁ : a₁ ≡ hl M) (eM : ∀ n → M n ≡ num (suc n))
  (eL : aL ≡ hl G) (G0 : G 0 ≡ a₀) (Gs : ∀ n → G (suc n) ≡ G n ⊞ a₁) where

  -- G (m+1) 字面是 lim (λ n → G m ⊞ M n)
  Gs′ : ∀ m → G (suc m) ≡ hl (λ n → G m ⊞ M n)
  Gs′ m = subst (λ z → G (suc m) ≡ G m ⊞ z) e₁ (Gs m)

  G≢hz : ∀ m → ¬ (G m ≡ hz)
  G≢hz zero e = hs≢hz (trans (sym (trans G0 e₀)) e)
  G≢hz (suc m) e = hl≢hz (trans (sym (Gs′ m)) e)

  notG : ∀ {w} m → ¬ (hl M ⊲[ w ] G m)
  notG {w} zero p = lim-not-fin 1 (subst (λ z → hl M ⊲[ w ] z) (trans G0 e₀) p)
  notG {w} (suc m) p = go (subst (λ z → hl M ⊲[ w ] z) (Gs′ m) p) refl refl
    where
    go : ∀ {a b} → a ⊲[ w ] b → a ≡ hl M → b ≡ hl (λ n → G m ⊞ M n) → ⊥
    go hself ea eb =
      G≢hz m (sym (hs-inj (trans (sym (eM 0)) (trans (cong (λ h → at h 0) (trans (sym ea) eb))
                                                     (cong (λ z → G m ⊞ z) (eM 0))))))
    go (hsuc p) ea eb = hs≢hl eb
    go {a} (hlim n q) ea eb =
      notG m (strip (suc n) (subst (λ z → hl M ⊲[ w ] G m ⊞ z) (eM n)
               (subst (λ z → z ⊲[ w ] G m ⊞ M n) ea (subst (λ z → a ⊲[ w ] z) (cong (λ h → at h n) eb) q))))
    go (hLim e q) ea ()

  acc-not-mono : ∀ {w} → ¬ (a₁ ⊲[ w ] aL)
  acc-not-mono {w} p = go (subst (λ z → z ⊲[ w ] hl G) e₁ (subst (λ z → a₁ ⊲[ w ] z) eL p)) refl refl
    where
    two≢ : ∀ {f : ℕ → HB S′} → ¬ (num {S′} 2 ≡ hl f)
    two≢ ()
    go : ∀ {a b} → a ⊲[ w ] b → a ≡ hl M → b ≡ hl G → ⊥
    go hself ea eb =
      two≢ (trans (sym (eM 1)) (trans (cong (λ h → at h 1) (trans (sym ea) eb))
              (trans (Gs 0) (cong (λ z → G 0 ⊞ z) e₁))))
    go (hsuc p) ea eb = hs≢hl eb
    go {a} (hlim m q) ea eb =
      notG m (subst (λ z → z ⊲[ w ] G m) ea (subst (λ z → a ⊲[ w ] z) (cong (λ h → at h m) eb) q))
    go (hLim e q) ea ()
```

输入一侧: $\lim(0,1,1,\dots)$ 合法, $1$ 是它的第一位置 (对一切种类结构, 一切世界).

```agda
module _ {S : KS} where
  Lg-fI : LgB {S} (hl fI)
  Lg-fI = st , lg
    where
    st : ∀ {w} n → fI n ⊲[ w ] fI (suc n)
    st zero = hsuc hself
    st (suc n) = hself
    lg : ∀ n → LgB {S} (fI n)
    lg zero = tt
    lg (suc n) = tt

  one⊲fI : ∀ {w} → hs hz ⊲[ w ] hl (fI {S})
  one⊲fI = hlim 1 hself
```

## §2 形状证书加余锥性推出像是一条链

`Cocone F w`: 每个 ℕ-极限的每一项的像都是极限的像的第一位置 (在世界 $w$ 里). 对一切输入 (不只合法的).

```agda
module _ {S S′ : KS} (F : HB S → HB S′) where
  Cocone : Wd S′ → Set
  Cocone w = ∀ (f : ℕ → HB S) n → F (f n) ⊲[ w ] F (hl f)

  two : HB S → HB S → ℕ → HB S
  two u v zero = u
  two u v (suc n) = v

  shape-cocone→chain : ∀ {w} → LgW S′ w → (∀ h → LgB (F h)) → Cocone w →
                       ∀ u v → (F v ⊲[ w ] F u) ⊎ (F u ⊲[ w ] F v)
  shape-cocone→chain lw shp coc u v = cmpB (coc (two u v) 0) (coc (two u v) 1) lw (shp (hl (two u v)))

  -- 逐点的 ℕ-极限子句满足余锥性
  pt→cocone : (∀ f → F (hl f) ≡ hl (λ n → F (f n))) → ∀ {w} → Cocone w
  pt→cocone pt {w} f n = subst (λ z → F (f n) ⊲[ w ] z) (sym (pt f)) (hlim n hself)

  pt-shape→chain : (∀ f → F (hl f) ≡ hl (λ n → F (f n))) → ∀ {w} → LgW S′ w → (∀ h → LgB (F h)) →
                   ∀ u v → (F v ⊲[ w ] F u) ⊎ (F u ⊲[ w ] F v)
  pt-shape→chain pt lw shp = shape-cocone→chain lw shp (pt→cocone pt)
```

### 实例: Fab3Typed 的 `Ψ` 逐点, 像不是链, 所以没有形状证书

`Ψ` 取 `Fab3Typed.Fold S⊥`, 世界 $(\mathrm{tt}, 0)$. $\Psi\lim(0,0,\dots)=\lim(1,1,\dots)$, $\Psi\lim(1,1,\dots)=\lim(\hat\omega,\hat\omega,\dots)$, 互不为第一位置.

```agda
import OCF.Align.Fab3Typed as F3
module P3 = F3.Fold S⊥

W₀ : Wd (step S⊥)
W₀ = tt , hz

Ψ₀ : HB (step S⊥) → HB S⊥
Ψ₀ = P3.Ψ W₀

Ψ-pt : ∀ f → Ψ₀ (hl f) ≡ hl (λ n → Ψ₀ (f n))
Ψ-pt f = refl

u₀ v₀ : HB (step S⊥)
u₀ = hl (λ _ → hz)
v₀ = hl (λ _ → hs hz)

mul1 : ∀ n → P3.mul (hs hz) n ≡ num (suc n)
mul1 zero = refl
mul1 (suc n) = cong hs (mul1 n)

-- lim(ω̂, ω̂, …) 不在 lim(1, 1, …) 下面
inc₁ : ¬ (Ψ₀ v₀ ⊲[ tt ] Ψ₀ u₀)
inc₁ p = go p refl refl
  where
  go : ∀ {a b} → a ⊲[ tt ] b → a ≡ Ψ₀ v₀ → b ≡ Ψ₀ u₀ → ⊥
  go hself ea eb = hs≢hl (sym (cong (λ h → at h 0) (trans (sym ea) eb)))
  go (hsuc p) ea ()
  go {a} (hlim n q) ea eb = lim-not-fin 1 (subst (λ z → z ⊲[ tt ] num 1) ea (subst (λ z → a ⊲[ tt ] z) (cong (λ h → at h n) eb) q))
  go (hLim {κ = ()} e q) ea eb

-- lim(1, 1, …) 不在 lim(ω̂, ω̂, …) 下面
inc₂ : ¬ (Ψ₀ u₀ ⊲[ tt ] Ψ₀ v₀)
inc₂ p = go p refl refl
  where
  hlM : ∀ {a} → a ⊲[ tt ] hl (P3.mul (hs hz)) → a ≡ Ψ₀ u₀ → ⊥
  hlM hself ea = hs≢hz (hs-inj (cong (λ h → at h 1) ea))
  hlM {a} (hlim k r) ea = lim-not-fin (suc k) (subst (λ z → z ⊲[ tt ] num (suc k)) ea (subst (λ z → a ⊲[ tt ] z) (mul1 k) r))
  go : ∀ {a b} → a ⊲[ tt ] b → a ≡ Ψ₀ u₀ → b ≡ Ψ₀ v₀ → ⊥
  go hself ea eb = hs≢hl (cong (λ h → at h 0) (trans (sym ea) eb))
  go (hsuc p) ea ()
  go {a} (hlim n q) ea eb = hlM (subst (λ z → a ⊲[ tt ] z) (cong (λ h → at h n) eb) q) ea
  go (hLim {κ = ()} e q) ea eb

fab3-incomp : ¬ ((Ψ₀ v₀ ⊲[ tt ] Ψ₀ u₀) ⊎ (Ψ₀ u₀ ⊲[ tt ] Ψ₀ v₀))
fab3-incomp (inj₁ p) = inc₁ p
fab3-incomp (inj₂ p) = inc₂ p

fab3-no-shape : ¬ (∀ h → LgB (Ψ₀ h))
fab3-no-shape shp = fab3-incomp (pt-shape→chain Ψ₀ Ψ-pt {w = tt} tt shp u₀ v₀)
```

## §3 C 线三段折叠都是部分和 (实例)

三条等式都是 `refl` (加 `mul1` 一类的数值等式). 可达性要写成 `acc rs` 才归约.

```agda
open import OCF.Align.TySupIf using (TySupIf; module TySupIf; AccR; acc)
import OCF.Align.TySupFold as TF

module _ (R : TySupIf) where
  open TySupIf R
  open TF R using (Φ; mul; Σ⁺)

  mulR : ∀ {S : KS} n → mul {S} (hs hz) n ≡ num (suc n)
  mulR zero = refl
  mulR (suc n) = cong hs (mulR n)

  Φ-acc : ∀ X rs lX t pt b {w : Wd (L t)} →
          ¬ (Φ X (acc rs) lX t pt b (hs hz) ⊲[ w ] Φ X (acc rs) lX t pt b (hl fI))
  Φ-acc X rs lX t pt b =
    AccNM.acc-not-mono _ _ _ (mul (hs hz)) (Σ⁺ (λ n → Φ X (acc rs) lX t pt b (fI n)))
      refl refl mulR refl refl (λ n → refl)

open import OCF.Align.PathOutIf using (PathOutIf; module PathOutIf)
import OCF.Align.PathOutFold as PF

module _ (P : PathOutIf) where
  open PathOutIf P
  open TySupIf R using (L)
  open PF P using (PH; Ψ)
  open TF R using (mul; Σ⁺)

  phI : ∀ W n → PH W (fI n)
  phI W zero = tt
  phI W (suc n) = tt

  Ψ-acc : ∀ W lW t pt b {w : Wd (L t)} →
          ¬ (Ψ W lW t pt b (hs hz) tt ⊲[ w ] Ψ W lW t pt b (hl fI) (phI W))
  Ψ-acc W lW t pt b =
    AccNM.acc-not-mono _ _ _ (mul (hs hz)) (Σ⁺ (λ n → Ψ W lW t pt b (fI n) (phI W n)))
      refl refl (mulR R) refl refl (λ n → refl)

open import OCF.Align.X1UpIf using (X1UpIf)
open import OCF.Align.TySupC using (_⊏ᶜ_)
open import OCF.Align.TySupSum using (ICdΣ)
import OCF.Align.X1UpFold as UF

module _ (U : X1UpIf) where
  open UF U using (LS; ΦU)
  open TF ICdΣ using (mul; Σ⁺)

  ΦU-acc : ∀ m rs lm t pt b {w : Wd (LS t)} →
           ¬ (ΦU m (acc rs) lm t pt b (hs hz) ⊲[ w ] ΦU m (acc rs) lm t pt b (hl fI))
  ΦU-acc m rs lm t pt b =
    AccNM.acc-not-mono _ _ _ (mul (hs hz)) (Σ⁺ (λ n → ΦU m (acc rs) lm t pt b (fI n)))
      refl refl (mulR ICdΣ) refl refl (λ n → refl)
```

## 结论 (按档)

- **[定理]** `lim-not-fin`, `strip`; **`AccNM.acc-not-mono`** (对一切种类结构, 只看三个值); `Lg-fI`, `one⊲fI`; **`shape-cocone→chain`**, `pt→cocone`, **`pt-shape→chain`** (对一切 $F$); `Ψ-pt` (refl), `inc₁`, `inc₂`, **`fab3-incomp`**, **`fab3-no-shape`** (Fab3Typed 的 `Ψ`); **`Φ-acc`** (对一切 `R`), **`Ψ-acc`** (对一切 `P`), **`ΦU-acc`** (对一切 `U`).
- **[判断]** ℕ-极限子句只有 "逐点" 与 "部分和" 两种自然写法: 判断, 下一路先挑战它. 不累加的折叠在 sup 层与 `lΩ` 层号上读输入合法并证单调: 未写, 未否定.
