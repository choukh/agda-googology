# 去累加, 否定一路 (一): 逐点子句与 "对一切输入的证书" 不相容; 第三种写法

> 不含记号. 入口 [NegNoAcc](NegNoAcc.lagda.md). 本篇**不依赖**构造一路的接口 `NoAccIf` (接口定稿之前写的部分). 只导入 [CRwBase](CRwBase.lagda.md), [NegCRwInst](NegCRwInst.lagda.md) 的小引理 (`num`, `at`, `lim-not-fin`, `strip`, `fI`, `Lg-fI`, `one⊲fI`, `AccNMᶜ`), 与 [CRwFold](CRwFold.lagda.md) 的 `Sh` (只作实例). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **问题.** 作者本轮选 "去累加: 证书读输入合法". 本篇问: (1) 去掉累加 (ℕ-极限逐点) 之后, 证书能不能仍然不读输入 (对一切输入)? (2) "ℕ-极限只有逐点与部分和两种写法" 这个判断能否被挑战?
>
> 1. **`no-up` (定理, 对一切种类结构, 一切世界).** $\lim(x,x,x,\dots)\not\lhd x$. 由更一般的 **`no-child`**: 树 $c$ 不是它自己的直接子树 (后继, ℕ-极限的一项, 界之下的 $\Omega$-分支) 的第一位置. 只用结构归纳, 不用秩.
> 2. **`pt-no-total` (定理, 对一切 `S`, `S′`, 一切 "ℕ-极限要求步进" 的谓词 $P$).** 若折叠 $F$ 的 ℕ-极限子句逐点 ($F(\lim f)=\lim(F\circ f)$, 字面等式, 对一切 $f$), 则 **不存在**对一切输入的证书 $\forall h.\,P(F\,h)$. 实例 $P=$ `LgB` (`pt-no-LgB`), $P=$ CRw 的形状 `Sh` (`pt-no-Sh`). 输入是 $\lim(\lim(0,0,\dots), 0, 0, \dots)$ (不合法): 它的像要求 $\lim(F0,F0,\dots)\lhd F0$, 与 1 矛盾. 这比 `NegCRwAcc.pt-shape→chain` (像是一条链) 强: 逐点子句与对一切输入的证书**直接矛盾**, 不要像不可比. 所以 "去累加" **逼出** "证书读输入合法": 作者选的组合是逐点子句下唯一可能的 (只对 "ℕ-极限要求步进" 的证书; 见下 "不否定").
> 3. **第三种写法 `Fᵗ` (定义) 与 `thr-not-mono` (定理).** ℕ-极限的第三种字面写法: **把界穿过序列** ($c_0=F_b(f\,0)$, $c_{n+1}=F_{c_n}(f(n+1))$; 后继同样穿界). 它既不逐点 (`thr-not-pt`, 定理), 也不是字面的 `⊞` 部分和. 它有对一切输入的证书 (`Fᵗ-lg`, 只读界的合法, 不读输入) . 但在合法输入 $\lim(0,1,1,\dots)$ 上不保第一位置 (`thr-not-mono`): 由一般化的三值引理 **`ThrNM`** (部分和是它的特例, `Σ-inst`). 原因: 穿界的点逐项等于部分和的点 (`dS-hz`: $F_b\,1$ 的第 $n$ 项 $=b\boxplus(n+1)$). 所以第三种写法在这个输入上就是累加.
>
> **前提实例.** 2: `w₀` 取 `S⊥` 的 `tt`; `P = LgB` 的步进由定义给出; 逐点子句的折叠存在 (例: 恒等 $F=\mathrm{id}$ 在 `Cd` 上逐点, `id-pt`). 3: 输入合法 (`Lg-fI`), $1\lhd$ 输入 (`one⊲fI`), `ThrNM` 的七条等式由 `Fᵗ` 的定义给出 (§3).
>
> **只否定什么.** 只否定: (a) 逐点子句的折叠有对一切输入的证书 (证书的 ℕ-极限要求步进); (b) 穿界写法保字面第一位置. **不否定**: 逐点子句加读输入合法的证书 (构造一路的路线; Fab3Typed 在后继层做到了); 不要求 ℕ-极限步进的证书 (例如值合法 `Mo`, 见 [NegNoAccMo](NegNoAccMo.lagda.md)); 其他第三种写法. "ℕ-极限只有逐点, 部分和, 穿界三种" 仍是**判断**; 本篇只给出第三种的实例并说明它在 $\lim(0,1,1,\dots)$ 上与部分和逐点同值.
>
> **对纲领与目标.** 纲领不受影响. 目标 "树侧的合法性标准": `pt-no-total` 说 "去累加" 与 "证书只看形状" 二者不可兼得, 这是由树侧的要求 (ℕ-极限步进, `no-up`) 逼出的, 不来自记号. 构造一路必须把合法读进证书; 中间层的输出只在合法输入上合法.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegNoAccPt where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Lean.CRwBase
open import OCF.Lean.NegCRwInst using (num; at; lim-not-fin; strip; hs≢hz; hl≢hz; hs≢hl; hs-inj; fI; Lg-fI; one⊲fI; module AccNMᶜ)
```

## §1 没有循环: 树不是自己的直接子树的第一位置

`Ch w d c`: $d$ 是 $c$ 的直接子树 (在世界 $w$ 里可走: $\Omega$-分支要坐标在界之下). 子树一侧用等式, 好对 $d$ 结构归纳.

```agda
module _ {S : KS} where
  data Ch (w : Wd S) (d : HB S) : HB S → Set where
    cs : Ch w d (hs d)
    cl : ∀ {f} n → f n ≡ d → Ch w d (hl f)
    cΩ : ∀ {κ g c} → Bd S κ c w → g c ≡ d → Ch w d (hΩ κ g)

  ch⊲ : ∀ {w d c} → Ch w d c → d ⊲[ w ] c
  ch⊲ cs = hsuc hself
  ch⊲ (cl n refl) = hlim n hself
  ch⊲ (cΩ e refl) = hLim e hself

  acycL : ∀ x {f : ℕ → HB S} n → f n ≡ x → x ≡ hl f → ⊥
  acycL hz n e1 ()
  acycL (hs x) n e1 ()
  acycL (hl g) n e1 refl = acycL (g n) n refl e1
  acycL (hΩ κ g) n e1 ()

  acycΩ : ∀ x {κ} {g : E S κ → HB S} c → g c ≡ x → x ≡ hΩ κ g → ⊥
  acycΩ hz c e1 ()
  acycΩ (hs x) c e1 ()
  acycΩ (hl f) c e1 ()
  acycΩ (hΩ κ g) c e1 refl = acycΩ (g c) c refl e1

  nc : ∀ {w} d {c} → c ⊲[ w ] d → Ch w d c → ⊥
  nc hz hself ()
  nc (hs d) hself ()
  nc (hs d) (hsuc q) ch = nc d (⊲ᴮ-tr (ch⊲ ch) q) cs
  nc (hl f) hself (cl n e) = acycL (f n) n refl e
  nc (hl f) (hlim n q) ch = nc (f n) (⊲ᴮ-tr (ch⊲ ch) q) (cl n refl)
  nc (hΩ κ g) hself (cΩ {c = c} e e′) = acycΩ (g c) c refl e′
  nc (hΩ κ g) (hLim {c = c} e q) ch = nc (g c) (⊲ᴮ-tr (ch⊲ ch) q) (cΩ e refl)

  no-child : ∀ {w} d {c} → Ch w d c → ¬ (c ⊲[ w ] d)
  no-child d ch p = nc d p ch

  no-up : ∀ {w} x → ¬ (hl (λ _ → x) ⊲[ w ] x)
  no-up x = no-child x (cl 0 refl)
```

## §2 逐点子句没有对一切输入的证书

$P$: 任一个 "ℕ-极限要求在世界 $w_0$ 里第 0 项是第 1 项的第一位置" 的谓词. 逐点只要求字面等式 (对一切 $f$), 不要外延.

```agda
two : ∀ {S : KS} → HB S → HB S → ℕ → HB S
two u v zero = u
two u v (suc n) = v

module PtNoTotal {S S′ : KS} (w₀ : Wd S′) (P : HB S′ → Set)
  (P-step : ∀ {f} → P (hl f) → f 0 ⊲[ w₀ ] f 1)
  (F : HB S → HB S′) (pt : ∀ f → F (hl f) ≡ hl (λ n → F (f n))) where

  u₀ : HB S
  u₀ = hl (λ _ → hz)

  pt-no-total : ¬ (∀ h → P (F h))
  pt-no-total tot = no-up (F hz) (subst (λ z → z ⊲[ w₀ ] F hz) (pt (λ _ → hz)) st)
    where
    st : F u₀ ⊲[ w₀ ] F hz
    st = P-step (subst P (pt (two u₀ hz)) (tot (hl (two u₀ hz))))
```

**实例.** `LgB` (目标任一种类结构, 任一世界), CRw 的形状 `Sh` (任一接口实例 `I`; `Sh` 与 `I` 无关, 只是写在那个参数化模块里).

```agda
pt-no-LgB : ∀ {S S′ : KS} (w₀ : Wd S′) (F : HB S → HB S′) →
            (∀ f → F (hl f) ≡ hl (λ n → F (f n))) → ¬ (∀ h → LgB (F h))
pt-no-LgB w₀ F pt = PtNoTotal.pt-no-total w₀ LgB (λ l → proj₁ l {w₀} 0) F pt

open import OCF.Lean.CRwIf using (CRwIf)
import OCF.Lean.CRwFold as CF

pt-no-Sh : ∀ (I : CRwIf) {S S′ : KS} (w₀ : Wd S′) (F : HB S → HB S′) →
           (∀ f → F (hl f) ≡ hl (λ n → F (f n))) → ¬ (∀ h → CF.Sh I (F h))
pt-no-Sh I w₀ F pt = PtNoTotal.pt-no-total w₀ (CF.Sh I) (λ s → proj₁ s {w₀} 0) F pt

-- 前提可满足: 逐点的折叠存在 (Cd 上的恒等)
id-pt : ∀ f → (λ (x : Cd) → x) (hl f) ≡ hl (λ n → f n)
id-pt f = refl
```

## §3 第三种写法: 把界穿过序列

`Fᵗ b x`: 当前界 $b$. $0\mapsto b+1$; 后继: $d_0=F_b\,x$, $d_{k+1}=F_{d_k}\,x$; ℕ-极限: $c_0=F_b(f\,0)$, $c_{k+1}=F_{c_k}(f(k+1))$. 没有 `⊞`. 只在 `Cd` 上写 (没有种类).

```agda
Fᵗ : Cd → Cd → Cd
dS : Cd → Cd → ℕ → Cd
cS : Cd → (ℕ → Cd) → ℕ → Cd
Fᵗ b hz = hs b
Fᵗ b (hs x) = hl (dS b x)
Fᵗ b (hl f) = hl (cS b f)
Fᵗ b (hΩ () _)
dS b x zero = Fᵗ b x
dS b x (suc k) = Fᵗ (dS b x k) x
cS b f zero = Fᵗ b (f 0)
cS b f (suc k) = Fᵗ (cS b f k) (f (suc k))
```

**对一切输入的证书** (只读界的合法): 界是输出的第一位置 (`Fᵗ-infl`), 所以穿界的序列自动步进.

```agda
Fᵗ-infl : ∀ {w} b x → b ⊲[ w ] Fᵗ b x
Fᵗ-infl b hz = hsuc hself
Fᵗ-infl b (hs x) = hlim 0 (Fᵗ-infl b x)
Fᵗ-infl b (hl f) = hlim 0 (Fᵗ-infl b (f 0))
Fᵗ-infl b (hΩ () _)

Fᵗ-lg : ∀ b x → LgB b → LgB (Fᵗ b x)
lg-dS : ∀ b x → LgB b → ∀ k → LgB (dS b x k)
lg-cS : ∀ b f → LgB b → ∀ k → LgB (cS b f k)
Fᵗ-lg b hz lb = lb
Fᵗ-lg b (hs x) lb = (λ k → Fᵗ-infl (dS b x k) x) , lg-dS b x lb
Fᵗ-lg b (hl f) lb = (λ k → Fᵗ-infl (cS b f k) (f (suc k))) , lg-cS b f lb
Fᵗ-lg b (hΩ () _) lb
lg-dS b x lb zero = Fᵗ-lg b x lb
lg-dS b x lb (suc k) = Fᵗ-lg (dS b x k) x (lg-dS b x lb k)
lg-cS b f lb zero = Fᵗ-lg b (f 0) lb
lg-cS b f lb (suc k) = Fᵗ-lg (cS b f k) (f (suc k)) (lg-cS b f lb k)

Fᵗ-shape : ∀ x → LgB (Fᵗ hz x)
Fᵗ-shape x = Fᵗ-lg hz x tt
```

**不逐点.** $F_0\lim(0,1,1,\dots)$ 的第 1 项是 $F_1\,1$, 逐点应是 $F_0\,1$; 两者第 0 项是 $2$ 与 $1$.

```agda
thr-not-pt : ¬ (Fᵗ hz (hl fI) ≡ hl (λ n → Fᵗ hz (fI n)))
thr-not-pt e = hs≢hz (hs-inj (cong (λ h → at (at h 1) 0) e))
```

**一般化的三值引理 `ThrNM`.** 与 `AccNMᶜ` 同, 只把 "$G(m+1)=G\,m\boxplus a_1$" 换成 "$G(m+1)$ 是 ℕ-极限, 第 $n$ 项等于 $G\,m\boxplus(n+1)$" (逐项的命题等式, 不要外延).

```agda
module ThrNM {S′ : KS} (a₀ a₁ aL : HB S′) (M G : ℕ → HB S′) (H : ℕ → ℕ → HB S′)
  (e₀ : a₀ ≡ num 1) (e₁ : a₁ ≡ hl M) (eM : ∀ n → M n ≡ num (suc n))
  (eL : aL ≡ hl G) (G0 : G 0 ≡ a₀) (Gs : ∀ m → G (suc m) ≡ hl (H m))
  (eH : ∀ m n → H m n ≡ G m ⊞ num (suc n)) where

  G≢hz : ∀ m → ¬ (G m ≡ hz)
  G≢hz zero e = hs≢hz (trans (sym (trans G0 e₀)) e)
  G≢hz (suc m) e = hl≢hz (trans (sym (Gs m)) e)

  notG : ∀ {w} m → ¬ (hl M ⊲[ w ] G m)
  notG {w} zero p = lim-not-fin 1 (subst (λ z → hl M ⊲[ w ] z) (trans G0 e₀) p)
  notG {w} (suc m) p = go (subst (λ z → hl M ⊲[ w ] z) (Gs m) p) refl refl
    where
    go : ∀ {a b} → a ⊲[ w ] b → a ≡ hl M → b ≡ hl (H m) → ⊥
    go hself ea eb =
      G≢hz m (sym (hs-inj (trans (sym (eM 0)) (trans (cong (λ h → at h 0) (trans (sym ea) eb)) (eH m 0)))))
    go (hsuc p) ea eb = hs≢hl eb
    go {a} (hlim n q) ea eb =
      notG m (strip (suc n) (subst (λ z → hl M ⊲[ w ] z) (eH m n)
               (subst (λ z → z ⊲[ w ] H m n) ea (subst (λ z → a ⊲[ w ] z) (cong (λ h → at h n) eb) q))))
    go (hLim e q) ea ()

  not-mono : ∀ {w} → ¬ (a₁ ⊲[ w ] aL)
  not-mono {w} p = go (subst (λ z → z ⊲[ w ] hl G) e₁ (subst (λ z → a₁ ⊲[ w ] z) eL p)) refl refl
    where
    two≢ : ∀ {f : ℕ → HB S′} → ¬ (num {S′} 2 ≡ hl f)
    two≢ ()
    go : ∀ {a b} → a ⊲[ w ] b → a ≡ hl M → b ≡ hl G → ⊥
    go hself ea eb = two≢ (trans (sym (eM 1)) (trans (cong (λ h → at h 1) (trans (sym ea) eb)) (Gs 0)))
    go (hsuc p) ea eb = hs≢hl eb
    go {a} (hlim m q) ea eb =
      notG m (subst (λ z → z ⊲[ w ] G m) ea (subst (λ z → a ⊲[ w ] z) (cong (λ h → at h m) eb) q))
    go (hLim e q) ea ()
```

**部分和是特例** (`Σ-inst`): $H\,m\,n = G\,m\boxplus M\,n$, 等式由 `⊞` 的定义给出.

```agda
module Σ-inst {S′ : KS} (a₀ a₁ aL : HB S′) (M G : ℕ → HB S′)
  (e₀ : a₀ ≡ num 1) (e₁ : a₁ ≡ hl M) (eM : ∀ n → M n ≡ num (suc n))
  (eL : aL ≡ hl G) (G0 : G 0 ≡ a₀) (Gs : ∀ n → G (suc n) ≡ G n ⊞ a₁) where

  Σ-not-mono : ∀ {w} → ¬ (a₁ ⊲[ w ] aL)
  Σ-not-mono = ThrNM.not-mono a₀ a₁ aL M G (λ m n → G m ⊞ M n) e₀ e₁ eM eL G0
    (λ m → subst (λ z → G (suc m) ≡ G m ⊞ z) e₁ (Gs m)) (λ m n → cong (λ z → G m ⊞ z) (eM n))
```

**穿界写法的实例.** $F_b\,1$ 的第 $n$ 项字面算出 $b\boxplus(n+1)$ (`dS-hz`, 对 $n$ 归纳).

```agda
dS-hz : ∀ b n → dS b hz n ≡ b ⊞ num (suc n)
dS-hz b zero = refl
dS-hz b (suc n) = cong hs (dS-hz b n)

dS-one : ∀ n → dS hz hz n ≡ num (suc n)
dS-one zero = refl
dS-one (suc n) = cong hs (dS-one n)

thr-not-mono : ¬ (Fᵗ hz (hs hz) ⊲ Fᵗ hz (hl fI))
thr-not-mono = ThrNM.not-mono (Fᵗ hz hz) (Fᵗ hz (hs hz)) (Fᵗ hz (hl fI))
  (dS hz hz) (cS hz fI) (λ m → dS (cS hz fI m) hz)
  refl refl dS-one refl refl (λ m → refl) (λ m n → dS-hz (cS hz fI m) n)

-- 输入一侧: 合法, 1 是它的第一位置
thr-input : LgB {S⊥} (hl fI) × (hs hz ⊲ hl fI)
thr-input = Lg-fI , one⊲fI
```

## 结论 (按档)

- **[定理]** `Ch`, `ch⊲`, `acycL`, `acycΩ`, `nc`, **`no-child`**, **`no-up`** (对一切 `S`); **`PtNoTotal.pt-no-total`** (对一切 `S`, `S′`, 一切 ℕ-极限要求步进的 $P$, 一切逐点的 $F$), 实例 **`pt-no-LgB`**, **`pt-no-Sh`**; `id-pt`; 穿界折叠 `Fᵗ` 与 `Fᵗ-infl`, **`Fᵗ-lg`**, `Fᵗ-shape` (对一切输入的证书), **`thr-not-pt`**; **`ThrNM.not-mono`** (三值引理, 一般形), `Σ-inst.Σ-not-mono` (部分和是特例), `dS-hz`, `dS-one`, **`thr-not-mono`**, `thr-input`.
- **[判断]** ℕ-极限子句的写法 "只有逐点, 部分和, 穿界" 是判断; 穿界在 $\lim(0,1,1,\dots)$ 上与部分和逐项同值是定理 (`dS-hz`), 在一般输入上是否总是如此未证. 去累加之后中间层的证书必须读输入合法, 这是对 "ℕ-极限要求步进" 的证书的定理; 对别的证书 (例如 `Mo`) 不适用.
