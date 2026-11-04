# AccTreeLab: 基本列下降的树与标签

> **判决: HOLDS (对写明的陈述).** 总判决在 [AccTree](AccTree.lagda.md).
>
> 1. **`lab-tree`: 遗传不碰 $\Omega$-共尾 (`HC t`) 时, `Lab (tree t h) t`,** 对一切 `h : Acc t`. `Lab` 的定义直接接上.
> 2. **`Lab` 恰好等于 `HC`.** `Lab→HC` 擦掉树, `labᴴ` 补回来; 带标签的树都 $\cong$ `tree t h` (`Lab≅tree`), FGH 都是记号的 `fghₙ` (`fgh-Lab`). 所以现有标签定理去掉树之后的内容, 正好是 "这个项的基本列遗传地良基且可数".
> 3. **"有 `Acc` 就自动有标签" 有三个读法.** 对基本列下降的 `Acc` 是假的 (`¬acc⇒lab`): $\Omega$ 有 `Acc`, 没有标签, 因为 `Lab` 没有 `cΩ` 行. 对字面的 `E.Acc` 成立 (`acc→lab`), 但那只是自然数. 对可数标准形上 `_<ᵀ_` 的良基成立 (`Std.wf→lab`), 这是正确的读法; $\omega$ 上有实例 (`acc-nc-ω`, `label-ω`, 而 `E.Acc ω` 是假的), 一般项上前提未证.
> 4. **前提可满足, 且不止自然数 (§3, §4).** `HC-ε₀`, `HC-BTBO`, `HC-tΩ·2`, `HC-tω` 无条件, 最高到 $\psi_0(\Omega_{\Omega\cdot\omega})$. 主线的 `fgh` 等于记号沿基本列的 `fghₙ` (`fgh-main`).
>
> **这些实例不是 "记号自己证了良基".** `HC` 由标签得出, 标签对树的结构归纳证明, 所以良基性来自树. 它们说明定理不空, 也说明方向: 对这些项, 树给记号基本列的良基性, 不是反过来.
>
> `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示. 验收文件, 读记号与标签.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.AccTreeLab where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import OCF.Align.Level using (Ordᶜ; zero; suc; lim; _≅_; z≅; s≅; l≅; ≅-refl⁰; ≅-trans; FGH; FGH-≅)
open import OCF.Align.Correspond using (Lab; l0; l1; lω; γᴱ; ε₀-label)
open import OCF.Align.Stage2 using (Lab-uniq)
open import OCF.Align.Standard using (NF; NFᴾ; n[]; n∷; nψ; Ctbl; c[]; c∷; Bnd; bnd[]; vh; vd; vt;
  NF-pred; NF-fsn; Ctbl-pred; Ctbl-fsn; Ctbl-cof)
open import OCF.Align.Label using (BTBO-label)
open import OCF.Align.NoCumsum using (BTBOᴵ)
import OCF.Align.EBO as E
open E using (T; ψ; 𝟏; natT; cof; pred; fsn; fsn↓; dec; _<ᵀ_; []<; hd<; tl<; lv<; ar<; Cof; c0; c1; cω; cΩ)
open import OCF.Align.AccTree
import OCF.Align.Uniform4TwoWalk as AW
import OCF.Align.ScafLadderQTop as Q
open import OCF.Align.ScafLadderZUniform3Base using (Ev)
open import OCF.Align.ScafLadderZUniform4Base using (Fl)
import OCF.Free.Bridge as B
import OCF.Free.Closed as FC
```

## §1 `HC`

`HC t` 是 `Lab` 擦掉树: 沿 `pred`, `fsn` 遗传地良基, 且不碰 `cΩ`. `inv` 按 `cof` 的值读出下一步; 把它写成一等的 `HCᶜ`, 省掉三乘三的分情况. `Same` 把 `cof` 的不同取值判成 $\bot$.

```agda
data HC (t : T) : Set where
  h0 : cof t ≡ c0 → HC t
  h1 : cof t ≡ c1 → HC (pred t) → HC t
  hω : cof t ≡ cω → (∀ n → HC (fsn t n)) → HC t

HCᶜ : T → Cof → Set
HCᶜ t c0     = ⊤
HCᶜ t c1     = HC (pred t)
HCᶜ t cω     = ∀ n → HC (fsn t n)
HCᶜ t (cΩ μ) = ⊥

inv : ∀ {t c} → HC t → cof t ≡ c → HCᶜ t c
inv {t} (h0 e)    e′ = subst (HCᶜ t) (trans (sym e) e′) tt
inv {t} (h1 e hp) e′ = subst (HCᶜ t) (trans (sym e) e′) hp
inv {t} (hω e hf) e′ = subst (HCᶜ t) (trans (sym e) e′) hf

Same : Cof → Cof → Set
Same c0     c0     = ⊤
Same c1     c1     = ⊤
Same cω     cω     = ⊤
Same (cΩ _) (cΩ _) = ⊤
Same _      _      = ⊥

same : ∀ c → Same c c
same c0     = tt
same c1     = tt
same cω     = tt
same (cΩ _) = tt

clash : ∀ {t c c′} → cof t ≡ c → cof t ≡ c′ → Same c c′
clash {c = c} e e′ = subst (Same c) (trans (sym e) e′) (same c)

Lab→HC : ∀ {X t} → Lab X t → HC t
Lab→HC (l0 c _)   = h0 c
Lab→HC (l1 c _ l) = h1 c (Lab→HC l)
Lab→HC (lω c _ h) = hω c (λ n → Lab→HC (h n))

HC→Acc : ∀ {t} → HC t → Acc t
HC→Acc (h0 e) = acc λ where
  (◁p e′)   → ⊥-elim (clash e e′)
  (◁ω e′ n) → ⊥-elim (clash e e′)
  (◁Ω e′ n) → ⊥-elim (clash e e′)
HC→Acc (h1 e hp) = acc λ where
  (◁p e′)   → HC→Acc hp
  (◁ω e′ n) → ⊥-elim (clash e e′)
  (◁Ω e′ n) → ⊥-elim (clash e e′)
HC→Acc (hω e hf) = acc λ where
  (◁p e′)   → ⊥-elim (clash e e′)
  (◁ω e′ n) → HC→Acc (hf n)
  (◁Ω e′ n) → ⊥-elim (clash e e′)
```

## §2 标签

`lab-tree` 对 `Acc` 证明递归, 所以任何 `h` 都可以. `Lab` 的三行正好是 `viewᶜ` 的三行, 第四行被 `HC` 排除.

```agda
lab-tree : ∀ t (h : Acc t) → HC t → Lab (tree t h) t
labᶜ : ∀ t c (e : cof t ≡ c) (rs : Rs t) → HC t → Lab (treeV (viewᶜ t c e) rs) t
lab-tree t (acc rs) hc = labᶜ t (cof t) refl rs hc
labᶜ t        c0     e  rs hc = l0 e z≅
labᶜ t        c1     e  rs hc = l1 e (≅-refl⁰ _) (lab-tree (pred t) (rs (◁p e)) (inv hc e))
labᶜ []       cω     () rs hc
labᶜ (x ∷ xs) cω     e  rs hc = lω e (≅-refl⁰ _) (λ n → lab-tree (fsn (x ∷ xs) n) (rs (◁ω e n)) (inv hc e n))
labᶜ []       (cΩ μ) () rs hc
labᶜ (x ∷ xs) (cΩ μ) e  rs hc = ⊥-elim (inv hc e)

treeᴴ : ∀ {t} → HC t → Ordᶜ zero
treeᴴ {t} hc = tree t (HC→Acc hc)

labᴴ : ∀ {t} (hc : HC t) → Lab (treeᴴ hc) t
labᴴ {t} hc = lab-tree t (HC→Acc hc) hc

Lab≅tree : ∀ {X t} → Lab X t → (h : Acc t) → X ≅ tree t h
Lab≅tree {t = t} l h = Lab-uniq l (lab-tree t h (Lab→HC l))

fgh-Lab : ∀ {X t} → Lab X t → (h : Acc t) → ∀ n → FGH X n ≡ fghₙ t h n
fgh-Lab {t = t} l h n = trans (FGH-≅ (Lab≅tree l h) n) (fgh-tree t h n)
```

只有 `Acc` 不够: $\Omega$ 有 `Acc` (`acc-Ω`), 没有标签.

```agda
¬Lab-Ω : ∀ {X} → Lab X Ωᵗ → ⊥
¬Lab-Ω l = inv (Lab→HC l) refl

¬acc⇒lab : (∀ t (h : Acc t) → Lab (tree t h) t) → ⊥
¬acc⇒lab f = ¬Lab-Ω (f Ωᵗ acc-Ω)
```

字面的 `E.Acc` 自动有标签, 但它只在自然数上成立 (`acc→nat`).

```agda
HC-nat : ∀ k → HC (natT k)
HC-nat zero    = h0 refl
HC-nat (suc k) = h1 (E.cof-natT k) (subst HC (sym (E.pred-natT k)) (HC-nat k))

acc→HC : ∀ {a} → E.Acc a → HC a
acc→HC {a} h with acc→nat a h
... | k , refl = HC-nat k

acc→lab : ∀ a (h : E.Acc a) → Lab (treeᴱ a h) a
acc→lab a h = lab-tree a (toAcc h) (acc→HC h)
```

**这句话的正确形式.** 类 `P` 对 `pred`, `fsn` 封闭且不含 $\Omega$-共尾的项, 在 `P` 内 `_<ᵀ_` 的良基 (`AccP`, 量词限制在 `P` 上, 不要求向下封闭) 推出 `HC`, 于是有标签. `AccP` 与 `E.Acc` 不同: 下面的 $1+\omega$ 不在标准形类里, 不必良基. 标准形与可数项给实例 (`NC`). 这里的前提 `AccP` 仓库里没有证明.

```agda
fsn< : ∀ a → cof a ≡ cω → ∀ n → fsn a n <ᵀ a
fsn< []       () n
fsn< (x ∷ xs) e  n = dec (fsn↓ x xs n)

module Class (P : T → Set)
  (P-pred : ∀ {t} → P t → cof t ≡ c1 → P (pred t))
  (P-fsn  : ∀ {t} → P t → cof t ≡ cω → ∀ n → P (fsn t n))
  (P-noΩ  : ∀ {t μ} → P t → cof t ≡ cΩ μ → ⊥) where

  data AccP (a : T) : Set where
    acc : (∀ {b} → P b → b <ᵀ a → AccP b) → AccP a

  wf→HC : ∀ {a} → P a → AccP a → HC a
  wf→HC {a} pa (acc rs) = go (cof a) refl where
    go : ∀ c → cof a ≡ c → HC a
    go c0     e = h0 e
    go c1     e = h1 e (wf→HC (P-pred pa e) (rs (P-pred pa e) (E.pred-< a e)))
    go cω     e = hω e (λ n → wf→HC (P-fsn pa e n) (rs (P-fsn pa e n) (fsn< a e n)))
    go (cΩ μ) e = ⊥-elim (P-noΩ pa e)

  wf→lab : ∀ {a} (pa : P a) (w : AccP a) → Lab (treeᴴ (wf→HC pa w)) a
  wf→lab pa w = labᴴ (wf→HC pa w)

NC : T → Set
NC t = NF t × Ctbl t

module Std = Class NC
  (λ (n , c) e → NF-pred n e , Ctbl-pred c)
  (λ (n , c) e k → NF-fsn n e k , Ctbl-fsn c e k)
  (λ (_ , c) e → Ctbl-cof c e)
```

**这个前提严格弱于 `E.Acc`, 且不空.** `E.Acc` 推出 `AccP` (`fromE`, 量词变少). 反向不成立: $\omega$ 没有 `E.Acc` (`¬acc-ω`), 但有 `AccP` (`acc-nc-ω`): 它下面的标准形只有自然数 (`nf-nat`). 于是 $\omega$ 走完整条路线得到标签 (`label-ω`). 再往上没有做: 这条路线的前提在一般项上就是标准形的良基性, 未证.

```agda
fromE : ∀ {a} → E.Acc a → Std.AccP a
fromE (E.acc rs) = Std.acc (λ _ q → fromE (rs q))

nf-nat : ∀ {xs} → NF (𝟏 ∷ xs) → Σ ℕ λ k → xs ≡ natT k
nf-nat {xs = []}               _ = 0 , refl
nf-nat {xs = ψ [] [] ∷ ys}     (n∷ _ nxs _) with nf-nat nxs
... | k , refl = suc k , refl
nf-nat {xs = ψ (w ∷ ws) a ∷ ys}  (n∷ _ _ (inj₁ ()))
nf-nat {xs = ψ (w ∷ ws) a ∷ ys}  (n∷ _ _ (inj₂ ()))
nf-nat {xs = ψ [] (c ∷ cs) ∷ ys} (n∷ _ _ (inj₁ ()))
nf-nat {xs = ψ [] (c ∷ cs) ∷ ys} (n∷ _ _ (inj₂ ()))

acc-nc-ω : Std.AccP ωt
acc-nc-ω = Std.acc go where
  go : ∀ {b} → NC b → b <ᵀ ωt → Std.AccP b
  go _       []<                   = fromE (E.accNat 0)
  go (n , _) (hd< (ar< []<)) with nf-nat n
  ... | k , refl = fromE (E.accNat (suc k))
  go _       (hd< (lv< ()))
  go _       (hd< (ar< (hd< (lv< ()))))
  go _       (hd< (ar< (hd< (ar< ()))))
  go _       (hd< (ar< (tl< ())))

nc-ω : NC ωt
nc-ω = n∷ (nψ n[] c[] (n∷ (nψ n[] c[] n[] bnd[]) n[] tt) bnd₁) n[] tt , c∷ c[] where
  bnd₁ : Bnd [] (𝟏 ∷ [])
  bnd₁ (vh _)  = []<
  bnd₁ (vd _ ())
  bnd₁ (vt ())

label-ω : Lab (treeᴴ (Std.wf→HC nc-ω acc-nc-ω)) ωt
label-ω = Std.wf→lab nc-ω acc-nc-ω
```

## §3 高处的实例

无条件, 由现有的标签定理得出 (`Lab→HC`). `fgh-BTBO`: 带标签的树 `BTBOᴵ` 的 FGH 就是记号沿基本列的 FGH.

```agda
HC-ε₀ : HC (γᴱ 1)
HC-ε₀ = Lab→HC ε₀-label

HC-BTBO : HC (E.EBOψ 2)
HC-BTBO = Lab→HC BTBO-label

fgh-BTBO : ∀ n → FGH BTBOᴵ n ≡ fghₙ (E.EBOψ 2) (HC→Acc HC-BTBO) n
fgh-BTBO = fgh-Lab BTBO-label (HC→Acc HC-BTBO)
```

## §4 主线

`FC.fgh` 是主线无记号闭项的 FGH (`OCF.Free.Closed`). `Bridge` 把它搬到本文件的树类型, 并给标签. 于是它就是记号沿基本列的 FGH, 在 $\psi_0(\Omega_{\Omega\cdot2})$ 处逐点相同. 最高处 $\psi_0(\Omega_{\Omega\cdot\omega})$ 的 `Tω-label` 带环境参数, 取闭合环境 `ev₀′` 后同样无条件.

```agda
HC-tΩ·2 : HC AW.tΩ·2
HC-tΩ·2 = Lab→HC B.TΩ₂-label

fgh-main : ∀ n → FC.fgh n ≡ fghₙ AW.tΩ·2 (HC→Acc HC-tΩ·2) n
fgh-main n = trans (B.FGH-⟦⟧ FC.TΩ₂ n) (fgh-Lab B.TΩ₂-label (HC→Acc HC-tΩ·2) n)

ev₀′ : Ev (suc zero) Fl
ev₀′ = tt , (λ q → q)

HC-tω : HC Q.tω
HC-tω = Lab→HC (proj₂ (Q.Tω-label ev₀′ zero))
```

有限测试, 不是证明.

```agda
_ : fghₙ (γᴱ 1) (HC→Acc HC-ε₀) 0 ≡ 1
_ = refl
```
