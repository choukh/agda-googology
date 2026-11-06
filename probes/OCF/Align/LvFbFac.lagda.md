# 层号由回灌给出 (W1): 外层界用差树表示, 塔的 ℕ-极限

> 不含记号. 入口 [LvFb](LvFb.lagda.md). 作者选定原话: "A3 提前探路". 本篇是三种不需要外延的写法里的第一种 (W1): 外层界不是一个经 ⊞ 算出的高度, 而是一串增量的部分和 $b_n$ (`psum`; 对照主线 `HtTowerFTree.sum`, `Lg-sum`: 部分和字面是第一位置), 极限界是 $\mathrm{hl}\,b_\bullet$. 针对的是 [AdmEvFeed](AdmEvFeed.lagda.md) 写下的第一个障碍: "塔的 ℕ-极限: 合到极限界 $\mathrm{hl}\,b$ 之下要沿 `hlim n hself` 与 `stepsᴮ` 的复合改贴; `fac` 只对 `⊞-⊲ b σ` 形状的长高路径; 把 $b_m$ 写成 $b_n\boxplus(\cdots)$ 要 ⊞ 的结合律, 在 ℕ-极限处要函数外延". 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> **结论.**
>
> 1. **因子化对路径复合封闭 (定理).** 把 `AdmEvGrow.fac` 的结论写成路径 $X : b\lhd B$ 的性质 `FacP lb lB X` ("沿 $X$ 弱化的证据与任一 $Y$ 的比较, 等于先比 $X$ 与 $Y$ 再在旧界下比"). `fac-self`: 自身路径有它; **`fac-tr`**: 它对路径复合封闭 (只用路径复合的结合律 `tr-assoc`, 那是对路径归纳的定理, 不是 ⊞ 的结合律); `fac-step`: 一步 `⊞-fst` 有它 (就是 `AdmEvGrow.Grow₀.facg`).
> 2. **部分和的极限包含有它 (定理).** **`fac-lim`**: 极限界 $\mathrm{hl}\,b_\bullet$ (合法证明取部分和的字面链), 包含 `hlim n hself` 满足 `FacP`. 证明里 `cmpB₀` 在两个 `hlim` 处按 $n$, $m$ 的大小走到 $b_{\max}$, 用的是 `stepsᴮ` 的因子化 (`fac-steps`, 由 `fac-tr` 对步数归纳); 从不把 $b_m$ 写成 $b_n\boxplus(\cdots)$. **所以不要 ⊞ 的结合律, 不要函数外延.**
> 3. **沿任一满足 `FacP` 的路径改贴保合法 (定理).** `RelX`: `AdmEvGrow` 的 `rest`, `sim`, `Lg-rl` 对一般路径 $X$ 写一遍 (只用 `FacP X`, `diag-tr`, `inj₂-strict`). 实例 **`Lg-rlω`**: 第 $n$ 站 ($b_n$ 之下的事件世界) 上的合法高度改贴到极限界 $\mathrm{hl}\,b_\bullet$ 之下仍合法.
> 4. **极限按差树写合法 (定理); 按站改贴的链有拷贝 (定理, 否定一侧).** `Lim.U`: 各站**自己新增的**部分 $d_n$ 从它出生的那一站直接改贴到极限, 再取部分和, `Lg-U` 合法由形状给出. 反过来, 若把第 $n$ 站的整个高度改贴到极限 (塔的写法: 第 $n+1$ 站的高度含 $\mathrm{rl}(t_n)$), 同一个旧 $\Omega$-节点经两条路走到极限得到**不同的种类** (`copy-lim`: $(c,\mathrm{hlim}\,n\,p)\ne(c,\mathrm{hlim}\,(n{+}1)\,(p⨾\mathrm{st}_n))$). 所以各站整个高度的改贴不能字面地连成 ℕ-极限; 极限要按增量写.
>
> **对 W1 的判决: 成立 (定理), 范围是事件世界 (`AdmEv`) 的外层界的 ℕ-极限.** 拷贝 (同一坐标两个证据, 两个种类) 仍在: 它们在一切世界里读到的界是否相同, 本篇没有证 (判断: 由 `FacP` 大概可证, 因为两个证据经因子化走到同一个 $b_m$).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvFbFac where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ; module Trich)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc)
open import OCF.Align.CumReadCF using (A; azero; Lg)
open import OCF.Align.HtTowerTy
open import OCF.Align.StallDxBdec using (_<ᴮ_; toLt)
open import OCF.Align.AdmWCmp using (cmpB₀; <ᴮ-tr)
open import OCF.Align.AdmEvBase using (module Rp₀; module EvKS₀)
open import OCF.Align.AdmEvGrow using (tr-assoc; diag-tr; inj₂-strict; module Fac; module Grow₀)
```

## §1 因子化作为路径的性质

```agda
module FacPath (a : A) (la : Lg a) where
  post : ∀ {b : HB S₀} → LgB b → ∀ {c c₀ : HB S₀} → c ⊲[ a ] b → (c₀ ⊲[ a ] b) ⊎ (b ⊲[ a ] c₀) → (c₀ ⊲[ a ] c) ⊎ (c ⊲[ a ] c₀)
  post {b} lb = Fac.post a la b lb

  FacP : ∀ {b B : HB S₀} → LgB b → LgB B → b ⊲[ a ] B → Set
  FacP {b} {B} lb lB X = ∀ {c c₀} (p : c ⊲[ a ] b) (Y : c₀ ⊲[ a ] B) →
    cmpB₀ (⊲ᴮ-tr p X) Y la lB ≡ post lb p (cmpB₀ X Y la lB)

  fac-self : ∀ {b} (lb : LgB b) → FacP lb lb hself
  fac-self lb p Y = refl

  tr-idˡ : ∀ {x y : HB S₀} (q : x ⊲[ a ] y) → ⊲ᴮ-tr hself q ≡ q
  tr-idˡ hself = refl
  tr-idˡ (hsuc q) = cong hsuc (tr-idˡ q)
  tr-idˡ (hlim n q) = cong (hlim n) (tr-idˡ q)
  tr-idˡ (hLim e q) = cong (hLim e) (tr-idˡ q)

  -- 复合封闭
  fac-tr : ∀ {b B C : HB S₀} {lb : LgB b} {lB : LgB B} {lC : LgB C} {X : b ⊲[ a ] B} {X′ : B ⊲[ a ] C} →
           FacP lb lB X → FacP lB lC X′ → FacP lb lC (⊲ᴮ-tr X X′)
  fac-tr {lb = lb} {lB} {lC} {X} {X′} F F′ p Y =
    trans (cong (λ t → cmpB₀ t Y la lC) (sym (tr-assoc p X X′)))
          (trans (F′ (⊲ᴮ-tr p X) Y)
                 (trans (pp (cmpB₀ X′ Y la lC)) (cong (post lb p) (sym (F′ X Y)))))
    where
    pp : ∀ R → post lB (⊲ᴮ-tr p X) R ≡ post lb p (post lB X R)
    pp (inj₁ r) = F p r
    pp (inj₂ s) = cong inj₂ (tr-assoc p X s)

  -- 一步 ⊞-fst (AdmEvGrow 的 facg)
  fac-step : ∀ {b} (lb : LgB b) δ (lδ : LgB δ) → FacP lb (Lg-⊞ b δ lb lδ) (⊞-fst b δ)
  fac-step {b} lb δ lδ p Y = Grow₀.facg a la b lb δ lδ p Y

  -- 步链的因子化: 对步数归纳
  fac-steps : ∀ {f : ℕ → HB S₀} (st : ∀ {w} n → f n ⊲[ w ] f (suc n)) (l : ∀ n → LgB (f n)) →
              (∀ k → FacP (l k) (l (suc k)) (st k)) → ∀ {n m} (q : n <ᴺ m) → FacP (l n) (l m) (stepsᴮ st q)
  fac-steps st l F zero = F _
  fac-steps st l F (suc q) = fac-tr (fac-steps st l F q) (F _)

  -- 极限包含
  fac-lim : ∀ {f : ℕ → HB S₀} (st : ∀ {w} n → f n ⊲[ w ] f (suc n)) (l : ∀ n → LgB (f n)) →
            (∀ k → FacP (l k) (l (suc k)) (st k)) → ∀ n → FacP {f n} {hl f} (l n) (st , l) (hlim n hself)
  fac-lim st l F n p hself = refl
  fac-lim st l F n p (hlim m Y) with <ᴺ-dec n m
  ... | injᵃ n<m =
    trans (fac-steps st l F n<m p Y)
          (cong (λ t → post (l n) p (cmpB₀ t Y la (l m))) (sym (tr-idˡ (stepsᴮ st n<m))))
  ... | injᵇ m<n = refl
  ... | injᶜ refl = refl
```

## §2 部分和 (差树) 的外层界

```agda
  module PSum (b₀ : HB S₀) (lb₀ : LgB b₀) (δ : ℕ → HB S₀) (lδ : ∀ n → LgB (δ n)) where
    psum : ℕ → HB S₀
    psum zero = b₀
    psum (suc n) = psum n ⊞ δ n

    lps : ∀ n → LgB (psum n)
    lps zero = lb₀
    lps (suc n) = Lg-⊞ (psum n) (δ n) (lps n) (lδ n)

    st : ∀ {w} n → psum n ⊲[ w ] psum (suc n)
    st n = ⊞-fst (psum n) (δ n)

    B : HB S₀
    B = hl psum

    lB : LgB B
    lB = st , lps

    Xn : ∀ n → psum n ⊲[ a ] B
    Xn n = hlim n hself

    fac-ps : ∀ n → FacP (lps n) lB (Xn n)
    fac-ps = fac-lim st lps (λ k → fac-step (lps k) (δ k) (lδ k))
```

## §3 沿满足 `FacP` 的路径改贴保合法

`AdmEvGrow` 的 `Grow₀`, `Relabel` 对一般路径 $X$ 重写; 只用 `FacP X`.

```agda
module RelX (a : A) (la : Lg a) (b : HB S₀) (lb : LgB b) (B : HB S₀) (lB : LgB B) (X : b ⊲[ a ] B)
            (facX : FacPath.FacP a la lb lB X)
            (v₀ : (c : HB S₀) → Wd (Lev c)) (lv₀ : ∀ c → LgW (Lev c) (v₀ c)) where
  open FacPath a la using (post)
  module O = Rp₀ a b la lb
  module N = Rp₀ a B la lB
  module K₀ = EvKS₀ a b la lb v₀ lv₀
  module K₁ = EvKS₀ a B la lB v₀ lv₀

  wk : ∀ {c} → c ⊲[ a ] b → c ⊲[ a ] B
  wk p = ⊲ᴮ-tr p X

  restE : ∀ {c₀} → (c₀ ⊲[ a ] b) ⊎ (b ⊲[ a ] c₀) → (δ′ : HB (Lev c₀)) → LgB δ′ → O.Hist → O.Hist
  restE (inj₁ r) δ′ l H = O.ev _ r δ′ l ∷ H
  restE (inj₂ _) δ′ l H = H

  rest : N.Hist → O.Hist
  rest [] = []
  rest (e ∷ H) = restE (cmpB₀ X (N.ep e) la lB) (N.eδ e) (N.elδ e) (rest H)

  private
    below-b : ∀ {c c₀} → c ⊲[ a ] b → b <ᴮ c₀ → c <ᴮ c₀
    below-b {c₀ = c₀} p l with toLt p
    ... | inj₁ refl = l
    ... | inj₂ m = <ᴮ-tr m l

  sim : ∀ H c (p : c ⊲[ a ] b) → N.rp H c (wk p) ≡ O.rp (rest H) c p
  sim [] c p = refl
  sim (e ∷ H) c p =
    trans (cong (λ r → N.contrib (N.fix r) (N.eδ e) (N.rp H c (wk p))) (facX p (N.ep e)))
          (stp (cmpB₀ X (N.ep e) la lB) refl)
    where
    stp : (R : (N.ec e ⊲[ a ] b) ⊎ (b ⊲[ a ] N.ec e)) → cmpB₀ X (N.ep e) la lB ≡ R →
          N.contrib (N.fix (post lb p R)) (N.eδ e) (N.rp H c (wk p)) ≡ O.rp (restE R (N.eδ e) (N.elδ e) (rest H)) c p
    stp (inj₁ r) eq = cong (O.contrib (O.cmpS p r) (N.eδ e)) (sim H c p)
    stp (inj₂ s) eq =
      trans (O.contrib-below (below-b p (inj₂-strict X (N.ep e) la lB eq)) (N.fix (inj₂ (⊲ᴮ-tr p s))) (N.eδ e) (N.rp H c (wk p)))
            (sim H c p)

  km : K₀.Kᵉ → K₁.Kᵉ
  km κ = proj₁ κ , wk (proj₂ κ)

  rl : HB K₀.evKS₀ → HB K₁.evKS₀
  rl hz = hz
  rl (hs t) = hs (rl t)
  rl (hl f) = hl (λ n → rl (f n))
  rl (hΩ κ g) = hΩ (km κ) (λ x → rl (g x))

  bd-to : ∀ H κ x → K₀.Bdᵉ κ x (rest H) → K₁.Bdᵉ (km κ) x H
  bd-to H κ x e = subst (λ t → x ⊲[ v₀ (proj₁ κ) ] t) (sym (sim H (proj₁ κ) (proj₂ κ))) e

  bd-from : ∀ H κ x → K₁.Bdᵉ (km κ) x H → K₀.Bdᵉ κ x (rest H)
  bd-from H κ x e = subst (λ t → x ⊲[ v₀ (proj₁ κ) ] t) (sim H (proj₁ κ) (proj₂ κ)) e

  rl⊲ : ∀ {H₀ H₁} → (∀ κ x → K₀.Bdᵉ κ x H₀ → K₁.Bdᵉ (km κ) x H₁) →
        ∀ {t t′} → _⊲[_]_ {K₀.evKS₀} t H₀ t′ → _⊲[_]_ {K₁.evKS₀} (rl t) H₁ (rl t′)
  rl⊲ tr hself = hself
  rl⊲ tr (hsuc q) = hsuc (rl⊲ tr q)
  rl⊲ tr (hlim n q) = hlim n (rl⊲ tr q)
  rl⊲ tr (hLim {κ = κ} {c = x} e q) = hLim (tr κ x e) (rl⊲ tr q)

  Lg-rl : ∀ t → LgB {K₀.evKS₀} t → LgB {K₁.evKS₀} (rl t)
  Lg-rl hz l = tt
  Lg-rl (hs t) l = Lg-rl t l
  Lg-rl (hl f) (st , l) = (λ {H} n → rl⊲ (bd-to H) (st {rest H} n)) , (λ n → Lg-rl (f n) (l n))
  Lg-rl (hΩ κ g) (mo , l) =
    (λ {H} {x} {x′} lw e e′ pr → rl⊲ (bd-to H) (mo {rest H} tt (bd-from H κ x e) (bd-from H κ x′ e′) pr)) ,
    (λ x lx → Lg-rl (g x) (l x lx))
```

## §4 塔的 ℕ-极限

外层 `A`-世界 $a$, 内层世界族 $v_0$; 外层界是部分和 $b_n$, 极限界 $B=\mathrm{hl}\,b_\bullet$. 第 $n$ 站的种类结构 $K_n$ (`evKS₀` 在 $b_n$ 之下), 极限的种类结构 $K_\omega$ (在 $B$ 之下).

```agda
module Lim (a : A) (la : Lg a) (b₀ : HB S₀) (lb₀ : LgB b₀) (δ : ℕ → HB S₀) (lδ : ∀ n → LgB (δ n))
           (v₀ : (c : HB S₀) → Wd (Lev c)) (lv₀ : ∀ c → LgW (Lev c) (v₀ c)) where
  open FacPath a la
  open PSum b₀ lb₀ δ lδ

  Kn : ℕ → KS
  Kn n = EvKS₀.evKS₀ a (psum n) la (lps n) v₀ lv₀

  Kω : KS
  Kω = EvKS₀.evKS₀ a B la lB v₀ lv₀

  -- 第 n 站到极限
  module Rω (n : ℕ) = RelX a la (psum n) (lps n) B lB (Xn n) (fac-ps n) v₀ lv₀
  -- 第 n 站到第 n+1 站
  module Rs (n : ℕ) = RelX a la (psum n) (lps n) (psum (suc n)) (lps (suc n)) (st n) (fac-step (lps n) (δ n) (lδ n)) v₀ lv₀

  rlω : ∀ n → HB (Kn n) → HB Kω
  rlω n = Rω.rl n

  Lg-rlω : ∀ n t → LgB {Kn n} t → LgB {Kω} (rlω n t)
  Lg-rlω n = Rω.Lg-rl n

  -- 差树的极限: 各站新增的部分 d n 从出生的那一站直接改贴, 取部分和
  module Inc (d : ∀ n → HB (Kn n)) (ld : ∀ n → LgB {Kn n} (d n)) where
    U : ℕ → HB Kω
    U zero = rlω 0 (d 0)
    U (suc n) = U n ⊞ rlω (suc n) (d (suc n))

    lU : ∀ n → LgB {Kω} (U n)
    lU zero = Lg-rlω 0 (d 0) (ld 0)
    lU (suc n) = Lg-⊞ (U n) (rlω (suc n) (d (suc n))) (lU n) (Lg-rlω (suc n) (d (suc n)) (ld (suc n)))

    Uω : HB Kω
    Uω = hl U

    Lg-U : LgB {Kω} Uω
    Lg-U = (λ n → ⊞-fst (U n) (rlω (suc n) (d (suc n)))) , lU

  -- 拷贝: 旧种类经第 n+1 站走到极限 ≠ 直接从第 n 站走到极限
  private
    idxL : ∀ {c : HB S₀} {f : ℕ → HB S₀} → c ⊲[ a ] hl f → ℕ
    idxL hself = 0
    idxL (hlim n _) = n

    n≢sn : ∀ (n : ℕ) → ¬ (suc n ≡ n)
    n≢sn zero ()
    n≢sn (suc n) e = n≢sn n (cong pr e)
      where
      pr : ℕ → ℕ
      pr zero = zero
      pr (suc k) = k

  copy-lim : ∀ n (κ : EvKS₀.Kᵉ a (psum n) la (lps n) v₀ lv₀) → ¬ (Rω.km (suc n) (Rs.km n κ) ≡ Rω.km n κ)
  copy-lim n κ e = n≢sn n (cong (λ k → idxL (proj₂ k)) e)
```

## §5 闭项实例

外层 `A`-世界 $0$, 内层世界族全 $0$ (`AdmWCoh.wz`), 起点界 $0$, 增量恒为 $1$ (所以 $b_n = n$, 极限界 $\omega$); 第 $n$ 站新增的是新界自己那个种类上的 $\Omega$-节点 (`AdmEvFeed.Tower.Ωnew` 的形状).

```agda
open import OCF.Align.AdmWCoh using (wz; lg-wz)

module Inst where
  δ₁ : ℕ → HB S₀
  δ₁ _ = hs hz

  open Lim azero tt hz tt δ₁ (λ _ → tt) wz lg-wz
  open FacPath.PSum azero tt hz tt δ₁ (λ _ → tt)

  dnew : ∀ n → HB (Kn n)
  dnew n = hΩ (psum n , hself) (λ _ → hz)

  ldnew : ∀ n → LgB {Kn n} (dnew n)
  ldnew n = (λ lw e e′ pr → hself) , (λ x lx → tt)

  open Inc dnew ldnew

  Tω : HB Kω
  Tω = Uω

  Lg-Tω : LgB {Kω} Tω
  Lg-Tω = Lg-U

  -- 第 n 个增量改贴后的种类是 (b_n, hlim n hself): 极限界之下的第 n 个新种类
  kind-n : ∀ n → rlω n (dnew n) ≡ hΩ (psum n , hlim n hself) (λ _ → hz)
  kind-n n = refl
```

## §6 结论 (按档)

- **[定理]** `fac-self`, `tr-idˡ`, **`fac-tr`**, `fac-step`, `fac-steps`, **`fac-lim`**, `PSum.fac-ps`.
- **[定理]** `RelX.sim`, `RelX.Lg-rl` (对一般满足 `FacP` 的路径); `Lim.Lg-rlω`; **`Lim.Inc.Lg-U`** (差树的极限合法由形状给出).
- **[定理, 否定一侧]** **`Lim.copy-lim`**: 经下一站改贴与直接改贴给同一旧种类不同的极限种类.
- **[定理]** 实例 `Inst.Lg-Tω`, `Inst.kind-n`.
- **[判断]** 拷贝 `copy-lim` 的两个种类在一切世界里读到同一个界 (由 `FacP` 大概可证); 本篇没写.
- **[判断]** 不要 ⊞ 的结合律: `fac-lim` 的证明只把路径复合, 不把高度重新括号.
