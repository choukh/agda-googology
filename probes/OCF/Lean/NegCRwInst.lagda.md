# C 线重写成一个折叠, 否定一路 (四): 对构造一路折叠与实例的检查

> 不含记号. 入口 [NegCRw](NegCRw.lagda.md). 只读导入构造一路的 [CRwBase](CRwBase.lagda.md), [CRwIf](CRwIf.lagda.md), [CRwFold](CRwFold.lagda.md), [CRwPath](CRwPath.lagda.md), [CRw](CRw.lagda.md) (01:12 版), 不改它们. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **检查五件事: 决定是否正确; 折叠是否单调; 中间层是否合法; 接口的盲区落到闭项上会怎样; 证书是否区分实例.**
>
> 1. **`ok-dcl`, `ok-dcx` (定理, 正面, 对一切 `I`).** 折叠的两个决定都正确: 留 ⇒ 种类的层号 $j$ 满足 $j+1\lhd t$; 同层 ⇒ $j=t$; 在上 ⇒ 报的层就是 $j$. 构造一路的入口没有列这条 (原 C 线有 `correct₁`, `okU`); 这里补上, 证明对 `pick` 逐情形. 盲 (`OkCl` 的 `bas` 行是 $\top$): 底种类一律留, 不说层号 (同 `NegX1UpInst.OkU-bas-blind`).
> 2. **`Φ-acc-sm`, `Φ-acc-cx` (定理, 对一切 `I`, 一切层号与目标).** 重写后的 `Φ` 仍是部分和子句, 不保第一位置: $1\lhd\lim(0,1,1,\dots)$, $\Phi\,1\not\lhd\Phi\lim(0,1,1,\dots)$; 同底与跨底都是. 由本篇 §1 的只看三个值的引理 (`AccNMᶜ`, 同 `NegCRwAcc.AccNM`, 换成 `CRwBase` 的类型).
> 3. **`kept-not-LgB-X` (定理, 对一切 `I`).** 第 $\Omega_1\oplus1$ 层里合法的输入 `inΩ` (底种类 $\Omega_1$ 的结点, 分支是坐标自己; `Lg-inΩ`) 经同底折叠折到 $\Omega_1$ 层 (闭项 `TU` 的中间一步 `inU` 用的正是这个折叠), 留下 $\Omega_1$ 结点 (`outX-kept`, refl), 输出**不满足 `LgB`**. 中间层只有 `Sh` 与路径.
> 4. **`stay-no-PH` (定理, 边界).** 接口的盲区 `NegCRwIf.stayOf` (进入后世界不动) 落到闭项上: 在 `stayOf I₁` 里, $\Omega_1$ 层的地板 `topL` 在世界 $1$ 里**不带路径** (分支 $3$ 处的种类要 $3\lhd1$). 所以闭项公式 `TX`, `TU` (都要 `PH-topL`) 在这个实例上写不出来; 接口的律不保证闭项可写. 补一条律 "$e+1\lhd\mathrm{nxt}_0\,B\,e\,a$" (`I₁` 满足, `cover-I₁`) 可排除这个实例 (判断: 是否足够, 未证).
> 5. **`blind-TX` (定理, 盲).** 接口的另一个盲区 `NegCRwIf.constShOf` (回灌与坐标无关) 不挡闭项: 地板仍带路径 (`PH-topL′`), 同一公式 `TX′` 也有 `LgB` 证书 (`LgB-TX′`), 而 `TX′ ≢ TX` (`TX-differ`, 由深度 5 的有界展开结点数 215 对 386, `refl` 计算). 证书不区分回灌是否依赖坐标.
>
> **前提实例.** 2: 输入合法 (`Lg-fI`), $1\lhd$ 输入 (`one⊲fI`). 3: 输入合法 (`Lg-inΩ`), 世界 `wX` 合法 (`lg-wX`). 4: 可入的坐标 $3$ ($1\lhd3$, $3$ 合法). 5: 实例 `constShOf I₁`.
>
> **只否定什么.** 只否定: (a) 重写后的折叠保字面第一位置 (2); (b) 同底折叠的中间输出满足 `LgB` (3); (c) 接口的律保证闭项可写 (4); (d) 证书反映回灌依赖坐标 (5). **不否定**: `Sh-Φ`, `PH-ΦX`, 闭项 `TX`, `TU m`, `TU2` 的 `LgB` 证书 (都对); 决定的正确 (1 是正面定理); 读法. 本篇没有关闭任何路线.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegCRwInst where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRwIf
import OCF.Lean.CRwFold as CF
import OCF.Lean.CRwPath as CP
open import OCF.Lean.NegCRwIf using (constShOf; stayOf)
```

## §1 只看三个值的引理 (`CRwBase` 的类型)

与 `NegCRwAcc` §0, §1 逐行同式, 只是 `HB` 换成 `CRwBase.HB` (两个不同的数据类型).

```agda
module _ {S : KS} where
  num : ℕ → HB S
  num zero = hz
  num (suc n) = hs (num n)

  at : HB S → ℕ → HB S
  at (hl f) n = f n
  at x n = x

  lim-not-fin : ∀ {w} {f : ℕ → HB S} k → ¬ (hl f ⊲[ w ] num k)
  lim-not-fin zero ()
  lim-not-fin (suc k) (hsuc p) = lim-not-fin k p

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

fI : ∀ {S : KS} → ℕ → HB S
fI zero = hz
fI (suc n) = hs hz

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

module AccNMᶜ {S′ : KS} (a₀ a₁ aL : HB S′) (M G : ℕ → HB S′)
  (e₀ : a₀ ≡ num 1) (e₁ : a₁ ≡ hl M) (eM : ∀ n → M n ≡ num (suc n))
  (eL : aL ≡ hl G) (G0 : G 0 ≡ a₀) (Gs : ∀ n → G (suc n) ≡ G n ⊞ a₁) where

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

## §2 对一切 `I`: 决定正确, 折叠不单调, 中间层不合法

```agda
module ForI (I : CRwIf) where
  open CF I

  -- 决定正确的判据 (同 NegTySupIf.OkAt): j 是种类的层号
  OkAt : ∀ {L X t A} → Cd → Dc L X t A → Set
  OkAt {t = t} j (keep _ _) = hs j ⊲ t
  OkAt {t = t} j (same _) = j ≡ t
  OkAt j (above i _ _ _) = i ≡ j

  ok-pick : ∀ S {X t i A} (to : HB (Tw S i) → A) (u : hs i ⊲ X) r → OkAt {Tw S} {X} {t} i (pick S to u r)
  ok-pick S to u (inj₂ q) = q
  ok-pick S to u (inj₁ hself) = hself
  ok-pick S to u (inj₁ (hsuc hself)) = refl
  ok-pick S to u (inj₁ (hsuc (hsuc q))) = refl
  ok-pick S to u (inj₁ (hsuc (hlim n q))) = refl
  ok-pick S to u (inj₁ (hsuc (hLim {κ = ()} _ _)))

  -- 底种类: ⊤ (盲); 新种类: OkAt j
  OkCl : ∀ {S m X t κ} → Cl {S} m κ → Dc (Tw S) X t (E (Tw S m) κ) → Set
  OkCl (bas _ _) d = ⊤
  OkCl (nw j _ _) d = OkAt j d

  ok-dcl : ∀ {S m t κ} (pt : t ⊲ m) (lm : LgB m) (c : Cl {S} m κ) → OkCl c (dcl pt lm c)
  ok-dcl pt lm (bas κ₀ to) = tt
  ok-dcl {S} pt lm (nw j pj to) = ok-pick S to pj (cmpB pj pt tt lm)

  ok-dcx : ∀ {B t c} {κ : K (Tw S⊥ (hs c))} (lB : LgB B) (pt : t ⊲ B) (ev : hs c ⊲ B) (k : Cl {S⊥} (hs c) κ) →
           OkCl {S⊥} {hs c} {B} k (dcx lB pt ev k)
  ok-dcx lB pt ev (bas () _)
  ok-dcx lB pt ev (nw j pj to) = ok-pick S⊥ to (⊲ᴮ-tr pj ev) (cmpB (⊲ᴮ-tr pj ev) pt tt lB)

  mulC : ∀ {S : KS} n → mul {S} (hs hz) n ≡ num (suc n)
  mulC zero = refl
  mulC (suc n) = cong hs (mulC n)

  -- 同底目标
  Φ-acc-sm : ∀ s m a lm t (pt : t ⊲ m) b {w : Wd (Lev s t)} →
    ¬ (Φ s m a lm s t (sm pt) b (hs hz) tt ⊲[ w ] Φ s m a lm s t (sm pt) b (hl fI) tt)
  Φ-acc-sm s m a lm t pt b =
    AccNMᶜ.acc-not-mono _ _ _ (mul (hs hz)) (Σ⁺ (λ n → Φ s m a lm s t (sm pt) b (fI n) tt))
      refl refl mulC refl refl (λ n → refl)

  -- 跨底目标 (Ω₁ 层到可数层号)
  phI : ∀ B n → PH PSX B (fI n)
  phI B zero = tt
  phI B (suc n) = tt

  Φ-acc-cx : ∀ a t B lB (pt : t ⊲ B) b {w : Wd (Lev b⊥ t)} →
    ¬ (Φ bX hz a tt b⊥ t (cx B lB pt) b (hs hz) tt ⊲[ w ] Φ bX hz a tt b⊥ t (cx B lB pt) b (hl fI) (phI B))
  Φ-acc-cx a t B lB pt b =
    AccNMᶜ.acc-not-mono _ _ _ (mul (hs hz)) (Σ⁺ (λ n → Φ bX hz a tt b⊥ t (cx B lB pt) b (fI n) (phI B n)))
      refl refl mulC refl refl (λ n → refl)
```

**中间层.** 第 $\Omega_1\oplus1$ 层 (`Lev bX 1` 字面是 `step XS`) 里底种类 $\Omega_1$ (`κΩ = (0 , inj₂ tt)`) 的结点, 分支在坐标 $c$ 处是 $c$ 自己 (`lift`). 合法. 折到 $\Omega_1$ 层: 留下, 分支 $c\mapsto\Phi(\mathrm{lift}\,c)$, 在 $1\lhd\lim(0,1,1,\dots)$ 处不单调.

```agda
  κΩ : K XS
  κΩ = hz , inj₂ tt

  lift : Cd → HB (step XS)
  lift hz = hz
  lift (hs c) = hs (lift c)
  lift (hl f) = hl (λ n → lift (f n))
  lift (hΩ () _)

  lift-⊲ : ∀ {c c′ w} {x : ⊤} → c ⊲[ x ] c′ → lift c ⊲[ w ] lift c′
  lift-⊲ hself = hself
  lift-⊲ (hsuc p) = hsuc (lift-⊲ p)
  lift-⊲ (hlim n p) = hlim n (lift-⊲ p)
  lift-⊲ (hLim {κ = ()} _ _)

  Lg-lift : ∀ c → LgB c → LgB (lift c)
  Lg-lift hz l = tt
  Lg-lift (hs c) l = Lg-lift c l
  Lg-lift (hl f) (st , l) = (λ n → lift-⊲ (st {tt} n)) , (λ n → Lg-lift (f n) (l n))
  Lg-lift (hΩ () _) l

  inΩ : HB (Lev bX (hs hz))
  inΩ = hΩ (inj₁ κΩ) lift

  Lg-inΩ : LgB inΩ
  Lg-inΩ = (λ lw e e′ p → lift-⊲ p) , (λ {w} {c} lw e → Lg-lift c (lgB⊲ e tt (proj₂ (proj₁ lw hz))))

  outX : HB XS → HB XS
  outX b = Φ bX (hs hz) (wf bX (hs hz)) tt bX hz (sm (z⊲ᴮ (hs hz))) b inΩ tt

  outX-kept : ∀ b → outX b ≡ hΩ κΩ (λ c → Φ bX (hs hz) (wf bX (hs hz)) tt bX hz (sm (z⊲ᴮ (hs hz))) b (lift c) tt)
  outX-kept b = refl

  -- 合法的世界: 每个分量的界都是 lim(0,1,1,…)
  wT : ∀ x → Wd (Tw S⊥ x)
  wT hz = tt
  wT (hs x) = wT x , hz
  wT (hl f) = λ n → wT (f n)
  wT (hΩ () _)

  lgT : ∀ x → LgW (Tw S⊥ x) (wT x)
  lgT hz = tt
  lgT (hs x) = lgT x , tt
  lgT (hl f) = λ n → lgT (f n)
  lgT (hΩ () _)

  wX : Wd XS
  wX c = wT c , hl fI

  lg-wX : LgW XS wX
  lg-wX c = lgT c , Lg-fI

  kept-not-LgB-X : ∀ b → ¬ LgB (outX b)
  kept-not-LgB-X b (mo , _) =
    AccNMᶜ.acc-not-mono _ _ _ (mul (hs hz))
      (Σ⁺ (λ n → Φ bX (hs hz) (wf bX (hs hz)) tt bX hz (sm (z⊲ᴮ (hs hz))) b (lift (fI n)) tt))
      refl refl mulC refl refl (λ n → refl)
      (mo {w = wX} {c = hs hz} {c′ = hl fI} lg-wX one⊲fI hself one⊲fI)
```

## §3 接口盲区落到闭项: 世界不动则地板不带路径

`stayOf I₁`: 进入 $\Omega_1$ 的分支后世界仍是 $B$. 地板的分支 $3$ (`gt 3`) 的根是第 3 层的种类 $(2,\cdot)$, 证据要 $3\lhd B$.

```agda
open import OCF.Lean.CRw using (I₁; W₀; TX; LgB-TX)

module St = CF (stayOf I₁)

three : Cd
three = hs (hs (hs hz))

no31 : ¬ (three ⊲ hs hz)
no31 (hsuc ())

stay-no-PH : ¬ St.PH St.PSX W₀ St.topL
stay-no-PH (_ , p) = no31 (proj₁ (p three (hsuc (hsuc hself) , tt)))

-- 补的律在 I₁ 上成立
cover-I₁ : ∀ {B e} (a : CRwIf.Adm₀ I₁ B e) → hs e ⊲ CRwIf.nxt₀ I₁ B e a
cover-I₁ a = hself
```

## §4 证书的盲: 回灌换成常值, 闭项仍有证书

`constShOf I₁` 只换回灌, 可入与新世界同 `I₁`. 地板的路径逐字同 `CRw` §2 (证明不读回灌).

```agda
I′ : CRwIf
I′ = constShOf I₁

module C′ = CF I′
module P′ = CP I′

PH-cd′ : ∀ {W} (e : Cd) → C′.PH C′.PSX W (ι {Cd} {λ c → C′.Tw S⊥ (hs c)} hz (up e))
PH-cd′ hz = tt
PH-cd′ (hs e) = PH-cd′ e
PH-cd′ (hl f) = λ n → PH-cd′ (f n)
PH-cd′ (hΩ () _)

PH-ιu′ : ∀ c W → hs c ⊲ W → ∀ (e : HB (C′.Tw S⊥ c)) → C′.PH C′.PSX W (ι {Cd} {λ c → C′.Tw S⊥ (hs c)} c (up e))
PH-ιu′ c W q hz = tt
PH-ιu′ c W q (hs e) = PH-ιu′ c W q e
PH-ιu′ c W q (hl f) = λ n → PH-ιu′ c W q (f n)
PH-ιu′ c W q (hΩ κ g) = q , λ e _ → PH-ιu′ c W q (g e)

PH-Ωc′ : ∀ c W → hs c ⊲ W → C′.PH C′.PSX W (ι {Cd} {λ c → C′.Tw S⊥ (hs c)} c (C′.topT S⊥ hz (hs c)))
PH-Ωc′ hz W q = q , λ e a → PH-cd′ e
PH-Ωc′ (hs c) W q = q , λ e a → PH-ιu′ (hs c) W q e
PH-Ωc′ (hl f) W q = q , λ e a → PH-ιu′ (hl f) W q e
PH-Ωc′ (hΩ () _) W q

PH-gt′ : ∀ y W → y ⊲ W → C′.PH C′.PSX W (C′.gt y)
PH-gt′ hz W q = tt
PH-gt′ (hs c) W q = P′.PH-⊞ C′.PSX (C′.gt c) (ι {Cd} {λ c → C′.Tw S⊥ (hs c)} c (C′.topT S⊥ hz (hs c)))
  (PH-gt′ c W (⊲ᴮ-tr (hsuc hself) q)) (PH-Ωc′ c W q)
PH-gt′ (hl f) W q = λ n → PH-gt′ (f n) W (⊲ᴮ-tr (hlim n hself) q)
PH-gt′ (hΩ () _) W q

PH-topL′ : ∀ B → hs hz ⊲ B → C′.PH C′.PSX B C′.topL
PH-topL′ B o = o , λ y a → PH-gt′ y (hs y) (hsuc hself)

TX′ : Cd
TX′ = C′.Φ C′.bX hz (C′.wf C′.bX hz) tt C′.b⊥ hz (C′.cx W₀ tt (z⊲ᴮ W₀)) hz C′.topL (PH-topL′ W₀ hself)

LgB-TX′ : LgB TX′
LgB-TX′ = C′.sh→lg TX′ (C′.Sh-Φ C′.bX hz (C′.wf C′.bX hz) tt C′.b⊥ hz (C′.cx W₀ tt (z⊲ᴮ W₀)) hz C′.topL (PH-topL′ W₀ hself))

-- 回灌与坐标无关 (refl)
sh-const : ∀ B c c′ → CRwIf.sh₀ I′ B c ≡ CRwIf.sh₀ I′ B c′
sh-const B c c′ = refl

blind-cert : LgB TX × LgB TX′
blind-cert = LgB-TX , LgB-TX′
```

## §5 两个闭项不同 (定理, 由有界展开的结点数)

`szN k`: 深度 $k$, 每个 ℕ-极限只展开前 $k$ 项的结点数 (同 `CRwCmp.szN`). 深度 $4$ 两者都是 $41$ (不区分); 深度 $5$ 是 $215$ 与 $386$ (`refl`). 由此 `TX ≢ TX′` 是定理 (`cong` 一步); 数值本身是计算, 不说明哪个大.

```agda
open import Data.Nat using (_+_)

szN : ℕ → Cd → ℕ
szsN : ℕ → ℕ → (ℕ → Cd) → ℕ
szN zero x = 0
szN (suc k) hz = 1
szN (suc k) (hs x) = suc (szN (suc k) x)
szN (suc k) (hl f) = suc (szsN k (suc k) f)
szN (suc k) (hΩ () g)
szsN k zero f = 0
szsN k (suc i) f = szN k (f i) + szsN k i f

sz5-TX : szN 5 TX ≡ 215
sz5-TX = refl

sz5-TX′ : szN 5 TX′ ≡ 386
sz5-TX′ = refl

TX-differ : ¬ (TX ≡ TX′)
TX-differ e with trans (sym sz5-TX) (trans (cong (szN 5) e) sz5-TX′)
... | ()

blind-TX : LgB TX × LgB TX′ × ¬ (TX ≡ TX′)
blind-TX = LgB-TX , LgB-TX′ , TX-differ
```
