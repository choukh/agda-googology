# 读回包 + 第 ω+1 级折叠, 否定一路 (一): 码的弱化, 极限站, 码世界的更新

> 不含记号. 入口 [NegLvRd](NegLvRd.lagda.md). 对着接口 [LvRdIf](LvRdIf.lagda.md) ("接口定稿 2026-11-05 14:28 (编译通过)", 变更记录: 无) 写, 导入它, 不另造接口. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> 针对嫌疑 (ii): "码在界长高时的弱化与码的相等判定是否相容, 两个码弱化后是否可能相等而原来不等 (拷贝合并)".
>
> 1. **嫌疑 (ii) 不成立 (定理, 反模型).** `wkLaw : WkLaw`: 沿路径把码嫁接 (`wkC p k`: 码 $k$ 的路径接上 $p$ 再取码) 满足接口 §7 的全部五条律. 关键是 `cd-tr` (接上路径的码 = 嫁接 `gr`), `gr-inj` (嫁接对尾部单射), `gr-assoc` (嫁接结合), `cdB-pB` (码与证据往返). 所以**弱化后不会合并**: 原来不等的码弱化后仍不等 (`wkC-inj`), 判定的结果不变 (`wk-≟`).
> 2. **W1 的极限站: 沿路径的弱化不相干 (定理, 否定一侧), 但码上有相干的规范弱化 (定理, 反模型).** 外层界是部分和 $b_n$ (`FacPath.PSum`), 极限界 $B=\mathrm{hl}\,b_\bullet$. `copy-code`: 经第 $n+1$ 站进极限与直接从第 $n$ 站进极限给出不同的码 (`LvFbFac.copy-lim` 的码版本). 但对**任一**部分和塔 (`Canon`), `canon n : Code a (b_n) → Code a B` 相干 (`canon-coh`: `canon (n+1) (wkS n k) ≡ canon n k`) 且保目标 (`canon-tgt`): 每个码沿 "它出生的那一站" 进极限; 判定 "这个码是不是上一站的码接上一步" 是码的前缀判定 (`prefix?`, 数据上的判定). 对照 `EvFoldLim.no-coh-ev` (种类带证据、沿证据改贴时**没有**相干族): 换成码之后相干族存在, 代价是它不是沿路径的弱化 (`canon≠wk`). 所以 "W1 的极限站有拷贝" 在码世界里**不是**墙.
> 3. **码世界的更新可满足 (定理, 反模型).** `raiseCd : Raise`: `Cd` 的相等可判定 (`≟Cd`), 由 Hedberg 有 UIP, 更新在一切码上有精确的 `at`. 接口 §4 的世界没有任何禁忌.
> 4. **同一坐标的码拷贝不能随更新同步 (定理, 对一切 `Raise`).** `sync→hz`: 对**任一**满足接口律的 `R : Raise`, 若更新前码 `kfin 2` 与它的拷贝 `c2′ = cP (cL 3 (cP cH))` (同为坐标 2, 槽类型都是 `Sk 2`, 定义相等) 的槽相等, 更新后仍相等, 则增量是 $0$. 这是 `NegFamFeed.offF→rd0` 在码世界里的对应. **只否定**按坐标同步拷贝; 接口的折叠只读 `kω` (第 ω 层只有这一个码, 判断) 与各级自己的 `kfin`, 不读拷贝, 所以这一条不否定接口 (判断).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegLvRdWk where

open import Data.Nat using (ℕ; zero; suc)
import Data.Nat as N
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (isYes)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg)
open import OCF.Align.HtTowerTy
open import OCF.Align.LvFbCode
  using (RA; aH; aP; aL; RB; bH; bP; bL; bΩ; vA; vAP; vAL; tA; pA; pAP; pAL; vA-prop;
         vB; vBP; vBL; vBΩ; tB; pB; pBP; pBL; pBΩ; vB-prop; Code; tgt; pth; ≟RA; code-≟;
         _⊲₀[_]_; cdA; vcdA; tcdA; cdB; cd; cd-tgt)
open import OCF.Align.LvFbFac using (module FacPath)
open import OCF.Align.NegFamFeed using (⊞≡→hz)
open import OCF.Align.LvRdIf
open import OCF.Align.FamFoldIf using (Sk)
```

## §1 码的嫁接

`gr X s`: 把码 $X$ 底部的 `bH` 换成 $s$. 路径接上 $X$ 之后的码就是嫁接 (`cd-tr`).

```agda
gr : RB → RB → RB
gr bH s = s
gr (bP r) s = bP (gr r s)
gr (bL n r) s = bL n (gr r s)
gr (bΩ ra r) s = bΩ ra (gr r s)

gr-assoc : ∀ x y r → gr x (gr y r) ≡ gr (gr x y) r
gr-assoc bH y r = refl
gr-assoc (bP x) y r = cong bP (gr-assoc x y r)
gr-assoc (bL n x) y r = cong (bL n) (gr-assoc x y r)
gr-assoc (bΩ ra x) y r = cong (bΩ ra) (gr-assoc x y r)

cd-tr : ∀ {a c b B} (p : c ⊲₀[ a ] b) (X : b ⊲₀[ a ] B) → cdB (⊲ᴮ-tr p X) ≡ gr (cdB X) (cdB p)
cd-tr p hself = refl
cd-tr p (hsuc X) = cong bP (cd-tr p X)
cd-tr p (hlim n X) = cong (bL n) (cd-tr p X)
cd-tr p (hLim e X) = cong (bΩ (cdA e)) (cd-tr p X)

unP unL unΩ : RB → RB
unP (bP r) = r
unP r = r
unL (bL n r) = r
unL r = r
unΩ (bΩ _ r) = r
unΩ r = r

gr-inj : ∀ r {s s′} → gr r s ≡ gr r s′ → s ≡ s′
gr-inj bH e = e
gr-inj (bP r) e = gr-inj r (cong unP e)
gr-inj (bL n r) e = gr-inj r (cong unL e)
gr-inj (bΩ ra r) e = gr-inj r (cong unΩ e)
```

码与证据往返: 证据 `pB … r v` 的码就是 $r$.

```agda
cdA-pA  : ∀ a r v → cdA (pA a r v) ≡ r
cdA-pAP : ∀ a r v → cdA (pAP a r v) ≡ aP r
cdA-pAL : ∀ a n r v → cdA (pAL a n r v) ≡ aL n r
cdA-pA a aH v = refl
cdA-pA a (aP r) v = cdA-pAP a r v
cdA-pA a (aL n r) v = cdA-pAL a n r v
cdA-pAP (asuc a) r v = cong aP (cdA-pA a r v)
cdA-pAL (alim f) n r v = cong (aL n) (cdA-pA (f n) r v)

cdB-pB  : ∀ a b r v → cdB (pB a b r v) ≡ r
cdB-pBP : ∀ a b r v → cdB (pBP a b r v) ≡ bP r
cdB-pBL : ∀ a b n r v → cdB (pBL a b n r v) ≡ bL n r
cdB-pBΩ : ∀ a b ra r v → cdB (pBΩ a b ra r v) ≡ bΩ ra r
cdB-pB a b bH v = refl
cdB-pB a b (bP r) v = cdB-pBP a b r v
cdB-pB a b (bL n r) v = cdB-pBL a b n r v
cdB-pB a b (bΩ ra r) v = cdB-pBΩ a b ra r v
cdB-pBP a (hs b) r v = cong bP (cdB-pB a b r v)
cdB-pBL a (hl f) n r v = cong (bL n) (cdB-pB a (f n) r v)
cdB-pBΩ a (hΩ κ g) ra r (va , v) =
  trans (cong (λ t → bΩ t (cdB (pB a (g (tA a ra va)) r v))) (cdA-pA a ra va)) (cong (bΩ ra) (cdB-pB a (g (tA a ra va)) r v))

-- 码相等由第一分量给出 (合法性是命题)
code-ext : ∀ {a b} (k k′ : Code a b) → proj₁ k ≡ proj₁ k′ → k ≡ k′
code-ext {a} {b} (r , v) (.r , v′) refl = cong (r ,_) (vB-prop a b r v v′)
```

## §2 嫌疑 (ii) 的反模型: 沿路径嫁接满足 `WkLaw`

```agda
wkC : ∀ {a b B} → b ⊲₀[ a ] B → Code a b → Code a B
wkC X k = cd (⊲ᴮ-tr (pth k) X)

wkC-r : ∀ {a b B} (X : b ⊲₀[ a ] B) (k : Code a b) → proj₁ (wkC X k) ≡ gr (cdB X) (proj₁ k)
wkC-r {a} {b} X (r , v) = trans (cd-tr (pB a b r v) X) (cong (gr (cdB X)) (cdB-pB a b r v))

wkC-tgt : ∀ {a b B} (X : b ⊲₀[ a ] B) (k : Code a b) → tgt (wkC X k) ≡ tgt k
wkC-tgt X k = cd-tgt (⊲ᴮ-tr (pth k) X)

-- 弱化是单射: 原来不等的两个码弱化后仍不等
wkC-inj : ∀ {a b B} (X : b ⊲₀[ a ] B) (k k′ : Code a b) → wkC X k ≡ wkC X k′ → k ≡ k′
wkC-inj X k k′ e = code-ext k k′ (gr-inj (cdB X) (trans (sym (wkC-r X k)) (trans (cong proj₁ e) (wkC-r X k′))))

wkC-≟ : ∀ {a b B} (X : b ⊲₀[ a ] B) (k k′ : Code a b) → isYes (code-≟ (wkC X k) (wkC X k′)) ≡ isYes (code-≟ k k′)
wkC-≟ X k k′ with code-≟ (wkC X k) (wkC X k′) | code-≟ k k′
... | yes _ | yes _ = refl
... | no _ | no _ = refl
... | yes e | no ne = ⊥-elim (ne (wkC-inj X k k′ e))
... | no ne | yes e = ⊥-elim (ne (cong (wkC X) e))

wkC-tr : ∀ {a b b′ b″} (p : b ⊲₀[ a ] b′) (q : b′ ⊲₀[ a ] b″) k → wkC q (wkC p k) ≡ wkC (⊲ᴮ-tr p q) k
wkC-tr p q k = code-ext (wkC q (wkC p k)) (wkC (⊲ᴮ-tr p q) k)
  (trans (wkC-r q (wkC p k))
  (trans (cong (gr (cdB q)) (wkC-r p k))
  (trans (gr-assoc (cdB q) (cdB p) (proj₁ k))
  (trans (cong (λ t → gr t (proj₁ k)) (sym (cd-tr p q))) (sym (wkC-r (⊲ᴮ-tr p q) k))))))

wkLaw : WkLaw
wkLaw = record { wk = wkC ; wk-tgt = wkC-tgt ; wk-inj = wkC-inj ; wk-≟ = wkC-≟ ; wk-tr = wkC-tr }
```

## §3 W1 的极限站: 码的前缀判定与相干的规范弱化

```agda
hdL : RB → ℕ
hdL (bL n _) = n
hdL _ = 0

hdΩ : RB → RA
hdΩ (bΩ ra _) = ra
hdΩ _ = aH

-- "t 是不是 r 接上某个 s": 码的数据判定
prefix? : ∀ r t → Dec (Σ RB (λ s → t ≡ gr r s))
prefix? bH t = yes (t , refl)
prefix? (bP r) (bP t) with prefix? r t
... | yes (s , e) = yes (s , cong bP e)
... | no ne = no (λ { (s , e) → ne (s , cong unP e) })
prefix? (bP r) bH = no (λ { (s , ()) })
prefix? (bP r) (bL m t) = no (λ { (s , ()) })
prefix? (bP r) (bΩ sa t) = no (λ { (s , ()) })
prefix? (bL n r) (bL m t) with n N.≟ m | prefix? r t
... | yes refl | yes (s , e) = yes (s , cong (bL n) e)
... | yes refl | no ne = no (λ { (s , e) → ne (s , cong unL e) })
... | no ne | _ = no (λ { (s , e) → ne (sym (cong hdL e)) })
prefix? (bL n r) bH = no (λ { (s , ()) })
prefix? (bL n r) (bP t) = no (λ { (s , ()) })
prefix? (bL n r) (bΩ sa t) = no (λ { (s , ()) })
prefix? (bΩ ra r) (bΩ sa t) with ≟RA ra sa | prefix? r t
... | yes refl | yes (s , e) = yes (s , cong (bΩ ra) e)
... | yes refl | no ne = no (λ { (s , e) → ne (s , cong unΩ e) })
... | no ne | _ = no (λ { (s , e) → ne (sym (cong hdΩ e)) })
prefix? (bΩ ra r) bH = no (λ { (s , ()) })
prefix? (bΩ ra r) (bP t) = no (λ { (s , ()) })
prefix? (bΩ ra r) (bL m t) = no (λ { (s , ()) })
```

嫁接的码往回读: 合法性与目标 (沿 $X$ 归纳; `hLim` 处沿 `tcdA` 搬, 搬的是 `A` 上的相等, 不比较高度).

```agda
module Back (a : A) where
  tA-eq : ∀ {c a′} (e : c ⊲ a′) (va : vA a′ (cdA e)) → tA a′ (cdA e) va ≡ c
  tA-eq e va = trans (cong (tA _ (cdA e)) (vA-prop _ (cdA e) va (vcdA e))) (tcdA e)

  vgr : ∀ {b B : HB S₀} (X : b ⊲₀[ a ] B) s → vB a B (gr (cdB X) s) → vB a b s
  vgr hself s v = v
  vgr (hsuc X) s v = vgr X s v
  vgr (hlim n X) s v = vgr X s v
  vgr (hLim {g = g} e X) s (va , v) = vgr X s (subst (λ z → vB a (g z) (gr (cdB X) s)) (tA-eq e va) v)

  tB-sub′ : ∀ (g : A → HB S₀) r {t x} (e : t ≡ x) (v : vB a (g t) r) →
            tB a (g x) r (subst (λ z → vB a (g z) r) e v) ≡ tB a (g t) r v
  tB-sub′ g r refl v = refl

  tgr : ∀ {b B : HB S₀} (X : b ⊲₀[ a ] B) s (v : vB a B (gr (cdB X) s)) → tB a b s (vgr X s v) ≡ tB a B (gr (cdB X) s) v
  tgr hself s v = refl
  tgr (hsuc X) s v = tgr X s v
  tgr (hlim n X) s v = tgr X s v
  tgr (hLim {g = g} e X) s (va , v) =
    trans (tgr X s (subst (λ z → vB a (g z) (gr (cdB X) s)) (tA-eq e va) v)) (tB-sub′ g (gr (cdB X) s) (tA-eq e va) v)

  tB-cv : ∀ (b : HB S₀) {t t′} (e : t ≡ t′) (v : vB a b t) → tB a b t′ (subst (vB a b) e v) ≡ tB a b t v
  tB-cv b refl v = refl
```

**任一部分和塔.** 外层 `A`-世界 $a$, 起点 $b_0$, 增量 $\sigma_n$ (接口 `Stages` 的形状, 合法). 第 $n$ 站的码 `CS n`, 极限界的码 `CB`.

```agda
module Canon (a : A) (la : Lg a) (b₀ : HB S₀) (lb₀ : LgB b₀) (σ : ℕ → HB S₀) (lσ : ∀ n → LgB (σ n)) where
  open FacPath.PSum a la b₀ lb₀ σ lσ using (psum; st; B; Xn)
  open Back a

  CS : ℕ → Set
  CS n = Code a (psum n)

  CB : Set
  CB = Code a B

  pre : ℕ → RB
  pre n = cdB (st {a} n)

  -- 相邻站与进极限: 都是沿路径的弱化 (W1 的写法换成码)
  wkS : ∀ n → CS n → CS (suc n)
  wkS n = wkC (st n)

  wkω : ∀ n → CS n → CB
  wkω n = wkC (Xn n)

  hd-wkω : ∀ n k → hdL (proj₁ (wkω n k)) ≡ n
  hd-wkω n k = refl

  n≢sn : ∀ (n : ℕ) → ¬ (suc n ≡ n)
  n≢sn zero ()
  n≢sn (suc n) e = n≢sn n (cong N.pred e)

  -- 否定一侧: 沿路径的弱化在极限处有拷贝
  copy-code : ∀ n (k : CS n) → ¬ (wkω (suc n) (wkS n k) ≡ wkω n k)
  copy-code n k e = n≢sn n (cong (λ j → hdL (proj₁ j)) e)

  -- 反模型: 规范的码, 沿码出生的那一站进极限
  canon : ∀ n → CS n → CB
  go : ∀ n (t : RB) (v : vB a (psum (suc n)) t) → Dec (Σ RB (λ s → t ≡ gr (pre n) s)) → CB
  canon zero k = wkω 0 k
  canon (suc n) (t , v) = go n t v (prefix? (pre n) t)
  go n t v (yes (s , e)) = canon n (s , vgr (st n) s (subst (vB a (psum (suc n))) e v))
  go n t v (no _) = bL (suc n) t , v

  canon-coh : ∀ n (k : CS n) → canon (suc n) (wkS n k) ≡ canon n k
  canon-coh n k = h (prefix? (pre n) (proj₁ (wkS n k)))
    where
    h : ∀ d → go n (proj₁ (wkS n k)) (proj₂ (wkS n k)) d ≡ canon n k
    h (yes (s , e)) = cong (canon n) (code-ext _ k (gr-inj (pre n) (trans (sym e) (wkC-r (st n) k))))
    h (no ne) = ⊥-elim (ne (proj₁ k , wkC-r (st n) k))

  canon-tgt : ∀ n (k : CS n) → tgt (canon n k) ≡ tgt k
  go-tgt : ∀ n t v d → tgt (go n t v d) ≡ tB a (psum (suc n)) t v
  canon-tgt zero k = wkC-tgt (Xn 0) k
  canon-tgt (suc n) (t , v) = go-tgt n t v (prefix? (pre n) t)
  go-tgt n t v (yes (s , e)) =
    trans (canon-tgt n (s , vgr (st n) s (subst (vB a (psum (suc n))) e v)))
          (trans (tgr (st n) s (subst (vB a (psum (suc n))) e v)) (tB-cv (psum (suc n)) e v))
  go-tgt n t v (no _) = refl
```

**实例**: 起点 $0$, 增量恒为 $1$ ($b_n = n$, 极限界 $\omega$). 第 1 站的码 `bP bH` (目标 $0$) 经规范弱化进第 $0$ 支, 经沿路径的弱化进第 $1$ 支: 规范弱化不是沿路径的弱化.

```agda
module CanonInst = Canon azero tt hz tt (λ _ → hs hz) (λ _ → tt)

k10 : CanonInst.CS 1
k10 = bP bH , tt

canon-k10 : hdL (proj₁ (CanonInst.canon 1 k10)) ≡ 0
canon-k10 = refl

canon≠wk : ¬ (CanonInst.canon 1 k10 ≡ CanonInst.wkω 1 k10)
canon≠wk e = CanonInst.n≢sn 0 (sym (cong (λ j → hdL (proj₁ j)) e))
```

## §4 码世界的更新: 可满足; 拷贝不能同步

```agda
unCP unCL : Cd → Cd
unCP (cP r) = r
unCP r = r
unCL (cL n r) = r
unCL r = r

hdC : Cd → ℕ
hdC (cL n _) = n
hdC _ = 0

≟Cd : (r s : Cd) → Dec (r ≡ s)
≟Cd cH cH = yes refl
≟Cd cH (cP s) = no (λ ())
≟Cd cH (cL m s) = no (λ ())
≟Cd (cP r) cH = no (λ ())
≟Cd (cP r) (cP s) with ≟Cd r s
... | yes refl = yes refl
... | no ne = no (λ e → ne (cong unCP e))
≟Cd (cP r) (cL m s) = no (λ ())
≟Cd (cL n r) cH = no (λ ())
≟Cd (cL n r) (cP s) = no (λ ())
≟Cd (cL n r) (cL m s) with n N.≟ m | ≟Cd r s
... | yes refl | yes refl = yes refl
... | no ne | _ = no (λ e → ne (cong hdC e))
... | yes refl | no ne = no (λ e → ne (cong unCL e))

cd-uip : ∀ {k k′ : Cd} (e e′ : k ≡ k′) → e ≡ e′
cd-uip = Decidable⇒UIP.≡-irrelevant ≟Cd

module RC (v : Wld) (k₀ : Cd) (δ : HB (Pc k₀)) where
  tp : ∀ {k} → k₀ ≡ k → HB (Pc k)
  tp e = subst (λ j → HB (Pc j)) e δ

  upd : ∀ {k} → Dec (k₀ ≡ k) → HB (Pc k) → HB (Pc k)
  upd (yes e) x = x ⊞ tp e
  upd (no _) x = x

  upd-at : ∀ (d : Dec (k₀ ≡ k₀)) x → upd d x ≡ x ⊞ δ
  upd-at (yes e) x = cong (λ e′ → x ⊞ tp e′) (cd-uip e refl)
  upd-at (no ne) x = ⊥-elim (ne refl)

  upd-off : ∀ {k} (d : Dec (k₀ ≡ k)) x → ¬ (k₀ ≡ k) → upd d x ≡ x
  upd-off (yes e) x ne = ⊥-elim (ne e)
  upd-off (no _) x ne = refl

  upd-mono : ∀ {k} (d : Dec (k₀ ≡ k)) x {w} → x ⊲[ w ] upd d x
  upd-mono (yes e) x = ⊞-fst x (tp e)
  upd-mono (no _) x = hself

  lg-tp : ∀ {k} (e : k₀ ≡ k) → LgB δ → LgB (tp e)
  lg-tp refl l = l

  upd-lg : ∀ {k} (d : Dec (k₀ ≡ k)) x → LgB δ → LgB x → LgB (upd d x)
  upd-lg (yes e) x lδ lx = Lg-⊞ x (tp e) lx (lg-tp e lδ)
  upd-lg (no _) x lδ lx = lx

  raise : Wld
  raise k = upd (≟Cd k₀ k) (v k)

raiseCd : Raise
raiseCd = record
  { raise = RC.raise
  ; at = λ v k₀ δ → RC.upd-at v k₀ δ (≟Cd k₀ k₀) (v k₀)
  ; off = λ v k₀ δ k ne → RC.upd-off v k₀ δ (≟Cd k₀ k) (v k) ne
  ; mono = λ v k₀ δ k → RC.upd-mono v k₀ δ (≟Cd k₀ k) (v k)
  ; legal = λ v k₀ δ lδ lv k → RC.upd-lg v k₀ δ (≟Cd k₀ k) (v k) lδ (lv k) }
```

**拷贝.** 坐标 $2$ 在外层界 $\omega+1$ 之下有码 `kfin 2` 与 `c2′` (经 $\omega$ 的第 3 支再退一步). 两处槽类型都是 `Sk 2` (定义相等). 同步 = 两处的槽相等.

```agda
c2′ : Cd
c2′ = cP (cL 3 (cP cH))

c2≢ : ¬ (kfin 2 ≡ c2′)
c2≢ ()

Sync : Wld → Set
Sync v = v (kfin 2) ≡ v c2′

sync→hz : ∀ (R : Raise) v (δ : HB (Sk 2)) → Sync v → Sync (Raise.raise R v (kfin 2) δ) → δ ≡ hz
sync→hz R v δ s s′ =
  ⊞≡→hz (v (kfin 2)) δ
    (trans (sym (Raise.at R v (kfin 2) δ)) (trans s′ (trans (Raise.off R v (kfin 2) δ c2′ c2≢) (sym s))))

-- 前提实例: 全 0 的世界同步; 增量 0 的更新保同步 (所以结论不是空话, 也不能加强到 "一切更新都破坏同步")
v0 : Wld
v0 k = hz

sync0 : Sync v0
sync0 = refl

sync0′ : Sync (Raise.raise raiseCd v0 (kfin 2) hz)
sync0′ = refl

-- 非零增量确实破坏同步
one≢z : ¬ (_≡_ {A = HB (Sk 2)} (hs hz) hz)
one≢z ()

desync : ¬ Sync (Raise.raise raiseCd v0 (kfin 2) (hs hz))
desync s = one≢z (sync→hz raiseCd v0 (hs hz) sync0 s)
```

## §5 结论 (按档)

- **[定理, 反模型]** `cd-tr`, `gr-inj`, `gr-assoc`, `cdB-pB`, `code-ext`; `wkC-tgt`, **`wkC-inj`**, **`wkC-≟`**, **`wkC-tr`**; **`wkLaw : WkLaw`**. 嫌疑 (ii) 的 "弱化后合并" 不成立.
- **[定理, 否定一侧]** `Canon.copy-code`: 沿路径的弱化进 W1 的极限有拷贝.
- **[定理, 反模型]** `prefix?`, `Back.vgr`, `Back.tgr`; **`Canon.canon-coh`**, **`Canon.canon-tgt`** (对任一部分和塔); 实例 `canon-k10`, `canon≠wk`.
- **[定理, 反模型]** `≟Cd`, `cd-uip`, **`raiseCd : Raise`**.
- **[定理, 对一切 `Raise`]** **`sync→hz`**; 前提实例 `sync0`, `sync0′`, `desync`.
- **[判断]** 第 ω 层在 `Cd` 里只有一个码 `kω` (`Pc` 只在 `cP cH` 给 `Gω`), 所以接口 §5, §6 的律没有拷贝问题; 拷贝只在有限坐标, 而有限级的折叠只读自己的 `kfin`.
- **[判断]** `canon` 不进接口: 接口 `Stages` 只到有限站; 走到极限站时, 规范弱化给出相干, 代价是它不是 `WkLaw.wk` 沿 `hlim n hself` 的值 (`canon≠wk`).
