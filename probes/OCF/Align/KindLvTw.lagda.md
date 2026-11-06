# 按级回灌 (四): 在新塔的层号对角上按级回灌的最终坍缩, 无条件闭项

> 不含记号. 入口 [KindLv](KindLv.lagda.md), 接口 [KindLvIf](KindLvIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提. 闭项, 证书, FGH 无模块参数.
>
> - **§1 一般坍缩 `collLv : CollLvFbTy`.** 同 `NewTwrColl.collG` 的式子 (基世界里把 $\Omega_\Lambda$ 的数据折到第 0 层, `sum` 成 `A`), 折叠换成 [KindLvRun](KindLvRun.lagda.md) (先查 `lv`, 再退回 `fbA`), 层 $\Lambda$ 不再接 $1\boxplus$ (第 1 层是 $\Lambda$ 的第一位置作为前提给出).
> - **§2 塔.** [NewTwr](NewTwr.lagda.md) 的塔的式子 (起点 $2$, 部分和对角), 每站下降是 [KindLvEv](KindLvEv.lagda.md) 的 `ρK` (与 `NewTwrEv.ρ′` 同一个求值, 折叠走 `KindLvRun` 取平凡级回灌; 与 `GenFoldRun` 逐行相同是判断, 没有定义相等的定理: 两者是两个模块的两份定义). 最终层 $\Lambda=\mathrm{up}\,\Lambda_B$.
> - **§3 每个种类的级回灌 `lvΛ`.** **第 1 站读回分量的头种类** `κ₁ = (1 , (inj₂ 2 , inj₂ tt))` (第 0 站的求值 `evN 1` 的头的种类, 经 `injL 2` 与 `ιΛ 1` 进对角; 坐标 `HB (step S₀)`): 级 $c=1$, 级层 $\mathrm{hs}(\mathrm{up}\,1)=2$, 是 $\Lambda$ 的字面第一位置 (`hlim 0 hself`, 对一切世界); 读回是级读回 `readL 1` ([KindLvRd](KindLvRd.lagda.md)), 坐标类型 `HB (Lev 1) = HB (step S₀)` 与种类的坐标定义相等; 升界是 ℕ 下标 $1$ 的点更新, 再在 `⊤ ⊎ HB S₀` 下标上对 `inj₂ 2` 的点更新: **$2$ 是不含函数的闭项, 一个下标是不是 $2$ 由模式匹配判定** (`isTwo`), 不撞 `upd₁-sep` (那里的下标 `jx f` 含函数 $f$), 不用升界算子 (`RaiseIf`, `RaiseC`). 其余种类 `inj₂ tt`, 即退回 `GΛ` 的 `fbA` (同 `NewTwr` 的 `TN`: 沿 `inj₁ tt` 链的底种类拷贝有 A-回灌, 其余有损).
> - **§4 无条件闭项** `TK`, 证书 `Lg-TK`, FGH `fghK`.
>
> **为什么只有第 1 站 (未走通的部分, 判断与编译失败).** 第 $s+1$ 站 ($s\ge1$) 的头种类 `(s+1 , (inj₂ B_s , inj₂ tt))` 的坐标是 `HB (Lev X_s)`, $X_s$ 在 `HB (Kc s)` 里; 级层要是 $\Lambda$ 的第一位置而且读回进 `HB (Lev X_s)`. 对角是部分和, $X_s$ 的拷贝不是它的第一位置 (`NegNewTwrShape.tw-not-below`), `Lev (up (ιΛ s X_s))` 与 `Lev X_s` 不定义相等; 下标 $B_s$ 含求值的函数分支, 不能按模式判定. 要让每站的级都是同一个类型里对角的字面第一位置, 种类结构族与级要互递归 (`C (s+1) = step (Lev (Y s))`, `Y s : HB (sup ℕ C)`): 本路写了, 检查器报 `TerminationIssue` (`C` 经 `Lev` 的隐式参数 `sup ℕ C` 调用自己, 不降; 日志与草稿在 scratch `kindlv/tw-IR-termination.log`, `KindLvTw-IR-attempt.lagda.md`). 这是一次编译失败, **不是否定定理**; 路线状态 "未走通".

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.KindLvTw where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg)
import OCF.Free.Level as FLv
open import OCF.Align.HtTowerTy
open import OCF.Align.GenFoldIf using (GenK; LgDn; FbLg; tpK; top; w₀; lw₀; module FoldTy; n0; n1; _⨾_)
open import OCF.Align.GenFoldTree using (module Tree; topStepG; accᴸ)
open import OCF.Align.GenFoldInst using (upd; upd-R; upd-Q)
open import OCF.Align.LvKtIf using (Kc; KΛc; FN; emb; injL; ιΛ)
open import OCF.Align.NewTwrEv using (two)
open import OCF.Align.NewTwrColl using (GΛ; LdΛ; flΛ)
open import OCF.Align.KindLvEv using (ρK; lρK)
open import OCF.Align.KindLvIf
import OCF.Align.KindLvRun as KR
import OCF.Align.KindLvRd as KRd
```

## §1 一般坍缩

```agda
module ColL {T : KS} (G : GenK T) (Ld : LgDn T) (fl : FbLg G) (Λ : HB (step T)) (lΛ : LgB Λ)
            (o : ∀ {w} → hs hz ⊲[ w ] Λ) (lv : LvFb T (tpK G) Λ) where
  open Tree T
  open Om (topStepG (tpK G))
  open KR T G Ld fl Λ lΛ o lv
  open FoldTy T Λ using (Ig; St; st; Df)

  Act : ∀ {ly W} → Ig ly W
  Act p lW′ _ Y = Stp Y

  Y₀ : ∀ {W} → St W
  Y₀ = st zeroD n0 n0

  W₁ : Wd L₀
  W₁ = w₀ G , hz

  lW₁ : LgW L₀ W₁
  lW₁ = lw₀ G , tt

  ΔΩ : Df W₁
  ΔΩ = Run accᴸ (Ωd Λ {W₁}) ≤rf lW₁ hself Act n0 Y₀

  ΨΩ : D hz W₁
  ΨΩ = n1 ⨾ yc ΔΩ (τ₀ lW₁)

  Tψ : A
  Tψ = sum azero ΨΩ

  Lg-Tψ : Lg Tψ
  Lg-Tψ = Lg-sum azero ΨΩ tt

collLv : CollLvFbTy
collLv G Ld fl Λ lΛ o lv = ColL.Tψ G Ld fl Λ lΛ o lv , ColL.Lg-Tψ G Ld fl Λ lΛ o lv
```

## §2 塔: 新塔的层号对角

同 `NewTwrK.Twr N₀` 的式子 ($B_0=2$, $B_{s+1}=\mathrm{emb}\,B_s\boxplus\mathrm{injL}\,B_s\,(\mathrm{hs}(\rho\,B_s))$, 对角取部分和), 下降 $\rho$ 换成 `KindLvEv.ρK` (同一个求值, 折叠走 `KindLvRun`). 直接写出, 不经 `NewTw` 记录.

```agda
-- 塔放在模块 NT₁ 里再公开 (否定一路 NegKindLvInst 用 NT₁.Bᴧ)
module NT₁ where
  B  : ∀ s → HB (Kc s)
  lB : ∀ s → LgB (B s)
  B zero = two
  B (suc s) = emb (B s) ⊞ injL (B s) (hs (ρK (B s)))
  lB zero = tt
  lB (suc s) = Lg-⊞ (emb (B s)) (injL (B s) (hs (ρK (B s))))
                    (Lg-ι {⊤ ⊎ HB (Kc s)} {FN (Kc s)} (inj₁ tt) (B s) (lB s))
                    (Lg-ι {⊤ ⊎ HB (Kc s)} {FN (Kc s)} (inj₂ (B s)) _ (lρK (B s)))

  inc : ∀ s → HB (Kc (suc s))
  inc s = injL (B s) (hs (ρK (B s)))

  Bᴧ  : ℕ → HB KΛc
  lBᴧ : ∀ s → LgB (Bᴧ s)
  Bᴧ zero = ιΛ 0 two
  Bᴧ (suc s) = Bᴧ s ⊞ ιΛ (suc s) (inc s)
  lBᴧ zero = tt
  lBᴧ (suc s) = Lg-⊞ (Bᴧ s) (ιΛ (suc s) (inc s)) (lBᴧ s) (Lg-ι {ℕ} {Kc} (suc s) (inc s) (Lg-ι {⊤ ⊎ HB (Kc s)} {FN (Kc s)} (inj₂ (B s)) _ (lρK (B s))))

  ΛB : HB KΛc
  ΛB = hl Bᴧ

  Λ : HB (step KΛc)
  Λ = up ΛB

  lΛ : LgB Λ
  lΛ = Lg-up ΛB ((λ n → ⊞-fst (Bᴧ n) (ιΛ (suc n) (inc n))) , lBᴧ)

  one⊲ : ∀ {w} → hs hz ⊲[ w ] Λ
  one⊲ = hlim 0 (hsuc hself)
open NT₁ public
```

## §3 每个种类的级回灌

第 1 站读回分量的头种类 $\kappa_1$. 下标 $2$ 的判定:

```agda
data IsTwo : HB S₀ → Set where
  yes : IsTwo two
  no  : ∀ {c} → IsTwo c

isTwo : (c : HB S₀) → IsTwo c
isTwo (hs (hs hz)) = yes
isTwo c = no

κ₁ : K KΛc
κ₁ = 1 , (inj₂ two , inj₂ tt)

W₁′ : Set
W₁′ = Wd (Kc 1)

sel : W₁′ → HB (step S₀) → (c : HB S₀) → IsTwo c → Wd (Lev c)
sel u v .(hs (hs hz)) yes = proj₁ (u (inj₂ two)) , v
sel u v c no = u (inj₂ c)

up₂ : W₁′ → HB (step S₀) → W₁′
up₂ u v (inj₁ tt) = u (inj₁ tt)
up₂ u v (inj₂ c) = sel u v c (isTwo c)

sel≤ : ∀ u v c (i : IsTwo c) → proj₂ (u (inj₂ two)) ⊲[ proj₁ (u (inj₂ two)) ] v → _≤w_ (Lev c) (u (inj₂ c)) (sel u v c i)
sel≤ u v .(hs (hs hz)) yes p = ≤w-rf (step S₀) , p
sel≤ u v c no p = ≤w-rf (Lev c)

up₂≤ : ∀ u v → proj₂ (u (inj₂ two)) ⊲[ proj₁ (u (inj₂ two)) ] v → _≤w_ (Kc 1) u (up₂ u v)
up₂≤ u v p (inj₁ tt) = ≤w-rf S₀
up₂≤ u v p (inj₂ c) = sel≤ u v c (isTwo c) p

selLg : ∀ u v c (i : IsTwo c) → LgW (Kc 1) u → LgB v → LgW (Lev c) (sel u v c i)
selLg u v .(hs (hs hz)) yes lu lv = proj₁ (lu (inj₂ two)) , lv
selLg u v c no lu lv = lu (inj₂ c)

up₂Lg : ∀ u v → LgW (Kc 1) u → LgB v → LgW (Kc 1) (up₂ u v)
up₂Lg u v lu lv (inj₁ tt) = lu (inj₁ tt)
up₂Lg u v lu lv (inj₂ c) = selLg u v c (isTwo c) lu lv

open KRd KΛc LdΛ using (readL; readL-fst; Lg-readL)

K1 : KLv KΛc (tpK GΛ) Λ κ₁
K1 = record
  { ℓ = lyL {KΛc} (hs hz) ; ℓ⊲ = λ {w} → hlim 0 hself
  ; rd = λ lW b x → readL (hs hz) lW b x
  ; rd-fst = λ lW b x → readL-fst (hs hz) lW b x
  ; rd-lg = λ lW b x lb → Lg-readL (hs hz) lW b x lb
  ; rs = λ w v → upd {λ m → Wd (Kc m)} w 1 (up₂ (w 1) v)
  ; rs≤ = λ {w} {v} p → upd-R {λ m → Wd (Kc m)} (λ m → _≤w_ (Kc m)) w 1 (up₂ (w 1) v) (λ m → ≤w-rf (Kc m)) (up₂≤ (w 1) v p)
  ; rsLg = λ {w} {v} lw lv → upd-Q {λ m → Wd (Kc m)} (λ m → LgW (Kc m)) w 1 (up₂ (w 1) v) lw (up₂Lg (w 1) v (lw 1) lv)
  ; rs-top = refl }

lvΛ : LvFb KΛc (tpK GΛ) Λ
lvΛ (suc zero , (inj₂ (hs (hs hz)) , inj₂ tt)) = inj₁ K1
lvΛ κ = inj₂ tt
```

## §4 无条件闭项

```agda
module CK = ColL GΛ LdΛ flΛ Λ lΛ one⊲ lvΛ

TK : A
TK = CK.Tψ

Lg-TK : Lg TK
Lg-TK = CK.Lg-Tψ

ordK : A → FLv.Ordᶜ FLv.zero
ordK azero = FLv.zero
ordK (asuc a) = FLv.suc (ordK a)
ordK (alim f) = FLv.lim (λ n → ordK (f n))

fghK : ℕ → ℕ
fghK = FLv.FGH (ordK TK)
```
