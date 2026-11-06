# 结构关系, 第四轮 (一): 沿对齐的两条路径走, 输出可比

> 不含记号. 入口 [StrRel4](StrRel4.lagda.md).
>
> `KNest2Glue.CellStep` 的前提只有值 (领先量、起点可比、$W\le W'$), 而沿任意字面路径只由值求对应位置推出 LPO (`StrRel2Neg.phead→LPO`). 这里把对齐**作为数据**交给一格: 一个关系 `Al p lb p′ lb′`, 由下面五个构造子生成, 每一对对应位置带着 $c\le c'$ 与到格世界的领先量 $\mathrm{Adm}(c,c';W,W')$.
>
> | 构造子 | 左 | 右 | 读法 |
> |---|---|---|---|
> | `aS` | 空路径 | 任意 | 左边没有位置 |
> | `aP` | 后继 | 后继 | 两边各一个位置, 互相对应 |
> | `aR` | 不变 | 后继 | 右边末尾多一个位置 |
> | `aRL` | 不变 | 极限 | 右边末尾多一段极限 |
> | `aL` | 极限 | 极限 | 前缀对前缀, 第 $m$ 段对第 $m$ 段 |
>
> 没有 "左边极限对右边一段前缀" 的构造子: 那正是 `KNestAdm.¬adm-end` 的形状.
>
> **定理 `walk`**: 若两条路径对齐, 两边状态满足 `Cxᴵ`, 且状态的回灌层把格世界上的领先量传下去 (`Ld`), 则两边 `Walk` 的输出在 `κ₀` 路径上对一切 $e\le e'$ 可比. 只用分支的交叉前提 `SX u u′`, 不用 `SX u u`, `SX u′ u′`, 不用两边树世界可比.
>
> **推论 `cellᴬˡ`**: `CellStep` 把三条值前提换成 `Al`, 结论原样 (第 0 层, 路径 `z⊲`). 证明对 `Al` 的推导归纳, 没有参数.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel4Walk where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; ≤l; l≤; ≤-refl; ≤-trans; ⊲→≤)
open import OCF.Align.SumOneTree using (D; _⨾_; sum; pt; sum-fst; Cut; tailP)
import OCF.Align.SumOneClosed as F
open import OCF.Align.LayerTrOne using (one)
open import OCF.Align.KValTree using (Bk)
open import OCF.Align.KValSem using (CohD; cdA; coh⊕; ac₁; κ₀; toV0)
open import OCF.Align.KValSound using (Sd; W; lW; ll; act; Ok; c0; c1)
open import OCF.Align.KNestInv using (ℓ; Cxᴵ; cLᴵ; cRᴵ; vleᴵ; nextᴵ; cohW)
open import OCF.Align.KNestAdm using (Adm)
open import OCF.Align.KNestSound using (SX; cxᴬ; adv-sum; adm-wk)
open import OCF.Align.KNest2Glue using (d0; Wk)
```

## §1 对齐

`L`, `L′` 是两边的格世界, 领先量都量到它们.

```agda
module _ (L L′ : A) where
  data Al : ∀ {a b a′ b′} → a ⊲ b → Lg b → a′ ⊲ b′ → Lg b′ → Set where
    aS  : ∀ {a a′ b′} {la : Lg a} (p′ : a′ ⊲ b′) (lb′ : Lg b′) → Al (C.self {a}) la p′ lb′
    aP  : ∀ {a c a′ c′} {p : a ⊲ c} {lc : Lg c} {p′ : a′ ⊲ c′} {lc′ : Lg c′} →
          Al p lc p′ lc′ → c ≤ c′ → Adm c c′ L L′ → Al (C.suc p) lc (C.suc p′) lc′
    aR  : ∀ {a b a′ c′} {p : a ⊲ b} {lb : Lg b} {p′ : a′ ⊲ c′} {lc′ : Lg c′} →
          Al p lb p′ lc′ → Al p lb (C.suc p′) lc′
    aRL : ∀ {a b a′ f′ n′} {p : a ⊲ b} {lb : Lg b} {p′ : a′ ⊲ f′ n′} {stp′ : ∀ n → f′ n ⊲ f′ (suc n)} {wl′ : ∀ n → Lg (f′ n)} →
          Al p lb p′ (wl′ n′) → Al p lb (C.lim {f = f′} n′ p′) (stp′ , wl′)
    aL  : ∀ {a f n a′ f′ n′} {p : a ⊲ f n} {p′ : a′ ⊲ f′ n′}
            {stp : ∀ n → f n ⊲ f (suc n)} {wl : ∀ n → Lg (f n)} {stp′ : ∀ n → f′ n ⊲ f′ (suc n)} {wl′ : ∀ n → Lg (f′ n)} →
          Al p (wl n) p′ (wl′ n′) →
          (∀ m → Al (stp (m + n)) (wl (suc (m + n))) (stp′ (m + n′)) (wl′ (suc (m + n′)))) →
          Al (C.lim {f = f} n p) (stp , wl) (C.lim {f = f′} n′ p′) (stp′ , wl′)
```

## §2 走一段

```agda
module Go (s s′ : Sd) (o : Ok s s′) {V V′} (u : Bk V) (u′ : Bk V′) (cr : SX u u′) where
  WL : ∀ {a b} (p : a ⊲ b) (ap : V ⊲ a) (lb : Lg b) (bV : b ⊲ W s) → D one (W s) → F.St (W s) → F.Df (W s)
  WL {b = b} p ap lb bV co Y = F.Walk ac₁ u b p ap lb bV (lW s) (ll s) (act s) co Y
  WR : ∀ {a b} (p : a ⊲ b) (ap : V′ ⊲ a) (lb : Lg b) (bV : b ⊲ W s′) → D one (W s′) → F.St (W s′) → F.Df (W s′)
  WR {b = b} p ap lb bV co Y = F.Walk ac₁ u′ b p ap lb bV (lW s′) (ll s′) (act s′) co Y

  Out : F.Df (W s) → F.Df (W s′) → Set
  Out Δ Δ′ = ∀ e e′ → e ≤ e′ → sum e (F.yc Δ (inj₁ (κ₀ (ll s))) tt) ≤ sum e′ (F.yc Δ′ (inj₁ (κ₀ (ll s′))) tt)

  -- 状态把格世界上的领先量传到回灌层
  Ld : F.St (W s) → F.St (W s′) → Set
  Ld Y Y′ = ∀ {c c′} → Adm c c′ (W s) (W s′) → Adm c c′ (ℓ Y) (ℓ Y′)

  adv : ∀ {Y Y′} (Δ : F.Df (W s)) (Δ′ : F.Df (W s′)) → CohD Δ → CohD Δ′ → Out Δ Δ′ → Cxᴵ s s′ Y Y′ → Ld Y Y′ →
        Cxᴵ s s′ (Y F.⊕ Δ) (Y′ F.⊕ Δ′) × Ld (Y F.⊕ Δ) (Y′ F.⊕ Δ′)
  adv Δ Δ′ cD cD′ O k h =
    nextᴵ Δ Δ′ k (coh⊕ (cLᴵ k) cD) (coh⊕ (cRᴵ k) cD′) (O _ _ (vleᴵ k)) , (λ a → adv-sum δ δ′ (h a) (toV0 δ δ′ le))
    where
    δ = F.yc Δ (inj₁ (z⊲ (W s))) tt
    δ′ = F.yc Δ′ (inj₁ (z⊲ (W s′))) tt
    le = ≤-trans (CohD.cdA cD _ (inj₁ (κ₀ (ll s))) azero) (≤-trans (O azero azero z≤) (CohD.cdA cD′ (inj₁ (κ₀ (ll s′))) _ azero))

  cL : ∀ {a b Y′} (p : a ⊲ b) ap lb bV co Y → Cxᴵ s s′ Y Y′ → CohD (WL p ap lb bV co Y)
  cL {b = b} p ap lb bV co Y k = cohW u b p ap lb bV (lW s) (ll s) (act s) co Y (c0 o) (cLᴵ k)
  cR : ∀ {a b Y₀} (p : a ⊲ b) ap lb bV co Y → Cxᴵ s s′ Y₀ Y → CohD (WR p ap lb bV co Y)
  cR {b = b} p ap lb bV co Y k = cohW u′ b p ap lb bV (lW s′) (ll s′) (act s′) co Y (c1 o) (cRᴵ k)
```

主定理. 每一种构造子对应 `Walk` 的一种展开; 极限一句照 `KNestSound.sndᴬ` 的 `nlᴬ` 一句逐段推进状态.

```agda
  walk : ∀ {a b a′ b′} {p : a ⊲ b} {lb : Lg b} {p′ : a′ ⊲ b′} {lb′ : Lg b′} → Al (W s) (W s′) p lb p′ lb′ →
         ∀ ap ap′ bV bV′ co co′ Y Y′ → Cxᴵ s s′ Y Y′ → Ld Y Y′ → Out (WL p ap lb bV co Y) (WR p′ ap′ lb′ bV′ co′ Y′)
  walk (aS p′ lb′) ap ap′ bV bV′ co co′ Y Y′ k h e e′ le = ≤-trans le (⊲→≤ (sum-fst e′ _))
  walk (aR {p′ = p′} {lc′} H) ap ap′ bV bV′ co co′ Y Y′ k h e e′ le =
    ≤-trans (walk H ap ap′ bV (⊲-tr (C.suc C.self) bV′) co co′ Y Y′ k h e e′ le) (⊲→≤ (sum-fst _ _))
  walk (aRL H) ap ap′ bV bV′ co co′ Y Y′ k h e e′ le =
    ≤-trans (walk H ap ap′ bV (⊲-tr (C.lim _ C.self) bV′) co co′ Y Y′ k h e e′ le) (≤l 0 (≤-refl _))
  walk (aP {c = c} {c′ = c′} {p = p} {lc} {p′} {lc′} H c≤ ad) ap ap′ bV bV′ co co′ Y Y′ k h e e′ le =
    cr (⊲-tr ap p) (⊲-tr ap′ p′) lc lc′ c≤ s s′ o (⊲-tr (C.suc C.self) bV) (⊲-tr (C.suc C.self) bV′)
       (co ⨾ Cut u c p ap lc (⊲-tr (C.suc C.self) bV)) (co′ ⨾ Cut u′ c′ p′ ap′ lc′ (⊲-tr (C.suc C.self) bV′))
       (Y F.⊕ Δ) (Y′ F.⊕ Δ′) (cxᴬ (proj₁ st) (proj₂ st ad)) _ _ (O e e′ le)
    where
    Δ = WL p ap lc (⊲-tr (C.suc C.self) bV) co Y
    Δ′ = WR p′ ap′ lc′ (⊲-tr (C.suc C.self) bV′) co′ Y′
    O = walk H ap ap′ (⊲-tr (C.suc C.self) bV) (⊲-tr (C.suc C.self) bV′) co co′ Y Y′ k h
    st = adv Δ Δ′ (cL p ap lc _ co Y k) (cR p′ ap′ lc′ _ co′ Y′ k) O k h
  walk (aL {f = f} {n} {f′ = f′} {n′} {p} {p′} {stp} {wl} {stp′} {wl′} H G) ap ap′ bV bV′ co co′ Y Y′ k h e e′ le =
    l≤ (λ m → ≤l m (proj₁ (go m)))
    where
    fV : ∀ m → f m ⊲ W s
    fV m = ⊲-tr (C.lim m C.self) bV
    fV′ : ∀ m → f′ m ⊲ W s′
    fV′ m = ⊲-tr (C.lim m C.self) bV′
    Δ = WL p ap (wl n) (fV n) co Y
    Δ′ = WR p′ ap′ (wl′ n′) (fV′ n′) co′ Y′
    O = walk H ap ap′ (fV n) (fV′ n′) co co′ Y Y′ k h
    R = F.WRp ac₁ u f stp wl p ap fV (lW s) (ll s) (act s) (co ⨾ Cut u (f n) p ap (wl n) (fV n)) (Y F.⊕ Δ)
    R′ = F.WRp ac₁ u′ f′ stp′ wl′ p′ ap′ fV′ (lW s′) (ll s′) (act s′) (co′ ⨾ Cut u′ (f′ n′) p′ ap′ (wl′ n′) (fV′ n′)) (Y′ F.⊕ Δ′)
    Sg : ℕ → F.Df (W s)
    Sg m = WL (stp (m + n)) (⊲-tr ap (tailP f stp p m)) (wl (suc (m + n))) (fV (suc (m + n))) (proj₁ (R m)) (proj₂ (R m))
    Sg′ : ℕ → F.Df (W s′)
    Sg′ m = WR (stp′ (m + n′)) (⊲-tr ap′ (tailP f′ stp′ p′ m)) (wl′ (suc (m + n′))) (fV′ (suc (m + n′))) (proj₁ (R′ m)) (proj₂ (R′ m))
    st0 = adv Δ Δ′ (cL p ap _ _ co Y k) (cR p′ ap′ _ _ co′ Y′ k) O k h
    go : ∀ m → (pt (sum e (F.yc Δ (inj₁ (κ₀ (ll s))) tt)) (λ j → F.yc (Sg j) (inj₁ (κ₀ (ll s))) tt) m ≤
                pt (sum e′ (F.yc Δ′ (inj₁ (κ₀ (ll s′))) tt)) (λ j → F.yc (Sg′ j) (inj₁ (κ₀ (ll s′))) tt) m) ×
               (Cxᴵ s s′ (proj₂ (R m)) (proj₂ (R′ m)) × Ld (proj₂ (R m)) (proj₂ (R′ m)))
    go zero = O e e′ le , st0
    go (suc m) =
      let (b≤ , (km , hm)) = go m
          Om = walk (G m) _ _ _ _ _ _ _ _ km hm
      in Om _ _ b≤ ,
         adv (Sg m) (Sg′ m) (cL (stp (m + n)) _ _ _ _ _ km) (cR (stp′ (m + n′)) _ _ _ _ _ km) Om km hm
```

## §3 一格

`CellStep` 的结论, 前提里的值对齐 (领先量、起点可比、$W\le W'$) 换成对齐 `Al`, 其余照旧. 回灌层 $\ell\le W$ 给出起点的 `Ld`.

```agda
CellStepᴬˡ : Set
CellStepᴬˡ = ∀ {V V′} {u : Bk V} {u′ : Bk V′} → SX u u′ →
             ∀ (s s′ : Sd) → Ok s s′ → ∀ {a a′} (p : a ⊲ W s) (p′ : a′ ⊲ W s′) (ap : V ⊲ a) (ap′ : V′ ⊲ a′) co co′ Y Y′ →
             Cxᴵ s s′ Y Y′ → ℓ Y ≤ W s → Al (W s) (W s′) p (lW s) p′ (lW s′) →
             ∀ e e′ → e ≤ e′ → sum e (d0 (Wk u s p ap co Y)) ≤ sum e′ (d0 (Wk u′ s′ p′ ap′ co′ Y′))

cellᴬˡ : CellStepᴬˡ
cellᴬˡ {u = u} {u′} cr s s′ o p p′ ap ap′ co co′ Y Y′ k hℓ H e e′ le =
  ≤-trans (CohD.cdA (G.cL p ap (lW s) C.self co Y k) _ _ e)
    (≤-trans (G.walk H ap ap′ C.self C.self co co′ Y Y′ k ld e e′ le)
             (CohD.cdA (G.cR p′ ap′ (lW s′) C.self co′ Y′ k) _ _ e′))
  where
  module G = Go s s′ o u u′ cr
  ld : G.Ld Y Y′
  ld = adm-wk hℓ (⊲→≤ (sum-fst (W s′) (F.z Y′)))
```
