# 结构关系, 第四轮 (二): 对齐从哪里来

> 不含记号. 入口 [StrRel4](StrRel4.lagda.md). 接 [StrRel4Walk](StrRel4Walk.lagda.md) 的 `Al`.
>
> `KNest2Glue.kstep` 里每一格的路径只有两种形状:
>
> - 第 $n+1$ 格: `sum-fst v d`, 其中 $d$ 是上一格的第 0 层输出, 长度证据是 `Lg-sum v d lv`;
> - 第 0 格: `⊲-tr q₀ (sum-fst W z)`, 其中 $q_0$ 是从树世界到运行世界的路径, $z$ 是状态的第 0 层累计.
>
> 本文证明: 只要两边的树由 `StrRel3Zero` 的结构关系 $\sqsubseteq^{\mathsf O}$ 相关, 两边起点 $b\le b'$, 末端有领先量, 沿 `sum-fst` 的两条路径就对齐 (**`gen`**). `⊑ᴼ` 的七个构造子 (含传递) 都处理了; 传递一句经过中间的格世界, 用对齐的传递律 (`Al-tr`) 与领先量的复合 (`adm-comp`, 用左消去). 第 0 格的前一段由拼接律 (`cat`) 接上. 由此:
>
> - **`alSucc`**: 第 $n+1$ 格的两条路径对齐, 只要上一格两边输出 $\sqsubseteq^{\mathsf O}$ 相关、两个起点可比;
> - **`alZero`**: 第 0 格的两条路径对齐, 只要前一段 $q_0,q_0'$ 已对齐、两边状态的第 0 层累计 $\sqsubseteq^{\mathsf O}$ 相关、两个运行世界可比.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel4Gen where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; lg⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; ⊲→≤; _⊞_; ⊞-mono; ⊞-asso; ⊞-assoʳ)
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; ni; nκ; nw; sum; pt; sum-fst; Lg-sum; Lg-pt)
open import OCF.Align.BrwMidZero using (sum-toA)
open import OCF.Align.KValTree using (V0)
open import OCF.Align.KValSem using (toV0)
open import OCF.Align.KNestAdm using (Adm)
open import OCF.Align.StrRel2Neg using (cancel)
open import OCF.Align.StrRel3Zero using (_⊑ᴼ_; z0; o1; sq; lm; wl; wr; tr)
open import OCF.Align.StrRel4Walk using (Al; aS; aP; aR; aRL; aL)
```

## §1 值的引理

```agda
≡→≤ : ∀ {a b} → a ≡ b → a ≤ b
≡→≤ {a} refl = ≤-refl a

-- ⊑ᴼ 的值可靠
vs : ∀ {V V′ b b′} {x : D azero V} {x′ : D azero V′} → x ⊑ᴼ x′ → b ≤ b′ → sum b x ≤ sum b′ x′
vs {b′ = b′} {x′ = x′} z0 h = ≤-trans h (⊲→≤ (sum-fst b′ x′))
vs o1 h = s≤ h
vs {b = b} {b′} (sq {x = x} {x′ = x′} hx hy) h = vs {b = sum b x} {sum b′ x′} hy (vs hx h)
vs {b = b} {b′} (lm {d = d} {d′} hd) h = l≤ (λ n → ≤l n (go n))
  where
  go : ∀ n → pt b d n ≤ pt b′ d′ n
  go zero = h
  go (suc n) = vs {b = pt b d n} {pt b′ d′ n} (hd n) (go n)
vs {b = b} {b′} (wl {x = x} {x′} hx) h = vs {b = b} {b′} {x} {x′} hx h
vs {b = b} {b′} (wr {x = x} {x′} hx) h = vs {b = b} {b′} {x} {x′} hx h
vs {b = b} {b′} (tr {x = x} {y} {z} hx hy) h = ≤-trans (vs {b = b} {b} {x} {y} hx (≤-refl b)) (vs {b = b} {b′} {y} {z} hy h)

-- 领先量往回推: 末端 E, E′ 处有领先量, 位置 c, c′ 之后各剩 ρ ≤ ρ′
adm-back : ∀ {E E′ L L′ c c′ ρ ρ′} → Adm E E′ L L′ → E ≤ c ⊞ ρ → c′ ⊞ ρ′ ≤ E′ → ρ ≤ ρ′ → Adm c c′ L L′
adm-back {c = c} {c′} {ρ} {ρ′} (δ , h₁ , h₂) e e′ r =
  (ρ ⊞ δ) , ≤-trans h₁ (≤-trans (⊞-mono e (≤-refl δ)) (⊞-assoʳ c ρ δ)) ,
            ≤-trans (⊞-asso c′ ρ δ) (≤-trans (⊞-mono (≤-trans (⊞-mono (≤-refl c′) r) e′) (≤-refl δ)) h₂)

-- 领先量的复合 (中间的格世界相同)
adm-comp : ∀ {c c′ c″ L L′ L″} → Adm c c′ L L′ → Adm c′ c″ L′ L″ → Adm c c″ L L″
adm-comp {c′ = c′} {c″} (δ , h₁ , h₂) (ε , g₁ , g₂) =
  δ , h₁ , ≤-trans (⊞-mono (≤-refl c″) (cancel c′ δ ε (≤-trans h₂ g₁))) g₂

-- 一段极限的尾巴
module Tail {V} (b : A) (d : ℕ → D azero V) where
  tl : ℕ → D azero V
  tl m = nl (λ j → d (j + m))

  ptsh : ∀ m j → pt (pt b d m) (λ i → d (i + m)) j ≡ pt b d (j + m)
  ptsh m zero = refl
  ptsh m (suc j) = cong (λ t → sum t (d (j + m))) (ptsh m j)

  pt-mono : ∀ i k → pt b d i ≤ pt b d (k + i)
  pt-mono i zero = ≤-refl _
  pt-mono i (suc k) = ≤-trans (pt-mono i k) (⊲→≤ (sum-fst (pt b d (k + i)) (d (k + i))))

  up : ∀ m → alim (pt b d) ≤ sum (pt b d m) (tl m)
  up m = l≤ (λ j → ≤l j (≤-trans (subst (λ k → pt b d j ≤ pt b d k) (+-comm m j) (pt-mono j m)) (≡→≤ (sym (ptsh m j)))))

  dn : ∀ m → sum (pt b d m) (tl m) ≤ alim (pt b d)
  dn m = l≤ (λ j → ≤l (j + m) (≡→≤ (ptsh m j)))
```

## §2 对齐的运算

```agda
Al-map : ∀ {L₁ L₁′ L₂ L₂′} → (∀ {c c′} → Adm c c′ L₁ L₁′ → Adm c c′ L₂ L₂′) →
         ∀ {a b a′ b′} {p : a ⊲ b} {lb} {p′ : a′ ⊲ b′} {lb′} → Al L₁ L₁′ p lb p′ lb′ → Al L₂ L₂′ p lb p′ lb′
Al-map g (aS p′ lb′) = aS p′ lb′
Al-map g (aP H c≤ ad) = aP (Al-map g H) c≤ (g ad)
Al-map g (aR H) = aR (Al-map g H)
Al-map g (aRL H) = aRL (Al-map g H)
Al-map g (aL H G) = aL (Al-map g H) (λ m → Al-map g (G m))

-- 传递: 对第二个推导归纳
Al-tr : ∀ {L Lm L′} {a b am bm a′ b′} {p : a ⊲ b} {lb} {q : am ⊲ bm} {lq} {r : a′ ⊲ b′} {lr} →
        Al L Lm p lb q lq → Al Lm L′ q lq r lr → Al L L′ p lb r lr
Al-tr (aS _ _) _ = aS _ _
Al-tr (aP H c≤ ad) (aP H′ c≤′ ad′) = aP (Al-tr H H′) (≤-trans c≤ c≤′) (adm-comp ad ad′)
Al-tr H₁@(aP _ _ _) (aR H′) = aR (Al-tr H₁ H′)
Al-tr H₁@(aP _ _ _) (aRL H′) = aRL (Al-tr H₁ H′)
Al-tr (aR H) (aP H′ _ _) = aR (Al-tr H H′)
Al-tr H₁@(aR _) (aR H′) = aR (Al-tr H₁ H′)
Al-tr H₁@(aR _) (aRL H′) = aRL (Al-tr H₁ H′)
Al-tr (aRL H) (aL H′ _) = aRL (Al-tr H H′)
Al-tr H₁@(aRL _) (aR H′) = aR (Al-tr H₁ H′)
Al-tr H₁@(aRL _) (aRL H′) = aRL (Al-tr H₁ H′)
Al-tr (aL H G) (aL H′ G′) = aL (Al-tr H H′) (λ m → Al-tr (G m) (G′ m))
Al-tr H₁@(aL _ _) (aR H′) = aR (Al-tr H₁ H′)
Al-tr H₁@(aL _ _) (aRL H′) = aRL (Al-tr H₁ H′)

lg-tr : ∀ {a b c} (P : a ⊲ b) (Q : b ⊲ c) (l : Lg c) → lg⊲ (⊲-tr P Q) l ≡ lg⊲ P (lg⊲ Q l)
lg-tr P C.self l = refl
lg-tr P (C.suc Q) l = lg-tr P Q l
lg-tr P (C.lim n Q) l = lg-tr P Q (proj₂ l n)

lgsf : ∀ {V} b (x : D azero V) (w : Lg b) → lg⊲ (sum-fst b x) (Lg-sum b x w) ≡ w
lgsf b n0 w = refl
lgsf b n1 w = refl
lgsf b (x ⨾ y) w =
  trans (lg-tr (sum-fst b x) (sum-fst (sum b x) y) (Lg-sum (sum b x) y (Lg-sum b x w)))
        (trans (cong (lg⊲ (sum-fst b x)) (lgsf (sum b x) y (Lg-sum b x w))) (lgsf b x w))
lgsf b (nl d) w = refl
lgsf b (ni () u) w
lgsf b (nκ () u) w
lgsf b (nw p x) w = lgsf b x w

-- 右边末尾接上任意一段
ext : ∀ {L L′ a b a′ b′ c′} {P : a ⊲ b} {lb} {P′ : a′ ⊲ b′} {lb″} (Q : b′ ⊲ c′) (lc′ : Lg c′) → lb″ ≡ lg⊲ Q lc′ →
      Al L L′ P lb P′ lb″ → Al L L′ P lb (⊲-tr P′ Q) lc′
ext C.self lc′ refl H = H
ext (C.suc Q) lc′ e H = aR (ext Q lc′ e H)
ext (C.lim n Q) (stp , wl′) e H = aRL (ext Q (wl′ n) e H)

-- 拼接
cat : ∀ {L L′ a b c a′ b′ c′} {P : a ⊲ b} {w} {P′ : a′ ⊲ b′} {w′} {Q : b ⊲ c} {lq} {Q′ : b′ ⊲ c′} {lq′} →
      Al L L′ P w P′ w′ → Al L L′ Q lq Q′ lq′ → w ≡ lg⊲ Q lq → w′ ≡ lg⊲ Q′ lq′ → Al L L′ (⊲-tr P Q) lq (⊲-tr P′ Q′) lq′
cat {P = P} {P′ = P′} H₀ (aS Q′ lq′) refl e′ = ext Q′ lq′ e′ H₀
cat H₀ (aP H c≤ ad) e e′ = aP (cat H₀ H e e′) c≤ ad
cat H₀ (aR H) e e′ = aR (cat H₀ H e e′)
cat H₀ (aRL H) e e′ = aRL (cat H₀ H e e′)
cat H₀ (aL H G) e e′ = aL (cat H₀ H e e′) G
```

## §3 由结构关系生成对齐

```agda
gen : ∀ {L L′ V V′ b b′} {x : D azero V} {x′ : D azero V′} → x ⊑ᴼ x′ → (w : Lg b) (w′ : Lg b′) → b ≤ b′ →
      Adm (sum b x) (sum b′ x′) L L′ → Al L L′ (sum-fst b x) (Lg-sum b x w) (sum-fst b′ x′) (Lg-sum b′ x′ w′)
gen {b′ = b′} {x′ = x′} z0 w w′ h ad = aS (sum-fst b′ x′) (Lg-sum b′ x′ w′)
gen {b = b} {b′} o1 w w′ h ad = aP (aS C.self w′) h (adm-back ad (≤-refl (asuc b)) (≤-refl (asuc b′)) (≤-refl _))
gen {b = b} {b′} (sq {x = x} {y} {x′} {y′} hx hy) w w′ h ad =
  cat (gen hx w w′ h adx) (gen hy (Lg-sum b x w) (Lg-sum b′ x′ w′) (vs hx h) ad)
      (sym (lgsf (sum b x) y (Lg-sum b x w))) (sym (lgsf (sum b′ x′) y′ (Lg-sum b′ x′ w′)))
  where
  adx = adm-back ad (proj₁ (sum-toA (sum b x) y)) (proj₂ (sum-toA (sum b′ x′) y′)) (toV0 y y′ (vs hy z≤))
gen {b = b} {b′} (lm {d = d} {d′} hd) w w′ h ad =
  aL (aS C.self w′) (λ m → gen (hd (m + 0)) (Lg-pt b d (m + 0) w) (Lg-pt b′ d′ (m + 0) w′) (ptle (m + 0)) (seg (m + 0)))
  where
  module T = Tail b d
  module T′ = Tail b′ d′
  ptle : ∀ n → pt b d n ≤ pt b′ d′ n
  ptle zero = h
  ptle (suc n) = vs {b = pt b d n} {pt b′ d′ n} (hd n) (ptle n)
  pos : ∀ m → Adm (pt b d m) (pt b′ d′ m) _ _
  pos m = adm-back ad (≤-trans (T.up m) (proj₁ (sum-toA (pt b d m) (T.tl m))))
                      (≤-trans (proj₂ (sum-toA (pt b′ d′ m) (T′.tl m))) (T′.dn m))
                      (toV0 (T.tl m) (T′.tl m) (vs (lm (λ j → hd (j + m))) z≤))
  seg : ∀ n → Adm (sum (pt b d n) (d n)) (sum (pt b′ d′ n) (d′ n)) _ _
  seg n = pos (suc n)
gen {b = b} {b′} (wl {x = x} {x′} hx) w w′ h ad = gen {b = b} {b′} {x} {x′} hx w w′ h ad
gen {b = b} {b′} (wr {x = x} {x′} hx) w w′ h ad = gen {b = b} {b′} {x} {x′} hx w w′ h ad
gen {L = L} {L′} {b = b} {b′} (tr {y = y} hx hy) w w′ h (δ , h₁ , h₂) =
  Al-tr (gen {L′ = Lm} hx w w (≤-refl b) (δ , h₁ , ≤-refl _)) (gen {L = Lm} hy w w′ h (δ , ≤-refl _ , h₂))
  where
  Lm = sum b y ⊞ δ
```

## §4 两种格

```agda
adm-self : ∀ L L′ → Adm L L′ L L′
adm-self L L′ = azero , ≤-refl L , ≤-refl L′

-- 第 n+1 格: 路径是上一格输出的 sum-fst
alSucc : ∀ {V V′ v v′} {d : D azero V} {d′ : D azero V′} → d ⊑ᴼ d′ → (lv : Lg v) (lv′ : Lg v′) → v ≤ v′ →
         Al (sum v d) (sum v′ d′) (sum-fst v d) (Lg-sum v d lv) (sum-fst v′ d′) (Lg-sum v′ d′ lv′)
alSucc {v = v} {v′} {d} {d′} h lv lv′ le = gen h lv lv′ le (adm-self (sum v d) (sum v′ d′))

-- 第 0 格: 前一段 q₀ 接上状态第 0 层累计的 sum-fst
alZero : ∀ {V V′ W₀ W₀′ W W′} {z : D azero V} {z′ : D azero V′} {q₀ : W₀ ⊲ W} {q₀′ : W₀′ ⊲ W′} (lW : Lg W) (lW′ : Lg W′) →
         Al (sum W z) (sum W′ z′) q₀ lW q₀′ lW′ → z ⊑ᴼ z′ → W ≤ W′ →
         Al (sum W z) (sum W′ z′) (⊲-tr q₀ (sum-fst W z)) (Lg-sum W z lW) (⊲-tr q₀′ (sum-fst W′ z′)) (Lg-sum W′ z′ lW′)
alZero {W = W} {W′} {z} {z′} lW lW′ Hq h le =
  cat Hq (gen h lW lW′ le (adm-self (sum W z) (sum W′ z′))) (sym (lgsf W z lW)) (sym (lgsf W′ z′ lW′))
```
