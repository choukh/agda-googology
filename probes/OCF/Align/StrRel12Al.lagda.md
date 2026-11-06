# 结构关系, 第十二轮 (一): 对齐路径的代数, `Lg` 的自洽

> 不读记号, 不提折叠. 入口 [StrRel12](StrRel12.lagda.md). 主线的三处 "沿一条路径逐位置做事" (`Cut`, `IW`, `Walk`) 都要在每个位置 $c$ 上给出两件东西: 从树世界到 $c$ 的**前段**的对齐路径对, 与从 $c$ 到运行世界的**后段**的对齐路径对. 后段由折叠的字面逐步接长 (`sfxS`, `extR`, `LimW.limSelf`). 前段要从整条路径的对齐里取出一段, 并把对齐的领先量换到这一段自己的顶端 (`Al-top`, `al-adm`, `preAP`).
>
> 另有一件读代码逼出的事: `Walk`/`Cut`/`IW` 在极限的尾段上用的是 `wl (suc (m+n))` 往下推出的 `Lg`, 而树世界那一端用的是 `wl n`. 两者一致要求极限的 `Lg` **自洽** (`Coh`: `lg⊲ (st n) (wl (suc n)) ≡ wl n`, 遗传). 合法性 `Lg` 不含这一条. `Lg-sum` 产生的 `Lg` 都自洽 (`StrRel12Rel.cohSum`), 闭项从 `tt` 起, 所以这一前提在主线上可满足.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel12Al where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm; +-assoc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; lg⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; ≤-suc; ⊲→≤; _⊞_; ⊞-mono)
open import OCF.Align.HtFeedTree using (tailP)
open import OCF.Align.KNestAdm using (Adm; adm-tr)
open import OCF.Align.StrRel4Walk using (Al; aS; aP; aR; aRL; aL)
open import OCF.Align.StrRel4Gen using (Al-map; lg-tr; cat; adm-self)
```

## 1 自洽的 `Lg`

```agda
Coh : ∀ {a} → Lg a → Set
Coh {a = azero} l = ⊤
Coh {a = asuc a} l = Coh {a} l
Coh {a = alim f} (st , wl) = (∀ n → lg⊲ (st n) (wl (suc n)) ≡ wl n) × (∀ n → Coh (wl n))

coh⊲ : ∀ {a b} (p : a ⊲ b) {l : Lg b} → Coh l → Coh (lg⊲ p l)
coh⊲ C.self c = c
coh⊲ (C.suc p) c = coh⊲ p c
coh⊲ (C.lim n p) {st , wl} (e , c) = coh⊲ p (c n)

cohEq : ∀ {a} {l l′ : Lg a} → l ≡ l′ → Coh l′ → Coh l
cohEq refl c = c
```

## 2 对齐的路径对 (同 `StrRel11Tg.APair`), 加上顶端可比与自洽 (`CP`)

`AP` 与 `StrRel11Tg.APair` 逐字相同 (在这里重写一次, 免得带上 $\Lambda$ 参数). `CP` = `AP` + 顶端世界可比 $W\le W'$ + 两个顶端 `Lg` 自洽. 顶端可比是 `Al` 的 `aP` 本来就要的值 (格的世界 $\Sigma_W z\le\Sigma_{W'}z'$ 要从 $W\le W'$ 推出); 自洽见文件头.

```agda
AP : ∀ {V V′ W W′} → Lg V → Lg V′ → V ⊲ W → Lg W → V′ ⊲ W′ → Lg W′ → Set
AP {V} {V′} {W} {W′} lV lV′ q lW q′ lW′ = Al W W′ q lW q′ lW′ × Adm V V′ W W′ × (lV ≡ lg⊲ q lW) × (lV′ ≡ lg⊲ q′ lW′)

ap-self : ∀ {W W′} (lW : Lg W) (lW′ : Lg W′) → AP lW lW′ C.self lW C.self lW′
ap-self {W} {W′} lW lW′ = aS C.self lW′ , adm-self W W′ , refl , refl

eq-tr : ∀ {a b c} (q : a ⊲ b) (r : b ⊲ c) (la : Lg a) (lb : Lg b) (lc : Lg c) →
        la ≡ lg⊲ q lb → lb ≡ lg⊲ r lc → la ≡ lg⊲ (⊲-tr q r) lc
eq-tr q r la lb lc e e′ = trans e (trans (cong (lg⊲ q) e′) (sym (lg-tr q r lc)))

ap-tr : ∀ {V V′ W W′ M M′} {lV : Lg V} {lV′ : Lg V′} {q : V ⊲ W} {lW : Lg W} {q′ : V′ ⊲ W′} {lW′ : Lg W′}
          {r : W ⊲ M} {lM : Lg M} {r′ : W′ ⊲ M′} {lM′ : Lg M′} →
        AP lV lV′ q lW q′ lW′ → AP lW lW′ r lM r′ lM′ → AP lV lV′ (⊲-tr q r) lM (⊲-tr q′ r′) lM′
ap-tr {lV = lV} {lV′} {q} {lW} {q′} {lW′} {r} {lM} {r′} {lM′} (H , ad , e , e′) (G , ad′ , f , f′) =
  cat (Al-map (λ a → adm-tr a ad′) H) G f f′ , adm-tr ad ad′ ,
  eq-tr q r lV lW lM e f , eq-tr q′ r′ lV′ lW′ lM′ e′ f′

CP : ∀ {V V′ W W′} → Lg V → Lg V′ → V ⊲ W → Lg W → V′ ⊲ W′ → Lg W′ → Set
CP {W = W} {W′ = W′} lV lV′ q lW q′ lW′ = AP lV lV′ q lW q′ lW′ × (W ≤ W′) × Coh lW × Coh lW′

cp-self : ∀ {W W′} (lW : Lg W) (lW′ : Lg W′) → W ≤ W′ → Coh lW → Coh lW′ → CP lW lW′ C.self lW C.self lW′
cp-self lW lW′ le c c′ = ap-self lW lW′ , le , c , c′

cp-top : ∀ {V V′ W W′} {lV : Lg V} {lV′ : Lg V′} {q : V ⊲ W} {lW : Lg W} {q′ : V′ ⊲ W′} {lW′ : Lg W′} →
         CP lV lV′ q lW q′ lW′ → CP lW lW′ C.self lW C.self lW′
cp-top (_ , le , c , c′) = cp-self _ _ le c c′

cp-tr : ∀ {V V′ W W′ M M′} {lV : Lg V} {lV′ : Lg V′} {q : V ⊲ W} {lW : Lg W} {q′ : V′ ⊲ W′} {lW′ : Lg W′}
          {r : W ⊲ M} {lM : Lg M} {r′ : W′ ⊲ M′} {lM′ : Lg M′} →
        AP lV lV′ q lW q′ lW′ → CP lW lW′ r lM r′ lM′ → CP lV lV′ (⊲-tr q r) lM (⊲-tr q′ r′) lM′
cp-tr a (b , le , c , c′) = ap-tr a b , le , c , c′

cp-coh : ∀ {V V′ W W′} {lV : Lg V} {lV′ : Lg V′} {q : V ⊲ W} {lW : Lg W} {q′ : V′ ⊲ W′} {lW′ : Lg W′} →
         CP lV lV′ q lW q′ lW′ → Coh lV × Coh lV′
cp-coh {q = q} {q′ = q′} ((_ , _ , e , e′) , _ , c , c′) = cohEq e (coh⊲ q c) , cohEq e′ (coh⊲ q′ c′)
```

## 3 领先量: 一步, 右端放大, 右起点降低, 极限

```agda
stepA : ∀ c c′ → Adm c c′ (asuc c) (asuc c′)
stepA c c′ = asuc azero , ≤-refl (asuc c) , ≤-refl (asuc c′)

adm-r : ∀ {x x′ b c′ d′} → c′ ≤ d′ → Adm x x′ b c′ → Adm x x′ b d′
adm-r le (δ , h , h′) = δ , h , ≤-trans h′ le

adm-lo : ∀ {x x′ x₀ b b′} → x₀ ≤ x′ → Adm x x′ b b′ → Adm x x₀ b b′
adm-lo le (δ , h , h′) = δ , h , ≤-trans (⊞-mono le (≤-refl δ)) h′

up : ∀ {f : ℕ → A} (st : ∀ n → f n ⊲ f (suc n)) j k → f k ⊲ f (j + k)
up st zero k = C.self
up st (suc j) k = ⊲-tr (up st j k) (st (j + k))

limAdm : ∀ {x x′} {f f′ : ℕ → A} {n n′} (st : ∀ k → f k ⊲ f (suc k)) →
         (∀ m → Adm x x′ (f (m + n)) (f′ (m + n′))) → Adm x x′ (alim f) (alim f′)
limAdm {x} {x′} {f} {f′} {n} {n′} st h =
  alim (λ m → proj₁ (h m)) ,
  l≤ (λ k → ≤l k (≤-trans (⊲→≤ (subst (λ i → f k ⊲ f i) (+-comm n k) (up st n k))) (proj₁ (proj₂ (h k))))) ,
  l≤ (λ m → ≤-trans (proj₂ (proj₂ (h m))) (≤l (m + n′) (≤-refl _)))

-- 极限的尾段: 由逐段的领先量拼出 "从第 i 段起到极限" 的领先量
module LimT {f f′ : ℕ → A} {n n′ : ℕ} (st : ∀ k → f k ⊲ f (suc k))
            (g : ∀ m → Adm (f (m + n)) (f′ (m + n′)) (f (suc (m + n))) (f′ (suc (m + n′)))) where
  gi : ∀ i m → Adm (f (m + (i + n))) (f′ (m + (i + n′))) (f (suc (m + (i + n)))) (f′ (suc (m + (i + n′))))
  gi i m = subst₂ (λ X X′ → Adm (f X) (f′ X′) (f (suc X)) (f′ (suc X′))) (+-assoc m i n) (+-assoc m i n′) (g (m + i))

  tc : ∀ i m → Adm (f (i + n)) (f′ (i + n′)) (f (m + (i + n))) (f′ (m + (i + n′)))
  tc i zero = adm-self _ _
  tc i (suc m) = adm-tr (tc i m) (gi i m)

  TF : ∀ i → Adm (f (i + n)) (f′ (i + n′)) (alim f) (alim f′)
  TF i = limAdm {n = i + n} {n′ = i + n′} st (tc i)
```

## 4 对齐给出的领先量; 把对齐换到自己的顶端

`al-adm`: 一条对齐的路径对, 底端到顶端有领先量 (左边每走一步, 右边都有一步与之对应). `Al-top`: 把对齐的领先量从任意的上界世界 $(L,L')$ 换到路径自己的顶端. 两条都对 `Al` 的推导结构递归.

```agda
al-adm : ∀ {L L′ a b a′ b′} {p : a ⊲ b} {lb : Lg b} {p′ : a′ ⊲ b′} {lb′ : Lg b′} → Al L L′ p lb p′ lb′ → Adm a a′ b b′
al-adm {a = a} (aS p′ lb′) = azero , ≤-refl a , ⊲→≤ p′
al-adm (aP {c = c} {c′ = c′} H c≤ ad) = adm-tr (al-adm H) (stepA c c′)
al-adm (aR H) = adm-r (≤-suc (≤-refl _)) (al-adm H)
al-adm (aRL {n′ = n′} H) = adm-r (≤l n′ (≤-refl _)) (al-adm H)
al-adm (aL {stp = stp} H G) = adm-tr (al-adm H) (LimT.TF stp (λ m → al-adm (G m)) 0)

Al-top : ∀ {L L′ a b a′ b′} {p : a ⊲ b} {lb : Lg b} {p′ : a′ ⊲ b′} {lb′ : Lg b′} → Al L L′ p lb p′ lb′ → Al b b′ p lb p′ lb′
Al-top (aS p′ lb′) = aS p′ lb′
Al-top (aP {c = c} {c′ = c′} H c≤ ad) = aP (Al-map (λ a → adm-tr a (stepA c c′)) (Al-top H)) c≤ (stepA c c′)
Al-top (aR H) = aR (Al-map (adm-r (≤-suc (≤-refl _))) (Al-top H))
Al-top (aRL {n′ = n′} H) = aRL (Al-map (adm-r (≤l n′ (≤-refl _))) (Al-top H))
Al-top (aL {stp = stp} H G) =
  aL (Al-map (λ a → adm-tr a (LimT.TF stp (λ m → al-adm (G m)) 0)) (Al-top H))
     (λ m → Al-map (λ a → adm-tr a (LimT.TF stp (λ m₁ → al-adm (G m₁)) (suc m))) (Al-top (G m)))

-- 前段: 树世界到底端, 再接上走过的一段 (对齐换到这一段的顶端)
preAP : ∀ {L L′ W₀ W₀′ a a′ b b′} {lW₀ : Lg W₀} {lW₀′ : Lg W₀′} {ap : W₀ ⊲ a} {ap′ : W₀′ ⊲ a′} {la : Lg a} {la′ : Lg a′}
          {p : a ⊲ b} {lb : Lg b} {p′ : a′ ⊲ b′} {lb′ : Lg b′} →
        AP lW₀ lW₀′ ap la ap′ la′ → Al L L′ p lb p′ lb′ → la ≡ lg⊲ p lb → la′ ≡ lg⊲ p′ lb′ →
        AP lW₀ lW₀′ (⊲-tr ap p) lb (⊲-tr ap′ p′) lb′
preAP hap H e e′ = ap-tr hap (Al-top H , al-adm H , e , e′)
```

## 5 后段: 右边在底部多一段, 后继一步

```agda
extB : ∀ {L L′ a b a′ b′ c′} {p : a ⊲ b} {lb : Lg b} {p′ : a′ ⊲ b′} {lb′ : Lg b′} (r : c′ ⊲ a′) →
       Al L L′ p lb p′ lb′ → Al L L′ p lb (⊲-tr r p′) lb′
extB r (aS p′ lb′) = aS (⊲-tr r p′) lb′
extB r (aP H c≤ ad) = aP (extB r H) c≤ ad
extB r (aR H) = aR (extB r H)
extB r (aRL H) = aRL (extB r H)
extB r (aL H G) = aL (extB r H) G

extR : ∀ {b b′ c′ V V′} {lb : Lg b} {lb′ : Lg b′} {bV : b ⊲ V} {lV : Lg V} {bV′ : b′ ⊲ V′} {lV′ : Lg V′} (r : c′ ⊲ b′) →
       CP lb lb′ bV lV bV′ lV′ → CP lb (lg⊲ r lb′) bV lV (⊲-tr r bV′) lV′
extR {bV′ = bV′} {lV′ = lV′} r ((H , ad , e , e′) , le , c , c′) =
  (extB r H , adm-lo (⊲→≤ r) ad , e , trans (cong (lg⊲ r) e′) (sym (lg-tr r bV′ lV′))) , le , c , c′

sfxS : ∀ {c c′ V V′} {lc : Lg c} {lc′ : Lg c′} {bV : asuc c ⊲ V} {lV : Lg V} {bV′ : asuc c′ ⊲ V′} {lV′ : Lg V′} → c ≤ c′ →
       CP {V = asuc c} {V′ = asuc c′} lc lc′ bV lV bV′ lV′ → CP lc lc′ (⊲-tr (C.suc C.self) bV) lV (⊲-tr (C.suc C.self) bV′) lV′
sfxS {c} {c′} {lc = lc} {lc′} c≤ h = cp-tr (aP (aS C.self lc′) c≤ (stepA c c′) , stepA c c′ , refl , refl) h

-- 一个位置上的前段 (带顶端可比与自洽)
posCP : ∀ {L L′ W₀ W₀′ a a′ c c′ V V′} {lW₀ : Lg W₀} {lW₀′ : Lg W₀′} {ap : W₀ ⊲ a} {ap′ : W₀′ ⊲ a′} {la : Lg a} {la′ : Lg a′}
          {p : a ⊲ c} {lc : Lg c} {p′ : a′ ⊲ c′} {lc′ : Lg c′} {bV : asuc c ⊲ V} {lV : Lg V} {bV′ : asuc c′ ⊲ V′} {lV′ : Lg V′} →
        AP lW₀ lW₀′ ap la ap′ la′ → Al L L′ p lc p′ lc′ → la ≡ lg⊲ p lc → la′ ≡ lg⊲ p′ lc′ → c ≤ c′ →
        CP {V = asuc c} {V′ = asuc c′} lc lc′ bV lV bV′ lV′ → CP lW₀ lW₀′ (⊲-tr ap p) lc (⊲-tr ap′ p′) lc′
posCP hap H e e′ c≤ hs = preAP hap H e e′ , c≤ , proj₁ (cp-coh hs) , proj₂ (cp-coh hs)
```

## 6 极限: 尾段的前段与后段

`aL H G` 一句的数据. 后段: 从第 $i$ 项走进极限 (`limSelf i`). 前段: 尾段 $m$ 的底端是 $f(m+n)$, 前段是 `tailP` (`TP m`); 它的 `Lg` 等式要自洽 (`eqT`).

```agda
module LimW {L L′} {f f′ : ℕ → A} {n n′ : ℕ} {a a′} {p : a ⊲ f n} {p′ : a′ ⊲ f′ n′}
            {stp : ∀ n → f n ⊲ f (suc n)} {wl : ∀ n → Lg (f n)} {stp′ : ∀ n → f′ n ⊲ f′ (suc n)} {wl′ : ∀ n → Lg (f′ n)}
            (H : Al L L′ p (wl n) p′ (wl′ n′))
            (G : ∀ m → Al L L′ (stp (m + n)) (wl (suc (m + n))) (stp′ (m + n′)) (wl′ (suc (m + n′))))
            (ch : Coh {alim f} (stp , wl)) (ch′ : Coh {alim f′} (stp′ , wl′)) where
  TF : ∀ i → Adm (f (i + n)) (f′ (i + n′)) (alim f) (alim f′)
  TF = LimT.TF stp (λ m → al-adm (G m))

  G̃ : ∀ k → Al (alim f) (alim f′) (stp (k + n)) (wl (suc (k + n))) (stp′ (k + n′)) (wl′ (suc (k + n′)))
  G̃ k = Al-map (λ x → adm-tr x (TF (suc k))) (Al-top (G k))

  limSelf : ∀ i → AP (wl (i + n)) (wl′ (i + n′)) (C.lim (i + n) C.self) (stp , wl) (C.lim (i + n′) C.self) (stp′ , wl′)
  limSelf i =
    aL (aS C.self (wl′ (i + n′)))
       (λ j → subst₂ (λ X X′ → Al (alim f) (alim f′) (stp X) (wl (suc X)) (stp′ X′) (wl′ (suc X′))) (+-assoc j i n) (+-assoc j i n′) (G̃ (j + i))) ,
    TF i , refl , refl

  TP : ∀ m → Al L L′ (tailP f stp p m) (wl (m + n)) (tailP f′ stp′ p′ m) (wl′ (m + n′))
  TP zero = H
  TP (suc m) = cat (TP m) (G m) (sym (proj₁ ch (m + n))) (sym (proj₁ ch′ (m + n′)))

  eqT : ∀ m → lg⊲ (tailP f stp p m) (wl (m + n)) ≡ lg⊲ p (wl n)
  eqT zero = refl
  eqT (suc m) = trans (lg-tr (tailP f stp p m) (stp (m + n)) (wl (suc (m + n)))) (trans (cong (lg⊲ (tailP f stp p m)) (proj₁ ch (m + n))) (eqT m))

  eqT′ : ∀ m → lg⊲ (tailP f′ stp′ p′ m) (wl′ (m + n′)) ≡ lg⊲ p′ (wl′ n′)
  eqT′ zero = refl
  eqT′ (suc m) = trans (lg-tr (tailP f′ stp′ p′ m) (stp′ (m + n′)) (wl′ (suc (m + n′)))) (trans (cong (lg⊲ (tailP f′ stp′ p′ m)) (proj₁ ch′ (m + n′))) (eqT′ m))

  eqA : ∀ {la : Lg a} → la ≡ lg⊲ p (wl n) → ∀ m → la ≡ lg⊲ (tailP f stp p m) (wl (m + n))
  eqA e m = trans e (sym (eqT m))

  eqA′ : ∀ {la′ : Lg a′} → la′ ≡ lg⊲ p′ (wl′ n′) → ∀ m → la′ ≡ lg⊲ (tailP f′ stp′ p′ m) (wl′ (m + n′))
  eqA′ e m = trans e (sym (eqT′ m))

  eaT : ∀ m → wl (m + n) ≡ lg⊲ (stp (m + n)) (wl (suc (m + n)))
  eaT m = sym (proj₁ ch (m + n))

  eaT′ : ∀ m → wl′ (m + n′) ≡ lg⊲ (stp′ (m + n′)) (wl′ (suc (m + n′)))
  eaT′ m = sym (proj₁ ch′ (m + n′))

  hapT : ∀ {W₀ W₀′} {lW₀ : Lg W₀} {lW₀′ : Lg W₀′} {ap : W₀ ⊲ a} {ap′ : W₀′ ⊲ a′} {la : Lg a} {la′ : Lg a′} →
         AP lW₀ lW₀′ ap la ap′ la′ → la ≡ lg⊲ p (wl n) → la′ ≡ lg⊲ p′ (wl′ n′) →
         ∀ m → AP lW₀ lW₀′ (⊲-tr ap (tailP f stp p m)) (wl (m + n)) (⊲-tr ap′ (tailP f′ stp′ p′ m)) (wl′ (m + n′))
  hapT hap e e′ m = preAP hap (TP m) (eqA e m) (eqA′ e′ m)
```
