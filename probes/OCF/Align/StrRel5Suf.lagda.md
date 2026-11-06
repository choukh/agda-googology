# 结构关系, 第五轮 (二): 剩下的路径也对齐

> 不含记号. 入口 [StrRel5](StrRel5.lagda.md).
>
> 内层 `nκ` 第 0 格的路径是 `⊲-tr q (sum-fst W z)`, 其中 $q$ 是外层 `Walk` 在这个位置**剩下的路径** (`⊲-tr (suc self) bV`). `StrRel4Gen.alZeroᴾ` 要 $q\sim q'$ 的对齐. 这里证明: 外层对齐时, 每一对对应位置剩下的两条路径也对齐, 所以分支的语义可以只对**对齐的** $q,q'$ 量化.
>
> 三条前端引理 (对齐推导上归纳, 位置是绝对的, 所以往前端加东西不动已有的对):
>
> - **`rfx`**: 右边前端多一段任意路径, 仍对齐 (多出的位置落进 `aS`);
> - **`fcs`**: 两边前端各加一个对应位置 ($c\le c'$, 领先量), 仍对齐;
> - **`fcl`**: 两边前端各加一段极限 (前缀空, 各段由给定的对齐相关), 仍对齐. 极限的长度证据由一条等式接上 (`lg⊲` 沿剩下的路径).
>
> **定理 `walkᵠ`**: 与 `StrRel5Walk.walkˢ` 相同, 只是分支前提 `br` 多一条: 剩下的两条路径对齐. `walkᵠ` 一路带着 "剩下的路径对齐" 与 "长度证据 = 沿剩下的路径取回" 两个不变量; 起点 (`bV = self`) 两者都平凡.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel5Suf where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-assoc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; lg⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_)
open import OCF.Align.SumOneTree using (D; _⨾_; Cut; tailP)
import OCF.Align.SumOneClosed as F
open import OCF.Align.KValTree using (Bk)
open import OCF.Align.KValSem using (ac₁)
open import OCF.Align.KNestAdm using (Adm)
open import OCF.Align.StrRel4Walk using (Al; aS; aP; aR; aRL; aL)
open import OCF.Align.StrRel4Gen using (lg-tr; ext)
open import OCF.Align.StrRel4Pr using (_⊑ᴾ_; z0; sq; lm; pr)
open import OCF.Align.StrRel5Walk using (Env; W; lW; ll; act; Rd; Rn; Wlk)
```

## §1 前端引理

```agda
module _ {L L′ : A} where
  rfx : ∀ {a b x a′ b′} {p : a ⊲ b} {lb} {p′ : a′ ⊲ b′} {lb′} (r : x ⊲ a′) → Al L L′ p lb p′ lb′ → Al L L′ p lb (⊲-tr r p′) lb′
  rfx r (aS p′ lb′) = aS (⊲-tr r p′) lb′
  rfx r (aP H c≤ ad) = aP (rfx r H) c≤ ad
  rfx r (aR H) = aR (rfx r H)
  rfx r (aRL H) = aRL (rfx r H)
  rfx r (aL H G) = aL (rfx r H) G

  fcs : ∀ {c c′ b b′} {bV : asuc c ⊲ b} {lb} {bV′ : asuc c′ ⊲ b′} {lb′} → c ≤ c′ → Adm c c′ L L′ →
        Al L L′ bV lb bV′ lb′ → Al L L′ (⊲-tr (C.suc C.self) bV) lb (⊲-tr (C.suc C.self) bV′) lb′
  fcs h ad (aS bV′ lb′) = ext bV′ lb′ refl (aP (aS C.self (lg⊲ bV′ lb′)) h ad)
  fcs h ad (aP H c≤ a) = aP (fcs h ad H) c≤ a
  fcs h ad (aR H) = aR (fcs h ad H)
  fcs h ad (aRL H) = aRL (fcs h ad H)
  fcs h ad (aL H G) = aL (fcs h ad H) G

  fcl : ∀ {f f′ b b′ N N′} {bV : alim f ⊲ b} {lb} {bV′ : alim f′ ⊲ b′} {lb′}
          {stp : ∀ n → f n ⊲ f (suc n)} {wl : ∀ n → Lg (f n)} {stp′ : ∀ n → f′ n ⊲ f′ (suc n)} {wl′ : ∀ n → Lg (f′ n)} →
        Al L L′ bV lb bV′ lb′ → lg⊲ bV lb ≡ (stp , wl) → lg⊲ bV′ lb′ ≡ (stp′ , wl′) →
        (∀ m → Al L L′ (stp (m + N)) (wl (suc (m + N))) (stp′ (m + N′)) (wl′ (suc (m + N′)))) →
        Al L L′ (⊲-tr (C.lim N C.self) bV) lb (⊲-tr (C.lim N′ C.self) bV′) lb′
  fcl {f = f} {N = N} {N′ = N′} {stp = stp} {wl} {stp′} {wl′} (aS bV′ lb′) e e′ G =
    subst (λ l → Al L L′ (C.lim {f = f} N C.self) l (⊲-tr (C.lim N′ C.self) bV′) lb′) (sym e)
          (ext bV′ lb′ (sym e′) (aL (aS C.self (wl′ N′)) G))
  fcl (aP H c≤ a) e e′ G = aP (fcl H e e′ G) c≤ a
  fcl (aR H) e e′ G = aR (fcl H e e′ G)
  fcl (aRL H) e e′ G = aRL (fcl H e e′ G)
  fcl (aL H Gx) e e′ G = aL (fcl H e e′ G) Gx

e-suc : ∀ {c b} (bV : asuc c ⊲ b) (l : Lg b) {lc : Lg c} → lc ≡ lg⊲ bV l → lc ≡ lg⊲ (⊲-tr (C.suc C.self) bV) l
e-suc bV l e = trans e (sym (lg-tr (C.suc C.self) bV l))

e-lim : ∀ {f b} (bV : alim f ⊲ b) (l : Lg b) {stp : ∀ n → f n ⊲ f (suc n)} {wl : ∀ n → Lg (f n)} k →
        (stp , wl) ≡ lg⊲ bV l → wl k ≡ lg⊲ (⊲-tr (C.lim k C.self) bV) l
e-lim bV l k e = trans (cong (λ x → proj₂ x k) e) (sym (lg-tr (C.lim k C.self) bV l))
```

## §2 `walkᵠ`

```agda
module GoQ (s s′ : Env) {V V′} (u : Bk V) (u′ : Bk V′) (R : F.St (W s) → F.St (W s′) → Set)
           (adv : ∀ {Y Y′} (Δ : F.Df (W s)) (Δ′ : F.Df (W s′)) → R Y Y′ → Rd s Δ ⊑ᴾ Rd s′ Δ′ → R (Y F.⊕ Δ) (Y′ F.⊕ Δ′))
           (br : ∀ {c c′} (p : V ⊲ c) (p′ : V′ ⊲ c′) (lc : Lg c) (lc′ : Lg c′) → c ≤ c′ → Adm c c′ (W s) (W s′) →
                 ∀ (q : c ⊲ W s) (q′ : c′ ⊲ W s′) → Al (W s) (W s′) q (lW s) q′ (lW s′) →
                 ∀ w w′ Y Y′ → R Y Y′ → Rd s (Rn s (u p lc) q w Y) ⊑ᴾ Rd s′ (Rn s′ (u′ p′ lc′) q′ w′ Y′)) where

  AlW = Al (W s) (W s′)

  walkᵠ : ∀ {a b a′ b′} {p : a ⊲ b} {lb : Lg b} {p′ : a′ ⊲ b′} {lb′ : Lg b′} → AlW p lb p′ lb′ →
          ∀ ap ap′ (bV : b ⊲ W s) (bV′ : b′ ⊲ W s′) → AlW bV (lW s) bV′ (lW s′) → lb ≡ lg⊲ bV (lW s) → lb′ ≡ lg⊲ bV′ (lW s′) →
          ∀ co co′ Y Y′ → R Y Y′ → Rd s (Wlk s u p ap lb bV co Y) ⊑ᴾ Rd s′ (Wlk s′ u′ p′ ap′ lb′ bV′ co′ Y′)
  walkᵠ (aS p′ lb′) ap ap′ bV bV′ hb e e′ co co′ Y Y′ r = z0
  walkᵠ (aR H) ap ap′ bV bV′ hb e e′ co co′ Y Y′ r =
    pr (walkᵠ H ap ap′ bV (⊲-tr (C.suc C.self) bV′) (rfx (C.suc C.self) hb) e (e-suc bV′ (lW s′) e′) co co′ Y Y′ r)
  walkᵠ (aRL {n′ = n′} H) ap ap′ bV bV′ hb e e′ co co′ Y Y′ r =
    pr (walkᵠ H ap ap′ bV (⊲-tr (C.lim n′ C.self) bV′) (rfx (C.lim n′ C.self) hb) e (e-lim bV′ (lW s′) n′ e′) co co′ Y Y′ r)
  walkᵠ (aP {c = c} {c′ = c′} {p = p} {lc} {p′} {lc′} H c≤ ad) ap ap′ bV bV′ hb e e′ co co′ Y Y′ r =
    sq O (br (⊲-tr ap p) (⊲-tr ap′ p′) lc lc′ c≤ ad q q′ hq
             (co ⨾ Cut u c p ap lc q) (co′ ⨾ Cut u′ c′ p′ ap′ lc′ q′) (Y F.⊕ Δ) (Y′ F.⊕ Δ′) (adv Δ Δ′ r O))
    where
    q = ⊲-tr (C.suc C.self) bV
    q′ = ⊲-tr (C.suc C.self) bV′
    hq = fcs c≤ ad hb
    Δ = Wlk s u p ap lc q co Y
    Δ′ = Wlk s′ u′ p′ ap′ lc′ q′ co′ Y′
    O = walkᵠ H ap ap′ q q′ hq (e-suc bV (lW s) e) (e-suc bV′ (lW s′) e′) co co′ Y Y′ r
  walkᵠ (aL {f = f} {n} {f′ = f′} {n′} {p} {p′} {stp} {wl} {stp′} {wl′} H G) ap ap′ bV bV′ hb e e′ co co′ Y Y′ r =
    sq O (lm (λ m → proj₁ (go m)))
    where
    fV : ∀ m → f m ⊲ W s
    fV m = ⊲-tr (C.lim m C.self) bV
    fV′ : ∀ m → f′ m ⊲ W s′
    fV′ m = ⊲-tr (C.lim m C.self) bV′
    Gs : ∀ k → (∀ j → AlW (stp (j + k + n)) (wl (suc (j + k + n))) (stp′ (j + k + n′)) (wl′ (suc (j + k + n′)))) →
         ∀ j → AlW (stp (j + (k + n))) (wl (suc (j + (k + n)))) (stp′ (j + (k + n′))) (wl′ (suc (j + (k + n′))))
    Gs k g j = subst₂ (λ x x′ → AlW (stp x) (wl (suc x)) (stp′ x′) (wl′ (suc x′))) (+-assoc j k n) (+-assoc j k n′) (g j)
    hF : ∀ k → AlW (fV (k + n)) (lW s) (fV′ (k + n′)) (lW s′)
    hF k = fcl {N = k + n} {N′ = k + n′} hb (sym e) (sym e′) (Gs k (λ j → G (j + k)))
    Δ = Wlk s u p ap (wl n) (fV n) co Y
    Δ′ = Wlk s′ u′ p′ ap′ (wl′ n′) (fV′ n′) co′ Y′
    O = walkᵠ H ap ap′ (fV n) (fV′ n′) (hF 0) (e-lim bV (lW s) n e) (e-lim bV′ (lW s′) n′ e′) co co′ Y Y′ r
    Rp = F.WRp ac₁ u f stp wl p ap fV (lW s) (ll s) (act s) (co ⨾ Cut u (f n) p ap (wl n) (fV n)) (Y F.⊕ Δ)
    Rp′ = F.WRp ac₁ u′ f′ stp′ wl′ p′ ap′ fV′ (lW s′) (ll s′) (act s′) (co′ ⨾ Cut u′ (f′ n′) p′ ap′ (wl′ n′) (fV′ n′)) (Y′ F.⊕ Δ′)
    Sg : ℕ → F.Df (W s)
    Sg m = Wlk s u (stp (m + n)) (⊲-tr ap (tailP f stp p m)) (wl (suc (m + n))) (fV (suc (m + n))) (proj₁ (Rp m)) (proj₂ (Rp m))
    Sg′ : ℕ → F.Df (W s′)
    Sg′ m = Wlk s′ u′ (stp′ (m + n′)) (⊲-tr ap′ (tailP f′ stp′ p′ m)) (wl′ (suc (m + n′))) (fV′ (suc (m + n′))) (proj₁ (Rp′ m)) (proj₂ (Rp′ m))
    st : ∀ m → R (proj₂ (Rp m)) (proj₂ (Rp′ m))
    go : ∀ m → (Rd s (Sg m) ⊑ᴾ Rd s′ (Sg′ m)) × R (proj₂ (Rp m)) (proj₂ (Rp′ m))
    go m = walkᵠ (G m) _ _ (fV (suc (m + n))) (fV′ (suc (m + n′))) (hF (suc m))
                 (e-lim bV (lW s) (suc (m + n)) e) (e-lim bV′ (lW s′) (suc (m + n′)) e′) _ _ _ _ (st m) , st m
    st zero = adv Δ Δ′ r O
    st (suc m) = adv (Sg m) (Sg′ m) (st m) (proj₁ (go m))

  -- 一格: 起点的剩下路径是 self
  cellᵠ : ∀ {a a′} {p : a ⊲ W s} {p′ : a′ ⊲ W s′} → AlW p (lW s) p′ (lW s′) → ∀ ap ap′ co co′ Y Y′ → R Y Y′ →
          Rd s (Wlk s u p ap (lW s) C.self co Y) ⊑ᴾ Rd s′ (Wlk s′ u′ p′ ap′ (lW s′) C.self co′ Y′)
  cellᵠ H ap ap′ co co′ Y Y′ r = walkᵠ H ap ap′ C.self C.self (aS C.self (lW s′)) refl refl co co′ Y Y′ r
```
