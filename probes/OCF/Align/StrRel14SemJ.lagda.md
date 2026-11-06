# 结构关系, 第十四轮 (一): 与层无关的六条规则与两世界走法, 带不变量 (生成)

> 由 `probes/Survey/scripts/strrel14/mk_semj.py` 从 [StrRel12Sem](StrRel12Sem.lagda.md) 生成 (从仓库根运行 `python3 probes/Survey/scripts/strrel14/mk_semj.py .`, 逐字节可重生成). 入口 [StrRel14J](StrRel14J.lagda.md). 不读记号. 证明逐句不变, 只换状态前提: `R∀c` 换成不变量记录 `I : Inv` ([StrRel14If](StrRel14If.lagda.md)) 的 `J`, `advRc`/`cvRc` 换成记录的封闭律 `⊕J`/`cvJ`, `R∀c` 的两个分量经 `toR` 取, `HAW`/`SemW`/`haw↾` 换成 `HAWJ`/`SemJ`/`haw↾J`. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.HtFeedTree using (H; LgH)
open import OCF.Align.StrRel14If using (Inv)
module OCF.Align.StrRel14SemJ (Λ : H) (lΛ : LgH Λ) (I : Inv Λ lΛ) where

open import OCF.Align.StrRel14If Λ lΛ using (module WithInv)
open WithInv I using (HAWJ; SemJ)
open Inv I using (J; toR; cvJ; ⊕J)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; _⊲_; Lg; ⊲-tr; lg⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_)
open import OCF.Align.HtFeedTree using (hz; D; n0; n1; _⨾_; nl; nw; AccY; tailP; Cut)
open import OCF.Align.HtFeedClosed using (module At)
open import OCF.Align.StrRel4Walk using (Al; aS; aP; aR; aRL; aL)
open import OCF.Align.StrRel12Al using (Coh; AP; CP; cp-self; cp-top; cp-tr; cp-coh; extR; sfxS; posCP; module LimW)
open import OCF.Align.StrRel12Rel using (Rel; n0ᴸ; n1ᴸ; ⨾ᴸ; nlᴸ; prᴸ; nwAᴸ)
open import OCF.Align.StrRel12Int using (module CutR)

open import OCF.Align.StrRel12Sem Λ lΛ using (Top; TC; OAc; R∀c)

module P = At Λ lΛ
open P using (Tg; tg; wm; tm; lm; tg↑; τ₀; St; Df; yc; d; z; cv; _⊕⟨_⟩_; Run; Rpt; Ig; Ig↾; LW; Walk; WRp; _⨾ᴰ_; nlᴰ; zeroD)

haw↾J : ∀ L {W W′ W₁ W₁′} {lW : Lg W} {lW′ : Lg W′} {p : W ⊲ W₁} {lW₁ : Lg W₁} {p′ : W′ ⊲ W₁′} {lW₁′ : Lg W₁′}
          {A₀ : Ig L W} {A₀′ : Ig L W′} → AP lW lW′ p lW₁ p′ lW₁′ → HAWJ L lW lW′ A₀ A₀′ → HAWJ L lW₁ lW₁′ (Ig↾ p A₀) (Ig↾ p′ A₀′)
haw↾J L {p = p} {p′ = p′} ap ha p₂ p₂′ l l′ cp = ha (⊲-tr p p₂) (⊲-tr p′ p₂′) l l′ (cp-tr ap cp)
```

## 3 与层无关的六条规则

```agda
sem-n0 : ∀ L {V V′} {lV : Lg V} {lV′ : Lg V′} {x′ : D L V′} → SemJ L lV lV′ n0 x′
sem-n0 L lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r T T′ ta = n0ᴸ

sem-n1 : ∀ L {V V′} {lV : Lg V} {lV′ : Lg V′} → SemJ L lV lV′ n1 n1
sem-n1 L lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r = ha C.self C.self lW lW′ (cp-top hq) w w′ hw Y Y′ r

sem-⨾ : ∀ L {V V′} {lV : Lg V} {lV′ : Lg V′} {x y : D L V} {x′ y′ : D L V′} →
        Rel L lV lV′ x x′ → SemJ L lV lV′ x x′ → SemJ L lV lV′ y y′ → SemJ L lV lV′ (x ⨾ y) (x′ ⨾ y′)
sem-⨾ L {x = x} {x′ = x′} hx sx sy lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r T T′ ta =
  ⨾ᴸ (Ox T T′ ta)
     (sy lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha (w ⨾ nw q x) (w′ ⨾ nw q′ x′) (⨾ᴸ hw (nwAᴸ (proj₁ hq) hx))
         _ _ (⊕J (cp-top hq) Y Y′ Δ Δ′ r Ox) T T′ ta)
  where
  Δ = Run ac x q lW ll A₀ w Y
  Δ′ = Run ac′ x′ q′ lW′ ll′ A₀′ w′ Y′
  Ox = sx lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r

sem-nw : ∀ L {V₀ V₀′ V V′} {lV₀ : Lg V₀} {lV₀′ : Lg V₀′} {lV : Lg V} {lV′ : Lg V′} {p : V₀ ⊲ V} {p′ : V₀′ ⊲ V′}
           {x : D L V₀} {x′ : D L V₀′} →
         AP lV₀ lV₀′ p lV p′ lV′ → SemJ L lV₀ lV₀′ x x′ → SemJ L lV lV′ (nw p x) (nw p′ x′)
sem-nw L hp sx lW lW′ ac ac′ ll ll′ q q′ hq = sx lW lW′ ac ac′ ll ll′ (⊲-tr _ q) (⊲-tr _ q′) (cp-tr hp hq)

sem-pr : ∀ L {V V′} {lV : Lg V} {lV′ : Lg V′} {x : D L V} {x′ y′ : D L V′} →
         SemJ L lV lV′ x x′ → SemJ L lV lV′ x (x′ ⨾ y′)
sem-pr L sx lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r T T′ ta =
  prᴸ (sx lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r T T′ ta)

module NL (L : H) {V V′} {lV : Lg V} {lV′ : Lg V′} {d₁ : ℕ → D L V} {d₁′ : ℕ → D L V′}
          (hd : ∀ n → Rel L lV lV′ (d₁ n) (d₁′ n)) (sd : ∀ n → SemJ L lV lV′ (d₁ n) (d₁′ n))
          {W W′} (lW : Lg W) (lW′ : Lg W′) (ac ac′ : AccY L) (ll : LW L W) (ll′ : LW L W′)
          (q : V ⊲ W) (q′ : V′ ⊲ W′) (hq : CP lV lV′ q lW q′ lW′)
          (A₀ : Ig L W) (A₀′ : Ig L W′) (ha : HAWJ L lW lW′ A₀ A₀′)
          (w : D L W) (w′ : D L W′) (hw : Rel L lW lW′ w w′) (Y : St W) (Y′ : St W′) (r : J lW lW′ Y Y′) where
  Pn : ℕ → D L W × St W
  Pn = Rpt ac d₁ q lW ll A₀ w Y
  Pn′ : ℕ → D L W′ × St W′
  Pn′ = Rpt ac′ d₁′ q′ lW′ ll′ A₀′ w′ Y′

  St′ : ℕ → Set
  St′ n = Rel L lW lW′ (proj₁ (Pn n)) (proj₁ (Pn′ n)) × J lW lW′ (proj₂ (Pn n)) (proj₂ (Pn′ n))

  out : ∀ n → St′ n → OAc lW lW′ (Run ac (d₁ n) q lW ll A₀ (proj₁ (Pn n)) (proj₂ (Pn n)))
                                   (Run ac′ (d₁′ n) q′ lW′ ll′ A₀′ (proj₁ (Pn′ n)) (proj₂ (Pn′ n)))
  out n (h , s) = sd n lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha _ _ h _ _ s

  go : ∀ n → St′ n
  go zero = hw , r
  go (suc n) = ⨾ᴸ (proj₁ (go n)) (nwAᴸ (proj₁ hq) (hd n)) ,
               ⊕J (cp-top hq) (proj₂ (Pn n)) (proj₂ (Pn′ n)) _ _ (proj₂ (go n)) (out n (go n))

sem-nl : ∀ L {V V′} {lV : Lg V} {lV′ : Lg V′} {d₁ : ℕ → D L V} {d₁′ : ℕ → D L V′} →
         (∀ n → Rel L lV lV′ (d₁ n) (d₁′ n)) → (∀ n → SemJ L lV lV′ (d₁ n) (d₁′ n)) → SemJ L lV lV′ (nl d₁) (nl d₁′)
sem-nl L hd sd lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r T T′ ta =
  nlᴸ (λ n → N.out n (N.go n) T T′ ta)
  where module N = NL L hd sd lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r
```

## 4 两世界的走法

分支 $u$ 在每个位置 $c$ 上跑: 树在前段的 `CP` 对上相关 (`h`, 即 `κᴸ` 的前提), 有语义 (`sb`); 运行路径是后段 (`sfxS`). 上下文是 `co` 接上前段的 `Cut` (`cutR`), 状态是前面各段的输出累加 (`advRc`).

```agda
module WalkR {ly W₀ W₀′ V₁ V₁′} {lW₀ : Lg W₀} {lW₀′ : Lg W₀′} {lV : Lg V₁} {lV′ : Lg V₁′} (ac ac₂ : AccY ly)
             {u : ∀ {c} → W₀ ⊲ c → Lg c → D ly c} {u′ : ∀ {c} → W₀′ ⊲ c → Lg c → D ly c}
             (h : ∀ {c c′} (P : W₀ ⊲ c) (P′ : W₀′ ⊲ c′) (lc : Lg c) (lc′ : Lg c′) → CP lW₀ lW₀′ P lc P′ lc′ → Rel ly lc lc′ (u P lc) (u′ P′ lc′))
             (sb : ∀ {c c′} (P : W₀ ⊲ c) (P′ : W₀′ ⊲ c′) (lc : Lg c) (lc′ : Lg c′) → CP lW₀ lW₀′ P lc P′ lc′ → SemJ ly lc lc′ (u P lc) (u′ P′ lc′))
             (ll : LW ly V₁) (ll′ : LW ly V₁′) (A₀ : Ig ly V₁) (A₀′ : Ig ly V₁′) (ha : HAWJ ly lV lV′ A₀ A₀′) (tp : Top lV lV′) where
  open CutR h

  walkR : ∀ {L L′ a b a′ b′} {p : a ⊲ b} {lb : Lg b} {p′ : a′ ⊲ b′} {lb′ : Lg b′} → Al L L′ p lb p′ lb′ →
          ∀ {la la′} (ap : W₀ ⊲ a) (ap′ : W₀′ ⊲ a′) → AP lW₀ lW₀′ ap la ap′ la′ → la ≡ lg⊲ p lb → la′ ≡ lg⊲ p′ lb′ →
          (bV : b ⊲ V₁) (bV′ : b′ ⊲ V₁′) → CP lb lb′ bV lV bV′ lV′ → ∀ {co co′} → Rel ly lV lV′ co co′ →
          ∀ {Y Y′} → J lV lV′ Y Y′ →
          OAc lV lV′ (Walk ac u b p ap lb bV lV ll A₀ co Y) (Walk ac₂ u′ b′ p′ ap′ lb′ bV′ lV′ ll′ A₀′ co′ Y′)
  walkR (aS p′ lb′) ap ap′ hap e e′ bV bV′ hs hco hY T T′ tc = n0ᴸ
  walkR (aP {c = c} {c′ = c′} {p = p} {lc} {p′} {lc′} H c≤ ad) ap ap′ hap e e′ bV bV′ hs {co} {co′} hco {Y} {Y′} hY T T′ tc =
    ⨾ᴸ (O T T′ tc)
       (sb (⊲-tr ap p) (⊲-tr ap′ p′) lc lc′ (posCP hap H e e′ c≤ hs) lV lV′ ac ac₂ ll ll′ _ _ hs₁ A₀ A₀′ ha _ _
           (⨾ᴸ hco (cutR H ap ap′ hap e e′ _ _ hs₁)) _ _ (⊕J tp Y Y′ _ _ hY O) T T′ tc)
    where
    hs₁ = sfxS c≤ hs
    O = walkR H ap ap′ hap e e′ _ _ hs₁ hco hY
  walkR (aR H) ap ap′ hap e e′ bV bV′ hs hco hY T T′ tc =
    prᴸ (walkR H ap ap′ hap e e′ bV (⊲-tr (C.suc C.self) bV′) (extR (C.suc C.self) hs) hco hY T T′ tc)
  walkR (aRL {n′ = n′} H) ap ap′ hap e e′ bV bV′ hs hco hY T T′ tc =
    prᴸ (walkR H ap ap′ hap e e′ bV (⊲-tr (C.lim n′ C.self) bV′) (extR (C.lim n′ C.self) hs) hco hY T T′ tc)
  walkR (aL {f = f} {n} {f′ = f′} {n′} {p} {p′} {stp} {wl} {stp′} {wl′} H G) ap ap′ hap e e′ bV bV′ hs {co} {co′} hco {Y} {Y′} hY T T′ tc =
    ⨾ᴸ (O₀ T T′ tc) (nlᴸ (λ m → proj₁ (go m) T T′ tc))
    where
    module W = LimW H G (proj₁ (cp-coh hs)) (proj₂ (cp-coh hs))
    fV : ∀ m → f m ⊲ V₁
    fV m = ⊲-tr (C.lim m C.self) bV
    fV′ : ∀ m → f′ m ⊲ V₁′
    fV′ m = ⊲-tr (C.lim m C.self) bV′
    hs₀ = cp-tr (W.limSelf 0) hs
    O₀ = walkR H ap ap′ hap e e′ (fV n) (fV′ n′) hs₀ hco hY
    Rp = WRp ac u f stp wl p ap fV lV ll A₀ (co ⨾ Cut u (f n) p ap (wl n) (fV n)) (Y ⊕⟨ lV ⟩ Walk ac u (f n) p ap (wl n) (fV n) lV ll A₀ co Y)
    Rp′ = WRp ac₂ u′ f′ stp′ wl′ p′ ap′ fV′ lV′ ll′ A₀′ (co′ ⨾ Cut u′ (f′ n′) p′ ap′ (wl′ n′) (fV′ n′))
              (Y′ ⊕⟨ lV′ ⟩ Walk ac₂ u′ (f′ n′) p′ ap′ (wl′ n′) (fV′ n′) lV′ ll′ A₀′ co′ Y′)
    Sg : ℕ → Df V₁
    Sg m = Walk ac u (f (suc (m + n))) (stp (m + n)) (⊲-tr ap (tailP f stp p m)) (wl (suc (m + n))) (fV (suc (m + n))) lV ll A₀ (proj₁ (Rp m)) (proj₂ (Rp m))
    Sg′ : ℕ → Df V₁′
    Sg′ m = Walk ac₂ u′ (f′ (suc (m + n′))) (stp′ (m + n′)) (⊲-tr ap′ (tailP f′ stp′ p′ m)) (wl′ (suc (m + n′))) (fV′ (suc (m + n′))) lV′ ll′ A₀′
               (proj₁ (Rp′ m)) (proj₂ (Rp′ m))
    Sm : ℕ → Set
    Sm m = Rel ly lV lV′ (proj₁ (Rp m)) (proj₁ (Rp′ m)) × J lV lV′ (proj₂ (Rp m)) (proj₂ (Rp′ m))
    st : ∀ m → Sm m
    go : ∀ m → OAc lV lV′ (Sg m) (Sg′ m) × Sm m
    go m = walkR (G m) _ _ (W.hapT hap e e′ m) (W.eaT m) (W.eaT′ m) (fV (suc (m + n))) (fV′ (suc (m + n′))) (cp-tr (W.limSelf (suc m)) hs)
                 (proj₁ (st m)) (proj₂ (st m)) , st m
    st zero = ⨾ᴸ hco (cutR H ap ap′ hap e e′ (fV n) (fV′ n′) hs₀) , ⊕J tp Y Y′ _ _ hY O₀
    st (suc m) = ⨾ᴸ (proj₁ (st m)) (cutR (G m) _ _ (W.hapT hap e e′ m) (W.eaT m) (W.eaT′ m) _ _ (cp-tr (W.limSelf (suc m)) hs)) ,
                 ⊕J tp _ _ (Sg m) (Sg′ m) (proj₂ (st m)) (proj₁ (go m))
```
