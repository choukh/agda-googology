# 结构关系, 第十五轮 (一): 两条状态律, 异质的六条规则, 左层为 $0$ 的语义

> 不读记号. 入口 [StrRel15](StrRel15.lagda.md). 接口 [StrRel15If](StrRel15If.lagda.md).
>
> 1. **(定理) `law⊕`, `lawcv`**: 接口的两条状态律 `Law⊕`, `Lawcv` 成立. `J²` 的三个分量各自封闭: `OA²` 逐目标对用 `⨾ˣ` (前进) 或把目标沿路径抬回去 (换世界, `cp-tr`); 第 $0$ 层分量用 $(\tau_0,\tau_0)$ 这一对 (`Top` 加 `s∞`); `NE` 用 `StrRel14J.ne⊕`, `necv`.
> 2. **(定理) 异质的六条规则** `sem-n0` … `sem-pr`: 左层 $L$, 右层 $L'$ 任意, 结论是目标层对上的 `OA²`. 证明逐句同 `StrRel12Sem` §3, 状态前进处用 `law⊕`.
> 3. **(定理) `semX0`**: 对一切右层 $L'$, `RelX hz L′ x x′` 蕴含 `SemX² hz L′ x x′`. 左层为 $0$ 时 `RelX` 的推导只用六条与层无关的规则 (第 $0$ 层没有节点种类, `NZ hz` 是空的), 对推导归纳.
> 4. 辅助: `haw↾²` (动作前提沿 `AP` 搬运), `sOutX` (从 `BelowX` 取出坐标层上的 `RelX`), `z⊑` ($0\sqsubseteq_\infty k$).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.HtFeedTree using (H; LgH)
module OCF.Align.StrRel15Sem (Λ : H) (lΛ : LgH Λ) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtFeedTree using (hz; hs; hl; hΩ; _⊲[_]_; hself; hsuc; hlim; hLim; StH; ss; sl; sL; D; n0; n1; _⨾_; nl; nw; AccY;
  outS)
open import OCF.Align.HtFeedClosed using (module At)
open import OCF.Align.StrRel11Rk Λ lΛ using (_⊑∞_; s∞; u∞; l∞; L∞)
open import OCF.Align.StrRel12Al using (AP; CP; cp-top; cp-tr)
open import OCF.Align.StrRel12Sem Λ lΛ using (Top)
open import OCF.Align.StrRel14If Λ lΛ using (RelX; BelowX; RelSX; RelAtX; n0ˣ; n1ˣ; ⨾ˣ; nlˣ; prˣ; nwˣ; niˣ; κˣ)
open import OCF.Align.StrRel14J Λ lΛ using (ne⊕; necv)
open import OCF.Align.StrRel15If Λ lΛ using (TX; OA²; R²; J²; Law⊕; Lawcv; HAW²; SemX²)

module P = At Λ lΛ
open P using (Tg; tg; wm; tm; lm; tg↑; τ₀; St; Df; yc; d; z; cv; _⊕⟨_⟩_; Run; Rpt; Ig; Ig↾; LW)
```

## 1 两条状态律

```agda
law⊕ : Law⊕
law⊕ {lW = lW} {lW′} tp Y Y′ Δ Δ′ ((r , rz) , (ne , ne′)) O =
  ((λ T T′ tx → ⨾ˣ (r T T′ tx) (O T T′ tx)) , ⨾ˣ rz (O (τ₀ lW) (τ₀ lW′) (tp , s∞))) ,
  (ne⊕ {lW = lW} Y Δ ne , ne⊕ {lW = lW′} Y′ Δ′ ne′)

lawcv : Lawcv
lawcv {q = q} {q′ = q′} ap Y Y′ ((r , rz) , (ne , ne′)) =
  ((λ T T′ tx → r (tg↑ q T) (tg↑ q′ T′) (cp-tr ap (proj₁ tx) , proj₂ tx)) , n0ˣ) , (necv q Y ne , necv q′ Y′ ne′)
```

## 2 辅助

```agda
z⊑ : ∀ k → hz ⊑∞ k
z⊑ hz = s∞
z⊑ (hs b) = u∞ (z⊑ b)
z⊑ (hl f) = l∞ 0 (z⊑ (f 0))
z⊑ (hΩ g) = L∞ azero (z⊑ (g azero))

atOutX : ∀ b {V k} (P : k ⊲[ V ] b) k′ {c c′} {lc : Lg c} {lc′ : Lg c′} {y : D k c} {y′ : D k′ c′} →
         RelAtX b P k′ lc lc′ y y′ → RelX k k′ lc lc′ y y′
atOutX b hself k′ h = h
atOutX (hs b) (hsuc P) k′ h = atOutX b P k′ h
atOutX (hl f) (hlim n P) k′ h = atOutX (f n) P k′ h
atOutX (hΩ g) (hLim e P) k′ h = atOutX (g _) P k′ h

sOutX : ∀ L {V k} (r : StH V k L) k′ {c c′} {lc : Lg c} {lc′ : Lg c′} {y : D k c} {y′ : D k′ c′} →
        RelSX L r k′ lc lc′ y y′ → RelX k k′ lc lc′ y y′
sOutX (hs b) (ss P) = atOutX b P
sOutX (hl f) (sl n P) = atOutX (f n) P
sOutX (hΩ g) (sL e P) = atOutX (g _) P

haw↾² : ∀ L L′ {W W′ W₁ W₁′} {lW : Lg W} {lW′ : Lg W′} {p : W ⊲ W₁} {lW₁ : Lg W₁} {p′ : W′ ⊲ W₁′} {lW₁′ : Lg W₁′}
          {A₀ : Ig L W} {A₀′ : Ig L′ W′} → AP lW lW′ p lW₁ p′ lW₁′ → HAW² L L′ lW lW′ A₀ A₀′ → HAW² L L′ lW₁ lW₁′ (Ig↾ p A₀) (Ig↾ p′ A₀′)
haw↾² L L′ {p = p} {p′ = p′} ap ha p₂ p₂′ l l′ cp = ha (⊲-tr p p₂) (⊲-tr p′ p₂′) l l′ (cp-tr ap cp)
```

## 3 异质的六条规则

```agda
module Six {L L′ : H} where
  sem-n0 : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {x′ : D L′ V′} → SemX² L L′ lV lV′ n0 x′
  sem-n0 lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r T T′ ta = n0ˣ

  sem-n1 : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} → SemX² L L′ lV lV′ n1 n1
  sem-n1 lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r = ha C.self C.self lW lW′ (cp-top hq) w w′ hw Y Y′ r

  sem-⨾ : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {x y : D L V} {x′ y′ : D L′ V′} →
          RelX L L′ lV lV′ x x′ → SemX² L L′ lV lV′ x x′ → SemX² L L′ lV lV′ y y′ → SemX² L L′ lV lV′ (x ⨾ y) (x′ ⨾ y′)
  sem-⨾ {x = x} {x′ = x′} hx sx sy lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r T T′ ta =
    ⨾ˣ (Ox T T′ ta)
       (sy lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha (w ⨾ nw q x) (w′ ⨾ nw q′ x′) (⨾ˣ hw (nwˣ (proj₁ hq) hx))
           _ _ (law⊕ (cp-top hq) Y Y′ Δ Δ′ r Ox) T T′ ta)
    where
    Δ = Run ac x q lW ll A₀ w Y
    Δ′ = Run ac′ x′ q′ lW′ ll′ A₀′ w′ Y′
    Ox = sx lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r

  sem-nw : ∀ {V₀ V₀′ V V′} {lV₀ : Lg V₀} {lV₀′ : Lg V₀′} {lV : Lg V} {lV′ : Lg V′} {p : V₀ ⊲ V} {p′ : V₀′ ⊲ V′}
             {x : D L V₀} {x′ : D L′ V₀′} →
           AP lV₀ lV₀′ p lV p′ lV′ → SemX² L L′ lV₀ lV₀′ x x′ → SemX² L L′ lV lV′ (nw p x) (nw p′ x′)
  sem-nw hp sx lW lW′ ac ac′ ll ll′ q q′ hq = sx lW lW′ ac ac′ ll ll′ (⊲-tr _ q) (⊲-tr _ q′) (cp-tr hp hq)

  sem-pr : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {x : D L V} {x′ y′ : D L′ V′} →
           SemX² L L′ lV lV′ x x′ → SemX² L L′ lV lV′ x (x′ ⨾ y′)
  sem-pr sx lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r T T′ ta =
    prˣ (sx lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r T T′ ta)

  module NL {V V′} {lV : Lg V} {lV′ : Lg V′} {d₁ : ℕ → D L V} {d₁′ : ℕ → D L′ V′}
            (hd : ∀ n → RelX L L′ lV lV′ (d₁ n) (d₁′ n)) (sd : ∀ n → SemX² L L′ lV lV′ (d₁ n) (d₁′ n))
            {W W′} (lW : Lg W) (lW′ : Lg W′) (ac : AccY L) (ac′ : AccY L′) (ll : LW L W) (ll′ : LW L′ W′)
            (q : V ⊲ W) (q′ : V′ ⊲ W′) (hq : CP lV lV′ q lW q′ lW′)
            (A₀ : Ig L W) (A₀′ : Ig L′ W′) (ha : HAW² L L′ lW lW′ A₀ A₀′)
            (w : D L W) (w′ : D L′ W′) (hw : RelX L L′ lW lW′ w w′) (Y : St W) (Y′ : St W′) (r : J² lW lW′ Y Y′) where
    Pn : ℕ → D L W × St W
    Pn = Rpt ac d₁ q lW ll A₀ w Y
    Pn′ : ℕ → D L′ W′ × St W′
    Pn′ = Rpt ac′ d₁′ q′ lW′ ll′ A₀′ w′ Y′

    St′ : ℕ → Set
    St′ n = RelX L L′ lW lW′ (proj₁ (Pn n)) (proj₁ (Pn′ n)) × J² lW lW′ (proj₂ (Pn n)) (proj₂ (Pn′ n))

    out : ∀ n → St′ n → OA² lW lW′ (Run ac (d₁ n) q lW ll A₀ (proj₁ (Pn n)) (proj₂ (Pn n)))
                                    (Run ac′ (d₁′ n) q′ lW′ ll′ A₀′ (proj₁ (Pn′ n)) (proj₂ (Pn′ n)))
    out n (h , s) = sd n lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha _ _ h _ _ s

    go : ∀ n → St′ n
    go zero = hw , r
    go (suc n) = ⨾ˣ (proj₁ (go n)) (nwˣ (proj₁ hq) (hd n)) ,
                 law⊕ (cp-top hq) (proj₂ (Pn n)) (proj₂ (Pn′ n)) _ _ (proj₂ (go n)) (out n (go n))

  sem-nl : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {d₁ : ℕ → D L V} {d₁′ : ℕ → D L′ V′} →
           (∀ n → RelX L L′ lV lV′ (d₁ n) (d₁′ n)) → (∀ n → SemX² L L′ lV lV′ (d₁ n) (d₁′ n)) → SemX² L L′ lV lV′ (nl d₁) (nl d₁′)
  sem-nl hd sd lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r T T′ ta =
    nlˣ (λ n → N.out n (N.go n) T T′ ta)
    where module N = NL hd sd lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r

open Six public
```

## 4 左层为 $0$: 只有六条规则

```agda
semX0 : ∀ {L′ V V′} {lV : Lg V} {lV′ : Lg V′} {x : D hz V} {x′ : D L′ V′} → RelX hz L′ lV lV′ x x′ → SemX² hz L′ lV lV′ x x′
semX0 n0ˣ = sem-n0
semX0 n1ˣ = sem-n1
semX0 (⨾ˣ hx hy) = sem-⨾ hx (semX0 hx) (semX0 hy)
semX0 (nlˣ hd) = sem-nl hd (λ n → semX0 (hd n))
semX0 (prˣ hx) = sem-pr (semX0 hx)
semX0 (nwˣ hp hx) = sem-nw hp (semX0 hx)
semX0 (niˣ {r = ()} _ _)
semX0 (κˣ {zz = ()} _)
```
