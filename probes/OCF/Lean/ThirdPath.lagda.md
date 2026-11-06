# Third (四): 下层的路径: 结点一份, 同底折叠保路径

> 不含记号. 入口 [Third](Third.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延. 对任一底 $U$, 世界 $w$, 洗法 `Sn`, 路径结构 `Q`.
>
> **与 `RecBPath` 的差.** RecB 的同底与跨底两条路径定理各写一遍结点的搬运 (`PH-pk`/`PH-nd` 与 `Cp.pk′`/`Cp.nd′`). 这里结点只有一份 `nodeG` (`ThirdFold`), 路径也只有一份 `PH-node`, 前提 `Ok` 按决定分三种. 留下的新种类多一步: 坐标先洗, 要 `ph-san`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdPS
import OCF.Lean.ThirdFold as TF
module OCF.Lean.ThirdPath (U : KS) (w : Wd U) (lw : LgW U w) (Sn : TF.San U w lw)
  {P : Po} (Q : PS P U) (O : Po.W P → Set) (o↑ : ∀ {a b} → Po._≤_ P a b → O a → O b) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Lean.ThirdIf
open import OCF.Lean.ThirdTw using (emb; frE; posE; along; frA)
open TF U w lw
open F Sn
open San Sn
open Po P

L = PSL Q
```

## §1 搬运 (同 `RecBPath.G`, 塔穿过 $\Omega$-结点)

```agda
ClP : ∀ m κ → Cg m κ → Set
ClP m κ (bas κ₀ to ad) =
  Σ (∀ {B} → PS.Ev (L m) B κ → PS.Ev Q B κ₀) (λ _ →
    ∀ {B} e (a : PS.Ad Q B κ₀ e) →
      Σ (PS.Ad (L m) B κ (to e)) (λ a′ → PS.nx (L m) B κ (to e) a′ ≤ PS.nx Q B κ₀ e a))
ClP m κ (nw j p to ad) =
  ∀ {B} c V → B ≤ V → PH (L j) V c →
    Σ (PS.Ad (L m) B κ (to c)) (λ a′ → PS.nx (L m) B κ (to c) a′ ≤ V)

pS : ∀ {x κ} (c : Cg x κ) → ClP x κ c → ClP (hs x) (inj₁ κ) (cgS c)
pS (bas κ₀ to ad) p = p
pS (nw j q to ad) p = p

pL : ∀ {f} n {κ} (c : Cg (f n) κ) → ClP (f n) κ c → ClP (hl f) (n , κ) (cgL n c)
pL n (bas κ₀ to ad) p = p
pL n (nw j q to ad) p = p

pO : ∀ {κ₀ g} e {κ} (b : Bd U κ₀ e w) (c : Cg (g e) κ) → ClP (g e) κ c → ClP (hΩ κ₀ g) (e , κ) (cgO e b c)
pO e b (bas κ₁ to ad) p = p
pO e b (nw j q to ad) p = p

clP : ∀ m κ (p : Pos U w m κ) → ClP m κ (cg m κ p)
clP hz κ _ = (λ ev → ev) , (λ e a → a , rf)
clP (hs x) (inj₁ κ) p = pS (cg x κ p) (clP x κ p)
clP (hs x) (inj₂ _) _ = λ c V le p → (V , le , p) , rf
clP (hl f) (n , κ) p = pL n (cg (f n) κ p) (clP (f n) κ p)
clP (hΩ κ₀ g) (e , κ) (b , p) = pO e b (cg (g e) κ p) (clP (g e) κ p)

evE : ∀ t {B} κ → PS.Ev Q B κ → PS.Ev (L t) B (emb t κ)
evE hz κ ev = ev
evE (hs x) κ ev = evE x κ ev
evE (hl f) κ ev = evE (f 0) κ ev
evE (hΩ κ₀ g) κ ev = evE (g (bot U κ₀)) κ ev

upkE : ∀ t {B} κ c (a : PS.Ad (L t) B (emb t κ) c) →
       Σ (PS.Ad Q B κ (frE t κ c)) (λ a₀ → PS.nx Q B κ (frE t κ c) a₀ ≤ PS.nx (L t) B (emb t κ) c a)
upkE hz κ c a = a , rf
upkE (hs x) κ c a = upkE x κ c a
upkE (hl f) κ c a = upkE (f 0) κ c a
upkE (hΩ κ₀ g) κ c a = upkE (g (bot U κ₀)) κ c a

evA : ∀ {i t} (q : hs i ⊲ᵘ t) {B} → PS.Ev (L t) B (along q)
evA hself = tt
evA (hsuc q) = evA q
evA (hlim n q) = evA q
evA (hLim _ q) = evA q

upkA : ∀ {i t} (q : hs i ⊲ᵘ t) {B} c (a : PS.Ad (L t) B (along q) c) →
       Σ W (λ V → (B ≤ V) × PH (L i) V (frA q c) × (V ≤ PS.nx (L t) B (along q) c a))
upkA hself c (V , le , p) = V , le , p , rf
upkA (hsuc q) c a = upkA q c a
upkA (hlim n q) c a = upkA q c a
upkA (hLim _ q) c a = upkA q c a
```

## §2 累加保路径

```agda
module _ {m : HB U} where
  LM = L m
  GTm = GT m

  PH-mulG : ∀ {V} (x : GTm) → PH LM V (proj₁ x) → ∀ n → PH LM V (proj₁ (mulG x n))
  PH-mulG x p zero = p
  PH-mulG x p (suc n) = PH-⊞ LM (proj₁ (mulG x n)) (proj₁ x) (PH-mulG x p n) p

  PH-ΣG : ∀ {V} (f : ℕ → GTm) → (∀ n → PH LM V (proj₁ (f n))) → ∀ n → PH LM V (proj₁ (ΣG f n))
  PH-ΣG f p zero = p 0
  PH-ΣG f p (suc n) = PH-⊞ LM (proj₁ (ΣG f n)) (proj₁ (f (suc n))) (PH-ΣG f p n) (p (suc n))

  PH-chainG : ∀ {V} (b : GTm) (k : GTm → GTm) → PH LM V (proj₁ b) →
              (∀ b′ → PH LM V (proj₁ b′) → PH LM V (proj₁ (k b′))) → ∀ n → PH LM V (proj₁ (chainG b k n))
  PH-chainG b k pb pk zero = pk b pb
  PH-chainG b k pb pk (suc n) =
    PH-⊞ LM (proj₁ (chainG b k n)) _ (PH-chainG b k pb pk n)
      (pk _ (PH-⊞ LM (proj₁ b) (proj₁ (chainG b k n)) pb (PH-chainG b k pb pk n)))
```

## §3 结点

`Ok V d`: 决定 $d$ 下, 输入分支 (`Pin`) 在需要的世界里带路径. 洗法与地板的前提写成模块参数 (实例在 `ThirdSan`).

```agda
module Node (ph-san : ∀ j {V} c → PH (L j) V c → PH (L j) V (san j c))
            (ph-tp : ∀ j V → O V → PH (L j) V (tp j)) where

  Ok : ∀ {X t} {A : Set} {R : A → Set} → (W → A → Set) → W → Dg X t A R → Set
  Ok {t = t} Pin V (keep κ′ p fr a) = PS.Ev (L t) V κ′ × (∀ c (x : PS.Ad (L t) V κ′ c) → Pin (PS.nx (L t) V κ′ c x) (fr c))
  Ok {t = t} Pin V (same to a) = ∀ c V′ → V ≤ V′ → PH (L t) V′ c → Pin V′ (to c)
  Ok Pin V (above i u q to a) = ∀ c V′ → V ≤ V′ → PH (L i) V′ c → Pin V′ (to c)

  PH-node : ∀ {X t} {A : Set} {R : A → Set} (Pin : W → A → Set) (d : Dg X t A R) (pt : t ⊲ᵘ X) (b : GT t) rec dn V → O V →
    PH (L t) V (proj₁ b) → Ok Pin V d →
    (∀ t′ pt′ b′ c pc V′ → O V′ → PH (L t′) V′ (proj₁ b′) → Pin V′ c → PH (L t′) V′ (proj₁ (rec t′ pt′ b′ c pc))) →
    (∀ i u q x V′ → O V′ → PH (L i) V′ (proj₁ x) → PH (L t) V′ (proj₁ b) → PH (L t) V′ (proj₁ (dn i u q x))) →
    PH (L t) V (proj₁ (nodeG d pt b rec dn))
  PH-node {t = t} Pin (keep κ′ p fr a) pt b rec dn V o pb (ev , k) hr hd =
    ev , λ c x → hr t pt b (fr c) (a c) _ (o↑ (PS.nx↑ (L t) {V} {κ′} {c} x) o) (PH-mono (L t) (PS.nx↑ (L t) {V} {κ′} {c} x) (proj₁ b) pb) (k c x)
  PH-node {t = t} Pin (same to a) pt b rec dn V o pb k hr hd =
    PH-chainG b _ pb (λ b′ pb′ → hr t pt b′ (to (proj₁ b′)) (a _ (proj₂ b′)) V o pb′ (k _ V rf pb′))
  PH-node Pin (above i u q to a) pt b rec dn V o pb k hr hd =
    hd i u q _ V o
      (PH-chainG (tp i , gd-tp i) _ (ph-tp i V o) (λ b′ pb′ → hr i (⊏⊑ u) b′ (to (proj₁ b′)) (a _ (proj₂ b′)) V o pb′ (k _ V rf pb′)))
      pb

  okP : ∀ {X t i} {A : Set} {R : A → Set} (Pin : W → A → Set) (Pin↑ : ∀ {a b e} → a ≤ b → Pin a e → Pin b e) V
        (to : HB (T i) → A) (ad : ∀ c → Gd i c → R (to c)) (u : hs i ⊲ᵘ X) →
        (∀ c V′ → V ≤ V′ → PH (L i) V′ c → Pin V′ (to c)) →
        (r : (t ⊲ᵘ hs i) ⊎ (hs i ⊲ᵘ t)) → Ok Pin V (pickG {X = X} {t = t} {A = A} {P = R} to ad u r)
  okP {i = i} Pin Pin↑ V to ad u k (inj₂ q) =
    evA q , λ c x →
      let r = upkA q c x ; V₀ = proj₁ r ; le = proj₁ (proj₂ r) ; pc = proj₁ (proj₂ (proj₂ r)) ; le′ = proj₂ (proj₂ (proj₂ r))
      in Pin↑ le′ (k (san i (frA q c)) V₀ le (ph-san i _ pc))
  okP {i = i} Pin Pin↑ V to ad u k (inj₁ hself) =
    tt , λ c x → k (san i c) (proj₁ x) (proj₁ (proj₂ x)) (ph-san i c (proj₂ (proj₂ x)))
  okP Pin Pin↑ V to ad u k (inj₁ (hsuc hself)) = k
  okP Pin Pin↑ V to ad u k (inj₁ (hsuc (hsuc _))) = k
  okP Pin Pin↑ V to ad u k (inj₁ (hsuc (hlim _ _))) = k
  okP Pin Pin↑ V to ad u k (inj₁ (hsuc (hLim _ _))) = k

  okB : ∀ {X t} {A : Set} {R : A → Set} (Pin : W → A → Set) (Pin↑ : ∀ {a b e} → a ≤ b → Pin a e → Pin b e) V κ₀
        (to : E U κ₀ → A) (ad : ∀ c → R (to c)) → PS.Ev Q V κ₀ →
        (∀ e (a : PS.Ad Q V κ₀ e) → Pin (PS.nx Q V κ₀ e a) (to e)) →
        Ok Pin V (keep {X = X} {t = t} {P = R} (emb t κ₀) (posE t κ₀) (λ c → to (frE t κ₀ c)) (λ c → ad (frE t κ₀ c)))
  okB {t = t} Pin Pin↑ V κ₀ to ad ev k =
    evE t κ₀ ev , λ c x → Pin↑ (proj₂ (upkE t κ₀ c x)) (k (frE t κ₀ c) (proj₁ (upkE t κ₀ c x)))
```

## §4 同底折叠保路径 (对一切 `Q`)

```agda
  module _ where
    Pm : ∀ {m κ} (g : E (T m) κ → HB (T m)) → W → E (T m) κ → Set
    Pm {m} g V c = PH (L m) V (g c)

    okD : ∀ m t κ (g : E (T m) κ → HB (T m)) (pt : t ⊲ᵘ m) (lm : LgB m) V (c : Cg m κ) → ClP m κ c →
          PS.Ev (L m) V κ → (∀ e (a : PS.Ad (L m) V κ e) → PH (L m) (PS.nx (L m) V κ e a) (g e)) →
          Ok (Pm {m} {κ} g) V (dcg pt lm c)
    okD m t κ g pt lm V (bas κ₀ to ad) (evd , pk) ev pg =
      okB {X = m} {t = t} {R = AdT m κ} (Pm {m} {κ} g) (λ le p → PH-mono (L m) le _ p) V κ₀ to ad (evd ev) (λ e a →
        PH-mono (L m) (proj₂ (pk e a)) _ (pg (to e) (proj₁ (pk e a))))
    okD m t κ g pt lm V (nw j pj to ad) pk ev pg =
      okP {X = m} {t = t} {R = AdT m κ} (Pm {m} {κ} g) (λ le p → PH-mono (L m) le _ p) V to ad pj
        (λ c V′ le p → PH-mono (L m) (proj₂ (pk c V′ le p)) _ (pg (to c) (proj₁ (pk c V′ le p))))
        (cmpB {U} pj pt lw lm)

    PH-Φ : ∀ m a lm t pt b h nd V → O V → PH (L t) V (proj₁ b) → PH (L m) V h →
           PH (L t) V (proj₁ (Φ m a lm t pt b h nd))
    PH-Φ m a lm t pt b hz nd V o pb ph = tt
    PH-Φ m a lm t pt b (hs h) nd V o pb ph = PH-mulG (Φ m a lm t pt b h nd) (PH-Φ m a lm t pt b h nd V o pb ph)
    PH-Φ m a lm t pt b (hl f) nd V o pb ph = PH-ΣG (λ n → Φ m a lm t pt b (f n) (nd n)) (λ n → PH-Φ m a lm t pt b (f n) (nd n) V o pb (ph n))
    PH-Φ m (acc rs) lm t pt b (hΩ κ g) (ev , pgd) V o pb (evL , pg) =
      PH-node {R = AdT m κ} (Pm {m} {κ} g) (dcg pt lm (cg m κ ev)) pt b _ _ V o pb
        (okD m t κ g pt lm V (cg m κ ev) (clP m κ ev) evL pg)
        (λ t′ pt′ b′ c pc V′ oV pb′ pin → PH-Φ m (acc rs) lm t′ pt′ b′ (g c) (pgd c pc) V′ oV pb′ pin)
        (λ i u q x V′ oV px pb′ → PH-Φ i (rs i u) (lg↓ u lm) t q b (proj₁ x) (proj₂ x) V′ oV pb′ px)
```
