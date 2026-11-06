# RecB (二): 路径对一切底; 同底折叠保路径; 跨底折叠把上抬的路径带下来

> 不含记号. 入口 [RecB](RecB.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延. 对任一满足接口的 `J`. 从 [CRwPath](CRwPath.lagda.md) 导入 `psStep`, `psSup`, `PH-mono`, `PH-⊞`, `PH-mul`, `PH-Σ`, `PH-chain`, `PH-up`, `PH-ι` (对一切路径结构, 不改原文件).
>
> **世界塔.** 第 $k$ 个底的路径结构 `PSX (k-1)` (世界 $B_k$ 界住第 $k$ 个底的分量序号) 在更高的底里**上抬** (`lift`): 第 $c$ 个分量里沿用 (`PSL Q (hs c)`: 底种类照旧, 塔的新种类 Kripke 式可入), 指标分量里平凡 (`triv`: 上层的指标种类不移动下层的世界). 一棵第 $n$ 个底的高度带一座塔的路径 (第 $n$ 层的自己的结构, 与第 $k<n$ 层上抬 $n-k$ 次的结构), 每层一个世界.
>
> **两条定理, 对一切结构 `Q`.**
>
> - `PH-ΦS` (同 CRw 的 `PH-ΦX`, 推广到一切底与一切 `Q`): 同底折叠保 `PSL Q`.
> - `PH-ΦX↓` (新): 跨底折叠 `ΦX (suc n)` 把输入的 `lift Q` 路径带成输出的 `PSL Q t` 路径. 跨底折叠回灌只发生在指标种类, 而 `lift Q` 在指标种类上平凡, 所以下层的世界不随上层的回灌移动 (`RecBIf` 文件头说的 "冻结"; 这里冻结的是上层的指标种类, 下层自己的 $\Omega_1$ 照常移动).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Lean.RecBIf
module OCF.Lean.RecBPath (J : RecBIf) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Lean.CRwBase
open RecBIf J
open import OCF.Lean.CRwFold mv
  using (Tw; Cl; bas; nw; cS; cL; cl; emb; frE; along; frA; Dc; keep; same; above; caseDc; pick; dcl;
         PS; module PS; PH; mul; chain; Σ⁺; lg↓; ⊏⊑; topT; ΣT)
open import OCF.Lean.CRwPath mv using (psStep; psSup; PH-mono; PH-⊞; PH-mul; PH-Σ; PH-chain; PH-up; PH-ι)
open import OCF.Lean.RecBFold J
```

## §1 塔上的路径结构, 上抬

```agda
module _ {S : KS} (Q : PS S) where
  PSL : ∀ m → PS (Tw S m)
  PSL hz = Q
  PSL (hs x) = psStep (PSL x)
  PSL (hl f) = psSup (λ n → PSL (f n))
  PSL (hΩ () _)

triv : ∀ {T} → PS T
triv = record { Ev = λ _ _ → ⊤ ; Ad = λ _ _ _ → ⊤ ; nx = λ B _ _ _ → B
              ; ev↑ = λ _ _ → tt ; ad↓ = λ q _ → tt , q ; nx↑ = λ _ → hself }

FQ : ∀ {S} → PS S → (i : Ix) → PS (FX S i)
FQ Q ix = triv
FQ Q (cp c) = PSL Q (hs c)

lift : ∀ {S} → PS S → PS (XSof S)
lift {S} Q = psSup {Ix} {FX S} (FQ Q)
```

## §2 搬运 (对一切 `Q`)

同 CRwPath §4, 把 `PSX` 换成任一 `Q`.

```agda
module G {S : KS} (Q : PS S) where
  L = PSL Q

  ClP : ∀ m κ → Cl {S} m κ → Set
  ClP m κ (bas κ₀ to) =
    Σ (∀ {B} → PS.Ev (L m) B κ → PS.Ev Q B κ₀) (λ _ →
      ∀ {B} e (a : PS.Ad Q B κ₀ e) →
        Σ (PS.Ad (L m) B κ (to e)) (λ a′ → PS.nx (L m) B κ (to e) a′ ⊲ PS.nx Q B κ₀ e a))
  ClP m κ (nw j p to) =
    ∀ {B} c V → B ⊲ V → PH (L j) V c →
      Σ (PS.Ad (L m) B κ (to c)) (λ a′ → PS.nx (L m) B κ (to c) a′ ⊲ V)

  pS : ∀ {x κ} (c : Cl {S} x κ) → ClP x κ c → ClP (hs x) (inj₁ κ) (cS c)
  pS (bas κ₀ to) p = p
  pS (nw j q to) p = p

  pL : ∀ {f} n {κ} (c : Cl {S} (f n) κ) → ClP (f n) κ c → ClP (hl f) (n , κ) (cL n c)
  pL n (bas κ₀ to) p = p
  pL n (nw j q to) p = p

  clP : ∀ m κ → ClP m κ (cl m κ)
  clP hz κ = (λ ev → ev) , (λ e a → a , hself)
  clP (hs x) (inj₁ κ) = pS (cl x κ) (clP x κ)
  clP (hs x) (inj₂ _) = λ c V w p → (V , w , p) , hself
  clP (hl f) (n , κ) = pL n (cl (f n) κ) (clP (f n) κ)
  clP (hΩ () _) _

  evE : ∀ t {B} κ → PS.Ev Q B κ → PS.Ev (L t) B (emb t κ)
  evE hz κ ev = ev
  evE (hs x) κ ev = evE x κ ev
  evE (hl f) κ ev = evE (f 0) κ ev
  evE (hΩ () _) κ ev

  upkE : ∀ t {B} κ c (a : PS.Ad (L t) B (emb t κ) c) →
         Σ (PS.Ad Q B κ (frE t κ c)) (λ a₀ → PS.nx Q B κ (frE t κ c) a₀ ⊲ PS.nx (L t) B (emb t κ) c a)
  upkE hz κ c a = a , hself
  upkE (hs x) κ c a = upkE x κ c a
  upkE (hl f) κ c a = upkE (f 0) κ c a
  upkE (hΩ () _) κ c a

  evA : ∀ {i t} (q : hs i ⊲ t) {B} → PS.Ev (L t) B (along q)
  evA hself = tt
  evA (hsuc q) = evA q
  evA (hlim n q) = evA q
  evA (hLim {κ = ()} _ _)

  upkA : ∀ {i t} (q : hs i ⊲ t) {B} c (a : PS.Ad (L t) B (along q) c) →
         Σ Cd (λ V → (B ⊲ V) × PH (L i) V (frA q c) × (V ⊲ PS.nx (L t) B (along q) c a))
  upkA hself c (V , w , p) = V , w , p , hself
  upkA (hsuc q) c a = upkA q c a
  upkA (hlim n q) c a = upkA q c a
  upkA (hLim {κ = ()} _ _) c a
```

**塔的地板带路径** (以底的地板带路径为前提).

```agda
  module Top (fb : HB S) (ptl : ∀ B → hs hz ⊲ B → PH Q B fb) where
    PH-top : ∀ m B → hs hz ⊲ B → PH (L m) B (topT S fb m)
    PH-ΣT : ∀ f B → hs hz ⊲ B → ∀ n → PH (L (hl f)) B (ΣT S fb f n)
    PH-top hz B o = ptl B o
    PH-top (hs x) B o = tt , λ c a → PH-up (L x) c (proj₂ (proj₂ a))
    PH-top (hl f) B o = PH-ΣT f B o
    PH-top (hΩ () _) B o
    PH-ΣT f B o zero = PH-ι (λ n → L (f n)) 0 _ (PH-top (f 0) B o)
    PH-ΣT f B o (suc n) = PH-⊞ (L (hl f)) (ΣT S fb f n) _ (PH-ΣT f B o n)
      (PH-ι (λ k → L (f k)) (suc n) _ (PH-top (f (suc n)) B o))
```

## §3 定理: 同底折叠保路径 (对一切底, 一切 `Q`)

```agda
    IH₁ : ∀ m → (∀ i → hs i ⊲ m → AccC i) → LgB m → (κ : K (Tw S m)) → (E (Tw S m) κ → HB (Tw S m)) → Set
    IH₁ m rs lm κ g = ∀ t′ (pt′ : t′ ⊲ m) b′ e V → hs hz ⊲ V → PH (L t′) V b′ → PH (L m) V (g e) →
                      PH (L t′) V (ΦS S fb m (acc rs) lm t′ pt′ b′ (g e))

    IH₂ : ∀ m → (∀ i → hs i ⊲ m → AccC i) → LgB m → ∀ t → HB (Tw S t) → Set
    IH₂ m rs lm t b = ∀ i (pi : hs i ⊲ m) (q : t ⊲ i) x V → hs hz ⊲ V → PH (L t) V b → PH (L i) V x →
                      PH (L t) V (ΦS S fb i (rs i pi) (lg↓ pi lm) t q b x)

    module Nk (m : Cd) (rs : ∀ i → hs i ⊲ m → AccC i) (lm : LgB m) (t : Cd) (pt : t ⊲ m)
              (b : HB (Tw S t)) (κ : K (Tw S m)) (g : E (Tw S m) κ → HB (Tw S m)) where
      Kc : (κ′ : K (Tw S t)) → (E (Tw S t) κ′ → E (Tw S m) κ) → HB (Tw S t)
      Kc κ′ fr = hΩ κ′ (λ c → ΦS S fb m (acc rs) lm t pt b (g (fr c)))
      Sc : (HB (Tw S t) → E (Tw S m) κ) → HB (Tw S t)
      Sc to = hl (chain b (λ b′ → ΦS S fb m (acc rs) lm t pt b′ (g (to b′))))
      Ac : (i : Cd) → hs i ⊲ m → t ⊲ i → (HB (Tw S i) → E (Tw S m) κ) → HB (Tw S t)
      Ac i pi q to = ΦS S fb i (rs i pi) (lg↓ pi lm) t q b
        (hl (chain (topT S fb i) (λ b′ → ΦS S fb m (acc rs) lm i (⊏⊑ pi) b′ (g (to b′)))))

    PH-ch : ∀ m rs lm κ (g : E (Tw S m) κ → HB (Tw S m)) {B} → hs hz ⊲ B → ∀ j pj (to : HB (Tw S j) → E (Tw S m) κ) →
            ClP m κ (nw j pj to) → PH (L m) B (hΩ κ g) → IH₁ m rs lm κ g →
            ∀ (pj′ : j ⊲ m) b₀ → PH (L j) B b₀ →
            PH (L j) B (hl (chain b₀ (λ b′ → ΦS S fb m (acc rs) lm j pj′ b′ (g (to b′)))))
    PH-ch m rs lm κ g {B} o j pj to pk (ev , pg) ih pj′ b₀ p₀ =
      PH-chain (L j) b₀ _ p₀ (λ b′ pb′ →
        let a′ = proj₁ (pk b′ B hself pb′) ; w = PS.nx↑ (L m) {B} {κ} {to b′} a′ in
        PH-mono (L j) (proj₂ (pk b′ B hself pb′)) _
          (ih j pj′ b′ (to b′) _ (⊲ᴮ-tr o w) (PH-mono (L j) w b′ pb′) (pg (to b′) a′)))

    PH-pk : ∀ m rs lm t pt b κ (g : E (Tw S m) κ → HB (Tw S m)) B → hs hz ⊲ B → ∀ j pj (to : HB (Tw S j) → E (Tw S m) κ) →
            ClP m κ (nw j pj to) → PH (L t) B b → PH (L m) B (hΩ κ g) → IH₁ m rs lm κ g → IH₂ m rs lm t b →
            (r : (t ⊲ hs j) ⊎ (hs j ⊲ t)) →
            PH (L t) B (caseDc (pick S to pj r) (Nk.Kc m rs lm t pt b κ g) (Nk.Sc m rs lm t pt b κ g) (Nk.Ac m rs lm t pt b κ g))
    PH-pk m rs lm t pt b κ g B o j pj to pk pb (ev , pg) ih₁ ih₂ (inj₂ q) =
      evA q , λ c a →
        let u = upkA q c a
            V = proj₁ u ; w = proj₁ (proj₂ u) ; pc = proj₁ (proj₂ (proj₂ u)) ; w′ = proj₂ (proj₂ (proj₂ u))
            a′ = proj₁ (pk (frA q c) V w pc) ; v = PS.nx↑ (L m) {B} {κ} {to (frA q c)} a′
        in PH-mono (L t) (⊲ᴮ-tr (proj₂ (pk (frA q c) V w pc)) w′) _
             (ih₁ t pt b (to (frA q c)) _ (⊲ᴮ-tr o v) (PH-mono (L t) v b pb) (pg _ a′))
    PH-pk m rs lm t pt b κ g B o j pj to pk pb (ev , pg) ih₁ ih₂ (inj₁ hself) =
      tt , λ c a →
        let a′ = proj₁ (pk c (proj₁ a) (proj₁ (proj₂ a)) (proj₂ (proj₂ a))) ; v = PS.nx↑ (L m) {B} {κ} {to c} a′
        in PH-mono (L t) (proj₂ (pk c (proj₁ a) (proj₁ (proj₂ a)) (proj₂ (proj₂ a)))) _
             (ih₁ t pt b (to c) _ (⊲ᴮ-tr o v) (PH-mono (L t) v b pb) (pg _ a′))
    PH-pk m rs lm t pt b κ g B o j pj to pk pb ph ih₁ ih₂ (inj₁ (hsuc hself)) =
      PH-ch m rs lm κ g o j pj to pk ph ih₁ pt b pb
    PH-pk m rs lm t pt b κ g B o j pj to pk pb ph ih₁ ih₂ (inj₁ (hsuc (hsuc q))) =
      ih₂ j pj (hsuc q) (hl (chain (topT S fb j) (λ b′ → ΦS S fb m (acc rs) lm j (⊏⊑ pj) b′ (g (to b′))))) B o pb (PH-ch m rs lm κ g o j pj to pk ph ih₁ (⊏⊑ pj) (topT S fb j) (PH-top j B o))
    PH-pk m rs lm t pt b κ g B o j pj to pk pb ph ih₁ ih₂ (inj₁ (hsuc (hlim n q))) =
      ih₂ j pj (hlim n q) (hl (chain (topT S fb j) (λ b′ → ΦS S fb m (acc rs) lm j (⊏⊑ pj) b′ (g (to b′))))) B o pb (PH-ch m rs lm κ g o j pj to pk ph ih₁ (⊏⊑ pj) (topT S fb j) (PH-top j B o))
    PH-pk m rs lm t pt b κ g B o j pj to pk pb ph ih₁ ih₂ (inj₁ (hsuc (hLim {κ = ()} _ _)))

    PH-nd : ∀ m rs lm t pt b κ (g : E (Tw S m) κ → HB (Tw S m)) B → hs hz ⊲ B → (c : Cl {S} m κ) → ClP m κ c →
            PH (L t) B b → PH (L m) B (hΩ κ g) → IH₁ m rs lm κ g → IH₂ m rs lm t b →
            PH (L t) B (caseDc (dcl pt lm c) (Nk.Kc m rs lm t pt b κ g) (Nk.Sc m rs lm t pt b κ g) (Nk.Ac m rs lm t pt b κ g))
    PH-nd m rs lm t pt b κ g B o (bas κ₀ to) (evd , pk) pb (ev , pg) ih₁ ih₂ =
      evE t κ₀ (evd ev) , λ c a →
        let u = upkE t κ₀ c a
            a′ = proj₁ (pk (frE t κ₀ c) (proj₁ u)) ; v = PS.nx↑ (L m) {B} {κ} {to (frE t κ₀ c)} a′
        in PH-mono (L t) (⊲ᴮ-tr (proj₂ (pk (frE t κ₀ c) (proj₁ u))) (proj₂ u)) _
             (ih₁ t pt b (to (frE t κ₀ c)) _ (⊲ᴮ-tr o v) (PH-mono (L t) v b pb) (pg _ a′))
    PH-nd m rs lm t pt b κ g B o (nw j pj to) pk pb ph ih₁ ih₂ =
      PH-pk m rs lm t pt b κ g B o j pj to pk pb ph ih₁ ih₂ (cmpB pj pt tt lm)

    PH-ΦS : ∀ m a lm t pt b h B → hs hz ⊲ B → PH (L t) B b → PH (L m) B h →
            PH (L t) B (ΦS S fb m a lm t pt b h)
    PH-ΦS m (acc rs) lm t pt b hz B o pb ph = tt
    PH-ΦS m (acc rs) lm t pt b (hs h) B o pb ph = PH-mul (L t) _ (PH-ΦS m (acc rs) lm t pt b h B o pb ph)
    PH-ΦS m (acc rs) lm t pt b (hl f) B o pb ph = PH-Σ (L t) _ (λ n → PH-ΦS m (acc rs) lm t pt b (f n) B o pb (ph n))
    PH-ΦS m (acc rs) lm t pt b (hΩ κ g) B o pb ph =
      PH-nd m rs lm t pt b κ g B o (cl m κ) (clP m κ) pb ph
        (λ t′ pt′ b′ e V oV pb′ pe → PH-ΦS m (acc rs) lm t′ pt′ b′ (g e) V oV pb′ pe)
        (λ i pi q x V oV pbx px → PH-ΦS i (rs i pi) (lg↓ pi lm) t q b x V oV pbx px)
```

## §4 定理: 跨底折叠把上抬的路径带下来

`Q` 是第 $n+1$ 个底上的任一路径结构, 前提: 指标种类在 $1$ 之上的世界里有证据 (`evI`), 地板带路径 (`ptl`). 输入在世界 $W$ 里带 `lift Q` 路径, 输出在同一个 $W$ 里带 `PSL Q t` 路径. 跨底折叠自己的世界 $B$ 怎么移动与 $W$ 无关.

```agda
module Down (n : ℕ) (Q : PS (Sb (suc n))) (evI : ∀ W → hs hz ⊲ W → PS.Ev Q W ιK)
            (ptl : ∀ B → hs hz ⊲ B → PH Q B (fl (suc n))) where
  open G Q
  open Top (fl (suc n)) ptl
  S₁ = Sb (suc n)
  LQ = lift Q

  module Cp (c : Cd) (κ : K (Tw S₁ (hs c))) (g : E (Tw S₁ (hs c)) κ → HB (Sb (suc (suc n))))
            (B : Cd) (lB : LgB B) (ev : hs c ⊲ B) (pg : ∀ e → ⊤ → PH (PSX (suc n)) B (g e))
            (W : Cd) (o : hs hz ⊲ W)
            (pgL : ∀ e (a : PS.Ad (L (hs c)) W κ e) → PH LQ (PS.nx (L (hs c)) W κ e a) (g e))
            (ih : ∀ t′ (pt′ : t′ ⊲ B) b′ e V → hs hz ⊲ V → PH (L t′) V b′ → PH LQ V (g e) →
                  PH (L t′) V (ΦX (suc n) t′ B lB pt′ b′ (g e) (pg e tt))) where
    ch : ∀ j pj (to : HB (Tw S₁ j) → E (Tw S₁ (hs c)) κ) → ClP (hs c) κ (nw j pj to) →
         ∀ (pj′ : j ⊲ B) b₀ → PH (L j) W b₀ →
         PH (L j) W (hl (chain b₀ (λ b′ → ΦX (suc n) j B lB pj′ b′ (g (to b′)) (pg _ tt))))
    ch j pj to pk pj′ b₀ p₀ =
      PH-chain (L j) b₀ _ p₀ (λ b′ pb′ →
        let a′ = proj₁ (pk b′ W hself pb′) ; w = PS.nx↑ (L (hs c)) {W} {κ} {to b′} a′ in
        PH-mono (L j) (proj₂ (pk b′ W hself pb′)) _
          (ih j pj′ b′ (to b′) _ (⊲ᴮ-tr o w) (PH-mono (L j) w b′ pb′) (pgL (to b′) a′)))

    Kc : ∀ t → t ⊲ B → HB (Tw S₁ t) → (κ′ : K (Tw S₁ t)) → (E (Tw S₁ t) κ′ → E (Tw S₁ (hs c)) κ) → HB (Tw S₁ t)
    Kc t pt b κ′ fr = hΩ κ′ (λ c′ → ΦX (suc n) t B lB pt b (g (fr c′)) (pg _ tt))
    Sc : ∀ t → t ⊲ B → HB (Tw S₁ t) → (HB (Tw S₁ t) → E (Tw S₁ (hs c)) κ) → HB (Tw S₁ t)
    Sc t pt b to = hl (chain b (λ b′ → ΦX (suc n) t B lB pt b′ (g (to b′)) (pg _ tt)))
    Ac : ∀ t → HB (Tw S₁ t) → (i : Cd) → hs i ⊲ B → t ⊲ i → (HB (Tw S₁ i) → E (Tw S₁ (hs c)) κ) → HB (Tw S₁ t)
    Ac t b i pi q to = ΦS S₁ (fl (suc n)) i (wfC i) (lg↓ pi lB) t q b
      (hl (chain (top (suc n) i) (λ b′ → ΦX (suc n) i B lB (⊏⊑ pi) b′ (g (to b′)) (pg _ tt))))

    pk′ : ∀ t (pt : t ⊲ B) b → PH (L t) W b → ∀ j (pj : hs j ⊲ hs c) (u : hs j ⊲ B) (to : HB (Tw S₁ j) → E (Tw S₁ (hs c)) κ) →
          ClP (hs c) κ (nw j pj to) → (r : (t ⊲ hs j) ⊎ (hs j ⊲ t)) →
          PH (L t) W (caseDc (pick S₁ to u r) (Kc t pt b) (Sc t pt b) (Ac t b))
    pk′ t pt b pb j pj u to pk (inj₂ q) =
      evA q , λ c′ a →
        let r = upkA q c′ a
            V = proj₁ r ; w = proj₁ (proj₂ r) ; pc = proj₁ (proj₂ (proj₂ r)) ; w′ = proj₂ (proj₂ (proj₂ r))
            a′ = proj₁ (pk (frA q c′) V w pc) ; v = PS.nx↑ (L (hs c)) {W} {κ} {to (frA q c′)} a′
        in PH-mono (L t) (⊲ᴮ-tr (proj₂ (pk (frA q c′) V w pc)) w′) _
             (ih t pt b (to (frA q c′)) _ (⊲ᴮ-tr o v) (PH-mono (L t) v b pb) (pgL _ a′))
    pk′ t pt b pb j pj u to pk (inj₁ hself) =
      tt , λ c′ a →
        let a′ = proj₁ (pk c′ (proj₁ a) (proj₁ (proj₂ a)) (proj₂ (proj₂ a))) ; v = PS.nx↑ (L (hs c)) {W} {κ} {to c′} a′
        in PH-mono (L t) (proj₂ (pk c′ (proj₁ a) (proj₁ (proj₂ a)) (proj₂ (proj₂ a)))) _
             (ih t pt b (to c′) _ (⊲ᴮ-tr o v) (PH-mono (L t) v b pb) (pgL _ a′))
    pk′ t pt b pb j pj u to pk (inj₁ (hsuc hself)) = ch j pj to pk pt b pb
    pk′ t pt b pb j pj u to pk (inj₁ (hsuc (hsuc q))) =
      PH-ΦS j (wfC j) (lg↓ u lB) t (hsuc q) b (hl (chain (top (suc n) j) (λ b′ → ΦX (suc n) j B lB (⊏⊑ u) b′ (g (to b′)) (pg _ tt)))) W o pb (ch j pj to pk (⊏⊑ u) (top (suc n) j) (PH-top j W o))
    pk′ t pt b pb j pj u to pk (inj₁ (hsuc (hlim k q))) =
      PH-ΦS j (wfC j) (lg↓ u lB) t (hlim k q) b (hl (chain (top (suc n) j) (λ b′ → ΦX (suc n) j B lB (⊏⊑ u) b′ (g (to b′)) (pg _ tt)))) W o pb (ch j pj to pk (⊏⊑ u) (top (suc n) j) (PH-top j W o))
    pk′ t pt b pb j pj u to pk (inj₁ (hsuc (hLim {κ = ()} _ _)))

    nd′ : ∀ t (pt : t ⊲ B) b → PH (L t) W b → PS.Ev (L (hs c)) W κ → (cc : Cl {S₁} (hs c) κ) → ClP (hs c) κ cc →
          PH (L t) W (caseDc (dcx lB pt ev cc) (Kc t pt b) (Sc t pt b) (Ac t b))
    nd′ t pt b pb evL (bas κ₀ to) (evd , pk) =
      evE t κ₀ (evd evL) , λ c′ a →
        let u = upkE t κ₀ c′ a
            a′ = proj₁ (pk (frE t κ₀ c′) (proj₁ u)) ; v = PS.nx↑ (L (hs c)) {W} {κ} {to (frE t κ₀ c′)} a′
        in PH-mono (L t) (⊲ᴮ-tr (proj₂ (pk (frE t κ₀ c′) (proj₁ u))) (proj₂ u)) _
             (ih t pt b (to (frE t κ₀ c′)) _ (⊲ᴮ-tr o v) (PH-mono (L t) v b pb) (pgL _ a′))
    nd′ t pt b pb evL (nw j pj to) pk =
      pk′ t pt b pb j pj (⊲ᴮ-tr pj ev) to pk (cmpB (⊲ᴮ-tr pj ev) pt tt lB)

  PH-ΦX↓ : ∀ t B lB pt b h nd W → hs hz ⊲ W → PH (L t) W b → PH LQ W h →
           PH (L t) W (ΦX (suc n) t B lB pt b h nd)
  PH-ΦX↓ t B lB pt b hz nd W o pb ph = tt
  PH-ΦX↓ t B lB pt b (hs h) nd W o pb ph = PH-mul (L t) _ (PH-ΦX↓ t B lB pt b h nd W o pb ph)
  PH-ΦX↓ t B lB pt b (hl f) nd W o pb ph = PH-Σ (L t) _ (λ k → PH-ΦX↓ t B lB pt b (f k) (nd k) W o pb (ph k))
  PH-ΦX↓ t B lB pt b (hΩ (ix , inj₁ ()) g) nd W o pb ph
  PH-ΦX↓ t B lB pt b (hΩ (ix , inj₂ _) g) (oB , pg) W o pb (_ , pgL) =
    evE t ιK (evI W o) , λ c′ a →
      let u = upkE t ιK c′ a ; v = PS.nx↑ Q {W} {ιK} {frE t ιK c′} (proj₁ u) in
      PH-mono (L t) (⊲ᴮ-tr v (proj₂ u)) _ (PH-ΦX↓ t _ _ _ b _ _ W o pb (pgL _ tt))
  PH-ΦX↓ t B lB pt b (hΩ (cp c , κ) g) (ev , pg) W o pb (evL , pgL) =
    Cp.nd′ c κ g B lB ev pg W o pgL
      (λ t′ pt′ b′ e V oV pb′ pe → PH-ΦX↓ t′ B lB pt′ b′ (g e) (pg e tt) V oV pb′ pe)
      t pt b pb evL (cl (hs c) κ) (clP (hs c) κ)
```
