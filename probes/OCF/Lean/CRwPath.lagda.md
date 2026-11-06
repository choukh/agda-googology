# CRw (三): 叠层的路径, 同底折叠保路径

> 不含记号. 入口 [CRw](CRw.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延. 对任一满足接口的 `I`.
>
> **重写.** 参考 `X1UpFold` §5–§9 (只作参考). 这一篇只为闭项服务: 闭项先把 $\Omega_1\oplus m$ 层的地板经同底折叠 (`sm`) 折到 $\Omega_1$ 层, 再经跨底折叠 (`cx`) 折到第 0 层; 后者要输入带路径 (`Nd`), 这里证同底折叠的输出带路径 (`PH-ΦX`, 对一切世界, 对一切 $m$, 目标, 界).
>
> - 叠层的路径结构 `PSL m` 逐层搭出: 旧种类原样; 叠层的新种类无证据, 可入是 Kripke 式 (有更大的世界 $V$, 坐标在 $V$ 里带路径; 进入后的世界就是 $V$). 理由同 X1Up `naive-anti`: 朴素的 "坐标在 $B$ 里带路径" 不随世界变小.
> - 与 X1Up 的差: 世界的移动不依赖证据 (`nx` 不取 `Ev`), 叠层的底就是 `XS` (不经 `PathOutIf`), 种类分类与嵌入是塔对一切底的那一份 (`CRwFold` §2).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Lean.CRwIf
module OCF.Lean.CRwPath (I : CRwIf) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRwFold I
```

## §1 叠层的路径结构

```agda
psStep : ∀ {T} → PS T → PS (step T)
psStep {T} Q = record { Ev = Ev⁺ ; Ad = Ad⁺ ; nx = nx⁺ ; ev↑ = ev↑⁺ ; ad↓ = ad↓⁺ ; nx↑ = nx↑⁺ }
  where
  open PS Q
  Ev⁺ : Cd → K (step T) → Set
  Ev⁺ B (inj₁ κ) = Ev B κ
  Ev⁺ B (inj₂ _) = ⊤
  Ad⁺ : Cd → (κ : K (step T)) → E (step T) κ → Set
  Ad⁺ B (inj₁ κ) e = Ad B κ e
  Ad⁺ B (inj₂ _) c = Σ Cd (λ V → B ⊲ V × PH Q V c)
  nx⁺ : (B : Cd) (κ : K (step T)) (e : E (step T) κ) → Ad⁺ B κ e → Cd
  nx⁺ B (inj₁ κ) e a = nx B κ e a
  nx⁺ B (inj₂ _) c a = proj₁ a
  ev↑⁺ : ∀ {B B′} → B ⊲ B′ → ∀ {κ} → Ev⁺ B κ → Ev⁺ B′ κ
  ev↑⁺ q {inj₁ κ} ev = ev↑ q ev
  ev↑⁺ q {inj₂ _} ev = tt
  ad↓⁺ : ∀ {B B′} → B ⊲ B′ → ∀ {κ e} (a′ : Ad⁺ B′ κ e) → Σ (Ad⁺ B κ e) (λ a → nx⁺ B κ e a ⊲ nx⁺ B′ κ e a′)
  ad↓⁺ q {inj₁ κ} {e} a′ = ad↓ q {κ} {e} a′
  ad↓⁺ q {inj₂ _} (V , w , p) = (V , ⊲ᴮ-tr q w , p) , hself
  nx↑⁺ : ∀ {B κ e} (a : Ad⁺ B κ e) → B ⊲ nx⁺ B κ e a
  nx↑⁺ {κ = inj₁ κ} {e} a = nx↑ {κ = κ} {e} a
  nx↑⁺ {κ = inj₂ _} (V , w , p) = w

psSup : ∀ {J : Set} {G : J → KS} → ((i : J) → PS (G i)) → PS (sup J G)
psSup Q = record
  { Ev = λ B κ → PS.Ev (Q (proj₁ κ)) B (proj₂ κ)
  ; Ad = λ B κ → PS.Ad (Q (proj₁ κ)) B (proj₂ κ)
  ; nx = λ B κ → PS.nx (Q (proj₁ κ)) B (proj₂ κ)
  ; ev↑ = λ q {κ} → PS.ev↑ (Q (proj₁ κ)) q
  ; ad↓ = λ q {κ} {e} → PS.ad↓ (Q (proj₁ κ)) q {proj₂ κ} {e}
  ; nx↑ = λ {B} {κ} {e} → PS.nx↑ (Q (proj₁ κ)) {B} {proj₂ κ} {e} }

PSL : ∀ m → PS (Tw XS m)
PSL hz = PSX
PSL (hs x) = psStep (PSL x)
PSL (hl f) = psSup (λ n → PSL (f n))
PSL (hΩ () _)
```

## §2 带路径对世界单调, 对加法封闭 (对一切路径结构)

```agda
module _ {T : KS} (Q : PS T) where
  open PS Q
  PH-mono : ∀ {B B′} → B ⊲ B′ → ∀ h → PH Q B h → PH Q B′ h
  PH-mono q hz p = tt
  PH-mono q (hs h) p = PH-mono q h p
  PH-mono q (hl f) p = λ n → PH-mono q (f n) (p n)
  PH-mono q (hΩ κ g) (ev , p) =
    ev↑ q ev , λ e a′ → PH-mono (proj₂ (ad↓ q {κ} {e} a′)) (g e) (p e (proj₁ (ad↓ q {κ} {e} a′)))

  PH-⊞ : ∀ {B} a h → PH Q B a → PH Q B h → PH Q B (a ⊞ h)
  PH-⊞ a hz pa ph = pa
  PH-⊞ a (hs h) pa ph = PH-⊞ a h pa ph
  PH-⊞ a (hl f) pa ph = λ n → PH-⊞ a (f n) pa (ph n)
  PH-⊞ a (hΩ κ g) pa (ev , ph) = ev , λ e x → PH-⊞ a (g e) (PH-mono (nx↑ {κ = κ} {e} x) a pa) (ph e x)

  PH-mul : ∀ {B} x → PH Q B x → ∀ n → PH Q B (mul x n)
  PH-mul x p zero = p
  PH-mul x p (suc n) = PH-⊞ (mul x n) x (PH-mul x p n) p

  PH-Σ : ∀ {B} f → (∀ n → PH Q B (f n)) → ∀ n → PH Q B (Σ⁺ f n)
  PH-Σ f p zero = p 0
  PH-Σ f p (suc n) = PH-⊞ (Σ⁺ f n) (f (suc n)) (PH-Σ f p n) (p (suc n))

  PH-chain : ∀ {B} b k → PH Q B b → (∀ b′ → PH Q B b′ → PH Q B (k b′)) → ∀ n → PH Q B (chain b k n)
  PH-chain b k pb pk zero = pk b pb
  PH-chain b k pb pk (suc n) =
    PH-⊞ (chain b k n) (k (b ⊞ chain b k n)) (PH-chain b k pb pk n)
      (pk (b ⊞ chain b k n) (PH-⊞ b (chain b k n) pb (PH-chain b k pb pk n)))
```

## §3 叠层地板带路径

`PH-top` 以 $\Omega_1$ 层的地板 `topL` 带路径为前提 (实例里是定理 `CRw.PH-topL`).

```agda
PH-up : ∀ {T} (Q : PS T) {B} c → PH Q B c → PH (psStep Q) B (up c)
PH-up Q hz p = tt
PH-up Q (hs c) p = PH-up Q c p
PH-up Q (hl f) p = λ n → PH-up Q (f n) (p n)
PH-up Q (hΩ κ g) (ev , p) = ev , λ e a → PH-up Q (g e) (p e a)

PH-ι : ∀ {J : Set} {G : J → KS} (Q : (i : J) → PS (G i)) i {B} c → PH (Q i) B c → PH (psSup Q) B (ι i c)
PH-ι Q i hz p = tt
PH-ι Q i (hs c) p = PH-ι Q i c p
PH-ι Q i (hl f) p = λ n → PH-ι Q i (f n) (p n)
PH-ι Q i (hΩ κ g) (ev , p) = ev , λ e a → PH-ι Q i (g e) (p e a)

module Top (ptl : ∀ B → hs hz ⊲ B → PH PSX B topL) where
  PH-top : ∀ m B → hs hz ⊲ B → PH (PSL m) B (top bX m)
  PH-ΣT : ∀ f B → hs hz ⊲ B → ∀ n → PH (PSL (hl f)) B (ΣT XS topL f n)
  PH-top hz B o = ptl B o
  PH-top (hs x) B o = tt , λ c a → PH-up (PSL x) c (proj₂ (proj₂ a))
  PH-top (hl f) B o = PH-ΣT f B o
  PH-top (hΩ () _) B o
  PH-ΣT f B o zero = PH-ι (λ n → PSL (f n)) 0 _ (PH-top (f 0) B o)
  PH-ΣT f B o (suc n) = PH-⊞ (PSL (hl f)) (ΣT XS topL f n) _ (PH-ΣT f B o n)
    (PH-ι (λ k → PSL (f k)) (suc n) _ (PH-top (f (suc n)) B o))
```

## §4 搬运

输入侧 (`clP`): 底种类的证据读回 `XS` 的证据, `XS` 的可入给出塔里的可入, 进入后的世界在下; 新种类在更大世界 $V$ 里带路径的坐标可入, 进入后的世界在 $V$ 之下. 输出侧: 留下的底种类 `emb` (`evE`, `upkE`), 留下的新种类 `along` (`evA`, `upkA`). 每条对层号递归, 每一步字面对上.

```agda
ClP : ∀ m κ → Cl {XS} m κ → Set
ClP m κ (bas κ₀ to) =
  Σ (∀ {B} → PS.Ev (PSL m) B κ → PS.Ev PSX B κ₀) (λ _ →
    ∀ {B} e (a : PS.Ad PSX B κ₀ e) →
      Σ (PS.Ad (PSL m) B κ (to e)) (λ a′ → PS.nx (PSL m) B κ (to e) a′ ⊲ PS.nx PSX B κ₀ e a))
ClP m κ (nw j p to) =
  ∀ {B} c V → B ⊲ V → PH (PSL j) V c →
    Σ (PS.Ad (PSL m) B κ (to c)) (λ a′ → PS.nx (PSL m) B κ (to c) a′ ⊲ V)

pS : ∀ {x κ} (c : Cl {XS} x κ) → ClP x κ c → ClP (hs x) (inj₁ κ) (cS c)
pS (bas κ₀ to) p = p
pS (nw j q to) p = p

pL : ∀ {f} n {κ} (c : Cl {XS} (f n) κ) → ClP (f n) κ c → ClP (hl f) (n , κ) (cL n c)
pL n (bas κ₀ to) p = p
pL n (nw j q to) p = p

clP : ∀ m κ → ClP m κ (cl m κ)
clP hz κ = (λ ev → ev) , (λ e a → a , hself)
clP (hs x) (inj₁ κ) = pS (cl x κ) (clP x κ)
clP (hs x) (inj₂ _) = λ c V w p → (V , w , p) , hself
clP (hl f) (n , κ) = pL n (cl (f n) κ) (clP (f n) κ)
clP (hΩ () _) _

evE : ∀ t {B} κ → PS.Ev PSX B κ → PS.Ev (PSL t) B (emb t κ)
evE hz κ ev = ev
evE (hs x) κ ev = evE x κ ev
evE (hl f) κ ev = evE (f 0) κ ev
evE (hΩ () _) κ ev

upkE : ∀ t {B} κ c (a : PS.Ad (PSL t) B (emb t κ) c) →
       Σ (PS.Ad PSX B κ (frE t κ c)) (λ a₀ → PS.nx PSX B κ (frE t κ c) a₀ ⊲ PS.nx (PSL t) B (emb t κ) c a)
upkE hz κ c a = a , hself
upkE (hs x) κ c a = upkE x κ c a
upkE (hl f) κ c a = upkE (f 0) κ c a
upkE (hΩ () _) κ c a

evA : ∀ {i t} (q : hs i ⊲ t) {B} → PS.Ev (PSL t) B (along q)
evA hself = tt
evA (hsuc q) = evA q
evA (hlim n q) = evA q
evA (hLim {κ = ()} _ _)

upkA : ∀ {i t} (q : hs i ⊲ t) {B} c (a : PS.Ad (PSL t) B (along q) c) →
       Σ Cd (λ V → (B ⊲ V) × PH (PSL i) V (frA q c) × (V ⊲ PS.nx (PSL t) B (along q) c a))
upkA hself c (V , w , p) = V , w , p , hself
upkA (hsuc q) c a = upkA q c a
upkA (hlim n q) c a = upkA q c a
upkA (hLim {κ = ()} _ _) c a
```

## §5 定理: 同底折叠的输出带路径

归纳假设写成两个函数类型 (同 X1Up): `IH₁` 同一层号的分支, 任意目标; `IH₂` 在上之后从第 $i$ 层折到 $t$. 世界都在 $1$ 之上 (`o`; $\Omega_1$ 地板的根要它).

```agda
module Thm (ptl : ∀ B → hs hz ⊲ B → PH PSX B topL) where
  open Top ptl

  IH₁ : ∀ m → (∀ s′ i → Lt s′ i bX m → Acc s′ i) → LgB m → (κ : K (Tw XS m)) → (E (Tw XS m) κ → HB (Tw XS m)) → Set
  IH₁ m rs lm κ g = ∀ t′ (pt′ : t′ ⊲ m) b′ e V → hs hz ⊲ V → PH (PSL t′) V b′ → PH (PSL m) V (g e) →
                    PH (PSL t′) V (Φ bX m (acc rs) lm bX t′ (sm pt′) b′ (g e) tt)

  IH₂ : ∀ m → (∀ s′ i → Lt s′ i bX m → Acc s′ i) → LgB m → ∀ t → HB (Tw XS t) → Set
  IH₂ m rs lm t b = ∀ i (pi : hs i ⊲ m) (q : t ⊲ i) x V → hs hz ⊲ V → PH (PSL t) V b → PH (PSL i) V x →
                    PH (PSL t) V (Φ bX i (rs bX i (lt pi)) (lg↓ pi lm) bX t (sm q) b x tt)

  module Nk (m : Cd) (rs : ∀ s′ i → Lt s′ i bX m → Acc s′ i) (lm : LgB m) (t : Cd) (pt : t ⊲ m)
            (b : HB (Tw XS t)) (κ : K (Tw XS m)) (g : E (Tw XS m) κ → HB (Tw XS m)) where
    Kc : (κ′ : K (Tw XS t)) → (E (Tw XS t) κ′ → E (Tw XS m) κ) → HB (Tw XS t)
    Kc κ′ fr = hΩ κ′ (λ c → Φ bX m (acc rs) lm bX t (sm pt) b (g (fr c)) tt)
    Sc : (HB (Tw XS t) → E (Tw XS m) κ) → HB (Tw XS t)
    Sc to = hl (chain b (λ b′ → Φ bX m (acc rs) lm bX t (sm pt) b′ (g (to b′)) tt))
    Ac : (i : Cd) → hs i ⊲ m → t ⊲ i → (HB (Tw XS i) → E (Tw XS m) κ) → HB (Tw XS t)
    Ac i pi q to = Φ bX i (rs bX i (lt pi)) (lg↓ pi lm) bX t (sm q) b
      (hl (chain (top bX i) (λ b′ → Φ bX m (acc rs) lm bX i (sm (⊏⊑ pi)) b′ (g (to b′)) tt))) tt

  PH-ch : ∀ m rs lm κ (g : E (Tw XS m) κ → HB (Tw XS m)) {B} → hs hz ⊲ B → ∀ j pj (to : HB (Tw XS j) → E (Tw XS m) κ) →
          ClP m κ (nw j pj to) → PH (PSL m) B (hΩ κ g) → IH₁ m rs lm κ g →
          ∀ (pj′ : j ⊲ m) b₀ → PH (PSL j) B b₀ →
          PH (PSL j) B (hl (chain b₀ (λ b′ → Φ bX m (acc rs) lm bX j (sm pj′) b′ (g (to b′)) tt)))
  PH-ch m rs lm κ g {B} o j pj to pk (ev , pg) ih pj′ b₀ p₀ =
    PH-chain (PSL j) b₀ _ p₀ (λ b′ pb′ →
      let a′ = proj₁ (pk b′ B hself pb′) ; w = PS.nx↑ (PSL m) {B} {κ} {to b′} a′ in
      PH-mono (PSL j) (proj₂ (pk b′ B hself pb′)) _
        (ih j pj′ b′ (to b′) _ (⊲ᴮ-tr o w) (PH-mono (PSL j) w b′ pb′) (pg (to b′) a′)))

  PH-pk : ∀ m rs lm t pt b κ (g : E (Tw XS m) κ → HB (Tw XS m)) B → hs hz ⊲ B → ∀ j pj (to : HB (Tw XS j) → E (Tw XS m) κ) →
          ClP m κ (nw j pj to) → PH (PSL t) B b → PH (PSL m) B (hΩ κ g) → IH₁ m rs lm κ g → IH₂ m rs lm t b →
          (r : (t ⊲ hs j) ⊎ (hs j ⊲ t)) →
          PH (PSL t) B (caseDc (pick XS to pj r) (Nk.Kc m rs lm t pt b κ g) (Nk.Sc m rs lm t pt b κ g) (Nk.Ac m rs lm t pt b κ g))
  PH-pk m rs lm t pt b κ g B o j pj to pk pb (ev , pg) ih₁ ih₂ (inj₂ q) =
    evA q , λ c a →
      let u = upkA q c a
          V = proj₁ u ; w = proj₁ (proj₂ u) ; pc = proj₁ (proj₂ (proj₂ u)) ; w′ = proj₂ (proj₂ (proj₂ u))
          a′ = proj₁ (pk (frA q c) V w pc) ; v = PS.nx↑ (PSL m) {B} {κ} {to (frA q c)} a′
      in PH-mono (PSL t) (⊲ᴮ-tr (proj₂ (pk (frA q c) V w pc)) w′) _
           (ih₁ t pt b (to (frA q c)) _ (⊲ᴮ-tr o v) (PH-mono (PSL t) v b pb) (pg _ a′))
  PH-pk m rs lm t pt b κ g B o j pj to pk pb (ev , pg) ih₁ ih₂ (inj₁ hself) =
    tt , λ c a →
      let a′ = proj₁ (pk c (proj₁ a) (proj₁ (proj₂ a)) (proj₂ (proj₂ a))) ; v = PS.nx↑ (PSL m) {B} {κ} {to c} a′
      in PH-mono (PSL t) (proj₂ (pk c (proj₁ a) (proj₁ (proj₂ a)) (proj₂ (proj₂ a)))) _
           (ih₁ t pt b (to c) _ (⊲ᴮ-tr o v) (PH-mono (PSL t) v b pb) (pg _ a′))
  PH-pk m rs lm t pt b κ g B o j pj to pk pb ph ih₁ ih₂ (inj₁ (hsuc hself)) =
    PH-ch m rs lm κ g o j pj to pk ph ih₁ pt b pb
  PH-pk m rs lm t pt b κ g B o j pj to pk pb ph ih₁ ih₂ (inj₁ (hsuc (hsuc q))) =
    ih₂ j pj (hsuc q) (hl (chain (top bX j) (λ b′ → Φ bX m (acc rs) lm bX j (sm (⊏⊑ pj)) b′ (g (to b′)) tt))) B o pb
      (PH-ch m rs lm κ g o j pj to pk ph ih₁ (⊏⊑ pj) (top bX j) (PH-top j B o))
  PH-pk m rs lm t pt b κ g B o j pj to pk pb ph ih₁ ih₂ (inj₁ (hsuc (hlim n q))) =
    ih₂ j pj (hlim n q) (hl (chain (top bX j) (λ b′ → Φ bX m (acc rs) lm bX j (sm (⊏⊑ pj)) b′ (g (to b′)) tt))) B o pb
      (PH-ch m rs lm κ g o j pj to pk ph ih₁ (⊏⊑ pj) (top bX j) (PH-top j B o))
  PH-pk m rs lm t pt b κ g B o j pj to pk pb ph ih₁ ih₂ (inj₁ (hsuc (hLim {κ = ()} _ _)))

  PH-nd : ∀ m rs lm t pt b κ (g : E (Tw XS m) κ → HB (Tw XS m)) B → hs hz ⊲ B → (c : Cl {XS} m κ) → ClP m κ c →
          PH (PSL t) B b → PH (PSL m) B (hΩ κ g) → IH₁ m rs lm κ g → IH₂ m rs lm t b →
          PH (PSL t) B (caseDc (dcl pt lm c) (Nk.Kc m rs lm t pt b κ g) (Nk.Sc m rs lm t pt b κ g) (Nk.Ac m rs lm t pt b κ g))
  PH-nd m rs lm t pt b κ g B o (bas κ₀ to) (evd , pk) pb (ev , pg) ih₁ ih₂ =
    evE t κ₀ (evd ev) , λ c a →
      let u = upkE t κ₀ c a
          a′ = proj₁ (pk (frE t κ₀ c) (proj₁ u)) ; v = PS.nx↑ (PSL m) {B} {κ} {to (frE t κ₀ c)} a′
      in PH-mono (PSL t) (⊲ᴮ-tr (proj₂ (pk (frE t κ₀ c) (proj₁ u))) (proj₂ u)) _
           (ih₁ t pt b (to (frE t κ₀ c)) _ (⊲ᴮ-tr o v) (PH-mono (PSL t) v b pb) (pg _ a′))
  PH-nd m rs lm t pt b κ g B o (nw j pj to) pk pb ph ih₁ ih₂ =
    PH-pk m rs lm t pt b κ g B o j pj to pk pb ph ih₁ ih₂ (cmpB pj pt tt lm)

  PH-ΦX : ∀ m a lm t pt b h B → hs hz ⊲ B → PH (PSL t) B b → PH (PSL m) B h →
          PH (PSL t) B (Φ bX m a lm bX t (sm pt) b h tt)
  PH-ΦX m (acc rs) lm t pt b hz B o pb ph = tt
  PH-ΦX m (acc rs) lm t pt b (hs h) B o pb ph = PH-mul (PSL t) _ (PH-ΦX m (acc rs) lm t pt b h B o pb ph)
  PH-ΦX m (acc rs) lm t pt b (hl f) B o pb ph = PH-Σ (PSL t) _ (λ n → PH-ΦX m (acc rs) lm t pt b (f n) B o pb (ph n))
  PH-ΦX m (acc rs) lm t pt b (hΩ κ g) B o pb ph =
    PH-nd m rs lm t pt b κ g B o (cl m κ) (clP m κ) pb ph
      (λ t′ pt′ b′ e V oV pb′ pe → PH-ΦX m (acc rs) lm t′ pt′ b′ (g e) V oV pb′ pe)
      (λ i pi q x V oV pbx px → PH-ΦX i (rs bX i (lt pi)) (lg↓ pi lm) t q b x V oV pbx px)
```
