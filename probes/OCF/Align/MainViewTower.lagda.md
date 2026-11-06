# 主线数据类型上的 View (五): 下标塔的数据树 `HtTowerFTree.D`

> 不含记号. 入口 [MainView](MainView.lagda.md). 下标塔一路 (`HtTowerF`, `HtTowerN*`) 的数据树是 [HtTowerFTree](HtTowerFTree.lagda.md) 的 `D L W`: 世界成对 `Wd₂ = A × H₀`, 路径 `_≤_`, 层 `Ht = HB S₁`, 八个构造子, 比 `HtFeedTree` 多一个 **`nμ`** (升高世界的高度分量, 分支对一切更大的世界). 这里:
>
> 1. **骨架 `TSkel`**: 与 [MainViewGen](MainViewGen.lagda.md) 同形, 对 `HtTowerFTree.D₊` 的一切参数 (所以一切层) 一条定义; 节点的段从两个变成**三个**: `SegI`, `SegK`, **`SegM`** (`nμ` 段). 良基同 (`D-i`, `D-κ`, **`D-μ`**).
> 2. **第 0 层**: `D hz` 没有节点 (`StH W k hz` 空, `NZ hz = NZ₁ hz = ⊥`), 三个段都是空函数, 读法是 `HtTowerFTree.sum`. `view₀ᵀ`, `wf₀ᵀ`, `fgh₀≡ᵀ` **无条件**.
> 3. **第 1 层**: `nμ` **不出现** (`NZ₁ (hs hz) = NZ hz = ⊥`, 定义相等, `no-nμ₁`), 段只有 `SegI`, `SegK`. 但第 1 层还没有值的读法, 本篇不给 View; 见 §4 的障碍.
> 4. **`nμ` 要的额外的东西** (精确到类型): 第 2 层以上的值的读法, 它的目标树要有**第三种 $\Omega$-极限** (按世界的高度分量分支), 加上 `SegM` 的一个居民.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.MainViewTower where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; subst₂; sym; trans; cong)
open import Induction.WellFounded using (Acc; acc; WellFounded)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (s≤; ≤l; l≤; ≤-refl; ≤-trans) renaming (_≤_ to _≤ᴬ_)
open import OCF.Align.HtTowerFTree using (Ht; Wd₂; LgW₂; ≤rf; ≤tr; StH; Vs; NZ; NZ₁; D₊; D; D₀; n0; n1; _⨾_; nl; ni; nκ; nμ; nw; sum; pt; sum-fst)
  renaming (_≤_ to _≤ʷ_)
open import OCF.Align.HtTowerTy using (hz; hs)
open import OCF.Align.BrwViewDef using (Sig; View; vz; vs; vl; vΩ; BrwView)
open import OCF.Align.BrwViewZero using (Sig₀)
open import OCF.Align.BrwWfDef using (Obj; Part; p-s; p-l; p-Ω; _◁_; BrwViewᵂ; measure)
open import OCF.Align.BrwWfRead using (rec′; module Read; Cong; module ReadOk)
open import OCF.Align.BrwWfZero using (SubA; sa-s; sa-l; SubA-wf; _≅_; z≅; s≅; l≅; ≅-trans; ≡→≅; fghA; iter; iter-cong; fgh-≅)
```

## §1 骨架, 三个段

```agda
module _ {Kd : Wd₂ → Ht → Set} {Vv : ∀ {W k} → Kd W k → Wd₂ → Set} {Z₀ Z₁ : Set} where
  psᵀ : ∀ {W} → (ℕ → D₊ Kd Vv Z₀ Z₁ W) → ℕ → D₊ Kd Vv Z₀ Z₁ W
  psᵀ d zero = n0
  psᵀ d (suc n) = psᵀ d n ⨾ d n

module TSkel {Nd : Wd₂ → Ht → Set} {Vv : ∀ {W k} → Nd W k → Wd₂ → Set} {Z₀ Z₁ : Set}
  (Sg : Sig) (open Sig Sg)
  (wd   : Ix → Wd₂)
  (val  : ∀ {i} → D₊ Nd Vv Z₀ Z₁ (wd i) → B i)
  (Lgl  : ∀ {W} → D₊ Nd Vv Z₀ Z₁ W → Set)
  (Sm   : ∀ {i W₀} → W₀ ≤ʷ wd i → B i → D₊ Nd Vv Z₀ Z₁ W₀ → B i)
  (≈-rf : ∀ {i} (a : B i) → a ≈ a)
  (e-n0 : ∀ {i W₀} (q : W₀ ≤ʷ wd i) b → Sm q b n0 ≡ b)
  (e-n1 : ∀ {i W₀} (q : W₀ ≤ʷ wd i) b → Sm q b n1 ≡ bs b)
  (e-⨾  : ∀ {i W₀} (q : W₀ ≤ʷ wd i) b y z → Sm q b (y ⨾ z) ≡ Sm q (Sm q b y) z)
  (e-nw : ∀ {i W₁ W₀} (r : W₁ ≤ʷ W₀) (q : W₀ ≤ʷ wd i) b y → Sm q b (nw r y) ≡ Sm (≤tr r q) b y)
  (e-val : ∀ {i} (x : D₊ Nd Vv Z₀ Z₁ (wd i)) {W₀} (q : W₀ ≤ʷ wd i) y → val (x ⨾ nw q y) ≡ Sm q (val x) y)
  (e-top : ∀ {i} (x : D₊ Nd Vv Z₀ Z₁ (wd i)) → val x ≡ Sm ≤rf (val (n0 {W = wd i})) x)
  (e-0  : ∀ {i} → val (n0 {W = wd i}) ≈ bz)
  (e-nl : ∀ {i} (x : D₊ Nd Vv Z₀ Z₁ (wd i)) {W₀} (q : W₀ ≤ʷ wd i) d → Sm q (val x) (nl d) ≈ bl (λ n → val (x ⨾ nw q (psᵀ d n))))
  (fst  : ∀ {i W₀} (q : W₀ ≤ʷ wd i) b y → Stp b (Sm q b y))
  (L-n0 : ∀ {W} → Lgl (n0 {W = W}))
  (L-⨾  : ∀ {W} {x y : D₊ Nd Vv Z₀ Z₁ W} → Lgl x → Lgl y → Lgl (x ⨾ y))
  (L-⨾₁ : ∀ {W} {x y : D₊ Nd Vv Z₀ Z₁ W} → Lgl (x ⨾ y) → Lgl x)
  (L-⨾₂ : ∀ {W} {x y : D₊ Nd Vv Z₀ Z₁ W} → Lgl (x ⨾ y) → Lgl y)
  (L-nl : ∀ {W} {d : ℕ → D₊ Nd Vv Z₀ Z₁ W} → Lgl (nl d) → ∀ n → Lgl (d n))
  (L-nw : ∀ {W₀ W} {p : W₀ ≤ʷ W} {y : D₊ Nd Vv Z₀ Z₁ W₀} → Lgl (nw p y) → Lgl y)
  (L-nwI : ∀ {W₀ W} {p : W₀ ≤ʷ W} {y : D₊ Nd Vv Z₀ Z₁ W₀} → Lgl y → Lgl (nw p y))
  where

  Dt : Wd₂ → Set
  Dt = D₊ Nd Vv Z₀ Z₁

  X : Ix → Set
  X i = Dt (wd i)

  Lgx : ∀ {i} → X i → Set
  Lgx x = Lgl x

  V : (i : Ix) → B i → Set
  V = View Sg X val Lgx

  Pt : ∀ {i v} → V i v → Obj Sg X val Lgx → Set
  Pt = Part Sg X val Lgx

  L-ps : ∀ {W} (d : ℕ → Dt W) → (∀ n → Lgl (d n)) → ∀ n → Lgl (psᵀ d n)
  L-ps d h zero = L-n0
  L-ps d h (suc n) = L-⨾ (L-ps d h n) (h n)

  SegI : Set
  SegI = ∀ {i} (x : X i) → Lgl x → V i (val x) → ∀ {W₀ k} (q : W₀ ≤ʷ wd i) (r : Nd W₀ k) (u : ∀ {W′} → W₀ ≤ʷ W′ → LgW₂ W′ → Vv r W′ → Dt W′) →
         Lgl (ni r u) → V i (Sm q (val x) (ni r u))

  SegK : Set
  SegK = ∀ {i} (x : X i) → Lgl x → V i (val x) → ∀ {W₀} (q : W₀ ≤ʷ wd i) (zz : Z₀) (u : ∀ {c} → proj₁ W₀ ⊲ c → Lg c → Dt (c , proj₂ W₀)) →
         Lgl (nκ zz u) → V i (Sm q (val x) (nκ zz u))

  -- nμ 段: 新节点要的那一件
  SegM : Set
  SegM = ∀ {i} (x : X i) → Lgl x → V i (val x) → ∀ {W₀} (q : W₀ ≤ʷ wd i) (zz : Z₁) (u : ∀ {W′} → W₀ ≤ʷ W′ → LgW₂ W′ → Dt W′) →
         Lgl (nμ zz u) → V i (Sm q (val x) (nμ zz u))

  E⨾ : ∀ {i} (x : X i) {W₀} (q : W₀ ≤ʷ wd i) (y₁ y₂ : Dt W₀) → Sm q (val (x ⨾ nw q y₁)) y₂ ≡ Sm q (val x) (y₁ ⨾ y₂)
  E⨾ x q y₁ y₂ = trans (cong (λ b → Sm q b y₂) (e-val x q y₁)) (sym (e-⨾ q (val x) y₁ y₂))

  Eps : ∀ {i} (x : X i) {W₀} (q : W₀ ≤ʷ wd i) (d : ℕ → Dt W₀) n →
        val (x ⨾ nw q (psᵀ d (suc n))) ≡ Sm q (Sm q (val x) (psᵀ d n)) (d n)
  Eps x q d n = trans (e-val x q (psᵀ d n ⨾ d n)) (e-⨾ q (val x) (psᵀ d n) (d n))

  module WithSeg (sgi : SegI) (sgk : SegK) (sgm : SegM) where
    vw : ∀ {i} (x : X i) → Lgl x → V i (val x) → ∀ {W₀} (q : W₀ ≤ʷ wd i) (y : Dt W₀) → Lgl y → V i (Sm q (val x) y)
    vw {i} x hx vx q n0 hy = subst (V i) (sym (e-n0 q (val x))) vx
    vw {i} x hx vx q n1 hy = vs x hx (subst (λ v → v ≈ bs (val x)) (sym (e-n1 q (val x))) (≈-rf (bs (val x))))
    vw {i} x hx vx q (y₁ ⨾ y₂) hy =
      subst (V i) (E⨾ x q y₁ y₂)
        (vw (x ⨾ nw q y₁) (L-⨾ hx (L-nwI (L-⨾₁ hy))) (subst (V i) (sym (e-val x q y₁)) (vw x hx vx q y₁ (L-⨾₁ hy))) q y₂ (L-⨾₂ hy))
    vw {i} x hx vx q (nl d) hy =
      vl (λ n → x ⨾ nw q (psᵀ d n)) (λ n → L-⨾ hx (L-nwI (L-ps d (L-nl hy) n)))
         (λ n → subst₂ Stp (sym (e-val x q (psᵀ d n))) (sym (Eps x q d n)) (fst q (Sm q (val x) (psᵀ d n)) (d n)))
         (e-nl x q d)
    vw {i} x hx vx q (nw r y) hy = subst (V i) (sym (e-nw r q (val x) y)) (vw x hx vx (≤tr r q) y (L-nw hy))
    vw x hx vx q (ni r u) hy = sgi x hx vx q r u hy
    vw x hx vx q (nκ zz u) hy = sgk x hx vx q zz u hy
    vw x hx vx q (nμ zz u) hy = sgm x hx vx q zz u hy

    view : BrwView Sg X val Lgx
    view = record { view = λ {i} x lx → subst (V i) (sym (e-top x)) (vw n0 L-n0 (vz e-0) ≤rf x lx) }

    Pt-subst : ∀ {i v v′} (e : v ≡ v′) (w : V i v) {o} → Pt (subst (V i) e w) o → Pt w o
    Pt-subst refl w p = p

    module Dec (T : Set) (_<ᵣ_ : T → T → Set) (wfᵣ : WellFounded _<ᵣ_) (rk : ∀ {i} → B i → T)
      (R-s : ∀ {i} (b : B i) → rk b <ᵣ rk (bs b))
      (R-l : ∀ {i} (x : X i) {W₀} (q : W₀ ≤ʷ wd i) (d : ℕ → Dt W₀) n → rk (val (x ⨾ nw q (psᵀ d n))) <ᵣ rk (Sm q (val x) (nl d)))
      (D-i : ∀ {i} (x : X i) (hx : Lgl x) (vx : V i (val x)) {W₀ k} (q : W₀ ≤ʷ wd i) (r : Nd W₀ k)
             (u : ∀ {W′} → W₀ ≤ʷ W′ → LgW₂ W′ → Vv r W′ → Dt W′) (hy : Lgl (ni r u)) →
             (∀ {o} → Pt vx o → rk (val (proj₁ (proj₂ o))) <ᵣ rk (val x)) →
             ∀ {o} → Pt (sgi x hx vx q r u hy) o → rk (val (proj₁ (proj₂ o))) <ᵣ rk (Sm q (val x) (ni r u)))
      (D-κ : ∀ {i} (x : X i) (hx : Lgl x) (vx : V i (val x)) {W₀} (q : W₀ ≤ʷ wd i) (zz : Z₀)
             (u : ∀ {c} → proj₁ W₀ ⊲ c → Lg c → Dt (c , proj₂ W₀)) (hy : Lgl (nκ zz u)) →
             (∀ {o} → Pt vx o → rk (val (proj₁ (proj₂ o))) <ᵣ rk (val x)) →
             ∀ {o} → Pt (sgk x hx vx q zz u hy) o → rk (val (proj₁ (proj₂ o))) <ᵣ rk (Sm q (val x) (nκ zz u)))
      (D-μ : ∀ {i} (x : X i) (hx : Lgl x) (vx : V i (val x)) {W₀} (q : W₀ ≤ʷ wd i) (zz : Z₁)
             (u : ∀ {W′} → W₀ ≤ʷ W′ → LgW₂ W′ → Dt W′) (hy : Lgl (nμ zz u)) →
             (∀ {o} → Pt vx o → rk (val (proj₁ (proj₂ o))) <ᵣ rk (val x)) →
             ∀ {o} → Pt (sgm x hx vx q zz u hy) o → rk (val (proj₁ (proj₂ o))) <ᵣ rk (Sm q (val x) (nμ zz u)))
      where

      rko : Obj Sg X val Lgx → T
      rko o = rk (val (proj₁ (proj₂ o)))

      ↑< : ∀ {i} {t : T} {b b′ : B i} → b ≡ b′ → t <ᵣ rk b → t <ᵣ rk b′
      ↑< e h = subst (λ v → _ <ᵣ rk v) e h

      dec : ∀ {i} (x : X i) (hx : Lgl x) (vx : V i (val x)) {W₀} (q : W₀ ≤ʷ wd i) (y : Dt W₀) (hy : Lgl y) →
            (∀ {o} → Pt vx o → rko o <ᵣ rk (val x)) →
            ∀ {o} → Pt (vw x hx vx q y hy) o → rko o <ᵣ rk (Sm q (val x) y)
      dec x hx vx q n0 hy H p = ↑< (sym (e-n0 q (val x))) (H (Pt-subst (sym (e-n0 q (val x))) vx p))
      dec x hx vx q n1 hy H p-s = ↑< (sym (e-n1 q (val x))) (R-s (val x))
      dec x hx vx q (y₁ ⨾ y₂) hy H p =
        ↑< (E⨾ x q y₁ y₂)
           (dec (x ⨾ nw q y₁) (L-⨾ hx (L-nwI (L-⨾₁ hy))) v₁′ q y₂ (L-⨾₂ hy)
                (λ p′ → ↑< (sym (e-val x q y₁)) (dec x hx vx q y₁ (L-⨾₁ hy) H (Pt-subst (sym (e-val x q y₁)) v₁ p′)))
                (Pt-subst (E⨾ x q y₁ y₂) _ p))
        where
        v₁ = vw x hx vx q y₁ (L-⨾₁ hy)
        v₁′ = subst (V _) (sym (e-val x q y₁)) v₁
      dec x hx vx q (nl d) hy H (p-l n) = R-l x q d n
      dec x hx vx q (nw r y) hy H p =
        ↑< (sym (e-nw r q (val x) y)) (dec x hx vx (≤tr r q) y (L-nw hy) H (Pt-subst (sym (e-nw r q (val x) y)) _ p))
      dec x hx vx q (ni r u) hy H p = D-i x hx vx q r u hy H p
      dec x hx vx q (nκ zz u) hy H p = D-κ x hx vx q zz u hy H p
      dec x hx vx q (nμ zz u) hy H p = D-μ x hx vx q zz u hy H p

      _◁ᴳ_ : Obj Sg X val Lgx → Obj Sg X val Lgx → Set
      _◁ᴳ_ = _◁_ Sg X val Lgx view

      dec-top : ∀ {o o′} → o′ ◁ᴳ o → rko o′ <ᵣ rko o
      dec-top {i , x , lx} p =
        ↑< (sym (e-top x)) (dec n0 L-n0 (vz e-0) ≤rf x lx (λ ()) (Pt-subst (sym (e-top x)) _ p))

      wf : WellFounded _◁ᴳ_
      wf = measure _◁ᴳ_ _<ᵣ_ rko wfᵣ dec-top

      viewᵂ : BrwViewᵂ Sg X val Lgx
      viewᵂ = record { bv = view ; wf = wf }
```

## §2 第 0 层, 无条件

```agda
open Sig Sig₀ using (_≈_)

≈r : ∀ a → a ≈ a
≈r a = ≤-refl a , ≤-refl a

lim≡ : ∀ (f g : ℕ → A) → (∀ n → f n ≡ g n) → alim f ≈ alim g
lim≡ f g e = l≤ (λ n → ≤l n (subst (λ a → f n ≤ᴬ a) (e n) (≤-refl (f n)))) ,
             l≤ (λ n → ≤l n (subst (λ a → g n ≤ᴬ a) (sym (e n)) (≤-refl (g n))))

ps-ptᵀ : ∀ {W₀} b (d : ℕ → D₀ W₀) n → sum b (psᵀ d n) ≡ pt b d n
ps-ptᵀ b d zero = refl
ps-ptᵀ b d (suc n) = cong (λ a → sum a (d n)) (ps-ptᵀ b d n)

module Zero (W : Wd₂) where
  open TSkel {Nd = λ W k → StH W k hz} {Vv = λ R → Vs hz R} {Z₀ = NZ hz} {Z₁ = NZ₁ hz}
             Sig₀ (λ _ → W) (λ x → sum azero x) (λ _ → ⊤) (λ q b y → sum b y) ≈r
             (λ q b → refl) (λ q b → refl) (λ q b y z → refl) (λ r q b y → refl) (λ x q y → refl) (λ x → refl) (≈r azero)
             (λ x q d → lim≡ _ _ (λ n → sym (ps-ptᵀ (sum azero x) d n))) (λ q b y → sum-fst b y)
             tt (λ _ _ → tt) (λ _ → tt) (λ _ → tt) (λ _ _ → tt) (λ _ → tt) (λ _ → tt)
    public

  open WithSeg (λ { x hx vx q () }) (λ { x hx vx q () }) (λ { x hx vx q () }) public

  view₀ᵀ : BrwView Sig₀ X (λ x → sum azero x) Lgx
  view₀ᵀ = view

  R-l₀ : ∀ (x : D₀ W) {W₀} (q : W₀ ≤ʷ W) (d : ℕ → D₀ W₀) n → SubA (sum azero (x ⨾ nw q (psᵀ d n))) (sum (sum azero x) (nl d))
  R-l₀ x q d n = subst (λ a → SubA a (alim (pt (sum azero x) d))) (sym (ps-ptᵀ (sum azero x) d n)) (sa-l n)

  open Dec A SubA SubA-wf (λ b → b) (λ b → sa-s) R-l₀ (λ { x hx vx q () }) (λ { x hx vx q () }) (λ { x hx vx q () }) public

  wf₀ᵀ : WellFounded _◁ᴳ_
  wf₀ᵀ = wf

  view₀ᵀᵂ : BrwViewᵂ Sig₀ X (λ x → sum azero x) Lgx
  view₀ᵀᵂ = viewᵂ

  Ob₀ : Set
  Ob₀ = Obj Sig₀ X (λ x → sum azero x) Lgx

  vo₀ : Ob₀ → A
  vo₀ (_ , x , _) = sum azero x

  Cong₀ : Cong view₀ᵀᵂ
  Cong₀ = record { tr = ≤-trans ; bs-m = s≤ ; bl-m = λ h → l≤ (λ n → ≤l n (h n)) ; bΩ-m = λ () }

  open Read view₀ᵀᵂ (λ c → tt) using (step; rd′; rd)

  rd₀≈ᵀ : ∀ o → (rd o ≤ᴬ vo₀ o) × (vo₀ o ≤ᴬ rd o)
  rd₀≈ᵀ = ReadOk.rd≈ view₀ᵀᵂ (λ c → tt) Cong₀

  Lit : ∀ {v} → V tt v → A → Set
  Lit w a = ∀ (r : ∀ {o} → Pt w o → A) → (∀ {o} (p : Pt w o) → r p ≅ vo₀ o) → step w r ≅ a

  lit : ∀ {W₀} (x : D₀ W) (vx : V tt (sum azero x)) (q : W₀ ≤ʷ W) (y : D₀ W₀) →
        Lit vx (sum azero x) → Lit (vw x tt vx q y tt) (sum (sum azero x) y)
  lit x vx q n0 h = h
  lit x vx q n1 h r e = s≅ (e p-s)
  lit x vx q (y₁ ⨾ y₂) h = lit (x ⨾ nw q y₁) (vw x tt vx q y₁ tt) q y₂ (lit x vx q y₁ h)
  lit x vx q (nl d) h r e = l≅ (λ n → ≅-trans (e (p-l n)) (≡→≅ (ps-ptᵀ (sum azero x) d n)))
  lit x vx q (ni () u) h
  lit x vx q (nκ () u) h
  lit x vx q (nμ () u) h
  lit x vx q (nw p y) h = lit x vx (≤tr p q) y h

  rd₀≅′ : ∀ o (a : Acc _◁ᴳ_ o) → rd′ o a ≅ vo₀ o
  rd₀≅′ (tt , x , tt) (acc rs) = lit n0 (vz (≈r azero)) ≤rf x (λ r e → z≅) _ (λ p → rd₀≅′ _ (rs p))

  rd₀≅ᵀ : ∀ o → rd o ≅ vo₀ o
  rd₀≅ᵀ o = rd₀≅′ o (wf₀ᵀ o)

  fstep : ∀ {v} (w : V tt v) → (∀ {o} → Pt w o → ℕ → ℕ) → ℕ → ℕ
  fstep (vz _) r n = suc n
  fstep (vs y ly _) r n = iter (r p-s) n n
  fstep (vl f lf _ _) r n = r (p-l n) n
  fstep (vΩ () g lg _) r n

  fgh₀′ : ∀ o → Acc _◁ᴳ_ o → ℕ → ℕ
  fgh₀′ = rec′ view₀ᵀᵂ (λ _ → ℕ → ℕ) (λ x lx r → fstep (BrwView.view view₀ᵀ x lx) r)

  fgh₀ᵀ : Ob₀ → ℕ → ℕ
  fgh₀ᵀ o = fgh₀′ o (wf₀ᵀ o)

  fstep≡ : ∀ {v} (w : V tt v) (r : ∀ {o} → Pt w o → ℕ → ℕ) (r′ : ∀ {o} → Pt w o → A) →
           (∀ {o} (p : Pt w o) n → r p n ≡ fghA (r′ p) n) → ∀ n → fstep w r n ≡ fghA (step w r′) n
  fstep≡ (vz _) r r′ e n = refl
  fstep≡ (vs y ly _) r r′ e n = iter-cong (e p-s) n n
  fstep≡ (vl f lf _ _) r r′ e n = e (p-l n) n
  fstep≡ (vΩ () g lg _) r r′ e n

  fgh-rd′ : ∀ o (a : Acc _◁ᴳ_ o) n → fgh₀′ o a n ≡ fghA (rd′ o a) n
  fgh-rd′ (tt , x , tt) (acc rs) = fstep≡ (BrwView.view view₀ᵀ x tt) _ _ (λ p → fgh-rd′ _ (rs p))

  fgh₀≡ᵀ : ∀ (x : D₀ W) n → fgh₀ᵀ (tt , x , tt) n ≡ fghA (sum azero x) n
  fgh₀≡ᵀ x n = trans (fgh-rd′ (tt , x , tt) (wf₀ᵀ _) n) (fgh-≅ (rd₀≅ᵀ (tt , x , tt)) n)
```

## §3 第 1 层没有 `nμ`

```agda
no-nμ₁ : NZ₁ (hs hz) → ⊥
no-nμ₁ ()
```

所以第 1 层的骨架只要 `SegI`, `SegK` (第三个段是空函数). `nμ` 从第 2 层起才有 (`NZ₁ (hs (hs hz)) = ⊤`).

## §4 第 1 层的障碍 (判断, 未编译)

`HtFeedTree` 的第 1 层可以经改名 `π` 读成 `SumOneTree` 的第 1 层, 再用 `LayerTrOne.toB` 求值 ([MainViewOne](MainViewOne.lagda.md)). `HtTowerFTree` 的第 1 层**不能照搬**: `ni` 的分支要的世界合法性是 `LgW₂ W′ = Lg (proj₁ W′) × LgB (proj₂ W′)`, 高度分量的合法性 `LgB` 要由读法提供.

- 照 `π` 逐构造子改名 (分支在 $(V,\beta_0)$, $\beta_0$ 是节点自己世界的高度分量): `LgB β₀` 只能从上面的世界经 `lgB⊲` 推出来, 推法依赖路径的证明项 (`Lg` 与 `LgB` 不是命题); 前缀抬升 (`nw (p , hself) x`) 改变推法, 分支收到不同的合法性证明, 值是否不变就是一个新的条件 (合法性证明无关), `HW` 不管它.
- 改为分支在顶层世界的高度分量 $(V,\beta)$ (证明取顶层给的那一个, 不推): 这正是 `LayerTrOne.S` 的做法 (分支只在比顶层大的世界上), 改名到 `SumOneTree` 表达不了 (那边的分支对比节点世界大的一切世界), 要在成对的世界上重写 `S`, `K`, `I` 与 `lift`, `JI`, `CK`, `Rv` 一套. 判断: 这一套与 `LayerTrOne` 加 `BrwView*`/`BrwWf*` 的第 1 层同形, 规模约四百行, 没有新想法; 本篇没有写. **暂停**, 不是否定.

## §5 `nμ` 要的额外的东西

`SegM` (§1) 就是 `nμ` 节点要的段. 要有居民, 先要第 2 层以上的值的读法, 它的目标树要有第三种 $\Omega$-极限, 种类 `kμ`, 坐标是更大的世界 $(W',p,l')$ (`W₀ ≤ W′`, 高度分量变大), 部分照 `nκ` 段的形状: 前缀抬到 $W'$, 接上沿高度路径的段 (`HtTowerFTree.Cut₁`, 它在 `hLim` 处插进旧种类的闭包 `nκ`), 再接 $u(W')$. 仓库里没有第 2 层的读法 (`BrwHW` 第 3 条, 本篇 [MainView](MainView.lagda.md) §5), 所以 `SegM` 现在只能作参数.
