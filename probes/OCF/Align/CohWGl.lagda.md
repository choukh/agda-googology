# 相干的世界 (五): 一个世界对一切层号

> 不含记号. 入口 [CohW](CohW.lagda.md). [CohWNeg](CohWNeg.lagda.md) 说 `U⋆` 只让**链上**的拷贝相干: `Lev` 部分新造的种类结构是低级种类的拷贝, 世界在独立的位置 (`no-cross`, `no-crossA`). 根子在 `KS` 把世界放进每个种类结构自己: 每造一个结构 (`step`, `sup`, `Lev`) 就多一个世界的位置, 同一个层号出现几次就有几份界.
>
> 这一篇把世界从种类结构里拿出来. **一个世界给每个层号一个界**:
>
> $$\mathrm{GW} = \prod_{y:\mathrm{LH}} H^0(\mathrm{Lv}\,y),$$
>
> $w\,y$ 是层号 $y$ 的新种类的界. 做法分三步:
>
> 1. **先只造种类与坐标** (`KE`: 种类, 坐标; 没有世界). 高度的形状 `H⁰` 只看种类与坐标. 层号块 `LH`, `Lv : LH → KE` 是 [LFReTy](LFReTy.lagda.md) 的四行, 底换成空结构, 每一行同 `LFReTy`.
> 2. **再定世界** `GW`. 它只用到 `H⁰`, 不用到界, 所以没有循环.
> 3. **最后对层号递归定界、第一位置、合法、比较**, 都在同一个世界 `GW` 里: 层号 $y$ 的新种类的界是 `cv y c ⊲[ w ] cv y (w y)` (`cv` 把 `H⁰` 原样换成 `HtTowerTy.HB`, 好用 `cmpB`). 每个层号给一个 `KS` (`Lv⋆ y`), 种类与坐标**定义上就是** `Lv y` 的, 世界都是 `GW`.
>
> 合法与世界序对层号递归 (`LgW⋆ (ls x)` 用到 `Lv⋆ x` 的 `LgB`, 层号更小), 停机检查直接过. 全部层号的并 `SL⋆` (同 `LFReTy.SL = sup LH (step ∘ Lv)`, 世界换成 `GW`) 是一个 `KS`, `cmpB` 原样可用.
>
> **相干定理 `glob`** (对一切层号、一切种类, 对层号与种类递归, 每一步 `refl`): 任一种类的界**只由它的读回层与世界在那一层的分量决定**: `Bd⋆ y κ c w ≡ (cv ℓ c ⊲[ w ] cv ℓ (w ℓ))`, $\ell=$ `lvl y κ`. 同一个层号无论出现在哪里, 界都是同一个. `no-cross` 那一对种类的形状在这里**是定理** (`cross`).
>
> 塔与对角: `LFReTower` 的 $\hat\Omega$, `tw`, **`Λ`**, 照抄到 `SL⋆` (`Ω̂`, `tw`, `Λ`, `Lg-Λ`), 合法性是一步定理, 由形状给出.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CohWGl where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFNeed using (KMatch)
open import OCF.Align.HtTowerNStage using (WMatch)
```

## §1 只有种类与坐标

```agda
record KE : Set₁ where
  constructor ke
  field
    Kᵉ : Set
    Eᵉ : Kᵉ → Set
open KE public

data H⁰ (S : KE) : Set where
  z⁰ : H⁰ S
  s⁰ : H⁰ S → H⁰ S
  l⁰ : (ℕ → H⁰ S) → H⁰ S
  Ω⁰ : (κ : Kᵉ S) → (Eᵉ S κ → H⁰ S) → H⁰ S

E⊥ : ⊥ → Set
E⊥ ()

stepᵉ : KE → KE
stepᵉ S = ke (Kᵉ S ⊎ ⊤) [ Eᵉ S , (λ _ → H⁰ S) ]′

supᵉ : (I : Set) → (I → KE) → KE
supᵉ I F = ke (Σ I (λ i → Kᵉ (F i))) (λ κ → Eᵉ (F (proj₁ κ)) (proj₂ κ))
```

层号块: `LFReTy` 的四行.

```agda
data LH : Set
Lv : LH → KE

data LH where
  lz : LH
  ls : LH → LH
  ll : (ℕ → LH) → LH
  lΩ : (k : LH) → (H⁰ (Lv k) → LH) → LH

Lv lz = ke ⊥ E⊥
Lv (ls x) = stepᵉ (Lv x)
Lv (ll f) = supᵉ ℕ (λ n → Lv (f n))
Lv (lΩ k g) = supᵉ (⊤ ⊎ H⁰ (Lv k)) [ (λ _ → stepᵉ (Lv k)) , (λ c → Lv (g c)) ]′
```

## §2 一个世界

```agda
GW : Set
GW = (y : LH) → H⁰ (Lv y)
```

## §3 每个层号一个种类结构, 世界都是 `GW`

`Lv⋆ y` 是一个记录, 字段是下面对层号递归的函数. 种类与坐标是 `Lv y` 的 (定义相等, 对一切 $y$). 新种类 (`inj₂`) 的界、第一位置、合法、比较都是 `HB (Lv⋆ x)` 的 `⊲`, `LgB`, `cmpB`, 在同一个世界 $w$ 里, 界是 $w\,x$.

```agda
mutual
  Lv⋆ : LH → KS
  Lv⋆ y = record
    { K = Kᵉ (Lv y) ; E = Eᵉ (Lv y) ; Wd = GW ; LgW = LgW⋆ y ; _≤w_ = Le⋆ y ; ≤w-rf = rf⋆ y ; ≤w-tr = tr⋆ y
    ; Bd = Bd⋆ y ; Pr = Pr⋆ y ; Bd↑ = Bd↑⋆ y ; cmpK = cmp⋆ y ; LgE = LgE⋆ y ; lgBd = lgBd⋆ y ; bot = bot⋆ y ; botBd = botBd⋆ y }

  cv : ∀ x → H⁰ (Lv x) → HB (Lv⋆ x)
  cv x z⁰ = hz
  cv x (s⁰ h) = hs (cv x h)
  cv x (l⁰ f) = hl (λ n → cv x (f n))
  cv x (Ω⁰ κ g) = hΩ κ (λ c → cv x (g c))

  Bd⋆ : (y : LH) (κ : Kᵉ (Lv y)) → Eᵉ (Lv y) κ → GW → Set
  Bd⋆ lz () c w
  Bd⋆ (ls x) (inj₁ κ) c w = Bd⋆ x κ c w
  Bd⋆ (ls x) (inj₂ _) c w = cv x c ⊲[ w ] cv x (w x)
  Bd⋆ (ll f) (n , κ) c w = Bd⋆ (f n) κ c w
  Bd⋆ (lΩ k g) (inj₁ _ , inj₁ κ) c w = Bd⋆ k κ c w
  Bd⋆ (lΩ k g) (inj₁ _ , inj₂ _) c w = cv k c ⊲[ w ] cv k (w k)
  Bd⋆ (lΩ k g) (inj₂ d , κ) c w = Bd⋆ (g d) κ c w

  Pr⋆ : (y : LH) (κ : Kᵉ (Lv y)) → GW → Eᵉ (Lv y) κ → Eᵉ (Lv y) κ → Set
  Pr⋆ lz () w c c′
  Pr⋆ (ls x) (inj₁ κ) w c c′ = Pr⋆ x κ w c c′
  Pr⋆ (ls x) (inj₂ _) w c c′ = cv x c ⊲[ w ] cv x c′
  Pr⋆ (ll f) (n , κ) w c c′ = Pr⋆ (f n) κ w c c′
  Pr⋆ (lΩ k g) (inj₁ _ , inj₁ κ) w c c′ = Pr⋆ k κ w c c′
  Pr⋆ (lΩ k g) (inj₁ _ , inj₂ _) w c c′ = cv k c ⊲[ w ] cv k c′
  Pr⋆ (lΩ k g) (inj₂ d , κ) w c c′ = Pr⋆ (g d) κ w c c′

  LgW⋆ : LH → GW → Set
  LgW⋆ lz w = ⊤
  LgW⋆ (ls x) w = LgW⋆ x w × LgB (cv x (w x))
  LgW⋆ (ll f) w = ∀ n → LgW⋆ (f n) w
  LgW⋆ (lΩ k g) w = (LgW⋆ k w × LgB (cv k (w k))) × (∀ d → LgW⋆ (g d) w)

  Le⋆ : LH → GW → GW → Set
  Le⋆ lz w w′ = ⊤
  Le⋆ (ls x) w w′ = Le⋆ x w w′ × (cv x (w x) ⊲[ w′ ] cv x (w′ x))
  Le⋆ (ll f) w w′ = ∀ n → Le⋆ (f n) w w′
  Le⋆ (lΩ k g) w w′ = (Le⋆ k w w′ × (cv k (w k) ⊲[ w′ ] cv k (w′ k))) × (∀ d → Le⋆ (g d) w w′)

  rf⋆ : ∀ y {w} → Le⋆ y w w
  rf⋆ lz = tt
  rf⋆ (ls x) = rf⋆ x , hself
  rf⋆ (ll f) = λ n → rf⋆ (f n)
  rf⋆ (lΩ k g) = (rf⋆ k , hself) , (λ d → rf⋆ (g d))

  tr⋆ : ∀ y {u v w} → Le⋆ y u v → Le⋆ y v w → Le⋆ y u w
  tr⋆ lz p q = tt
  tr⋆ (ls x) (p , b) (q , c) = tr⋆ x p q , ⊲ᴮ-tr (⊲ᴮ↑ q b) c
  tr⋆ (ll f) p q = λ n → tr⋆ (f n) (p n) (q n)
  tr⋆ (lΩ k g) ((p , b) , p′) ((q , c) , q′) = (tr⋆ k p q , ⊲ᴮ-tr (⊲ᴮ↑ q b) c) , (λ d → tr⋆ (g d) (p′ d) (q′ d))

  Bd↑⋆ : ∀ y {κ c w w′} → Le⋆ y w w′ → Bd⋆ y κ c w → Bd⋆ y κ c w′
  Bd↑⋆ lz {()}
  Bd↑⋆ (ls x) {inj₁ κ} (q , _) e = Bd↑⋆ x q e
  Bd↑⋆ (ls x) {inj₂ _} (q , b) e = ⊲ᴮ-tr (⊲ᴮ↑ q e) b
  Bd↑⋆ (ll f) {n , κ} q e = Bd↑⋆ (f n) (q n) e
  Bd↑⋆ (lΩ k g) {inj₁ _ , inj₁ κ} ((q , _) , _) e = Bd↑⋆ k q e
  Bd↑⋆ (lΩ k g) {inj₁ _ , inj₂ _} ((q , b) , _) e = ⊲ᴮ-tr (⊲ᴮ↑ q e) b
  Bd↑⋆ (lΩ k g) {inj₂ d , κ} (_ , q) e = Bd↑⋆ (g d) (q d) e

  cmp⋆ : ∀ y {κ c c′ w} → Bd⋆ y κ c w → Bd⋆ y κ c′ w → LgW⋆ y w → Pr⋆ y κ w c′ c ⊎ Pr⋆ y κ w c c′
  cmp⋆ lz {()}
  cmp⋆ (ls x) {inj₁ κ} e e′ (lw , _) = cmp⋆ x e e′ lw
  cmp⋆ (ls x) {inj₂ _} e e′ (lw , lb) = cmpB e e′ lw lb
  cmp⋆ (ll f) {n , κ} e e′ lw = cmp⋆ (f n) e e′ (lw n)
  cmp⋆ (lΩ k g) {inj₁ _ , inj₁ κ} e e′ ((lw , _) , _) = cmp⋆ k e e′ lw
  cmp⋆ (lΩ k g) {inj₁ _ , inj₂ _} e e′ ((lw , lb) , _) = cmpB e e′ lw lb
  cmp⋆ (lΩ k g) {inj₂ d , κ} e e′ (_ , lw) = cmp⋆ (g d) e e′ (lw d)

  LgE⋆ : (y : LH) (κ : Kᵉ (Lv y)) → Eᵉ (Lv y) κ → Set
  LgE⋆ lz () c
  LgE⋆ (ls x) (inj₁ κ) c = LgE⋆ x κ c
  LgE⋆ (ls x) (inj₂ _) c = LgB (cv x c)
  LgE⋆ (ll f) (n , κ) c = LgE⋆ (f n) κ c
  LgE⋆ (lΩ k g) (inj₁ _ , inj₁ κ) c = LgE⋆ k κ c
  LgE⋆ (lΩ k g) (inj₁ _ , inj₂ _) c = LgB (cv k c)
  LgE⋆ (lΩ k g) (inj₂ d , κ) c = LgE⋆ (g d) κ c

  lgBd⋆ : ∀ y {κ c w} → Bd⋆ y κ c w → LgW⋆ y w → LgE⋆ y κ c
  lgBd⋆ lz {()}
  lgBd⋆ (ls x) {inj₁ κ} e (lw , _) = lgBd⋆ x e lw
  lgBd⋆ (ls x) {inj₂ _} e (lw , lb) = lgB⊲ e lw lb
  lgBd⋆ (ll f) {n , κ} e lw = lgBd⋆ (f n) e (lw n)
  lgBd⋆ (lΩ k g) {inj₁ _ , inj₁ κ} e ((lw , _) , _) = lgBd⋆ k e lw
  lgBd⋆ (lΩ k g) {inj₁ _ , inj₂ _} e ((lw , lb) , _) = lgB⊲ e lw lb
  lgBd⋆ (lΩ k g) {inj₂ d , κ} e (_ , lw) = lgBd⋆ (g d) e (lw d)

  bot⋆ : (y : LH) (κ : Kᵉ (Lv y)) → Eᵉ (Lv y) κ
  bot⋆ lz ()
  bot⋆ (ls x) (inj₁ κ) = bot⋆ x κ
  bot⋆ (ls x) (inj₂ _) = z⁰
  bot⋆ (ll f) (n , κ) = bot⋆ (f n) κ
  bot⋆ (lΩ k g) (inj₁ _ , inj₁ κ) = bot⋆ k κ
  bot⋆ (lΩ k g) (inj₁ _ , inj₂ _) = z⁰
  bot⋆ (lΩ k g) (inj₂ d , κ) = bot⋆ (g d) κ

  botBd⋆ : ∀ y κ w → Bd⋆ y κ (bot⋆ y κ) w
  botBd⋆ lz ()
  botBd⋆ (ls x) (inj₁ κ) w = botBd⋆ x κ w
  botBd⋆ (ls x) (inj₂ _) w = z⊲ᴮ (cv x (w x))
  botBd⋆ (ll f) (n , κ) w = botBd⋆ (f n) κ w
  botBd⋆ (lΩ k g) (inj₁ _ , inj₁ κ) w = botBd⋆ k κ w
  botBd⋆ (lΩ k g) (inj₁ _ , inj₂ _) w = z⊲ᴮ (cv k (w k))
  botBd⋆ (lΩ k g) (inj₂ d , κ) w = botBd⋆ (g d) κ w
```

## §4 一切层号的并

同 `LFReTy.SL = sup LH (step ∘ Lv)`: 种类是 $(y, \kappa)$, $\kappa$ 是 `Lv (ls y)` 的种类 (`Lv y` 的旧种类与 $y$ 的新种类). **世界是 `GW` 本身**, 不是逐分量的积: 各分量读同一个 $w$.

```agda
K⋆ : Set
K⋆ = Σ LH (λ y → Kᵉ (Lv (ls y)))

E⋆ : K⋆ → Set
E⋆ κ = Eᵉ (Lv (ls (proj₁ κ))) (proj₂ κ)

SL⋆ : KS
SL⋆ = record
  { K = K⋆ ; E = E⋆ ; Wd = GW
  ; LgW = λ w → ∀ y → LgW⋆ (ls y) w
  ; _≤w_ = λ w w′ → ∀ y → Le⋆ (ls y) w w′
  ; ≤w-rf = λ y → rf⋆ (ls y)
  ; ≤w-tr = λ p q y → tr⋆ (ls y) (p y) (q y)
  ; Bd = λ κ c w → Bd⋆ (ls (proj₁ κ)) (proj₂ κ) c w
  ; Pr = λ κ w c c′ → Pr⋆ (ls (proj₁ κ)) (proj₂ κ) w c c′
  ; Bd↑ = λ {κ} q e → Bd↑⋆ (ls (proj₁ κ)) {proj₂ κ} (q (proj₁ κ)) e
  ; cmpK = λ {κ} e e′ lw → cmp⋆ (ls (proj₁ κ)) {proj₂ κ} e e′ (lw (proj₁ κ))
  ; LgE = λ κ → LgE⋆ (ls (proj₁ κ)) (proj₂ κ)
  ; lgBd = λ {κ} e lw → lgBd⋆ (ls (proj₁ κ)) {proj₂ κ} e (lw (proj₁ κ))
  ; bot = λ κ → bot⋆ (ls (proj₁ κ)) (proj₂ κ)
  ; botBd = λ κ w → botBd⋆ (ls (proj₁ κ)) (proj₂ κ) w }

cmpL⋆ : ∀ {a b L W} → a ⊲[ W ] L → b ⊲[ W ] L → LgW SL⋆ W → LgB L → (b ⊲[ W ] a) ⊎ (a ⊲[ W ] b)
cmpL⋆ = cmpB {SL⋆}
```

**每个层号进并: 种类与世界的对应.** 世界的对应是**恒等**.

```agda
kmS : ∀ y → KMatch (Lv⋆ y) SL⋆
kmS y = record { km = λ κ → y , inj₁ κ ; to = λ κ c → c ; fr = λ κ c → c ; fr-to = λ κ c → refl }

wmS : ∀ y → WMatch (Lv⋆ y) SL⋆ (kmS y)
wmS y = record { wm = λ w → w ; bd→ = λ e → e ; bd← = λ e → e ; lgw = λ l → proj₁ (l y) }

ιS : ∀ y → HB (Lv⋆ y) → HB SL⋆
ιS y hz = hz
ιS y (hs x) = hs (ιS y x)
ιS y (hl f) = hl (λ n → ιS y (f n))
ιS y (hΩ κ g) = hΩ (y , inj₁ κ) (λ c → ιS y (g c))

ιS-⊲ : ∀ {y a b} {w : GW} → a ⊲[ w ] b → ιS y a ⊲[ w ] ιS y b
ιS-⊲ hself = hself
ιS-⊲ (hsuc p) = hsuc (ιS-⊲ p)
ιS-⊲ (hlim n p) = hlim n (ιS-⊲ p)
ιS-⊲ (hLim e p) = hLim e (ιS-⊲ p)

Lg-ιS : ∀ y a → LgB a → LgB (ιS y a)
Lg-ιS y hz l = tt
Lg-ιS y (hs a) l = Lg-ιS y a l
Lg-ιS y (hl f) (st , l) = (λ n → ιS-⊲ (st n)) , (λ n → Lg-ιS y (f n) (l n))
Lg-ιS y (hΩ κ g) (mo , l) = (λ lw e e′ p → ιS-⊲ (mo (proj₁ (lw y)) e e′ p)) , (λ c lc → Lg-ιS y (g c) (l c lc))
```

## §5 相干: 界只看读回层

`lvl y κ`: 种类 $\kappa$ 的读回层 (同 `LFReTy.lvl`, 少了底的情形, 因为底是空的). 坐标类型就是读回层的形状 (`E-lvl`). **`glob`**: 界就是读回层的新种类在 $w$ 的那一层分量下的 `⊲`. 对 $y$ 与 $\kappa$ 递归, 每一步要么 `refl`, 要么归纳假设原样.

```agda
lvl : (y : LH) → Kᵉ (Lv y) → LH
lvl lz ()
lvl (ls x) (inj₁ κ) = lvl x κ
lvl (ls x) (inj₂ _) = x
lvl (ll f) (n , κ) = lvl (f n) κ
lvl (lΩ k g) (inj₁ _ , inj₁ κ) = lvl k κ
lvl (lΩ k g) (inj₁ _ , inj₂ _) = k
lvl (lΩ k g) (inj₂ d , κ) = lvl (g d) κ

E-lvl : ∀ y κ → Eᵉ (Lv y) κ ≡ H⁰ (Lv (lvl y κ))
E-lvl lz ()
E-lvl (ls x) (inj₁ κ) = E-lvl x κ
E-lvl (ls x) (inj₂ _) = refl
E-lvl (ll f) (n , κ) = E-lvl (f n) κ
E-lvl (lΩ k g) (inj₁ _ , inj₁ κ) = E-lvl k κ
E-lvl (lΩ k g) (inj₁ _ , inj₂ _) = refl
E-lvl (lΩ k g) (inj₂ d , κ) = E-lvl (g d) κ

cast : ∀ {A B : Set} → A ≡ B → A → B
cast refl a = a

glob : ∀ y κ c w → Bd⋆ y κ c w ≡ (cv (lvl y κ) (cast (E-lvl y κ) c) ⊲[ w ] cv (lvl y κ) (w (lvl y κ)))
glob lz () c w
glob (ls x) (inj₁ κ) c w = glob x κ c w
glob (ls x) (inj₂ _) c w = refl
glob (ll f) (n , κ) c w = glob (f n) κ c w
glob (lΩ k g) (inj₁ _ , inj₁ κ) c w = glob k κ c w
glob (lΩ k g) (inj₁ _ , inj₂ _) c w = refl
glob (lΩ k g) (inj₂ d , κ) c w = glob (g d) κ c w

globPr : ∀ y κ w c c′ → Pr⋆ y κ w c c′ ≡ (cv (lvl y κ) (cast (E-lvl y κ) c) ⊲[ w ] cv (lvl y κ) (cast (E-lvl y κ) c′))
globPr lz () w c c′
globPr (ls x) (inj₁ κ) w c c′ = globPr x κ w c c′
globPr (ls x) (inj₂ _) w c c′ = refl
globPr (ll f) (n , κ) w c c′ = globPr (f n) κ w c c′
globPr (lΩ k g) (inj₁ _ , inj₁ κ) w c c′ = globPr k κ w c c′
globPr (lΩ k g) (inj₁ _ , inj₂ _) w c c′ = refl
globPr (lΩ k g) (inj₂ d , κ) w c c′ = globPr (g d) κ w c c′
```

**推论 `cross`**: 并里任意两个种类, 读回层相等, 坐标经读回层对上, 就在**每一个**世界里界相同. 这是 `HtTowerNStage.no-wmatch` 与 `CohWNeg.no-cross` 否定的形状, 在 `SL⋆` 里对一切种类成立.

```agda
mvL : ∀ {ℓ ℓ′} → ℓ ≡ ℓ′ → H⁰ (Lv ℓ) → H⁰ (Lv ℓ′)
mvL refl h = h

same-lvl : ∀ {ℓ ℓ′} (p : ℓ ≡ ℓ′) {h : H⁰ (Lv ℓ)} {h′ : H⁰ (Lv ℓ′)} → mvL p h ≡ h′ → ∀ (w : GW) →
           (cv ℓ h ⊲[ w ] cv ℓ (w ℓ)) ≡ (cv ℓ′ h′ ⊲[ w ] cv ℓ′ (w ℓ′))
same-lvl refl refl w = refl

cross : ∀ {κ κ′ : K⋆} (p : lvl (ls (proj₁ κ)) (proj₂ κ) ≡ lvl (ls (proj₁ κ′)) (proj₂ κ′)) {c c′} →
        mvL p (cast (E-lvl (ls (proj₁ κ)) (proj₂ κ)) c) ≡ cast (E-lvl (ls (proj₁ κ′)) (proj₂ κ′)) c′ →
        ∀ w → Bd SL⋆ κ c w ≡ Bd SL⋆ κ′ c′ w
cross {κ} {κ′} p q w =
  trans (glob (ls (proj₁ κ)) (proj₂ κ) _ w) (trans (same-lvl p q w) (sym (glob (ls (proj₁ κ′)) (proj₂ κ′) _ w)))
```

**例子: `no-cross` 那一对在这里界相同.** 层号 $1$ (`ls lz`) 的新种类 (坐标是 `H⁰ (Lv 1)`, 读 `H₀`) 在并里的两个位置: 链上的 `κa = (1, new)`; 一个 $\Omega$-层号 `lΩ lz g` ($g$ 取常值 $2$) 的坐标 $0$ 分量里的拷贝 `κb`. 与 `CohWNeg` 的 `κ0⋆`, `κL` 同一种情形 (`sup` 的高度下标的分量里新造的拷贝), 这里界是同一个类型, `refl`.

```agda
gb : H⁰ (Lv lz) → LH
gb _ = ls (ls lz)

κa κb : K⋆
κa = ls lz , inj₂ tt
κb = lΩ lz gb , inj₁ (inj₂ z⁰ , inj₂ tt)

cross-ex : ∀ c w → Bd SL⋆ κa c w ≡ Bd SL⋆ κb c w
cross-ex c w = refl
```

## §6 塔与对角: `LFReTower` 照抄

`ofHB`: 高度读成层号 (同 `LFReTy.ofHB`, `node`). $\hat\Omega$: $\hat\Omega(h+1)$ 是层号 `ofHB h` 的新种类上的 $\Omega$-极限, 第 $c$ 支是 $\hat\Omega(h)$ 接上坐标 $c$ (经 `cv`, `ιS`). 合法: 一条对高度的一步定理 `Lg-Ω̂`. 用到的字段: 新种类的第一位置是 `HB (Lv⋆ y)` 在 $w$ 里的 `⊲` (定义相等), `ιS-⊲`, `⊞-⊲`.

```agda
node : (k : LH) (κ : Kᵉ (Lv k)) → (Eᵉ (Lv k) κ → LH) → LH
node lz () h
node (ls x) (inj₁ κ) h = node x κ h
node (ls x) (inj₂ _) h = lΩ x h
node (ll f) (n , κ) h = node (f n) κ h
node (lΩ k g) (inj₁ _ , inj₁ κ) h = node k κ h
node (lΩ k g) (inj₁ _ , inj₂ _) h = lΩ k h
node (lΩ k g) (inj₂ d , κ) h = node (g d) κ h

ofHB : HB SL⋆ → LH
ofHB hz = lz
ofHB (hs h) = ls (ofHB h)
ofHB (hl f) = ll (λ n → ofHB (f n))
ofHB (hΩ (k , inj₂ _) g) = lΩ k (λ c → ofHB (g c))
ofHB (hΩ (k , inj₁ κ) g) = node k κ (λ c → ofHB (g c))

ν : LH → K SL⋆
ν y = y , inj₂ tt

Ω̂ : HB SL⋆ → HB SL⋆
Ω̂ hz = hs hz
Ω̂ (hs h) = hΩ (ν (ofHB h)) (λ c → Ω̂ h ⊞ ιS (ofHB h) (cv (ofHB h) c))
Ω̂ (hl f) = hl (λ n → Ω̂ (f n))
Ω̂ (hΩ κ g) = hΩ κ (λ c → Ω̂ (g c))

Ω̂-suc : ∀ {W} h → Ω̂ h ⊲[ W ] Ω̂ (hs h)
Ω̂-suc {W} h = hLim (botBd SL⋆ (ν (ofHB h)) W) (⊞-fst (Ω̂ h) hz)

Ω̂-⊲ : ∀ {x y W} → x ⊲[ W ] y → Ω̂ x ⊲[ W ] Ω̂ y
Ω̂-⊲ hself = hself
Ω̂-⊲ (hsuc {b = b} p) = ⊲ᴮ-tr (Ω̂-⊲ p) (Ω̂-suc b)
Ω̂-⊲ (hlim n p) = hlim n (Ω̂-⊲ p)
Ω̂-⊲ (hLim e p) = hLim e (Ω̂-⊲ p)

Lg-Ω̂ : ∀ h → LgB h → LgB (Ω̂ h)
Lg-Ω̂ hz l = tt
Lg-Ω̂ (hs h) l =
  (λ {W} lw e e′ p → ⊞-⊲ (Ω̂ h) (ιS-⊲ {ofHB h} {w = W} p)) ,
  (λ c lc → Lg-⊞ (Ω̂ h) (ιS (ofHB h) (cv (ofHB h) c)) (Lg-Ω̂ h l) (Lg-ιS (ofHB h) (cv (ofHB h) c) lc))
Lg-Ω̂ (hl f) (st , l) = (λ n → Ω̂-⊲ (st n)) , (λ n → Lg-Ω̂ (f n) (l n))
Lg-Ω̂ (hΩ κ g) (mo , l) = (λ lw e e′ p → Ω̂-⊲ (mo lw e e′ p)) , (λ c lc → Lg-Ω̂ (g c) (l c lc))
```

塔 `tw n` ($\hat\Omega^n(0)$), 对角 **`Λ`**, 不动点的形状, 第 $n$ 个不动点.

```agda
tw : ℕ → HB SL⋆
tw zero = hz
tw (suc n) = Ω̂ (tw n)

tw-st : ∀ {W} n → tw n ⊲[ W ] tw (suc n)
tw-st zero = z⊲ᴮ (hs hz)
tw-st (suc n) = Ω̂-⊲ (tw-st n)

Lg-tw : ∀ n → LgB (tw n)
Lg-tw zero = tt
Lg-tw (suc n) = Lg-Ω̂ (tw n) (Lg-tw n)

Λ : HB SL⋆
Λ = hl tw

Lg-Λ : LgB Λ
Lg-Λ = (λ n → tw-st n) , Lg-tw

fix-form : Ω̂ Λ ≡ hl (λ n → tw (suc n))
fix-form = refl

it : HB SL⋆ → ℕ → HB SL⋆
it b zero = b
it b (suc n) = it b n ⊞ Ω̂ (it b n)

Lg-it : ∀ b → LgB b → ∀ n → LgB (it b n)
Lg-it b l zero = l
Lg-it b l (suc n) = Lg-⊞ (it b n) (Ω̂ (it b n)) (Lg-it b l n) (Lg-Ω̂ (it b n) (Lg-it b l n))

fix : HB SL⋆ → HB SL⋆
fix b = hl (it b)

Lg-fix : ∀ b → LgB b → LgB (fix b)
Lg-fix b l = (λ n → ⊞-fst (it b n) (Ω̂ (it b n))) , Lg-it b l

Λn : ℕ → HB SL⋆
Λn zero = Λ
Λn (suc n) = fix (hs (Λn n))

Lg-Λn : ∀ n → LgB (Λn n)
Lg-Λn zero = Lg-Λ
Lg-Λn (suc n) = Lg-fix (hs (Λn n)) (Lg-Λn n)
```
