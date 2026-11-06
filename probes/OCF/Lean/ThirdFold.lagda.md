# Third (三): 同底折叠 (折叠与路径合一), 以 "洗法" 为参数

> 不含记号. 入口 [Third](Third.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延. 只导入 stdlib, [CRwBase](CRwBase.lagda.md), [ThirdIf](ThirdIf.lagda.md), [ThirdTw](ThirdTw.lagda.md).
>
> **这一篇做什么.** 在一个底 $U$ 与一个固定的合法世界 $w$ 里, 把第 $m$ 层折到第 $t$ 层 (`Φ`), 高度是值. 输入要带路径 `Gd`: 每个结点的种类有位置 (`Pos`); 新种类的分支只在 "坐标本身带路径" 处有要求 (`AdT`). 折叠同时返回输出与输出的路径 (折叠与路径定理合一): "在上" 与 "同层" 的链要把上一步的输出当坐标喂回去, 那些坐标要带路径, 所以路径定理不能写在折叠之后.
>
> **缺的东西写成模块参数 `San`.** 留下的新种类的输出分支要在**任意**坐标 $c$ 处有定义, 而输入只在带路径的坐标处能折. RecB 没有这件事 (可数高度, 位置与世界无关). 这里写成参数: 洗法 `san j : HB (Tw U j) → HB (Tw U j)`, 输出都带路径. 第 $j$ 层的地板 `tp j` 也是参数. 否定一路 `NegThirdIf.no-wash`: 洗法若保住输入的根种类, 推出 LPO; `pos-dec→LPO`: 判定 `Pos` 推出 LPO. 所以洗法**必须**在没有 `Pos` 的结点上换根种类, 而且不能判定是否有 `Pos`: 实例 `Er` (下面) 对穿过 $\Omega$-分量的种类一律不留. 这丢掉了那些种类 (见入口 §2).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Lean.CRwBase
module OCF.Lean.ThirdFold (U : KS) (w : Wd U) (lw : LgW U w) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Lean.ThirdIf
open import OCF.Lean.ThirdTw using (emb; frE; posE; along; frA; posA)
```

## §1 路径

```agda
T : HB U → KS
T = Tw U

infix 4 _⊲ᵘ_
_⊲ᵘ_ : HB U → HB U → Set
a ⊲ᵘ b = _⊲[_]_ {U} a w b

Gd : ∀ m → HB (T m) → Set
AdT : ∀ m κ → E (T m) κ → Set
Gd m hz = ⊤
Gd m (hs h) = Gd m h
Gd m (hl f) = ∀ n → Gd m (f n)
Gd m (hΩ κ g) = Pos U w m κ × (∀ e → AdT m κ e → Gd m (g e))
AdT hz κ e = ⊤
AdT (hs x) (inj₁ κ) e = AdT x κ e
AdT (hs x) (inj₂ _) e = Gd x e
AdT (hl f) (n , κ) e = AdT (f n) κ e
AdT (hΩ κ₀ g) (c , κ) e = AdT (g c) κ e

record San : Set where
  field
    san    : ∀ j → HB (T j) → HB (T j)
    gd-san : ∀ j c → Gd j (san j c)
    tp     : ∀ j → HB (T j)
    gd-tp  : ∀ j → Gd j (tp j)

Gd-⊞ : ∀ {m} a h → Gd m a → Gd m h → Gd m (a ⊞ h)
Gd-⊞ a hz pa ph = pa
Gd-⊞ a (hs h) pa ph = Gd-⊞ a h pa ph
Gd-⊞ a (hl f) pa ph = λ n → Gd-⊞ a (f n) pa (ph n)
Gd-⊞ a (hΩ κ g) pa (ev , ph) = ev , λ e x → Gd-⊞ a (g e) pa (ph e x)

GT : HB U → Set
GT m = Σ (HB (T m)) (Gd m)
```

## §2 累加 (带路径)

同 `CRwFold` 的 `mul`, `chain`, `Σ⁺`; 链的步函数只在带路径的值上有定义, 所以链返回值与路径.

```agda
module _ {m : HB U} where
  mulG : GT m → ℕ → GT m
  mulG x zero = x
  mulG x (suc n) = (proj₁ (mulG x n) ⊞ proj₁ x) , Gd-⊞ (proj₁ (mulG x n)) (proj₁ x) (proj₂ (mulG x n)) (proj₂ x)

  ΣG : (ℕ → GT m) → ℕ → GT m
  ΣG f zero = f 0
  ΣG f (suc n) = (proj₁ (ΣG f n) ⊞ proj₁ (f (suc n))) , Gd-⊞ (proj₁ (ΣG f n)) (proj₁ (f (suc n))) (proj₂ (ΣG f n)) (proj₂ (f (suc n)))

  chainG : GT m → (GT m → GT m) → ℕ → GT m
  chainG b k zero = k b
  chainG b k (suc n) =
    (proj₁ (chainG b k n) ⊞ proj₁ (k (bm n))) , Gd-⊞ (proj₁ (chainG b k n)) (proj₁ (k (bm n))) (proj₂ (chainG b k n)) (proj₂ (k (bm n)))
    where
    bm : ℕ → GT m
    bm n = (proj₁ b ⊞ proj₁ (chainG b k n)) , Gd-⊞ (proj₁ b) (proj₁ (chainG b k n)) (proj₂ b) (proj₂ (chainG b k n))

  limG : (ℕ → GT m) → GT m
  limG f = hl (λ n → proj₁ (f n)) , λ n → proj₂ (f n)
```

## §3 决定 (带路径)

```agda
module F (Sn : San) where
  open San Sn

  data Cg (m : HB U) (κ : K (T m)) : Set where
    bas : (κ₀ : K U) (to : E U κ₀ → E (T m) κ) → (∀ e → AdT m κ (to e)) → Cg m κ
    nw  : (j : HB U) → hs j ⊲ᵘ m → (to : HB (T j) → E (T m) κ) → (∀ c → Gd j c → AdT m κ (to c)) → Cg m κ

  cgS : ∀ {x κ} → Cg x κ → Cg (hs x) (inj₁ κ)
  cgS (bas κ₀ to ad) = bas κ₀ to ad
  cgS (nw j q to ad) = nw j (hsuc q) to ad

  cgL : ∀ {f} n {κ} → Cg (f n) κ → Cg (hl f) (n , κ)
  cgL n (bas κ₀ to ad) = bas κ₀ to ad
  cgL n (nw j q to ad) = nw j (hlim n q) to ad

  cgO : ∀ {κ₀ g} e {κ} → Bd U κ₀ e w → Cg (g e) κ → Cg (hΩ κ₀ g) (e , κ)
  cgO e b (bas κ₁ to ad) = bas κ₁ to ad
  cgO e b (nw j q to ad) = nw j (hLim b q) to ad

  cg : ∀ m κ → Pos U w m κ → Cg m κ
  cg hz κ _ = bas κ (λ e → e) (λ e → tt)
  cg (hs x) (inj₂ _) _ = nw x hself (λ c → c) (λ c p → p)
  cg (hs x) (inj₁ κ) p = cgS (cg x κ p)
  cg (hl f) (n , κ) p = cgL n (cg (f n) κ p)
  cg (hΩ κ₀ g) (e , κ) (b , p) = cgO e b (cg (g e) κ p)

  data Dg (X t : HB U) (A : Set) (P : A → Set) : Set where
    keep  : (κ′ : K (T t)) → Pos U w t κ′ → (fr : E (T t) κ′ → A) → (∀ c → P (fr c)) → Dg X t A P
    same  : (to : HB (T t) → A) → (∀ c → Gd t c → P (to c)) → Dg X t A P
    above : (i : HB U) → hs i ⊲ᵘ X → t ⊲ᵘ i → (to : HB (T i) → A) → (∀ c → Gd i c → P (to c)) → Dg X t A P

  -- 留下的新种类: 坐标先洗
  pickG : ∀ {X t i A P} (to : HB (T i) → A) → (∀ c → Gd i c → P (to c)) → hs i ⊲ᵘ X →
          (t ⊲ᵘ hs i) ⊎ (hs i ⊲ᵘ t) → Dg X t A P
  pickG {i = i} to ad u (inj₂ q) = keep (along q) (posA q) (λ c → to (san i (frA q c))) (λ c → ad _ (gd-san i (frA q c)))
  pickG {i = i} to ad u (inj₁ hself) = keep (inj₂ tt) tt (λ c → to (san i c)) (λ c → ad _ (gd-san i c))
  pickG to ad u (inj₁ (hsuc hself)) = same to ad
  pickG to ad u (inj₁ (hsuc q@(hsuc _))) = above _ u q to ad
  pickG to ad u (inj₁ (hsuc q@(hlim _ _))) = above _ u q to ad
  pickG to ad u (inj₁ (hsuc q@(hLim _ _))) = above _ u q to ad

  dcg : ∀ {m t κ} → t ⊲ᵘ m → LgB m → Cg m κ → Dg m t (E (T m) κ) (AdT m κ)
  dcg {t = t} pt lm (bas κ₀ to ad) = keep (emb t κ₀) (posE t κ₀) (λ c → to (frE t κ₀ c)) (λ c → ad _)
  dcg pt lm (nw j pj to ad) = pickG to ad pj (cmpB {U} pj pt lw lm)
```

## §4 折叠

```agda
  data AccC (m : HB U) : Set where
    acc : (∀ i → hs i ⊲ᵘ m → AccC i) → AccC m

  wfC : ∀ m → AccC m
  gC : ∀ m i → hs i ⊲ᵘ m → AccC i
  wfC m = acc (gC m)
  gC (hs x) .x hself = wfC x
  gC (hs x) i (hsuc p) = gC x i p
  gC (hl f) i (hlim n p) = gC (f n) i p
  gC (hΩ κ g) i (hLim b p) = gC (g _) i p

  lg↓ : ∀ {i X} → hs i ⊲ᵘ X → LgB X → LgB i
  lg↓ p l = lgB⊲ {U} (⊲ᴮ-tr {U} (hsuc hself) p) lw l

  ⊏⊑ : ∀ {i X} → hs i ⊲ᵘ X → i ⊲ᵘ X
  ⊏⊑ p = ⊲ᴮ-tr {U} (hsuc hself) p

  -- 结点: 三种决定一份; rec 折分支, dn 从第 i 层折到 t
  nodeG : ∀ {X t A P} → Dg X t A P → t ⊲ᵘ X → GT t →
          (rec : ∀ t′ → t′ ⊲ᵘ X → GT t′ → (c : A) → P c → GT t′) →
          (dn : ∀ i → hs i ⊲ᵘ X → t ⊲ᵘ i → GT i → GT t) → GT t
  nodeG {t = t} (keep κ′ p fr a) pt b rec dn =
    hΩ κ′ (λ c → proj₁ (rec t pt b (fr c) (a c))) , p , λ c _ → proj₂ (rec t pt b (fr c) (a c))
  nodeG {t = t} (same to a) pt b rec dn =
    limG (chainG b (λ b′ → rec t pt b′ (to (proj₁ b′)) (a _ (proj₂ b′))))
  nodeG (above i u q to a) pt b rec dn =
    dn i u q (limG (chainG (tp i , gd-tp i) (λ b′ → rec i (⊏⊑ u) b′ (to (proj₁ b′)) (a _ (proj₂ b′)))))

  Φ : ∀ m → AccC m → LgB m → ∀ t → t ⊲ᵘ m → GT t → (h : HB (T m)) → Gd m h → GT t
  Φ m a lm t pt b hz nd = hs hz , tt
  Φ m a lm t pt b (hs h) nd = limG (mulG (Φ m a lm t pt b h nd))
  Φ m a lm t pt b (hl f) nd = limG (ΣG (λ n → Φ m a lm t pt b (f n) (nd n)))
  Φ m (acc rs) lm t pt b (hΩ κ g) (ev , pg) = nodeG (dcg pt lm (cg m κ ev)) pt b
    (λ t′ pt′ b′ c pc → Φ m (acc rs) lm t′ pt′ b′ (g c) (pg c pc))
    (λ i u q x → Φ i (rs i u) (lg↓ u lm) t q b (proj₁ x) (proj₂ x))
```

## §5 形状给出的合法 (对一切 `San`)

```agda
  Sh : ∀ {S : KS} → HB S → Set
  Sh hz = ⊤
  Sh (hs h) = Sh h
  Sh {S} (hl f) = (∀ {v : Wd S} n → f n ⊲[ v ] f (suc n)) × (∀ n → Sh (f n))
  Sh (hΩ κ g) = ∀ c → Sh (g c)

  Sh-⊞ : ∀ {S : KS} (a b : HB S) → Sh a → Sh b → Sh (a ⊞ b)
  Sh-⊞ a hz sa sb = sa
  Sh-⊞ a (hs b) sa sb = Sh-⊞ a b sa sb
  Sh-⊞ a (hl f) sa (st , sf) = (λ n → ⊞-⊲ a (st n)) , (λ n → Sh-⊞ a (f n) sa (sf n))
  Sh-⊞ a (hΩ κ g) sa sg = λ c → Sh-⊞ a (g c) sa (sg c)

  ShG : ∀ {m} → GT m → Set
  ShG x = Sh (proj₁ x)

  Sh-mul : ∀ {m} (x : GT m) → ShG x → ShG (limG (mulG x))
  Sh-mul x s = (λ n → ⊞-fst (proj₁ (mulG x n)) (proj₁ x)) , go
    where go : ∀ n → Sh (proj₁ (mulG x n))
          go zero = s
          go (suc n) = Sh-⊞ _ (proj₁ x) (go n) s

  Sh-Σ : ∀ {m} (f : ℕ → GT m) → (∀ n → ShG (f n)) → ShG (limG (ΣG f))
  Sh-Σ f sf = (λ n → ⊞-fst (proj₁ (ΣG f n)) (proj₁ (f (suc n)))) , go
    where go : ∀ n → Sh (proj₁ (ΣG f n))
          go zero = sf 0
          go (suc n) = Sh-⊞ _ _ (go n) (sf (suc n))

  Sh-chain : ∀ {m} (b : GT m) (k : GT m → GT m) → (∀ b′ → ShG (k b′)) → ShG (limG (chainG b k))
  Sh-chain b k sk = (λ n → ⊞-fst (proj₁ (chainG b k n)) _) , go
    where go : ∀ n → Sh (proj₁ (chainG b k n))
          go zero = sk b
          go (suc n) = Sh-⊞ _ _ (go n) (sk _)

  Sh-node : ∀ {X t A P} (d : Dg X t A P) (pt : t ⊲ᵘ X) (b : GT t) rec dn →
    (∀ t′ pt′ b′ c pc → ShG (rec t′ pt′ b′ c pc)) → (∀ i u q x → ShG (dn i u q x)) → ShG (nodeG d pt b rec dn)
  Sh-node {t = t} (keep κ′ p fr a) pt b rec dn sr sd = λ c → sr t pt b (fr c) (a c)
  Sh-node {t = t} (same to a) pt b rec dn sr sd = Sh-chain b _ (λ b′ → sr t pt b′ (to (proj₁ b′)) (a _ (proj₂ b′)))
  Sh-node (above i u q to a) pt b rec dn sr sd = sd i u q _

  Sh-Φ : ∀ m a lm t pt b h nd → ShG (Φ m a lm t pt b h nd)
  Sh-Φ m a lm t pt b hz nd = tt
  Sh-Φ m a lm t pt b (hs h) nd = Sh-mul _ (Sh-Φ m a lm t pt b h nd)
  Sh-Φ m a lm t pt b (hl f) nd = Sh-Σ _ (λ n → Sh-Φ m a lm t pt b (f n) (nd n))
  Sh-Φ m (acc rs) lm t pt b (hΩ κ g) (ev , pg) = Sh-node (dcg pt lm (cg m κ ev)) pt b _ _
    (λ t′ pt′ b′ c pc → Sh-Φ m (acc rs) lm t′ pt′ b′ (g c) (pg c pc))
    (λ i u q x → Sh-Φ i (rs i u) (lg↓ u lm) t q b (proj₁ x) (proj₂ x))
```
