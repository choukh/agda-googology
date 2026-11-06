# 结构关系, 第二轮 (一): `Walk` 的位置与树的位置

> 不含记号, 不提折叠的动作与状态. 入口 [StrRel2](StrRel2.lagda.md). `SumOneFold.Walk` 与 `HtFeedFold.Walk` 的定义逐字同形 (世界都是 `CumReadCF.A`, 路径 `_⊲_`, 合法性 `Lg`), 对路径 $p:a\lhd b$ 递归, 不对树递归. 这里把它走到的层写出来:
>
> - **`WP b p lb`**: 沿 $p$ (合法性 `lb`) 走时被走到的位置, **逐句照 `Walk` 的三个子句定义**: `self` 没有位置; `suc p` 是 $p$ 的位置加上这一步; `lim n p` 是 $p$ 的位置 (进到 $f\,n$) 加上尾巴第 $m$ 段 (路径 `stp (m + n)`) 的位置. `Walk` 的输出在每个这样的位置上恰好调一次 `Run` (分支取在层 `lev`), 由定义的同形可见 (判断: 没有把 "输出是位置上的和" 写成定理).
> - **复合** (`wL`, `wR`, `wS`): `⊲-tr p q` 的位置就是 $p$ 的位置 (合法性取 `lg⊲ q lb`) 并上 $q$ 的位置, 层不变. 尾巴的类型不看里面的路径, 所以 `tailP`/`WRp` 的下标 $m+n$ 不用搬.
> - **桥** (`toW`, `fromW`): 沿 `sum-fst v x` 的位置与 `StrRelHead.Sp x` 一一对应, 层**定义性地相等到命题等式** ($\mathrm{lev}=v+\mathrm{pre}\,s$). 极限那一句: 树的第 $n$ 段是 `Walk` 尾巴的第 $m$ 段, $m+0=n$ (`+-identityʳ`, 只在 `toW` 一边要).
> - **`walkHead`**: 两格的坐标 $x\sqsubseteq_0 x'$, 起点 $v\le v'$ ⇒ 左格 `Walk` 的每个位置有右格 `Walk` 的位置, 层 $\le$, 领先量 $\mathrm{Adm}(c,c';v+x,v'+x')$. 这是 `KNest2` §3 要的 "桥 + 首对齐", 在 `HtFeedTree` 的第 0 层树上.
> - **`walkHeadᴼ`**: 同一件事, 在 `SumOneTree` 的第 0 层树上 (经 `MonoPortBridge.ofS`; 两种 `sum` 只在值上互相 $\le$). 路径与区间正是 `KNest2Glue.CellStep` 第 $n+1$ 格的: `sum-fst v d`, 格世界 `sum v d`.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel2Pos where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst; sym; trans)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; lg⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans)
open import OCF.Align.HtFeedTree using (D; hz; n0; n1; _⨾_; nl; ni; nκ; nw; sum; pt; sum-fst; Lg-sum; Lg-pt)
import OCF.Align.SumOneTree as SO
open import OCF.Align.StrRelDef {azero} tt using (_⊑₀_; preL)
open import OCF.Align.StrRelHead using (Sp; here; inl; inr; inn; inw; pre; headAdm; Adm; pt≡; ≡→≤; bmono)
```

## §0 翻译

`ofS` 与 `MonoPortBridge.ofS` 逐字相同; 本地写一份, 不导入 `MonoPortBridge` (它的闭包里有 `DValCanon`).

```agda
ofS : ∀ {V} → SO.D azero V → D hz V
ofS SO.n0 = n0
ofS SO.n1 = n1
ofS (x SO.⨾ y) = ofS x ⨾ ofS y
ofS (SO.nl d) = nl (λ n → ofS (d n))
ofS (SO.ni () u)
ofS (SO.nκ () u)
ofS (SO.nw p x) = nw p (ofS x)
```

## §1 位置

```agda
WP : ∀ b {a} → a ⊲ b → Lg b → Set
WP b C.self lb = ⊥
WP (asuc c) (C.suc p) lb = WP c p lb ⊎ ⊤
WP (alim f) (C.lim n p) lb = WP (f n) p (proj₂ lb n) ⊎ Σ ℕ (λ m → WP (f (suc (m + n))) (proj₁ lb (m + n)) (proj₂ lb (suc (m + n))))

lev : ∀ b {a} (p : a ⊲ b) lb → WP b p lb → A
lev b C.self lb ()
lev (asuc c) (C.suc p) lb (inj₁ w) = lev c p lb w
lev (asuc c) (C.suc p) lb (inj₂ _) = c
lev (alim f) (C.lim n p) lb (inj₁ w) = lev (f n) p (proj₂ lb n) w
lev (alim f) (C.lim n p) lb (inj₂ (m , w)) = lev (f (suc (m + n))) (proj₁ lb (m + n)) (proj₂ lb (suc (m + n))) w

-- 合法性证明相等时搬运, 层不变
levL : ∀ b {a} (p : a ⊲ b) {l l′} (e : l ≡ l′) (w : WP b p l) → lev b p l′ (subst (WP b p) e w) ≡ lev b p l w
levL b p refl w = refl
```

## §2 复合

```agda
wL : ∀ {a m} b (p : a ⊲ m) (q : m ⊲ b) lb (w : WP m p (lg⊲ q lb)) → Σ (WP b (⊲-tr p q) lb) (λ w′ → lev b (⊲-tr p q) lb w′ ≡ lev m p (lg⊲ q lb) w)
wL b p C.self lb w = w , refl
wL (asuc c) p (C.suc q) lb w = let (w′ , e) = wL c p q lb w in inj₁ w′ , e
wL (alim f) p (C.lim n q) lb w = let (w′ , e) = wL (f n) p q (proj₂ lb n) w in inj₁ w′ , e

wR : ∀ {a m} b (p : a ⊲ m) (q : m ⊲ b) lb (w : WP b q lb) → Σ (WP b (⊲-tr p q) lb) (λ w′ → lev b (⊲-tr p q) lb w′ ≡ lev b q lb w)
wR b p C.self lb ()
wR (asuc c) p (C.suc q) lb (inj₁ w) = let (w′ , e) = wR c p q lb w in inj₁ w′ , e
wR (asuc c) p (C.suc q) lb (inj₂ t) = inj₂ t , refl
wR (alim f) p (C.lim n q) lb (inj₁ w) = let (w′ , e) = wR (f n) p q (proj₂ lb n) w in inj₁ w′ , e
wR (alim f) p (C.lim n q) lb (inj₂ mw) = inj₂ mw , refl

wS : ∀ {a m} b (p : a ⊲ m) (q : m ⊲ b) lb (w : WP b (⊲-tr p q) lb) →
     Σ (WP m p (lg⊲ q lb)) (λ w₁ → lev m p (lg⊲ q lb) w₁ ≡ lev b (⊲-tr p q) lb w) ⊎ Σ (WP b q lb) (λ w₂ → lev b q lb w₂ ≡ lev b (⊲-tr p q) lb w)
wS b p C.self lb w = inj₁ (w , refl)
wS (asuc c) p (C.suc q) lb (inj₁ w) with wS c p q lb w
... | inj₁ (w₁ , e) = inj₁ (w₁ , e)
... | inj₂ (w₂ , e) = inj₂ (inj₁ w₂ , e)
wS (asuc c) p (C.suc q) lb (inj₂ t) = inj₂ (inj₂ t , refl)
wS (alim f) p (C.lim n q) lb (inj₁ w) with wS (f n) p q (proj₂ lb n) w
... | inj₁ (w₁ , e) = inj₁ (w₁ , e)
... | inj₂ (w₂ , e) = inj₂ (inj₁ w₂ , e)
wS (alim f) p (C.lim n q) lb (inj₂ mw) = inj₂ (inj₂ mw , refl)

lg-tr : ∀ {a m b} (p : a ⊲ m) (q : m ⊲ b) l → lg⊲ (⊲-tr p q) l ≡ lg⊲ p (lg⊲ q l)
lg-tr p C.self l = refl
lg-tr p (C.suc q) l = lg-tr p q l
lg-tr p (C.lim n q) l = lg-tr p q (proj₂ l n)
```

## §3 桥: `HtFeedTree` 的第 0 层树

```agda
lgFst : ∀ {V} b (y : D hz V) lb → lg⊲ (sum-fst b y) (Lg-sum b y lb) ≡ lb
lgFst b n0 lb = refl
lgFst b n1 lb = refl
lgFst b (x ⨾ y) lb =
  trans (lg-tr (sum-fst b x) (sum-fst (sum b x) y) (Lg-sum (sum b x) y (Lg-sum b x lb)))
        (trans (cong (lg⊲ (sum-fst b x)) (lgFst (sum b x) y (Lg-sum b x lb))) (lgFst b x lb))
lgFst b (nl d) lb = refl
lgFst b (ni () u) lb
lgFst b (nκ () u) lb
lgFst b (nw p x) lb = lgFst b x lb

Pw : ∀ {V} v (x : D hz V) lv → Set
Pw v x lv = WP (sum v x) (sum-fst v x) (Lg-sum v x lv)

levw : ∀ {V} v (x : D hz V) lv → Pw v x lv → A
levw v x lv = lev (sum v x) (sum-fst v x) (Lg-sum v x lv)

-- 第 k 段: 尾巴的类型族
Fk : ∀ {V} v (d : ℕ → D hz V) lv → ℕ → Set
Fk v d lv k = Pw (pt v d k) (d k) (Lg-pt v d k lv)

levF : ∀ {V} v (d : ℕ → D hz V) lv {k k′} (e : k ≡ k′) (w : Fk v d lv k) →
       levw (pt v d k′) (d k′) (Lg-pt v d k′ lv) (subst (Fk v d lv) e w) ≡ levw (pt v d k) (d k) (Lg-pt v d k lv) w
levF v d lv refl w = refl

toW : ∀ {V} v (x : D hz V) lv (s : Sp x) → Σ (Pw v x lv) (λ w → levw v x lv w ≡ sum v (pre s))
toW v n1 lv here = inj₂ tt , refl
toW v (x ⨾ y) lv (inl s) =
  let (w₀ , e₀) = toW v x lv s
      e = sym (lgFst (sum v x) y (Lg-sum v x lv))
      (w′ , e′) = wL (sum (sum v x) y) (sum-fst v x) (sum-fst (sum v x) y) (Lg-sum (sum v x) y (Lg-sum v x lv)) (subst (WP (sum v x) (sum-fst v x)) e w₀)
  in w′ , trans e′ (trans (levL (sum v x) (sum-fst v x) e w₀) e₀)
toW v (x ⨾ y) lv (inr s) =
  let (w₀ , e₀) = toW (sum v x) y (Lg-sum v x lv) s
      (w′ , e′) = wR (sum (sum v x) y) (sum-fst v x) (sum-fst (sum v x) y) (Lg-sum (sum v x) y (Lg-sum v x lv)) w₀
  in w′ , trans e′ e₀
toW v (nl d) lv (inn n s) =
  let (w₀ , e₀) = toW (pt v d n) (d n) (Lg-pt v d n lv) s
      e = sym (+-identityʳ n)
  in inj₂ (n , subst (Fk v d lv) e w₀) ,
     trans (levF v d lv e w₀) (trans e₀ (cong (λ t → sum t (pre s)) (pt≡ v d n)))
toW v (nw p x) lv (inw s) = toW v x lv s

fromW : ∀ {V} v (x : D hz V) lv (w : Pw v x lv) → Σ (Sp x) (λ s → levw v x lv w ≡ sum v (pre s))
fromW v n0 lv ()
fromW v n1 lv (inj₁ ())
fromW v n1 lv (inj₂ tt) = here , refl
fromW v (x ⨾ y) lv w with wS (sum (sum v x) y) (sum-fst v x) (sum-fst (sum v x) y) (Lg-sum (sum v x) y (Lg-sum v x lv)) w
... | inj₁ (w₁ , e₁) =
  let e = lgFst (sum v x) y (Lg-sum v x lv)
      (s , e₂) = fromW v x lv (subst (WP (sum v x) (sum-fst v x)) e w₁)
  in inl s , trans (sym e₁) (trans (sym (levL (sum v x) (sum-fst v x) e w₁)) e₂)
... | inj₂ (w₂ , e₁) = let (s , e₂) = fromW (sum v x) y (Lg-sum v x lv) w₂ in inr s , trans (sym e₁) e₂
fromW v (nl d) lv (inj₁ ())
fromW v (nl d) lv (inj₂ (m , w)) =
  let (s , e) = fromW (pt v d (m + 0)) (d (m + 0)) (Lg-pt v d (m + 0) lv) w
  in inn (m + 0) s , trans e (cong (λ t → sum t (pre s)) (pt≡ v d (m + 0)))
fromW v (ni () u) lv w
fromW v (nκ () u) lv w
fromW v (nw p x) lv w = let (s , e) = fromW v x lv w in inw s , e
```

## §4 首对齐落到 `Walk` 的位置上

```agda
admR : ∀ {α α′ β β′ ℓ ℓ′} → α ≡ β → α′ ≡ β′ → Adm α α′ ℓ ℓ′ → Adm β β′ ℓ ℓ′
admR refl refl h = h

walkHead : ∀ {V V′} {x : D hz V} {x′ : D hz V′} → x ⊑₀ x′ → ∀ {v v′} (lv : Lg v) (lv′ : Lg v′) → v ≤ v′ →
           (w : Pw v x lv) → Σ (Pw v′ x′ lv′) (λ w′ → (levw v x lv w ≤ levw v′ x′ lv′ w′) ×
                                                     Adm (levw v x lv w) (levw v′ x′ lv′ w′) (sum v x) (sum v′ x′))
walkHead {x = x} {x′} h {v} {v′} lv lv′ hv w =
  let (s , e) = fromW v x lv w
      (s′ , le , ad) = headAdm h hv s
      (w′ , e′) = toW v′ x′ lv′ s′
  in w′ , (≤-trans (≡→≤ e) (≤-trans le (≡→≤ (sym e′))) , admR (sym e) (sym e′) ad)
```

## §5 同一件事, 在 `SumOneTree` 的第 0 层树上

`SumOneTree` 的 `sum` 与 `HtFeedTree` 的 `sum` 经 `ofS` 只在值上互相 $\le$ (`sO≤`, `≤sO`; 极限处要逐项, 不用外延性), 所以层的关系是值的 $\approx$.

```agda
sO≤ : ∀ {V} {b b′} → b ≤ b′ → (x : SO.D azero V) → SO.sum b x ≤ sum b′ (ofS x)
ptO≤ : ∀ {V} {b b′} → b ≤ b′ → (d : ℕ → SO.D azero V) (n : ℕ) → SO.pt b d n ≤ pt b′ (λ m → ofS (d m)) n
sO≤ h SO.n0 = h
sO≤ h SO.n1 = s≤ h
sO≤ h (x SO.⨾ y) = sO≤ (sO≤ h x) y
sO≤ h (SO.nl d) = l≤ (λ n → ≤l n (ptO≤ h d n))
sO≤ h (SO.ni () u)
sO≤ h (SO.nκ () u)
sO≤ h (SO.nw p x) = sO≤ h x
ptO≤ h d zero = h
ptO≤ h d (suc n) = sO≤ (ptO≤ h d n) (d n)

≤sO : ∀ {V} {b b′} → b ≤ b′ → (x : SO.D azero V) → sum b (ofS x) ≤ SO.sum b′ x
≤ptO : ∀ {V} {b b′} → b ≤ b′ → (d : ℕ → SO.D azero V) (n : ℕ) → pt b (λ m → ofS (d m)) n ≤ SO.pt b′ d n
≤sO h SO.n0 = h
≤sO h SO.n1 = s≤ h
≤sO h (x SO.⨾ y) = ≤sO (≤sO h x) y
≤sO h (SO.nl d) = l≤ (λ n → ≤l n (≤ptO h d n))
≤sO h (SO.ni () u)
≤sO h (SO.nκ () u)
≤sO h (SO.nw p x) = ≤sO h x
≤ptO h d zero = h
≤ptO h d (suc n) = ≤sO (≤ptO h d n) (d n)

lgFstᴼ : ∀ {V} b (y : SO.D azero V) lb → lg⊲ (SO.sum-fst b y) (SO.Lg-sum b y lb) ≡ lb
lgFstᴼ b SO.n0 lb = refl
lgFstᴼ b SO.n1 lb = refl
lgFstᴼ b (x SO.⨾ y) lb =
  trans (lg-tr (SO.sum-fst b x) (SO.sum-fst (SO.sum b x) y) (SO.Lg-sum (SO.sum b x) y (SO.Lg-sum b x lb)))
        (trans (cong (lg⊲ (SO.sum-fst b x)) (lgFstᴼ (SO.sum b x) y (SO.Lg-sum b x lb))) (lgFstᴼ b x lb))
lgFstᴼ b (SO.nl d) lb = refl
lgFstᴼ b (SO.ni () u) lb
lgFstᴼ b (SO.nκ () u) lb
lgFstᴼ b (SO.nw p x) lb = lgFstᴼ b x lb

Pwᴼ : ∀ {V} v (x : SO.D azero V) lv → Set
Pwᴼ v x lv = WP (SO.sum v x) (SO.sum-fst v x) (SO.Lg-sum v x lv)

levᴼ : ∀ {V} v (x : SO.D azero V) lv → Pwᴼ v x lv → A
levᴼ v x lv = lev (SO.sum v x) (SO.sum-fst v x) (SO.Lg-sum v x lv)

Fkᴼ : ∀ {V} v (d : ℕ → SO.D azero V) lv → ℕ → Set
Fkᴼ v d lv k = Pwᴼ (SO.pt v d k) (d k) (SO.Lg-pt v d k lv)

levFᴼ : ∀ {V} v (d : ℕ → SO.D azero V) lv {k k′} (e : k ≡ k′) (w : Fkᴼ v d lv k) →
        levᴼ (SO.pt v d k′) (d k′) (SO.Lg-pt v d k′ lv) (subst (Fkᴼ v d lv) e w) ≡ levᴼ (SO.pt v d k) (d k) (SO.Lg-pt v d k lv) w
levFᴼ v d lv refl w = refl

_≈_ : A → A → Set
a ≈ b = (a ≤ b) × (b ≤ a)

≈≡ : ∀ {a b c} → a ≡ b → b ≈ c → a ≈ c
≈≡ refl h = h

pre≈ : ∀ {V} v (d : ℕ → SO.D azero V) n → SO.pt v d n ≈ sum v (preL (λ m → ofS (d m)) n)
pre≈ v d n = ≤-trans (ptO≤ (≤-refl v) d n) (≡→≤ (pt≡ v (λ m → ofS (d m)) n)) ,
             ≤-trans (≡→≤ (sym (pt≡ v (λ m → ofS (d m)) n))) (≤ptO (≤-refl v) d n)

bm≈ : ∀ {V} {a b} (y : D hz V) → a ≈ b → sum a y ≈ sum b y
bm≈ y (h , h′) = bmono y h , bmono y h′

sumO≈ : ∀ {V} v (x : SO.D azero V) → SO.sum v x ≈ sum v (ofS x)
sumO≈ v x = sO≤ (≤-refl v) x , ≤sO (≤-refl v) x

toWᴼ : ∀ {V} v (x : SO.D azero V) lv (s : Sp (ofS x)) → Σ (Pwᴼ v x lv) (λ w → levᴼ v x lv w ≈ sum v (pre s))
toWᴼ v SO.n1 lv here = inj₂ tt , (≤-refl v , ≤-refl v)
toWᴼ v (x SO.⨾ y) lv (inl s) =
  let (w₀ , e₀) = toWᴼ v x lv s
      e = sym (lgFstᴼ (SO.sum v x) y (SO.Lg-sum v x lv))
      (w′ , e′) = wL (SO.sum (SO.sum v x) y) (SO.sum-fst v x) (SO.sum-fst (SO.sum v x) y) (SO.Lg-sum (SO.sum v x) y (SO.Lg-sum v x lv))
                     (subst (WP (SO.sum v x) (SO.sum-fst v x)) e w₀)
  in w′ , ≈≡ (trans e′ (levL (SO.sum v x) (SO.sum-fst v x) e w₀)) e₀
toWᴼ v (x SO.⨾ y) lv (inr s) =
  let (w₀ , e₀) = toWᴼ (SO.sum v x) y (SO.Lg-sum v x lv) s
      (w′ , e′) = wR (SO.sum (SO.sum v x) y) (SO.sum-fst v x) (SO.sum-fst (SO.sum v x) y) (SO.Lg-sum (SO.sum v x) y (SO.Lg-sum v x lv)) w₀
      b = bm≈ (pre s) (sumO≈ v x)
  in w′ , ≈≡ e′ (≤-trans (proj₁ e₀) (proj₁ b) , ≤-trans (proj₂ b) (proj₂ e₀))
toWᴼ v (SO.nl d) lv (inn n s) =
  let (w₀ , e₀) = toWᴼ (SO.pt v d n) (d n) (SO.Lg-pt v d n lv) s
      e = sym (+-identityʳ n)
      b = bm≈ (pre s) (pre≈ v d n)
  in inj₂ (n , subst (Fkᴼ v d lv) e w₀) ,
     ≈≡ (levFᴼ v d lv e w₀) (≤-trans (proj₁ e₀) (proj₁ b) , ≤-trans (proj₂ b) (proj₂ e₀))
toWᴼ v (SO.nw p x) lv (inw s) = toWᴼ v x lv s

fromWᴼ : ∀ {V} v (x : SO.D azero V) lv (w : Pwᴼ v x lv) → Σ (Sp (ofS x)) (λ s → levᴼ v x lv w ≈ sum v (pre s))
fromWᴼ v SO.n0 lv ()
fromWᴼ v SO.n1 lv (inj₁ ())
fromWᴼ v SO.n1 lv (inj₂ tt) = here , (≤-refl v , ≤-refl v)
fromWᴼ v (x SO.⨾ y) lv w with wS (SO.sum (SO.sum v x) y) (SO.sum-fst v x) (SO.sum-fst (SO.sum v x) y) (SO.Lg-sum (SO.sum v x) y (SO.Lg-sum v x lv)) w
... | inj₁ (w₁ , e₁) =
  let e = lgFstᴼ (SO.sum v x) y (SO.Lg-sum v x lv)
      (s , e₂) = fromWᴼ v x lv (subst (WP (SO.sum v x) (SO.sum-fst v x)) e w₁)
  in inl s , ≈≡ (trans (sym e₁) (sym (levL (SO.sum v x) (SO.sum-fst v x) e w₁))) e₂
... | inj₂ (w₂ , e₁) =
  let (s , e₂) = fromWᴼ (SO.sum v x) y (SO.Lg-sum v x lv) w₂
      b = bm≈ (pre s) (sumO≈ v x)
  in inr s , ≈≡ (sym e₁) (≤-trans (proj₁ e₂) (proj₁ b) , ≤-trans (proj₂ b) (proj₂ e₂))
fromWᴼ v (SO.nl d) lv (inj₁ ())
fromWᴼ v (SO.nl d) lv (inj₂ (m , w)) =
  let (s , e) = fromWᴼ (SO.pt v d (m + 0)) (d (m + 0)) (SO.Lg-pt v d (m + 0) lv) w
      b = bm≈ (pre s) (pre≈ v d (m + 0))
  in inn (m + 0) s , (≤-trans (proj₁ e) (proj₁ b) , ≤-trans (proj₂ b) (proj₂ e))
fromWᴼ v (SO.ni () u) lv w
fromWᴼ v (SO.nκ () u) lv w
fromWᴼ v (SO.nw p x) lv w = let (s , e) = fromWᴼ v x lv w in inw s , e

admW : ∀ {α α′ β β′ ℓ ℓ′ ℓ₂ ℓ₂′} → α ≤ β → β′ ≤ α′ → ℓ₂ ≤ ℓ → ℓ′ ≤ ℓ₂′ → Adm α α′ ℓ ℓ′ → Adm β β′ ℓ₂ ℓ₂′
admW {β = β} {β′} h h′ g g′ (δ , a , b) =
  δ , ≤-trans g (≤-trans a (⊞m h)) , ≤-trans (⊞m h′) (≤-trans b g′)
  where
  open import OCF.Align.TLRuleSpec using (_⊞_; ⊞-mono)
  ⊞m : ∀ {x y} → x ≤ y → x ⊞ δ ≤ y ⊞ δ
  ⊞m h₁ = ⊞-mono h₁ (≤-refl δ)

walkHeadᴼ : ∀ {V V′} {d : SO.D azero V} {d′ : SO.D azero V′} → ofS d ⊑₀ ofS d′ → ∀ {v v′} (lv : Lg v) (lv′ : Lg v′) → v ≤ v′ →
            (w : Pwᴼ v d lv) → Σ (Pwᴼ v′ d′ lv′) (λ w′ → (levᴼ v d lv w ≤ levᴼ v′ d′ lv′ w′) ×
                                                       Adm (levᴼ v d lv w) (levᴼ v′ d′ lv′ w′) (SO.sum v d) (SO.sum v′ d′))
walkHeadᴼ {d = d} {d′} h {v} {v′} lv lv′ hv w =
  let (s , e) = fromWᴼ v d lv w
      (s′ , le , ad) = headAdm h hv s
      (w′ , e′) = toWᴼ v′ d′ lv′ s′
  in w′ , (≤-trans (proj₁ e) (≤-trans le (proj₂ e′)) ,
           admW (proj₂ e) (proj₁ e′) (proj₁ (sumO≈ v d)) (proj₂ (sumO≈ v′ d′)) ad)
```
