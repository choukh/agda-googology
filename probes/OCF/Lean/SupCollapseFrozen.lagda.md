# 冻结 sup 分量更新的实际折叠变体

本实验从 `Fold1Fold` 复制定义与证明，仅改 `liftL` 的坍缩分支：
原 `updAt` 换为恒等世界，其合法性证明换为输入合法性。不是重写，
也不称新强度。保留后继层自身更新；只冻结穿过 sup 的更新。
下面原有说明中的“换界”若涉及 sup 分量，应读成此变体不执行换界；
代码为准。`Φ-lg` 的条件仍是合法世界与 `Lg*` 输入，不是任意输入。
值是否保持须由独立验收确定。没有改变旧模块。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.SupCollapseFrozen where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If
open import OCF.Lean.Fold1Base
```

## §1 ℕ-极限层的分量: 留下还是递归; 输入一侧的世界 `ext`

```agda
lgk : ∀ {f : ℕ → Cd} → LgB (hl f) → ∀ k → LgB (f k)
lgk lm k = proj₂ lm k

-- 分量 f k 与目标 t 都在 lim f 之下: 公共上界 lim f
cmpk : ∀ {f : ℕ → Cd} → LgB (hl f) → ∀ {t n} → t ⊲ f n → ∀ k → (t ⊲ f k) ⊎ (f k ⊲ t)
cmpk lm p k = cmpB (hlim k hself) (hlim _ p) tt lm

extC : ∀ {x t} → (t ⊲ x → Wd (Lv x)) → Wd (Lv t) → (t ⊲ x) ⊎ (x ⊲ t) → Wd (Lv x)
extC rec v (inj₁ p′) = rec p′
extC rec v (inj₂ q) = sub q v

ext : ∀ m (lm : LgB m) t (pt : t ⊲ m) → Wd (Lv t) → Wd (Lv m) → Wd (Lv m)
ext _ lm _ hself v W = v
ext (hs x) lm t (hsuc p) v W = ext x lm t p v (proj₁ W) , proj₂ W
ext (hl f) lm t (hlim n p) v W = λ k → extC (λ p′ → ext (f k) (lgk lm k) t p′ v (W k)) v (cmpk lm p k)
ext _ _ _ (hLim {κ = ()} _ _) _ _

extLg : ∀ m lm t pt {v W} → LgW* (ℓT t) v → LgW* (ℓT m) W → LgW* (ℓT m) (ext m lm t pt v W)
extLg _ lm _ hself lv lW = lv
extLg (hs x) lm t (hsuc p) lv lW = extLg x lm t p lv (proj₁ lW) , proj₂ lW
extLg (hl f) lm t (hlim n p) {v} {W} lv lW = λ k → go k (cmpk lm p k) (λ p′ → extLg (f k) (lgk lm k) t p′ lv (lW k))
  where
  go : ∀ k r → (∀ p′ → LgW* (ℓT (f k)) (ext (f k) (lgk lm k) t p′ v (W k))) →
       LgW* (ℓT (f k)) (extC (λ p′ → ext (f k) (lgk lm k) t p′ v (W k)) v r)
  go k (inj₁ p′) h = h p′
  go k (inj₂ q) h = lgSub q lv
extLg _ _ _ (hLim {κ = ()} _ _) _ _
```

## §2 种类的视图

`Vw m t X κ`: 第 $m$ 层的种类 $\kappa$ 对目标 $t$ 的视图, $X$ 是输入一侧的世界 (`ext`). **留** `kp`: 第 $t$ 层的种类 $\kappa'$ 与坐标的搬运 `fr`, 界, `Pr`, 坐标合法沿它搬运. **坍缩** `co`: 坐标是第 $x$ 层的高度 (`to`), $x\lhd m$; 世界里的界 `rd`, 换界 `upd`; 界之下的坐标在界的第一位置 (`cBd`), 合法的高度是合法坐标 (`cLg`), 合法世界的界合法 (`cRd`), 换成合法的界仍是合法世界 (`cUp`).

```agda
data Vw (m t : Cd) (X : Wd (Lv t) → Wd (Lv m) → Wd (Lv m)) (κ : K (Lv m)) : Set where
  kp : (κ′ : K (Lv t)) (fr : E (Lv t) κ′ → E (Lv m) κ) →
       (∀ {v W c} → Bd (Lv m) κ c (X v W) → Σ (E (Lv t) κ′) (λ d → (fr d ≡ c) × Bd (Lv t) κ′ d v)) →
       (∀ {v W d} → Bd (Lv t) κ′ d v → Bd (Lv m) κ (fr d) (X v W)) →
       (∀ {v W d d′} → Pr (Lv t) κ′ v d d′ → Pr (Lv m) κ (X v W) (fr d) (fr d′)) →
       (∀ {d} → LgE* (ℓT t) κ′ d → LgE* (ℓT m) κ (fr d)) → Vw m t X κ
  co : (x : Cd) → x ⊲ m → (to : HB (Lv x) → E (Lv m) κ) (rd : Wd (Lv m) → HB (Lv x))
       (upd : Wd (Lv m) → HB (Lv x) → Wd (Lv m)) →
       (∀ {v W c} → Bd (Lv m) κ c (X v W) → Bd (Lv m) κ (to (rd W)) (X v W) × Pr (Lv m) κ (X v W) c (to (rd W))) →
       (∀ {e} → Lg* (ℓT x) e → LgE* (ℓT m) κ (to e)) →
       (∀ {W} → LgW* (ℓT m) W → Lg* (ℓT x) (rd W)) →
       (∀ {W e} → LgW* (ℓT m) W → Lg* (ℓT x) e → LgW* (ℓT m) (upd W e)) → Vw m t X κ

liftS : ∀ {x t} {X : Wd (Lv t) → Wd (Lv x) → Wd (Lv x)} {κ} → Vw x t X κ →
        Vw (hs x) t (λ v W → X v (proj₁ W) , proj₂ W) (inj₁ κ)
liftS (kp κ′ fr a b c d) =
  kp κ′ fr (λ {v} {W} e → a {v} {proj₁ W} e) (λ {v} {W} e → b {v} {proj₁ W} e) (λ {v} {W} e → c {v} {proj₁ W} e) d
liftS (co y py to rd upd a b c d) =
  co y (hsuc py) to (λ W → rd (proj₁ W)) (λ W e → upd (proj₁ W) e , proj₂ W)
     (λ {v} {W} e → a {v} {proj₁ W} e) b (λ lW → c (proj₁ lW)) (λ lW le → d (proj₁ lW) le , proj₂ lW)

liftL : ∀ {f : ℕ → Cd} {t} {Y : ∀ i → Wd (Lv t) → Wd (Lv (f i)) → Wd (Lv (f i))} {k κ} → Vw (f k) t (Y k) κ →
        Vw (hl f) t (λ v W i → Y i v (W i)) (k , κ)
liftL {k = k} (kp κ′ fr a b c d) =
  kp κ′ fr (λ {v} {W} e → a {v} {W k} e) (λ {v} {W} e → b {v} {W k} e) (λ {v} {W} e → c {v} {W k} e) d
liftL {f} {k = k} (co y py to rd upd a b c d) =
  co y (hlim k py) to (λ W → rd (W k)) (λ W e → W)
     (λ {v} {W} e → a {v} {W k} e) b (λ lW → c (lW k))
     (λ lW le → lW)

vwC : ∀ {x t} {rec : t ⊲ x → Wd (Lv t) → Wd (Lv x) → Wd (Lv x)} κ r →
      (∀ p′ → Vw x t (rec p′) κ) → Vw x t (λ v w → extC (λ p′ → rec p′ v w) v r) κ
vwC κ (inj₁ p′) h = h p′
vwC κ (inj₂ q) h =
  kp (liftK q κ) (frK q κ) (λ {v} {W} {c} b → toK q κ c , ftK q κ c , bdUp q κ b)
     (λ b → bdDn q κ b) (λ p → prDn q κ p) (λ l → lgDn q κ l)

vw : ∀ m lm t pt κ → Vw m t (ext m lm t pt) κ
vw _ lm _ hself κ = kp κ (λ d → d) (λ {v} {W} {c} b → c , refl , b) (λ b → b) (λ p → p) (λ l → l)
vw (hs x) lm t (hsuc p) (inj₂ _) =
  co x (hsuc hself) (λ e → e) proj₂ (λ W e → proj₁ W , e) (λ b → hself , b) (λ l → l) proj₂ (λ lW le → proj₁ lW , le)
vw (hs x) lm t (hsuc p) (inj₁ κ) = liftS (vw x lm t p κ)
vw (hl f) lm t (hlim n p) (k , κ) =
  liftL {f} {Y = λ i v w → extC (λ p′ → ext (f i) (lgk lm i) t p′ v w) v (cmpk lm p i)}
    (vwC κ (cmpk lm p k) (λ p′ → vw (f k) (lgk lm k) t p′ κ))
vw _ _ _ (hLim {κ = ()} _ _) _
```

## §3 折叠

`Col`: 坍缩的链 (坐标 `ce`, 世界 `cw`, 输出点 `oo`, 输出的部分和 `oO`), 对类型一般. `ΦV`: 按视图给出 $\Omega$-结点的输出; `rec y py W′ e` 是 "在世界 $W'$ 里把分支 $g\,e$ 折到第 $y$ 层".

```agda
module Col {A X T : Set} (_⊕_ : X → X → X) (_⊕ᵗ_ : T → T → T) (W : A) (B : X) (upd : A → X → A)
           (kx : A → X → X) (kt : A → X → T) where
  ce : ℕ → X
  cw : ℕ → A
  ce zero = B
  ce (suc n) = ce n ⊕ kx (cw n) (ce n)
  cw zero = W
  cw (suc n) = upd W (ce (suc n))

  oo : ℕ → T
  oo n = kt (cw n) (ce n)

  oO : ℕ → T
  oO zero = oo 0
  oO (suc n) = oO n ⊕ᵗ oo (suc n)

ΦV : ∀ m (lm : LgB m) t (pt : t ⊲ m) (W : Wd (Lv m)) κ →
     (∀ y → y ⊲ m → Wd (Lv m) → E (Lv m) κ → HB (Lv y)) → Vw m t (ext m lm t pt) κ → HB (Lv t)
ΦV m lm t pt W κ rec (kp κ′ fr _ _ _ _) = hΩ κ′ (λ d → rec t pt W (fr d))
ΦV m lm t pt W κ rec (co x px to rd upd _ _ _ _) =
  hl (Col.oO _⊞_ _⊞_ W (rd W) upd (λ W′ e → rec x px W′ (to e)) (λ W′ e → rec t pt W′ (to e)))

Φ : ∀ m (lm : LgB m) t (pt : t ⊲ m) → Wd (Lv m) → HB (Lv m) → HB (Lv t)
Φ m lm t pt W hz = hs hz
Φ m lm t pt W (hs h) = hl (mul (Φ m lm t pt W h))
Φ m lm t pt W (hl f) = hl (λ n → Φ m lm t pt W (f n))
Φ m lm t pt W (hΩ κ g) = ΦV m lm t pt W κ (λ y py W′ e → Φ m lm y py W′ (g e)) (vw m lm t pt κ)
```

## §4 单调

`Φ-mono`: 在合法的目标世界 $v$ 与合法的输入世界 $W$ 里, 输入 $a\lhd c$ (世界 `ext v W`, $c$ 合法) 推出 $\Phi\,a\lhd\Phi\,c$ (世界 $v$). 对 $c$ 结构归纳. 坍缩的结点处: 界之下的坐标 $c'$ 与界 $e_0$ 在输入的单调下给出 $g\,c'\lhd g\,e_0$, 而输出的第 $0$ 项就是 $\Phi(g\,e_0)$. 留下的结点处: 界沿视图搬到目标世界.

```agda
monoV : ∀ m lm t pt {v W κ} (g : E (Lv m) κ → HB (Lv m)) (V : Vw m t (ext m lm t pt) κ) {a c} →
  LgW* (ℓT t) v → LgW* (ℓT m) W → Lg* (ℓT m) (hΩ κ g) →
  Bd (Lv m) κ c (ext m lm t pt v W) → a ⊲[ ext m lm t pt v W ] g c →
  (∀ {a′} e → Lg* (ℓT m) (g e) → a′ ⊲[ ext m lm t pt v W ] g e → Φ m lm t pt W a′ ⊲[ v ] Φ m lm t pt W (g e)) →
  Φ m lm t pt W a ⊲[ v ] ΦV m lm t pt W κ (λ y py W′ e → Φ m lm y py W′ (g e)) V
monoV m lm t pt g (kp κ′ fr kBd kBd⁺ kPr kLg) lv lW (mo , l) e p ih with kBd e
... | d , refl , bd = hLim bd (ih (fr d) (l (fr d) (kLg (lgBd* (ℓT t) bd lv))) p)
monoV m lm t pt {v} {W} g (co x px to rd upd cBd cLg cRd cUp) {c = c} lv lW (mo , l) e p ih =
  ⊲ᴮ-tr (ih c (l c (lgBd* (ℓT m) e lwx)) p)
    (⊲ᴮ-tr (ih (to (rd W)) (l _ (cLg (cRd lW))) (mo lwx e (proj₁ (cBd e)) (proj₂ (cBd e)))) (hlim 0 hself))
  where lwx = extLg m lm t pt lv lW

Φ-mono : ∀ m lm t pt {v W} → LgW* (ℓT t) v → LgW* (ℓT m) W → ∀ {a} c → Lg* (ℓT m) c →
         a ⊲[ ext m lm t pt v W ] c → Φ m lm t pt W a ⊲[ v ] Φ m lm t pt W c
Φ-mono m lm t pt lv lW c l hself = hself
Φ-mono m lm t pt lv lW (hs c) l (hsuc p) = ⊲ᴮ-tr (Φ-mono m lm t pt lv lW c l p) (hlim 0 hself)
Φ-mono m lm t pt lv lW (hl f) l (hlim n p) = hlim n (Φ-mono m lm t pt lv lW (f n) (proj₂ l n) p)
Φ-mono m lm t pt lv lW (hΩ κ g) l (hLim e p) =
  monoV m lm t pt g (vw m lm t pt κ) lv lW l e p (λ e′ le q → Φ-mono m lm t pt lv lW (g e′) le q)
```

## §5 合法

`Φ-lg`: 合法的输入世界里, 合法输入折出合法输出 (`Lg*`). ℕ-极限处用 `Φ-mono` (输入的步进在世界 `ext v W` 里); 留下的结点处, 输出的 $\Omega$-单调同样由 `Φ-mono` 给出; 坍缩处输出是部分和, 步进由 `⊞-fst` 给出, 每一点合法由坐标链合法 (对 $n$ 归纳: 界合法, 加上折到第 $x$ 层的输出合法) 给出.

```agda
lgV : ∀ m lm t pt {W κ} (g : E (Lv m) κ → HB (Lv m)) (V : Vw m t (ext m lm t pt) κ) →
  LgW* (ℓT m) W → Lg* (ℓT m) (hΩ κ g) →
  (∀ y py {W′} e → LgW* (ℓT m) W′ → Lg* (ℓT m) (g e) → Lg* (ℓT y) (Φ m lm y py W′ (g e))) →
  Lg* (ℓT t) (ΦV m lm t pt W κ (λ y py W′ e → Φ m lm y py W′ (g e)) V)
lgV m lm t pt {W} g (kp κ′ fr kBd kBd⁺ kPr kLg) lW (mo , l) ih =
  (λ {v} lv b b′ pr → Φ-mono m lm t pt lv lW (g (fr _)) (l _ (kLg (lgBd* (ℓT t) b′ lv)))
       (mo (extLg m lm t pt lv lW) (kBd⁺ {v} {W} b) (kBd⁺ {v} {W} b′) (kPr {v} {W} pr))) ,
  (λ d ld → ih t pt (fr d) lW (l (fr d) (kLg ld)))
lgV m lm t pt {W} g (co x px to rd upd cBd cLg cRd cUp) lW (mo , l) ih = (λ lv n → ⊞-fst _ _) , lO
  where
  open Col {Wd (Lv m)} {HB (Lv x)} {HB (Lv t)} _⊞_ _⊞_ W (rd W) upd
             (λ W′ e → Φ m lm x px W′ (g (to e))) (λ W′ e → Φ m lm t pt W′ (g (to e)))
  lE : ∀ n → Lg* (ℓT x) (ce n)
  lW′ : ∀ n → LgW* (ℓT m) (cw n)
  lE zero = cRd lW
  lE (suc n) = Lg*-⊞ (ℓT x) (ce n) _ (lE n) (ih x px (to (ce n)) (lW′ n) (l _ (cLg (lE n))))
  lW′ zero = lW
  lW′ (suc n) = cUp lW (lE (suc n))
  lo : ∀ n → Lg* (ℓT t) (oo n)
  lo n = ih t pt (to (ce n)) (lW′ n) (l _ (cLg (lE n)))
  lO : ∀ n → Lg* (ℓT t) (oO n)
  lO zero = lo 0
  lO (suc n) = Lg*-⊞ (ℓT t) (oO n) _ (lO n) (lo (suc n))

Φ-lg : ∀ m lm t pt {W} → LgW* (ℓT m) W → ∀ h → Lg* (ℓT m) h → Lg* (ℓT t) (Φ m lm t pt W h)
Φ-lg m lm t pt lW hz l = tt
Φ-lg m lm t pt {W} lW (hs h) l =
  (λ lv n → ⊞-fst (mul (Φ m lm t pt W h) n) _) , Lg*-mul (ℓT t) _ (Φ-lg m lm t pt lW h l)
Φ-lg m lm t pt lW (hl f) (st , l) =
  (λ lv n → Φ-mono m lm t pt lv lW (f (suc n)) (l (suc n)) (st (extLg m lm t pt lv lW) n)) ,
  (λ n → Φ-lg m lm t pt lW (f n) (l n))
Φ-lg m lm t pt lW (hΩ κ g) l =
  lgV m lm t pt g (vw m lm t pt κ) lW l (λ y py e lW′ le → Φ-lg m lm y py lW′ (g e) le)
```

## §6 值: 无 $\Omega$ 的输入

`Φ-≤`: 无 $\Omega$ 的输入上, 值关系 $\le$ 被保持 (对一切层号, 目标, 世界). 只用到 $0$, 后继, ℕ-极限三个子句 (否定一路 `NegFold1If` 指出: 这一条对任何满足这三个子句的函数都成立, 不约束 $\Omega$-结点的折法).

```agda
module _ {m lm t pt} {W : Wd (Lv m)} where
  one≤Φ : ∀ c → OF c → hs hz ≤ᵛ Φ m lm t pt W c
  one≤Φ hz o = s≤s z≤
  one≤Φ (hs c) o = ≤l 0 (one≤Φ c o)
  one≤Φ (hl f) o = ≤l 0 (one≤Φ (f 0) (o 0))
  one≤Φ (hΩ _ _) ()

  Φ-≤ : ∀ {a c} → OF a → OF c → a ≤ᵛ c → Φ m lm t pt W a ≤ᵛ Φ m lm t pt W c
  Φ-≤ {c = c} oa oc z≤ = one≤Φ c oc
  Φ-≤ oa oc (s≤s p) = l≤ (λ n → ≤l n (mul-≤ (Φ-≤ oa oc p) n))
  Φ-≤ oa oc (≤s p) = ≤l 0 (Φ-≤ oa oc p)
  Φ-≤ oa oc (l≤ h) = l≤ (λ n → Φ-≤ (oa n) oc (h n))
  Φ-≤ oa oc (≤l n p) = ≤l n (Φ-≤ oa (oc n) p)
  Φ-≤ oa () (≤Ω _ _)
  Φ-≤ () oc (Ω≤Ω _)
```

## §7 目标是第 $0$ 层时, 输入一侧的世界就是 $W$

目标 $t=0$ 时没有留下的种类 (第 $0$ 层没有种类), `ext tt W` 与 $W$ 的界逐种类相同. 这里对地板世界 `Wi` 写出 (接口 `Φ-mono` 用).

```agda
noK : ∀ {x} → x ⊲ hz → K (Lv x) → ⊥
noK hself ()

trBd : ∀ m lm (pt : hz ⊲ m) κ c → Bd (Lv m) κ c (Wi m) → Bd (Lv m) κ c (ext m lm hz pt tt (Wi m))
trBd _ lm hself () c b
trBd (hs x) lm (hsuc p) (inj₂ _) c b = trW (Lv x) (trBd x lm p) b
trBd (hs x) lm (hsuc p) (inj₁ κ) c b = trBd x lm p κ c b
trBd (hl f) lm (hlim n p) (k , κ) c b = go (cmpk lm p k) (λ p′ → trBd (f k) (lgk lm k) p′ κ c b)
  where
  go : ∀ r → (∀ p′ → Bd (Lv (f k)) κ c (ext (f k) (lgk lm k) hz p′ tt (Wi (f k)))) →
       Bd (Lv (f k)) κ c (extC (λ p′ → ext (f k) (lgk lm k) hz p′ tt (Wi (f k))) tt r)
  go (inj₁ p′) h = h p′
  go (inj₂ q) h = ⊥-elim (noK q κ)
trBd _ _ (hLim {κ = ()} _ _) _ _ _
```
